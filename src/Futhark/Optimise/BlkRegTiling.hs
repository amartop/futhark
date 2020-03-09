{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
-- | Perform a restricted form of block+register tiling corresponding to
--   the following pattern:
--     * a redomap is quasi-perfectly nested inside a kernel with at
--       least two parallel dimension (the perfectly nested restriction
--       is relaxed a bit to allow for SGEMM);
--     * all streamed arrays are one dimensional;
--     * all streamed arrays are variant to exacly one of the two
--       innermost parallel dimensions, and conversely for each of
--       the two innermost parallel dimensions, there is at least
--       one streamed array variant to it;
--     * the stream's result is a tuple of scalar values, which are
--       also the "thread-in-space" return of the kernel.
--   Test code can be found in "tests/mmm/sgemm.fut".
module Futhark.Optimise.BlkRegTiling
       ( mmmTiling2D )
       where
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Seq
import Data.List
import Data.Maybe

import Futhark.MonadFreshNames
import Futhark.Representation.Kernels
import Futhark.Tools
import Futhark.Transform.Substitute
import Futhark.Transform.Rename
import Futhark.Representation.AST.Attributes.Names

import Debug.Trace
import Futhark.Util.Pretty

type TileM = ReaderT (Scope Kernels) (State VNameSource)
type VarianceTable = M.Map VName Names

_pretty :: Pretty a => a -> String
_pretty = (++ "\n\n====================="
           ++ "========================="
           ++ "========================="
           ++ "=====================\n\n") . pretty




-- mmmTiling2D lvl space ts kbody
mmmTiling2D :: Stm Kernels -> TileM (Maybe (Stms Kernels, Stm Kernels))
mmmTiling2D stm@(Let pat aux (Op (SegOp (SegMap lvl@SegThread{} space ts old_kbody))))
  | KernelBody () kstms kres <- old_kbody,

    -- build the variance table, that records, for
    -- each variable name, the variables it depends on
    initial_variance <- M.map mempty $ scopeOfSegSpace space,
    variance <- varianceInStms initial_variance kstms,

    -- check that the code fits the pattern having:
    -- some `code1`, followed by one Screma SOAC, followed by some `code2`
    (code1, Just screma_stmt, code2)   <- matchCodeStreamCode kstms,
    Let pat_redomap aux_redomap (Op _) <- screma_stmt,

    -- checks that the Screma SOAC is actually a redomap and normalizes it
    Just (common_dim, arrs, (red_comm, red_lam, red_nes, map_lam)) <- isTileableRedomap screma_stmt,

    -- checks that the input arrays to redomap are variant to
    -- exactly one of the two innermost dimensions of the kernel
    Just arr_var_dims <- isInvarTo1of2InnerDims mempty space variance arrs,

    -- get the variables on which the first result of redomap depends on
    fst_res : _      <- patternValueElements pat_redomap,
    Just res_red_var <- M.lookup (patElemName fst_res) variance, -- variance of the reduce result

    -- we furthermore check that code1 is only formed by
    -- 1. statements that slice some globally-declared arrays
    --    to produce the input for the redomap, and
    -- 2. potentially some statements on which the redomap
    --    is independent; these are recorded in `code2'`
    Just (code2', arr_tab0) <- foldl (processIndirections (namesFromList arrs) res_red_var)
                                     (Just (Seq.empty, M.empty)) code1,

    -- we get the global-thread id for the two inner dimensions,
    --   as we are probably going to use it in code generation
    (gidx, width_B) : (gidy, height_A) : rem_outer_dims <- reverse $ unSegSpace space,

    -- sanity check that the reduce part is not missing
    not (null red_nes) = do

      ------------------------------------
      -- in this binder: outer seggroup --
      ------------------------------------
      (new_kernel, host_stms) <- runBinder $ do -- host code

        ty_name  <- nameFromString . pretty <$> newVName "Ty"
        tx_name  <- nameFromString . pretty <$> newVName "Tx"
        tk_name  <- nameFromString . pretty <$> newVName "Tk"
        ry_name  <- nameFromString . pretty <$> newVName "Ry"
        rx_name  <- nameFromString . pretty <$> newVName "Rx"

        gid_y    <- newVName "gid_y"
        gid_x    <- newVName "gid_x"
        gid_flat <- newVName "gid_flat"
        tid_y    <- newVName "tid_y"
        tid_x    <- newVName "tid_x"
        tid_flat <- newVName "tid_flat"

        ty <- letSubExp "Ty" $ Op $ SizeOp $ GetSize ty_name SizeTile
        tx <- letSubExp "Tx" $ Op $ SizeOp $ GetSize tx_name SizeTile
        tk <- letSubExp "Tk" $ Op $ SizeOp $ GetSize tk_name SizeTile
        ry <- letSubExp "Ry" $ Op $ SizeOp $ GetSize ty_name SizeTile
        rx <- letSubExp "Rx" $ Op $ SizeOp $ GetSize tx_name SizeTile

        tx_rx <- letSubExp "tx_rx" $ BasicOp $ BinOp (Mul Int32) tx rx -- tx rx
        ty_ry <- letSubExp "ty_ry" $ BasicOp $ BinOp (Mul Int32) ty ry -- ty ry

        group_size <- letSubExp "group_size" $ BasicOp $ BinOp (Mul Int32) ty tx

        grid_dimy <- letSubExp "grid_dimy" =<< eDivRoundingUp Int32 (eSubExp height_A) (eSubExp ty_ry)
        grid_dimx <- letSubExp "grid_dimx" =<< eDivRoundingUp Int32 (eSubExp width_B)  (eSubExp tx_rx)
        grid_size <- letSubExp "grid_size" $ BasicOp $ BinOp (Mul Int32) grid_dimx grid_dimy

        -----------------------------------------------------------
        -- in this binder: first segmap, zero-initializing cssss --
        -----------------------------------------------------------
        (ret_segmap0, stms_segmap0) <- runBinder $ do

          --------------------------------------------------
          -- in this binder: [ry][rx] replicate of zeroes --
          --------------------------------------------------
          ((shape_rep, ret_rep), stms_rep) <- runBinder $ do
            let shape_rep = Shape [ry, rx]
            tmp_zero <- letSubExp "tmp_zero" $ BasicOp $ SubExp $ intConst Int32 0
            rep      <- letSubExp "css"      $ BasicOp $ Replicate shape_rep tmp_zero
            return $ (shape_rep, [Returns ResultPrivate rep])
          ------------------------------------------------------------------------

          let rep_kbody = KernelBody () stms_rep ret_rep

          segmap0 <- letSubExp "cssss" $ Op $ SegOp $ SegMap
            (SegThread (Count grid_size) (Count group_size) SegNoVirt)
            (SegSpace tid_flat [(tid_y, ty), (tid_x, tx)])
            [Array int32 shape_rep $ NoUniqueness]
            rep_kbody

          return $ Returns ResultPrivate segmap0
        ------------------------------------------------------------------------------------

        let segmap0_body = KernelBody () stms_segmap0 [ret_segmap0]

        -----------------------------------
        -- in this binder: outer kk loop --
        -----------------------------------
        (ret_loop_kk, stms_loop_kk) <- runBinder $ do -- build first for loop

          kk       <- newVName "kk"
          kk_bound <- letSubExp "kk_bound" =<<
            eDivRoundingUp Int32 (eSubExp common_dim) (eSubExp tk)
          let loop_kk_form = ForLoop kk Int32 kk_bound []

          ---------------------------------------------------------------------------
          -- in this binder: kk loop body (copy from global to shared mem; k loop) --
          ---------------------------------------------------------------------------
          (ret_loop_kk_body, stms_loop_kk_body) <- runBinder $ do


            -- insert copies from global to shared mem of A and B
            -- a_shr <- copy ...
            -- b_shr <- copy ...

            k <- newVName "k"
            let loop_k_form = ForLoop k Int32 tk []

            ------------------------------------------------------------
            -- in this binder: k loop body (copying A and B from      --
            --                 global to shared mem; compute redomap) --
            ------------------------------------------------------------
            (ret_loop_k_body, stms_loop_k_body) <- runBinder $ do

              {--
              -- insert copies from shared to private mem of A and B
              let shape_asss = Shape [ry, k] -- dummy
              let shape_bsss = Shape [k, rx] -- dummy

              ------------------------------------------------------------------------------
              -- in this binder: build the segmap which copies from shared to private mem --
              ------------------------------------------------------------------------------
              (ret_segmap1, stms_segmap1) <- runBinder $ do
                foo <- letSubExp ...
                return ...

              let segmap1_body = KernelBody () stms_segmap1 [ret_segmap1]

              (asss, bssss) <- letSubExp "asss" $ Op $ SegOp $ SegMap
                               (SegThread (Count grid_size) (Count group_size) SegNoVirt)
                               (SegSpace tid_flat [(tid_y, ty), (tid_x, tx)]) -- TODO: can we reuse these?
                               [Array int32 shape_a_shr $ NoUniqueness,
                                Array int32 shape_b_shr $ NoUniqueness]
                               segmap1_body

              --}
              foo <- letSubExp "foo" $ BasicOp $ SubExp $ intConst Int32 42
              return foo
            ------------------------------------------------------------------------


            let loop_k_body = mkBody stms_loop_k_body [ret_loop_k_body]
            loop_k_init <- letSubExp "foo" $ BasicOp $ SubExp $ intConst Int32 43 -- dummy

            loop_k <- letSubExp "loop_k" $
                        DoLoop [] [{-(FParam ..., loop_k_init) -}] loop_k_form loop_k_body

            return loop_k -- mkBody needs a 'Result', not a KernelResult (ask Troels)
          ------------------------------------------------------------------------


          let loop_kk_body = mkBody stms_loop_kk_body [ret_loop_kk_body]

          -- let loop_kk_init = kernelResultSubExp ret_segmap0
          loop_kk_init <- letSubExp "foo" $ BasicOp $ SubExp $ intConst Int32 0 -- dummy

          loop_kk <- letSubExp "loop_kk" $
                       DoLoop [] [{- (FParam ..., loop_kk_init) -}] loop_kk_form loop_kk_body

          return $ Returns ResultPrivate ret_loop_kk_body -- TODO: what exactly to return here?
        ------------------------------------------------------------------------

        let all_stms = stms_segmap0 <> stms_loop_kk

        let new_kbody = KernelBody () all_stms
                                   [ret_loop_kk] -- dummy

        let ts' = ts -- for now, just ts - but should probably remain so?
        return $ Let pat aux $ Op $ SegOp $
                   SegMap (SegGroup (Count grid_size) (Count group_size) SegNoVirt)
                          (SegSpace gid_flat [(gid_y, grid_dimy), (gid_x, grid_dimx)])
                          ts' new_kbody
      ------------------------------------------------------------------------


      trace (">> host_stms:\n"  ++ _pretty host_stms ++
             ">> new_kernel:\n" ++ _pretty new_kernel)
            $ return $ Just (host_stms, new_kernel)



  where -- | There are two supported cases here:
        --   1. the statement is a slice that produces one of the
        --      arrays that are input to redomap. Also the streamed
        --      array is one dimensional. This info is accumulated
        --      in a table for later use.
        --   2. the redomap does not depend on this statement, hence
        --      this statement may as well come after redomap.
        processIndirections :: Names   -- input arrays to redomap
                            -> Names   -- variables on which the result of redomap depends on.
                            -> Maybe (Stms Kernels, M.Map VName (VName, Slice SubExp, Type))
                            -> Stm Kernels
                            -> Maybe (Stms Kernels, M.Map VName (VName, Slice SubExp, Type))
        processIndirections arrs _ acc (Let patt _ (BasicOp (Index arr_nm slc)))
          | Just (ss, tab) <- acc,
            [p] <- patternValueElements patt,
            (p_nm, p_tp) <- (patElemName p, patElemType p),
            nameIn p_nm arrs,
            Array _ (Shape [_]) _ <- p_tp =
              Just (ss, M.insert p_nm (arr_nm,slc,p_tp) tab)

        processIndirections _ res_red_var acc stm'@(Let patt _ _)
          | Just (ss, tab) <- acc,
            ps <- patternValueElements patt,
            all (\p -> not (nameIn (patElemName p) res_red_var)) ps =
              Just (ss Seq.|> stm', tab)
          | otherwise = Nothing

mmmTiling2D _ = trace "nej" $ return Nothing

---------------
--- HELPERS ---
---------------

-- | Translates an LParam to an FParam
translParamToFParam :: LParam Kernels -> FParam Kernels
translParamToFParam = fmap (`toDecl` Nonunique)

-- | Tries to identify the following pattern:
--   code followed by some Screma followed by more code.
matchCodeStreamCode :: Stms Kernels ->
                       ([Stm Kernels], Maybe (Stm Kernels), [Stm Kernels])
matchCodeStreamCode kstms =
  foldl (\acc stmt ->
            case (acc, stmt) of
              ((cd1, Nothing, cd2), Let _ _ (Op (OtherOp (Screma _ _ _)))) ->
               (cd1, Just stmt, cd2)

              ((cd1, Nothing, cd2), _) ->
               (cd1 ++ [stmt], Nothing, cd2)

              ((cd1, Just strm, cd2), _) ->
               (cd1, Just strm, cd2++[stmt])
        ) ([], Nothing, []) (stmsToList kstms)

isTileableRedomap :: Stm Kernels
         -> Maybe (SubExp, [VName],
                   (Commutativity, Lambda Kernels, [SubExp], Lambda Kernels))
isTileableRedomap stm
  | Op (OtherOp (Screma w form arrs)) <- stmExp stm,
    Just (reds, map_lam)              <- isRedomapSOAC form,
    Reduce red_comm red_lam red_nes   <- singleReduce reds,
    all (primType . rowType . paramType) $ lambdaParams red_lam,
    all (primType . rowType . paramType) $ lambdaParams map_lam,
    lambdaReturnType map_lam == lambdaReturnType red_lam, -- No mapout arrays.
    not (null arrs),
    all primType $ lambdaReturnType map_lam,
    all (primType . paramType) $ lambdaParams map_lam =
      Just (w, arrs, (red_comm, red_lam, red_nes, map_lam))
  | otherwise =
      Nothing

-- | Checks that all streamed arrays are variant to exacly one of
--   the two innermost parallel dimensions, and conversely, for
--   each of the two innermost parallel dimensions, there is at
--   least one streamed array variant to it. The result is the
--   number of the only variant parallel dimension for each array.
isInvarTo1of2InnerDims :: Names -> SegSpace -> VarianceTable -> [VName]
                       -> Maybe [Int]
isInvarTo1of2InnerDims branch_variant kspace variance arrs =
  let inner_perm0 = map varToOnly1of2InnerDims arrs
      inner_perm  = catMaybes inner_perm0
      ok1 = elem 0 inner_perm && elem 1 inner_perm
      ok2 = length inner_perm0 == length inner_perm
  in  if ok1 && ok2 then Just inner_perm else Nothing
  where varToOnly1of2InnerDims :: VName -> Maybe Int
        varToOnly1of2InnerDims arr = do
          (j, _) : (i, _) : _ <- Just $ reverse $ unSegSpace kspace
          let variant_to       = M.findWithDefault mempty arr variance
              branch_invariant = not $ nameIn j branch_variant ||
                                       nameIn i branch_variant
          if not branch_invariant then Nothing     -- if i or j in branch_variant; return nothing
          else if nameIn i variant_to && not (nameIn j variant_to) then Just 0
          else if nameIn j variant_to && not (nameIn i variant_to) then Just 1
          else Nothing

variantToOuterDim :: VarianceTable -> VName -> VName -> Bool
variantToOuterDim variance gid_outer nm =
  gid_outer == nm || (nameIn gid_outer $ M.findWithDefault mempty nm variance)

varianceInStms :: VarianceTable -> Stms Kernels -> VarianceTable
varianceInStms = foldl varianceInStm

-- just in case you need the Screma being treated differently than
-- by default; previously Cosmin had to enhance it when dealing with stream.
varianceInStm :: VarianceTable -> Stm Kernels -> VarianceTable
varianceInStm v0 bnd@(Let pat _ (Op (OtherOp (Screma _ _ _))))
  | Just (w, arrs, (red_comm, red_lam, red_nes, map_lam)) <- isTileableRedomap bnd =
    let v = defVarianceInStm v0 bnd
        red_args  = lambdaParams red_lam
        map_args  = lambdaParams map_lam
        card_red  = length red_nes
        acc_lam_f = take (card_red `quot` 2) red_args
        arr_lam_f = drop (card_red `quot` 2) red_args
        stm_lam   = (bodyStms $ lambdaBody map_lam) <> (bodyStms $ lambdaBody red_lam)

        v' = foldl' (\vacc (v_a, v_fm, v_fr_acc, v_fr_var) ->
                      let vrc   = oneName v_a <> M.findWithDefault mempty v_a vacc
                          vacc' = M.insert v_fm vrc vacc
                          vrc'  = oneName v_fm <> vrc
                      in  M.insert v_fr_acc (oneName v_fr_var <> vrc') $ M.insert v_fr_var vrc' vacc'
                    ) v $ zip4 arrs (map paramName map_args) (map paramName acc_lam_f) (map paramName arr_lam_f)
    in varianceInStms v' stm_lam
  | otherwise = defVarianceInStm v0 bnd

varianceInStm v0 bnd = defVarianceInStm v0 bnd

defVarianceInStm :: VarianceTable -> Stm Kernels -> VarianceTable
defVarianceInStm variance bnd =
  foldl' add variance $ patternNames $ stmPattern bnd
  where add variance' v = M.insert v binding_variance variance'
        look variance' v = oneName v <> M.findWithDefault mempty v variance'
        binding_variance = mconcat $ map (look variance) $ namesToList (freeIn bnd)

-- sufficientGroups :: [(VName, SubExp, VName, SubExp)] -- gspace
sufficientGroups :: MonadBinder m =>
                    [(VName, SubExp, VName, SubExp)] -- gspace
                 -> SubExp                           -- group_size
                 -> m (SubExp, SubExp)               -- (x, y) grid dimensions?
sufficientGroups gspace group_size = do

  groups_in_dims <- forM gspace $ \(_, gd, _, ld) ->
                      letSubExp "groups_in_dim" =<<
                      eDivRoundingUp Int32 (eSubExp gd) (eSubExp ld)

  num_groups <- letSubExp "num_groups" =<<
                foldBinOp (Mul Int32) (constant (1::Int32)) groups_in_dims

  num_threads <- letSubExp "num_threads" (BasicOp (BinOp (Mul Int32) num_groups group_size))

  traceM ("num_threads:\n" ++ _pretty num_threads ++
          "num_groups:\n"  ++ _pretty num_groups)

  return (num_threads, num_groups)



    -- not (null red_nes) = do
    --
    --   (new_kernel, host_stms) <- runBinder $ do
    --     ty_name  <- nameFromString . pretty <$> newVName "Ty"
    --     tx_name  <- nameFromString . pretty <$> newVName "Tx"
    --     tk_name  <- nameFromString . pretty <$> newVName "Tk"
    --     ry_name  <- nameFromString . pretty <$> newVName "Ry"
    --     rx_name  <- nameFromString . pretty <$> newVName "Rx"
    --     gid_y    <- newVName "gid_y"
    --     gid_x    <- newVName "gid_x"
    --     gid_flat <- newVName "gid_flat"
    --     tid_y    <- newVName "tid_y"
    --     tid_x    <- newVName "tid_x"
    --     tid_flat <- newVName "tid_flat"
    --
    --     ty    <- letSubExp "Ty" $ Op $ SizeOp $ GetSize ty_name SizeTile
    --     tx    <- letSubExp "Tx" $ Op $ SizeOp $ GetSize tx_name SizeTile
    --     tk    <- letSubExp "Tk" $ Op $ SizeOp $ GetSize tk_name SizeTile
    --     ry    <- letSubExp "Ry" $ Op $ SizeOp $ GetSize ty_name SizeTile
    --     rx    <- letSubExp "Rx" $ Op $ SizeOp $ GetSize tx_name SizeTile
    --     tx_rx <- letSubExp "tx_rx" $ BasicOp $ BinOp (Mul Int32) tx rx -- tx rx
    --     ty_ry <- letSubExp "ty_ry" $ BasicOp $ BinOp (Mul Int32) ty ry -- ty ry
    --
    --     group_size <- letSubExp "group_size" $ BasicOp $ BinOp (Mul Int32) ty tx
    --
    --     grid_dimy <- letSubExp "grid_dimy" =<< eDivRoundingUp Int32 (eSubExp height_A) (eSubExp ty_ry)
    --     grid_dimx <- letSubExp "grid_dimx" =<< eDivRoundingUp Int32 (eSubExp width_B)  (eSubExp tx_rx)
    --     grid_size <- letSubExp "grid_size" $ BasicOp $ BinOp (Mul Int32) grid_dimx grid_dimy
    --
    --     (skrald, init_stms) <- runBinder $ do
    --
    --       -- create first inner segmap_thread
    --       tmp_zero <- letSubExp "tmp_zero" $ BasicOp $ SubExp $ intConst Int32 0
    --
    --       let rep_exp = BasicOp $ Replicate (Shape [ry, rx]) tmp_zero
    --       rep <- letSubExp "zero_rep" rep_exp
    --
    --       rep_name <- newVName "rep"
    --       let rep_type = Array (IntType Int32) (Shape [ry, rx]) NoUniqueness
    --       let rep_pat  = Pattern [] [PatElem rep_name rep_type]
    --       let rep_aux  = StmAux (Certificates []) ()
    --       let rep_stm  = Let rep_pat rep_aux rep_exp
    --
    --       let init_kbody = KernelBody () (stmsFromList [rep_stm]) [Returns ResultPrivate rep]
    --
    --       let lvl_t   = SegThread (Count grid_size) (Count group_size) SegNoVirt
    --       let space_t = SegSpace tid_flat [(tid_y, ty), (tid_x, tx)]
    --
    --       zero_init_name <- newVName "zero_init"
    --       -- let zero_init_type = Array (IntType Int32) (Shape [ty, tx, ry, rx]) NoUniqueness
    --       -- let zero_init_pat  = Pattern [] [PatElem zero_init_name zero_init_type]
    --       -- let zero_init_aux  = StmAux (Certificates []) ()
    --       -- let zero_init_stm  = Let zero_init_pat zero_init_aux $ Op $ SegOp $ SegMap lvl_t space_t [rep_type] init_kbody
    --
    --       -- create outer segmap_group
    --
    --       -- let new_kbody = KernelBody () (stmsFromList [zero_init_stm]) [Returns ResultNoSimplify dummy_subexp]
    --
    --       kk       <- newVName "kk"
    --       -- kk_bound <- letSubExp "kk_bound" =<< eDivRoundingUp Int32 (eSubExp w) (eSubExp tk)
    --       -- let my_loop = ForLoop kk (Int32) kk_bound
    --
    --       trace (">> kk:\n"       ++ _pretty kk ++ "\n")
    --              --">> kk_bound:\n" ++ _pretty kk_bound)
    --             $ return $ Let pat aux $ Op $ SegOp $ SegMap lvl space [rep_type] old_kbody -- new_kbody
    --
    --     -- init_stms
    --     let lvl'   = SegGroup (Count grid_size) (Count group_size) SegNoVirt
    --     let space' = SegSpace gid_flat [(gid_y, grid_dimy), (gid_x, grid_dimx)]
    --
    --     dummy_subexp <- letSubExp "dummy" $ BasicOp $ SubExp $ intConst Int32 3
    --     let new_kbody = KernelBody () init_stms [Returns ResultNoSimplify dummy_subexp]
    --
    --     -- Let pat aux $ Op $ SegOp $ SegMap lvl' space' [rep_type] new_kbody
    --     return $ Let pat aux $ Op $ SegOp $ SegMap lvl' space' ts new_kbody
    --
    --   trace (
    --          -- ">> Variant arrays:\n"           ++ _pretty arr_var_dims ++
    --          -- ">> Variance table:\n"           ++ _pretty variance     ++
    --          -- ">> reduce result variance:\n"   ++ _pretty res_red_var  ++
    --          -- ">> indirect-slice table:\n"     ++ _pretty arr_tab0     ++
    --          -- ">> (gidx, m_X) : (gidy, m_Y)\n" ++ _pretty [(gidx, width_B), (gidy, height_A)] ++
    --          ">> kstms:\n"                    ++ _pretty kstms ++
    --          ">> stms:\n"                     ++ _pretty host_stms ++
    --          ">> stm':\n"                     ++ _pretty new_kernel)
    --
    --          $ return $ Just (host_stms, new_kernel)