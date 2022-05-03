-- TODO: Move to IR/Graph.hs at some point, for now keeping in Optimise/

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
module Futhark.Optimise.GraphRep (module Futhark.Optimise.GraphRep)
  -- (FusionEnvM,
  -- FusionEnv,
  -- runFusionEnvM,
  -- freshFusionEnv,
  -- mkDepGraph,
  -- isArray,
  -- pprg)
  where

import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
-- import Data.Maybe
import Futhark.IR.SOACS hiding (SOAC (..))
import qualified Futhark.IR.SOACS as Futhark
import qualified Futhark.Analysis.Alias as Alias
import Futhark.IR.Prop.Aliases
import qualified Futhark.Analysis.HORep.SOAC as H
import qualified Futhark.Optimise.Fusion.LoopKernel as LK

--import qualified Data.Graph.Inductive.Query.DFS as Q
import qualified Data.Graph.Inductive.Tree as G
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Dot
--import Futhark.IR.Pretty as PP
import qualified Futhark.Util.Pretty as PP

--import Debug.Trace

import Futhark.Builder (MonadFreshNames (putNameSource), VNameSource, getNameSource, modifyNameSource, blankNameSource, runBuilder, auxing, letBind)
--import Futhark.Pass
import Data.Foldable (foldlM)
import Control.Monad.State
import Futhark.Transform.Substitute (Substitute (substituteNames), Substitutable)
import Control.Monad.Reader (ReaderT (runReaderT))
import Foreign (bitReverse32)
import Futhark.MonadFreshNames (newName)
import Debug.Trace (trace)
import Data.Maybe (isJust, isNothing, mapMaybe)
import Futhark.Analysis.HORep.SOAC (lambda)
import System.Posix.Internals (puts)
-- import qualified Futhark.Analysis.HORep.MapNest as HM




-- TODO: Move to IR/Graph.hs at some point, for now keeping in Optimise/

-- SNode: Stm [InputTransforms] [OutputTransforms]
data EdgeT =
    Alias VName
  | InfDep VName
  | Dep VName
  | Cons VName
  | Fake VName
  | Res VName
  | ScanRed VName
  | TrDep VName
  deriving (Eq, Ord)

data NodeT =
    StmNode (Stm SOACS)
  | SoacNode (H.SOAC SOACS) [H.Input] (StmAux (ExpDec SOACS))
  | RNode VName
  | InNode VName
  | FinalNode [Stm SOACS] NodeT
  | IfNode (Stm SOACS) [(NodeT, [EdgeT])]
  | DoNode (Stm SOACS) [(NodeT, [EdgeT])]
  deriving (Eq)


getSoac :: NodeT -> Maybe (H.SOAC SOACS)
getSoac s = case s of
  SoacNode soac _ _ -> Just soac
  _ -> Nothing



getName :: EdgeT -> VName
getName edgeT = case edgeT of
  Alias vn -> vn
  InfDep vn -> vn
  Dep vn -> vn
  Cons vn -> vn
  Fake vn -> vn
  Res vn -> vn
  ScanRed vn -> vn
  TrDep   vn -> vn


setName :: VName -> EdgeT -> EdgeT
setName vn edgeT = case edgeT of
  Alias _ -> Alias vn
  InfDep _ -> InfDep vn
  Dep _ -> Dep vn
  Cons _ -> Cons vn
  Fake _ -> Fake vn
  Res _ -> Res vn
  ScanRed _ -> ScanRed vn
  TrDep   _ -> TrDep vn

inputFromPat :: Typed rep => Pat rep -> [H.Input]
inputFromPat = map H.identInput . patIdents

makeMap :: Ord a => [a] -> [b] -> M.Map a b
makeMap x y = M.fromList $ zip x y

fuseMaps :: Ord b => M.Map a b -> M.Map b c -> M.Map a c
fuseMaps m1 m2 = M.mapMaybe (`M.lookup` m2 ) m1

instance Substitute EdgeT where
  substituteNames m edgeT =
    let newName = substituteNames m (getName edgeT)
    in setName newName edgeT


instance Substitute NodeT where
  substituteNames m nodeT = case nodeT of
    StmNode stm -> StmNode (f stm)
    SoacNode so pat sa ->
      let so' = case so of
                H.Stream se sf la ses ins -> H.Stream (f se) (fStreamForm sf) (f la) (f ses) (f ins)
                H.Scatter se la ins x0 -> H.Scatter (f se) (f la) (f ins) (map fShape x0)
                H.Screma se sf ins -> H.Screma (f se) (fScremaForm sf) (f ins)
                H.Hist se hos la ins -> H.Hist (f se) (map fHistOp hos) (f la) (f ins)
      in SoacNode so' (f pat) (f sa)
    RNode vn -> RNode (f vn)
    InNode vn -> InNode (f vn)
    FinalNode stms nt -> FinalNode (map f stms) (f nt)
    IfNode stm nodes -> IfNode (f stm) (map f nodes)
    DoNode stm nodes -> DoNode (f stm) (map f nodes)
    where
      f :: Substitute a => a -> a
      f = substituteNames m
      fStreamForm :: StreamForm SOACS -> StreamForm SOACS
      fStreamForm (Parallel o comm lam0) =
        Parallel o comm (f lam0)
      fStreamForm s = s
      fShape (shp, i, vn) = (f shp, i, f vn)
      fHistOp (HistOp shape rf op_arrs nes op) =
          HistOp (f shape) (f rf) (f op_arrs) (f nes) (f op)
      fScremaForm (ScremaForm scans reds lam) = ScremaForm (map fScan scans) (map fRed reds) (f lam)
      fScan (Scan red_lam red_nes) = Scan (f red_lam) (map f red_nes)
      fRed (Reduce comm red_lam red_nes) = Reduce comm (f red_lam) (map f red_nes)



instance Show EdgeT where
  show (Dep vName) = "Dep " <> ppr vName
  show (InfDep vName) = "iDep " <> ppr vName
  show (Cons _) = "Cons"
  show (Fake _) = "Fake"
  show (Res _) = "Res"
  show (Alias _) = "Alias"
  show (ScanRed vName) = "SR " <> ppr vName
  show (TrDep vName) = "Tr " <> ppr vName

-- inputs could have their own edges - to facilitate fusion


-- nodeT_to_str
instance Show NodeT where
    show (StmNode (Let pat _ _)) = L.intercalate ", " $ map ppr $ patNames pat
    show (SoacNode _ pat _) = L.intercalate ", " $ map (ppr . H.inputArray) pat
    show (FinalNode stms nt) = show nt
    show (RNode name)  = ppr $ "Res: "   ++ ppr name
    show (InNode name) = ppr $ "Input: " ++ ppr name
    show (IfNode stm nodes) =  "If: " ++ L.intercalate ", " (map ppr $ getStmNames stm)
    show (DoNode stm nodes) =  "Do: " ++ L.intercalate ", " (map ppr $ getStmNames stm)


-- does the node acutally represent something in the program
-- (non-real nodes are not delayed-fused into other nodes)
isRealNode :: NodeT -> Bool
isRealNode RNode {} = False
isRealNode InNode {} = False
isRealNode _ = True


-- PrettyPrinter
ppr :: PP.Pretty m => m -> String
ppr k = PP.prettyDoc 80 (PP.ppr k)

pprg :: DepGraph -> String
pprg = showDot . fglToDotString . nemap show show

type DepNode = LNode NodeT
type DepEdge = LEdge EdgeT
type DepContext = Context NodeT EdgeT
type DepGraph = G.Gr NodeT EdgeT

-- depGenerators can be used to make edgeGenerators
type DepGenerator = Stm SOACS -> [VName]
-- for each node, what producer should the node depend on and what type
type EdgeGenerator = NodeT -> [(VName, EdgeT)]

-- monadic state environment for fusion.
data FusionEnv = FusionEnv
  {
    -- nodeMap :: M.Map VName [VName],
    vNameSource :: VNameSource,
    --reachabilityG :: G.Gr () (),
    producerMapping :: M.Map VName Node,
    fuseScans :: Bool
  }

freshFusionEnv :: FusionEnv
freshFusionEnv = FusionEnv {vNameSource = blankNameSource,
                            producerMapping = M.empty,
                            fuseScans = True}

newtype FusionEnvM a = FusionEnvM ( ReaderT
          (Scope SOACS)
          (State FusionEnv)
          a
    )
  deriving
    (
      Monad,
      Applicative,
      Functor,
      MonadState FusionEnv,
      HasScope SOACS,
      LocalScope SOACS
    )

instance MonadFreshNames FusionEnvM where
  getNameSource = gets vNameSource
  putNameSource source =
    modify (\env -> env {vNameSource = source})


runFusionEnvM ::  MonadFreshNames m => Scope SOACS -> FusionEnv -> FusionEnvM a -> m a
-- runFusionEnvM scope fenv (FusionEnvM a) = do
--   ns <- getNameSource
--   let r = runReaderT a scope
--   let fenv2 = fenv {vNameSource = ns}
--   return $ evalState r fenv2
runFusionEnvM scope fenv (FusionEnvM a) = modifyNameSource $ \src ->
    let x = runReaderT a scope in
    let (y,z) = runState x (fenv {vNameSource = src}) in
    (y, vNameSource z)
  -- modifyNameSource $



-- runFusionEnvM ::
--   MonadFreshNames m =>
--   FusionEnvM a ->
--   FusionEnv ->
--   m a
-- runFusionEnvM (FusionEnvM a) env =
--   modifyNameSource $ \src -> let (new_a, new_env) = runState a (env {vNameSource = src}) in (new_a, vNameSource new_env)


-- most everything is going to be a graph augmentation g -> M g.
-- these can be efficiently strung together using applyAugs
type DepGraphAug = DepGraph -> FusionEnvM DepGraph


-- transform functions for fusing over transforms
-- appendTransformations :: DepGraphAug
-- appendTransformations g = applyAugs (map appendTransform $ labNodes g) g


-- appendTransform :: DepNode -> DepGraphAug
-- appendTransform node_to_fuse g =
--   if gelem (nodeFromLNode node_to_fuse) g
--   then applyAugs (map (appendT node_to_fuse_id) fuses_to) g
--   else pure g
--   where
--     fuses_to = map nodeFromLNode $ input g node_to_fuse
--     node_to_fuse_id = nodeFromLNode node_to_fuse


-- --- Graph Construction ---

-- appendT :: Node -> Node -> DepGraphAug
-- appendT transformNode to g
--   | not (gelem transformNode g && gelem to g) = pure g
--   | outdeg g to == 1 =
--     case mapT (lFromNode g) (transformNode, to) of
--       (SNode (Let _ aux_1 exp_1) _, SNode s@(Let _ aux_2 (Op (Futhark.Screma sub_exp ouputs scremaform))) outTrans) ->
--         case (HOREPSOAC.transformFromExp (stmAuxCerts aux_1) exp_1, isMapSOAC scremaform) of
--           (Just (vn,transform), Just lam) -> do
--             let newNodeL = SNode s (outTrans HOREPSOAC.|> transform)
--             let newContext = mergedContext newNodeL (context g to) (context g transformNode)
--             contractEdge transformNode newContext g
--           _ -> pure g
--       _ -> pure g
--   | otherwise = pure g





      -- (SNode (Let _ aux exp) _ _) ->
      --   case transformFromExp (stmAuxCerts aux) exp of
      --     Just (vn, transform) ->
      --       if lnodeFromNode $ to g
      --       contractEdge transformNode (context to) g
      --     Nothing -> pure g


    -- gen_names_map :: [DepNode] -> M.Map VName Node
    -- gen_names_map s = M.fromList $ concatMap gen_dep_list s

-- the same as that fixed-point function in util
keepTrying :: DepGraphAug -> DepGraphAug
keepTrying f g =
  do
  r  <- f g
  r2 <- f r
  if equal r r2 then pure r
  else keepTrying f r2

emptyG2 :: [Stm SOACS] -> [VName] -> [VName] -> DepGraph
emptyG2 stms res inputs = mkGraph (label_nodes (snodes ++ rnodes ++ inNodes)) []
  where
    label_nodes = zip [0..]
    snodes = map StmNode stms
    rnodes = map RNode res
    inNodes= map InNode inputs

initGraph :: DepGraphAug
initGraph g = do
  _ <- makeMapping g
  addDepEdges g


isArray :: FParam SOACS -> Bool
isArray p = case paramDec p of
  Array {} -> True
  _ -> False

-- displayGraphFromfun ::  FunDef SOACS -> FusionEnvM String
-- displayGraphFromfun fun = do
--   g <- mkDepGraph stms resNames inputNames
--   let str = pprg g
--   strs <-  mapM displayGraphFromNode (nodes' g)
--   return $ str ++ concat strs
--   where
--     stms = (stmsToList . bodyStms . funDefBody) fun
--     resNames = namesFromRes ((bodyResult . funDefBody) fun)
--     inputNames = map paramName $ filter isArray (funDefParams  fun)
--     nodes' g' = mapMaybe (lab g') (nodes g')

-- -- runInnerDisplay :: DepGraph -> String
-- -- runInnerDisplay =


-- displayGraphFromNode :: NodeT -> FusionEnvM String
-- displayGraphFromNode n = case n of
--   SoacNode soac _ _ -> do
--     g <- mkDepGraph ((stmsToList . bodyStms . lambdaBody . lambda)soac) [] []
--     return $ pprg g
--   _ -> return ""




mkDepGraph :: [Stm SOACS] -> [VName] -> [VName] -> FusionEnvM DepGraph
mkDepGraph stms res inputs = do
  let g = emptyG2 stms res inputs
  _ <- makeMapping g
  addDepEdges g

addDepEdges :: DepGraphAug
addDepEdges = applyAugs
  [addDeps2,
  makeScanInfusible,
  addInfDeps,
  addCons,
  addExtraCons,
  addResEdges,
  addAliases,--, appendTransformations
  convertGraph, -- this one must be done last
  keepTrying addTransforms,
  iswim]

updateTrEdges :: Node -> DepGraphAug
updateTrEdges n1 g = do
  let (inc, _, nt, otg) = context g n1
  let relevantInc = relNodes inc
  let relevantOtg = relNodes otg
  let augs = map ( updateTrEdgesBetween  n1) relevantInc <>
             map (`updateTrEdgesBetween` n1) relevantOtg
  applyAugs augs g
  where
    relNodes :: Adj EdgeT ->[Node]
    relNodes adjs = map snd $ filter (isDep . fst) adjs

updateTrEdgesBetween :: Node -> Node -> DepGraphAug
updateTrEdgesBetween n1 n2 g = do
    let ns = map (getName . edgeLabel) $ filter (isDep . edgeLabel) $ edgesBetween g n1 n2
    let edgs = mapMaybe insEdge ns
    depGraphInsertEdges edgs =<< delLEdges edgs g
    where
      (nt1, nt2) = mapT (lab' . context g) (n1, n2)
      insEdge :: VName -> Maybe DepEdge
      insEdge name =
        if H.nullTransforms $ findTransformsBetween name nt1 nt2
        then Nothing
        else Just (n2, n1, TrDep name)

-- findTransFormFrom :: VName
transformsFromInputs :: VName -> [H.Input] -> H.ArrayTransforms
transformsFromInputs name1 is = case L.filter filterFun is of
  [] -> error "missing input from list"
  [x]-> H.inputTransforms x
  xs | [ts] <- L.nub (map H.inputTransforms xs) -> ts
  _ -> error "variable with differeing transformations"
  where
    filterFun (H.Input _ name2 _) = name1 == name2

nodeInputTransforms  :: VName -> NodeT -> H.ArrayTransforms
nodeInputTransforms  vname nodeT = case nodeT of
  SoacNode soac _ _ -> transformsFromInputs vname (H.inputs soac)
  _ -> H.noTransforms

nodeOutputTransforms :: VName -> NodeT -> H.ArrayTransforms
nodeOutputTransforms vname nodeT = case nodeT of
  SoacNode _ outs _ -> transformsFromInputs vname outs
  _ -> H.noTransforms


findTransformsBetween :: VName -> NodeT -> NodeT -> H.ArrayTransforms
findTransformsBetween vname n1 n2 =
  let outs = nodeOutputTransforms vname n1 in
  let ins  = nodeInputTransforms  vname n2 in
  outs <> ins

iswim :: DepGraphAug
iswim = mapAcrossWithSE f
  where
    f (n, lab) g =
      case lab of
        SoacNode soac ots aux -> do
          scope <- askScope
          maybeISWIM <- LK.tryFusion (LK.iswim Nothing soac H.noTransforms) scope
          case  maybeISWIM of
            Just (newSOAC, newts) ->
              trace (show $ H.width newSOAC) $
              updateNode n (const (Just $ SoacNode newSOAC (map (internalizeOutput . H.addTransforms newts) ots) aux)) g
                >>= updateTrEdges n
            Nothing -> pure g
        _ -> pure g

internalizeOutput :: H.Input -> H.Input
internalizeOutput i@(H.Input ts name tp) = H.Input ts name (H.inputType i)


makeMapping :: DepGraphAug
makeMapping g = do
  let mapping = M.fromList $ concatMap gen_dep_list (labNodes g)
  modify (\s -> s{producerMapping = mapping})
  pure g
    where
      gen_dep_list :: DepNode -> [(VName, Node)]
      gen_dep_list (i, node) = [(name, i) | name <- getOutputs node]


makeEdges :: [EdgeT] -> FusionEnvM [(Node, EdgeT)]
makeEdges edgs = do
  mapping <- gets producerMapping
  pure $ map (makeEdge mapping) edgs
  where
    makeEdge mp e =
      let node = mp M.! getName e in (node, e)


-- creates deps for the given nodes on the graph using the edgeGenerator
genEdges :: [DepNode] -> EdgeGenerator -> DepGraphAug
genEdges l_stms edge_fun g = do
  name_map <- gets producerMapping
  depGraphInsertEdges (concatMap (gen_edge name_map) l_stms) g
  where
    -- statements -> mapping from declared array names to soac index
    gen_edge ::  M.Map VName Node -> DepNode -> [LEdge EdgeT]
    gen_edge name_map (from, node) = [toLEdge (from,to) edgeT  | (dep, edgeT) <- edge_fun node,
                                              Just to <- [M.lookup dep name_map]]

delLEdges :: [DepEdge] -> DepGraphAug
delLEdges edgs g = pure $ foldl (flip ($)) g (map delLEdge edgs)

depGraphInsertEdges :: [DepEdge] -> DepGraphAug
depGraphInsertEdges edgs g = return $ insEdges edgs g

applyAugs :: [DepGraphAug] -> DepGraphAug
applyAugs augs g = foldlM (flip ($)) g augs

mapAcross :: (DepContext -> FusionEnvM DepContext) -> DepGraphAug
mapAcross f g =
  do
    let ns = nodes g
    foldlM (flip helper) g ns
    where
      helper :: Node -> DepGraphAug
      helper n g' = case match n g' of
        (Just c, g_new) ->
          do
            c' <- f c
            pure $ c' & g_new
        (Nothing, _) -> pure g'

--
mapAcrossNodeTs :: (NodeT -> FusionEnvM NodeT) -> DepGraphAug
mapAcrossNodeTs f = mapAcross f'
  where
    f' (ins, n, nodeT, outs) =
      do
        nodeT' <- f nodeT
        return (ins, n, nodeT', outs)


mapAcrossWithSE :: (DepNode -> DepGraphAug) -> DepGraphAug
mapAcrossWithSE f g =
  applyAugs (map f (labNodes g)) g



addTransforms :: DepGraphAug
addTransforms g =
  applyAugs (map helper ns) g
  where
    ns = nodes g
    helper :: Node -> DepGraphAug
    helper n g = case lab g n of
      Just (StmNode (Let pat aux exp))
        | Just (vn, transform) <- H.transformFromExp (stmAuxCerts aux) exp,
          [n'] <- L.nub $ suc g n,
          vn `notElem` map (getName . edgeLabel) (filter (\(a,_,_) -> a/=n) (inn g n')),
          Just (SoacNode soac outps aux2) <- lab g n',
          [trName] <- patNames pat
        -> do
          let sucNodes = pre g n
          let edgs = inn g n
          g' <- depGraphInsertEdges (map (\nd -> (nd, n', TrDep trName)) sucNodes) g
          let outps' = map (\inp -> if H.inputArray inp /= vn
                                    then inp
                                    else H.addTransform transform inp)  outps
          let mapping = makeMap [vn] [trName]
          let newNode = substituteNames mapping (SoacNode soac outps' (aux <> aux2))
          let ctx = mergedContext newNode (context g' n') (context g' n)
          contractEdge n ctx g'
      _ -> pure g
-- the context part could be nicer


-- addTransformToInputs :: H.Transform -> H.Input
-- (map (\inp -> if inputArray inp /= trName then inp
--                                   else addTransform transform inp))


substituteNamesInNodes :: M.Map VName VName -> [Node] -> DepGraphAug
substituteNamesInNodes submap ns =
  applyAugs (map (substituteNameInNode submap) ns)
  where
    substituteNameInNode :: M.Map VName VName -> Node -> DepGraphAug
    substituteNameInNode m n =
      updateNode n (Just . substituteNames m)

mapEdgeT :: (EdgeT -> EdgeT) -> DepEdge -> DepEdge
mapEdgeT f (n1, n2, e) = (n1, n2, f e)

substituteNamesInEdges :: M.Map VName VName -> [DepEdge] -> DepGraphAug
substituteNamesInEdges m edgs g =
  let edgs' = map (mapEdgeT (substituteNames m)) edgs in
  pure $ insEdges edgs' $ foldl (flip ($)) g (map delLEdge edgs)


updateNode :: Node -> (NodeT -> Maybe NodeT) -> DepGraphAug
updateNode n f g =
  case context g n of
    (ins, _, lab, outs) ->
      case f lab of
        Just newLab ->
          pure $ (&) (ins, n, newLab, outs) (delNode n g)
        Nothing -> pure g



nodeToSoacNode :: NodeT -> FusionEnvM NodeT
nodeToSoacNode n@(StmNode s@(Let pats aux op)) = case op of
  Op {} -> do
    maybeSoac <- H.fromExp op
    case maybeSoac of
      Right hsoac -> pure $ SoacNode hsoac (inputFromPat pats) aux
      Left H.NotSOAC -> pure n
  -- add if, loops, (maybe transformations)
  DoLoop {} -> -- loop-node
    pure $ DoNode s []
  If {} ->
    pure $ IfNode s []
  _ -> pure n
nodeToSoacNode n = pure n

convertGraph :: DepGraphAug
convertGraph = mapAcrossNodeTs nodeToSoacNode


--- /Graph Construction

--- Extracting Nodes/Edges ---

label :: DepNode -> NodeT
label = snd

-- do not use outside of edge generation
stmFromNode :: NodeT -> [Stm SOACS]
stmFromNode (StmNode x) = [x]
-- stmFromNode SoacNode {} = []
-- stmFromNode (FinalNode x nt) = x ++ stmFromNode nt
stmFromNode _ = []


-- possibly should be combined with the copy aliased
-- -- started this - but seems unreasonably hard.
-- finalizeStmFromNode :: NodeT -> FusionEnvM [Stm SOACS]
-- finalizeStmFromNode (SNode stm transforms)
--   | HOREPSOAC.nullTransforms transforms = pure [stm]
--   | otherwise = case stm of
--     Let pat sa (Op (Futhark.Screma size inputs  (ScremaForm [] [] lam))) ->
--       let names = patNames pat



--       pure []
--     _ -> error "transformations applied to non-map"
-- finalizeStmFromNode _ = pure []


nodeFromLNode :: DepNode -> Node
nodeFromLNode = fst

lNodeFromNode :: DepGraph -> Node -> DepNode
lNodeFromNode g n = labNode' (context g n)

lFromNode :: DepGraph -> Node -> NodeT
lFromNode g n = label $ lNodeFromNode g n


labFromEdge :: DepGraph -> DepEdge -> DepNode
labFromEdge g (n1, _, _) = lNodeFromNode g n1


depsFromEdge ::  DepEdge -> VName
depsFromEdge = getName . edgeLabel


input :: DepGraph -> DepNode -> [DepNode]
input g node = map (labNode' . context g) $ suc g $ nodeFromLNode node

output :: DepGraph -> DepNode -> [DepNode]
output g node = map (labNode' . context g) $ pre g $ nodeFromLNode node

edgesBetween :: DepGraph -> Node -> Node -> [DepEdge]
edgesBetween g n1 n2 = labEdges $ subgraph [n1,n2] g

--- Extracting Nodes/Edges ---

--- Augmentations ---

-- Utility func for augs
augWithFun :: EdgeGenerator -> DepGraphAug
augWithFun f g = genEdges (labNodes g) f g


toAlias :: DepGenerator -> EdgeGenerator
toAlias f stmt = map (\vname ->  (vname, Alias vname)) (concatMap f (stmFromNode stmt))

toDep :: DepGenerator -> EdgeGenerator
toDep f stmt = map (\vname ->  (vname, Dep vname)) (concatMap f (stmFromNode stmt))

addDeps2 :: DepGraphAug
addDeps2 = augWithFun $ toDep fusableInputs

toInfDep :: DepGenerator -> EdgeGenerator
toInfDep f stmt = map (\vname ->  (vname, InfDep vname)) (concatMap f (stmFromNode stmt))

addInfDeps :: DepGraphAug
addInfDeps = augWithFun $ toInfDep infusableInputs


addAliases :: DepGraphAug
addAliases = augWithFun $ toAlias aliasInputs
-- --unused?
-- addDeps :: DepGraphAug
-- addDeps = augWithFun getStmDeps

addCons :: DepGraphAug
addCons = augWithFun getStmCons


-- Merges two contexts
mergedContext :: (Eq b) => a -> Context a b -> Context a b -> Context a b
mergedContext mergedlabel (inp1, n1, _, out1) (inp2, n2, _, out2) =
  let new_inp = L.nub $ filter (\n -> snd n /= n1 && snd n /= n2) (inp1  `L.union` inp2) in
  let new_out = L.nub $ filter (\n -> snd n /= n1 && snd n /= n2) (out1 `L.union` out2)
  in (new_inp, n1, mergedlabel, new_out)
  -- update keys of gen n2 with n1


-- n1 remains
contractEdge :: Node -> DepContext -> DepGraphAug
contractEdge n2 cxt g = do
  let n1 = node' cxt

  mapping <- gets producerMapping
  let newMapping = fuseMaps mapping (makeMap [n2] [n1])


  -- -- Modify reachabilityG
  -- rg <- gets reachabilityG
  -- let newContext = mergedContext () (context rg n1) (context rg n2)
  -- modify (\s -> s {reachabilityG = (&) newContext $ delNodes [n1, n2] rg})

  pure $ (&) cxt $ delNodes [n1, n2] g
-- BUG: should modify name_mappings



-- extra dependencies mask the fact that consuming nodes "depend" on all other
-- nodes coming before it
addExtraCons :: DepGraphAug
addExtraCons g = depGraphInsertEdges new_edges g
  where
    new_edges = concatMap make_edge (labEdges g)
    make_edge :: DepEdge -> [DepEdge]
    make_edge (from, to, Cons cname) = [toLEdge (from, to2) (Fake cname) | (to2, _) <- filter (\(tonode,toedge)->
      tonode /= from
      && cname == getName toedge
      ) $ lpre g to]
    make_edge _ = []

addResEdges :: DepGraphAug
addResEdges = augWithFun getStmRes

-- and reduce, actually
makeScanInfusible :: DepGraphAug
makeScanInfusible g = return $ emap change_node_to_idep g
  where
    find_scan_results :: Stm SOACS -> [VName]
    find_scan_results  (Let pat _ (Op (Futhark.Screma  _ _ (ScremaForm scns rdcs _)))) =
      let resLen = scanResults scns + redResults rdcs
      in take resLen (patNames pat)
    -- find_scan_results  (Let pat _ (Op Futhark.Scatter {})) = patNames pat
    -- find_scan_results  (Let pat _ (Op Futhark.Hist {})) = patNames pat
    find_scan_results _ = []

    scan_res_set :: S.Set VName
    scan_res_set = S.fromList (concatMap find_scan_results (concatMap (stmFromNode . label) (labNodes g)))

    is_scan_res :: VName -> Bool
    is_scan_res name = S.member name scan_res_set

    change_node_to_idep :: EdgeT -> EdgeT
    change_node_to_idep (Dep name) = if is_scan_res name
      then ScanRed name
      else Dep name
    change_node_to_idep e = e

-- Utils for fusibility/infusibility
-- find dependencies - either fusable or infusable. edges are generated based on these


fusableInputs :: Stm SOACS -> [VName]
fusableInputs (Let _ _ expr) = fusableInputsFromExp expr

fusableInputsFromExp :: Exp SOACS -> [VName]
fusableInputsFromExp (If _ b1 b2 _) =
  concatMap fusableInputs (bodyStms b1) <> namesFromRes (bodyResult b1) <>
  concatMap fusableInputs (bodyStms b2) <> namesFromRes (bodyResult b2)
fusableInputsFromExp (DoLoop _ _ b1) =
  concatMap fusableInputs (bodyStms b1) <> namesFromRes (bodyResult b1)
fusableInputsFromExp (Op soac) = case soac of
  Futhark.Screma  _ is _     -> is
  Futhark.Hist    _ is _ _   -> is
  Futhark.Scatter _ is _ _   -> is
  Futhark.Stream  _ is _ _ _ -> is
fusableInputsFromExp _ = []

infusableInputs :: Stm SOACS -> [VName]
infusableInputs (Let _ aux expr) = infusableInputsFromExp expr ++ namesToList (freeIn aux)

infusableInputsFromExp :: Exp SOACS -> [VName]
infusableInputsFromExp (Op soac) = case soac of
  Futhark.Screma  e _ s  ->
    namesToList $ freeIn $ Futhark.Screma e [] s
  Futhark.Hist    e _ histops lam ->
    namesToList $ freeIn $ Futhark.Hist e [] histops lam
  Futhark.Scatter e _ lam other       ->
    namesToList $ freeIn $ Futhark.Scatter e [] lam other
  Futhark.Stream  a1 _ a3 a4 lam     ->
    namesToList $ freeIn $ Futhark.Stream a1 [] a3 a4 lam
-- infusableInputsFromExp op@(BasicOp x) = namesToList $ freeIn op
infusableInputsFromExp (If exp b1 b2 cond) =
  let emptyB = Body mempty mempty mempty :: Body SOACS in
  namesToList (freeIn exp
  <> freeIn cond)
  <> concatMap infusableInputs (bodyStms b1)
  <> concatMap infusableInputs (bodyStms b2)
infusableInputsFromExp (DoLoop exp loopform b1) =
  let emptyB = Body mempty mempty mempty :: Body SOACS in
  concatMap infusableInputs (bodyStms b1)
    <> namesToList (freeIn (DoLoop exp loopform emptyB))
infusableInputsFromExp op = namesToList $ freeIn op

aliasInputs :: Stm SOACS -> [VName]
aliasInputs op = case op of
  Let _ _ expr -> concatMap namesToList $ expAliases $ Alias.analyseExp mempty expr

--- /Augmentations ---

--- Inspecting Stms ---

getStmNames :: Stm SOACS -> [VName]
getStmNames s = case s of
  Let pat _ _ -> patNames pat


getStmCons :: EdgeGenerator
getStmCons (StmNode s) = zip names (map Cons names)
  where
    names =  namesToList . consumedInStm . Alias.analyseStm mempty $ s
getStmCons _ = []

getStmRes :: EdgeGenerator
getStmRes (RNode name) = [(name, Res name)]
getStmRes _ = []

-- TODO: Figure out where to put this
namesFromRes :: [SubExpRes] -> [VName]
namesFromRes = concatMap ((\case
     Var z -> [z]
     Constant _ -> []
  ) . resSubExp)
-- THIS IS BUGGY!!!! Constants are yeeted from lambda outputs after fusion


getOutputs :: NodeT -> [VName]
getOutputs node = case node of
  (StmNode stm) -> getStmNames stm
  (RNode _)   -> []
  (InNode name) -> [name]
  (IfNode stm nodes) -> getStmNames stm
  (DoNode stm nodes) -> getStmNames stm
  (FinalNode stms _) -> error "Final nodes cannot generate edges" -- concatMap getStmNames stms
  (SoacNode _ outputs _) -> map H.inputArray outputs

--- /Inspecting Stms ---


mapT :: (a -> b) -> (a,a) -> (b,b)
mapT f (a,b) = (f a, f b)


inputSetName ::  VName  -> H.Input -> H.Input
inputSetName vn (H.Input ts _ tp) = H.Input ts vn tp


isNotVarInput :: [H.Input] -> [H.Input]
isNotVarInput = filter (isNothing . H.isVarInput)

hasNoDifferingInputs :: [H.Input] -> [H.Input] -> Bool
hasNoDifferingInputs is1 is2 =
  let (vs1, vs2) = mapT isNotVarInput (is1, is2 L.\\ is1) in
  null $ vs1 `L.intersect` vs2

genOutTransformStms :: [H.Input] -> FusionEnvM (M.Map VName VName,Stms SOACS)
genOutTransformStms inps = do
  let inps' = isNotVarInput inps
  let names = map H.inputArray inps'
  newNames <- mapM newName names
  let newInputs = zipWith inputSetName newNames inps'
  let weirdScope = scopeOfPat (basicPat (map inputToIdent newInputs))
  (namesToRep, stms) <- localScope weirdScope  $ runBuilder (H.inputsToSubExps newInputs)
  pure (makeMap names newNames, substituteNames (makeMap namesToRep names) stms)

inputToIdent :: H.Input -> Ident
inputToIdent i@(H.Input _ vn tp) = Ident vn tp

-- inputToIdent2 :: H.Input -> Ident
-- inputToIdent2 i@(H.Input _ vn tp) = Ident vn (H.inputType i)

finalizeNode :: NodeT -> FusionEnvM [Stm SOACS]
finalizeNode nt = case nt of
  StmNode stm -> pure [stm]
  SoacNode soac outputs aux -> do -- TODO handle these
    (mapping, outputTrs) <- genOutTransformStms outputs
    (_, stms) <-  runBuilder $ do
      new_soac <- H.toSOAC soac
      auxing aux $ letBind (basicPat (map inputToIdent outputs)) $ Op new_soac
    return $ stmsToList (substituteNames mapping stms <> outputTrs)
  RNode vn  -> pure []
  InNode vn -> pure []
  DoNode stm lst -> do
    stmsNotFused <- mapM (finalizeNode . fst) lst
    pure $ concat stmsNotFused ++ [stm]
  IfNode stm lst -> do
    stmsNotFused <- mapM (finalizeNode . fst) lst
    pure $ concat stmsNotFused ++ [stm]
  FinalNode stms nt' -> do
    stms' <- finalizeNode nt'
    pure $ stms <> stms'


-- any (isNothing . isVarInput) outputs


-- contextFromLNode :: DepGraph -> DepNode -> DepContext
-- contextFromLNode g lnode = context g $ nodeFromLNode lnode

-- isRes :: (Node, EdgeT) -> Bool
-- isRes (_, Res _) = True
-- isRes _ = False

isDep :: EdgeT -> Bool
isDep (Dep _) = True
isDep (ScanRed _) = True
isDep _ = False

isInf :: (Node, Node, EdgeT) -> Bool
isInf (_,_,e) = case e of
  InfDep _ -> True
  Cons _ -> False -- you would think this sholud be true - but mabye this works
  Fake _ -> True -- this is infusible to avoid simultaneous cons/dep edges
  TrDep _ -> False -- lets try this
  _ -> False

isCons :: EdgeT -> Bool
isCons (Cons _) = True
isCons _ = False

isScanRed :: EdgeT -> Bool
isScanRed (ScanRed _) = True
isScanRed _ = False

isTrDep :: EdgeT -> Bool
isTrDep (TrDep _) = True
isTrDep _ = False
