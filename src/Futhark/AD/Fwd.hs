{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.AD.Fwd (fwdADEntryPoints) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import qualified Data.Map as M
import Data.Sequence (Seq (..))
import Futhark.AD.Derivatives
import Futhark.Analysis.PrimExp.Convert
import Futhark.Binder
import Futhark.Construct
import Futhark.IR.SOACS
import Futhark.Pass

data REnv = REnv
  { tans :: M.Map VName VName,
    envScope :: Scope SOACS
  }

newtype ADM a = ADM (ReaderT REnv (State VNameSource) a)
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadReader REnv,
      MonadFreshNames
    )

instance HasScope SOACS ADM where
  askScope = asks envScope

instance LocalScope SOACS ADM where
  localScope scope = local $ \env -> env {envScope = scope <> envScope env}

runADM :: MonadFreshNames m => ADM a -> REnv -> m a
runADM (ADM m) renv =
  modifyNameSource $ runState $ runReaderT m renv

tanVName :: VName -> ADM VName
tanVName v = newVName (baseString v <> "_tan")

zeroTan :: Type -> ADM SubExp
zeroTan (Prim t) = return $ constant $ blankPrimValue t

class TanBinder a where
  mkTan :: a -> ADM a
  getVNames :: a -> [VName]
  withTans :: [a] -> ([a] -> ADM b) -> ADM b
  withTans as m = do
    as' <- mapM mkTan as
    let f env =
          env
            { tans =
                M.fromList (zip (concatMap getVNames as) (concatMap getVNames as'))
                  `M.union` tans env
            }
    local f $ m as'
  withTan :: a -> (a -> ADM b) -> ADM b
  withTan a m = withTans [a] $ \[a'] -> m a'

instance TanBinder (PatElemT dec) where
  mkTan (PatElem p t) = do
    p' <- tanVName p
    return $ PatElem p' t
  getVNames = pure . patElemName

instance TanBinder (Param attr) where
  mkTan (Param p t) = do
    p' <- tanVName p
    return $ Param p' t
  getVNames = pure . paramName

instance (TanBinder a) => TanBinder [a] where
  mkTan = mapM mkTan
  getVNames = concatMap getVNames

data TanStm = TanStm
  { primalStm :: Stms SOACS,
    tanStms :: Stms SOACS
  }

class Tangent a where
  type TangentType a
  tangent :: a -> ADM (TangentType a)

instance Tangent VName where
  type TangentType VName = VName
  tangent v = do
    maybeTan <- asks $ M.lookup v . tans
    case maybeTan of
      Just v' -> return v'
      Nothing -> error "Oh no!"

instance Tangent SubExp where
  type TangentType SubExp = SubExp
  tangent (Constant c) = zeroTan $ Prim $ primValueType c
  tangent (Var v) = do
    maybeTan <- asks $ M.lookup v . tans
    case maybeTan of
      Just v' -> return $ Var v'
      Nothing -> do t <- lookupType v; zeroTan t

instance Tangent Stm where
  type TangentType Stm = TanStm
  tangent = flip fwdStm return

--
fwdStm :: Stm -> (TanStm -> ADM a) -> ADM a
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (SubExp se))) m = do
  se' <- tangent se
  withTans pes $ \pes' ->
    m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (SubExp se'))))
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (Opaque se))) m = do
  se' <- tangent se
  withTans pes $ \pes' ->
    m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (Opaque se'))))
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (ArrayLit ses t))) m = do
  ses' <- mapM tangent ses
  withTans pes $ \pes' ->
    m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (ArrayLit ses' t))))
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (UnOp op x))) m = do
  x' <- tangent x
  withTans pes $ \pes' ->
    m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (UnOp op x'))))
fwdStm stm@(Let (Pattern [] [pe]) _aux (BasicOp (BinOp op x y))) m = do
  let t = binOpType op
  x_tan <- primExpFromSubExp t <$> tangent x
  y_tan <- primExpFromSubExp t <$> tangent y
  withTan pe $ \pe' -> do
    stms <- runBinder_ $ do
      let (wrt_x, wrt_y) =
            pdBinOp op (primExpFromSubExp t x) (primExpFromSubExp t y)
      letBindNames [patElemName pe'] <=< toExp $
        x_tan ~*~ wrt_x ~+~ y_tan ~*~ wrt_y
    m $ TanStm (oneStm stm) stms
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (ConvOp op x))) m = do
  x' <- tangent x
  withTan pes $ \pes' ->
    m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (ConvOp op x'))))
fwdStm stm@(Let (Pattern [] pes) aux assert@(BasicOp Assert {})) m =
  withTan pes $ \pes' ->
    m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux assert))
fwdStm stm@(Let (Pattern [] pes) aux cOp@(BasicOp CmpOp {})) m =
  withTan pes $ \pes' ->
    m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux cOp))
fwdStm stm@(Let (Pattern [] pes) _ (Apply f args _ _)) m
  | Just (_, argts) <- M.lookup f builtInFunctions = do
    arg_tans <-
      zipWith primExpFromSubExp argts <$> mapM (tangent . fst) args
    withTans pes $ \pes' -> do
      let arg_pes = zipWith primExpFromSubExp argts (map fst args)

      stms <- runBinder_ $
        case pdBuiltin f arg_pes of
          Nothing ->
            error $ "No partial derivative defined for builtin function: " ++ pretty f
          Just derivs ->
            zipWithM_ (letBindNames . pure . patElemName) pes'
              =<< mapM toExp (zipWith (~*~) arg_tans derivs)

      m $ TanStm (oneStm stm) stms
fwdStm stm@(Let (Pattern [] pes) aux (If cond t f attr)) m = do
  t' <- fwdBodyInterleave' t
  f' <- fwdBodyInterleave' f
  withTan pes $ \pes' ->
    m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (If cond t' f' attr)))
fwdStm (Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' -> do
    body' <- fwdBodyInterleave' body
    withTans pes $ \pes' ->
      m $
        TanStm mempty $
          oneStm
            ( Let (Pattern [] pes') aux $
                DoLoop
                  []
                  (valPats ++ zip valParams' vals')
                  (WhileLoop v)
                  body'
            )
fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop v it bound []) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' -> do
    (_, body') <- fwdBodyAfter' body
    withTans pes $ \pes' ->
      m $
        TanStm
          (oneStm stm)
          ( oneStm
              ( Let (Pattern [] pes') aux $
                  DoLoop
                    []
                    (valPats ++ zip valParams' vals')
                    (ForLoop v it bound [])
                    body'
              )
          )
fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop i it bound loop_vars) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' ->
    withTans (map fst loop_vars) $ \loopParams' -> do
      let f p n = do n' <- tangent n; return (p, n')
      loop_vars' <- zipWithM f loopParams' (map snd loop_vars)
      (_, body') <- fwdBodyAfter' body
      withTans pes $ \pes' ->
        m $
          TanStm
            (oneStm stm)
            ( oneStm
                ( Let (Pattern [] pes') aux $
                    DoLoop
                      []
                      (valPats ++ zip valParams' vals')
                      (ForLoop i it bound (loop_vars ++ loop_vars'))
                      body'
                )
            )
fwdStm stm _ =
  error $ "unhandled AD for Stm: " ++ pretty stm ++ "\n" ++ show stm

fwdBodyInterleave :: Stms SOACS -> ADM Body -> ADM Body
fwdBodyInterleave stms m =
  case stms of
    (stm :<| stms') ->
      fwdStm stm $ \tStm -> do
        Body _ stms'' res <- fwdBodyInterleave stms' m
        return $ mkBody (primalStm tStm <> tanStms tStm <> stms'') res
    Empty -> m

fwdBodyInterleave' :: Body -> ADM Body
fwdBodyInterleave' (Body _ stms res) =
  fwdBodyInterleave stms $ do
    res' <- mapM tangent res
    return $ mkBody mempty $ res ++ res'

fwdBodyAfter :: Stms SOACS -> ADM (Body, Body) -> ADM (Body, Body)
fwdBodyAfter stms m =
  case stms of
    (stm :<| stms') ->
      fwdStm stm $ \tStm -> do
        (Body _ stms1 res1, Body _ stms2 res2) <- fwdBodyAfter stms' m
        return (mkBody (primalStm tStm <> stms1) res1, mkBody (tanStms tStm <> stms2) res2)
    Empty -> m

fwdBodyAfter' :: Body -> ADM (Body, Body)
fwdBodyAfter' (Body _ stms res) =
  fwdBodyAfter stms $ do
    res' <- mapM tangent res
    return (mkBody mempty res, mkBody mempty res')

fwdFun :: Stms SOACS -> FunDef SOACS -> PassM (FunDef SOACS)
fwdFun consts fundef = do
  let initial_renv = REnv {tans = mempty, envScope = mempty}
  flip runADM initial_renv $
    inScopeOf consts $
      withTan (funDefParams fundef) $ \params' -> do
        body' <- fwdBodyInterleave' $ funDefBody fundef
        pure
          fundef
            { funDefParams = funDefParams fundef ++ params',
              funDefBody = body',
              funDefRetType = funDefRetType fundef ++ funDefRetType fundef,
              funDefEntryPoint = (\(a, r) -> (a ++ a, r ++ r)) <$> funDefEntryPoint fundef
            }

fwdADEntryPoints :: Pass SOACS SOACS
fwdADEntryPoints =
  Pass
    { passName = "forward-ad",
      passDescription = "Apply forward-mode algebraic differentiation on all entry points",
      passFunction = intraproceduralTransformationWithConsts pure fwdFun
    }