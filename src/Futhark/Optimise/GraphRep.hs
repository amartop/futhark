-- Maybe move to IR/Graph.hs at some point, for now keeping in Optimise/

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
module Futhark.Optimise.GraphRep (module Futhark.Optimise.GraphRep) where

import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Futhark.IR.SOACS hiding (SOAC (..))
import qualified Futhark.IR.SOACS as Futhark
import qualified Futhark.Analysis.Alias as Alias
import Futhark.IR.Prop.Aliases ( consumedInStm, expAliases )
import Futhark.Analysis.HORep.SOAC
import qualified Data.Sequence as Seq

import qualified Data.Graph.Inductive.Tree as G
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Dot
import qualified Futhark.Util.Pretty as PP

import Futhark.Builder (MonadFreshNames (putNameSource), VNameSource, getNameSource, modifyNameSource, blankNameSource)
import Data.Foldable (foldlM)
import Control.Monad.State

data EdgeT = Alias VName | InfDep VName | Dep VName | TrDep VName | Cons VName | Fake VName | Res VName deriving (Eq, Ord)
data NodeT = SNode (Stm SOACS) [Input] ArrayTransforms | RNode VName | InNode VName | FinalNode [Stm SOACS]
  deriving (Eq, Ord)


instance Show EdgeT where
  show (Dep vName) = "Dep " <> ppr vName
  show (TrDep vName) = "TrDep " <> ppr vName
  show (InfDep vName) = "iDep " <> ppr vName
  show (Cons _) = "Cons"
  show (Fake _) = "Fake"
  show (Res _) = "Res"
  show (Alias _) = "Alias"

-- inputs could have their own edges - to facilitate fusion


instance Show NodeT where
    show (SNode (Let pat _ _) _ _) = ppr $ L.intercalate ", " $ map ppr $ patNames pat -- show (namesToList $ freeIn stm)
    show (FinalNode stms) = concatMap ppr stms
    show (RNode name)  = ppr $ "Res: "   ++ ppr name
    show (InNode name) = ppr $ "Input: " ++ ppr name

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
    scope :: Scope SOACS,
    producerMapping :: M.Map VName Node
  }

freshFusionEnv :: Scope SOACS -> FusionEnv
freshFusionEnv stms_scope = FusionEnv {vNameSource = blankNameSource, scope = stms_scope, producerMapping = M.empty}

newtype FusionEnvM a = FusionEnvM (State FusionEnv a)
  deriving
    (
      Monad,
      Applicative,
      Functor,
      MonadState FusionEnv
    )

instance MonadFreshNames FusionEnvM where
  getNameSource = gets vNameSource
  putNameSource source =
    modify (\env -> env {vNameSource = source})

instance HasScope SOACS FusionEnvM where
  askScope = gets scope


runFusionEnvM ::
  MonadFreshNames m =>
  FusionEnvM a ->
  FusionEnv ->
  m a
runFusionEnvM (FusionEnvM a) env =
  modifyNameSource $ \src -> let (new_a, new_env) = runState a (env {vNameSource = src}) in (new_a, vNameSource new_env)


-- most everything is going to be a graph augmentation g -> M g.
-- these can be efficiently strung together using applyAugs
type DepGraphAug = DepGraph -> FusionEnvM DepGraph


addTransforms :: DepGraphAug
addTransforms g = foldlM (flip helper) g (nodes g)
  where
    helper :: Node -> DepGraphAug
    helper n g
      | gelem n g = 
        case lFromNode g n of
          SNode (Let _ aux_1 exp_1) _ _ -> 
            case (transformFromExp (stmAuxCerts aux_1) exp_1, context g n) of
              (Just (vn, transform), (ins, _, lab, [o])) -> do
                let g' = insEdges (map (\i -> (snd i, snd o, TrDep vn)) ins) g -- todo: what about other than dep edges?
                pure (appendTransformToNode (delNode n g') (snd o) transform)
              _ -> pure g
          _ -> pure g
      | otherwise = pure g

appendTransformToNode :: DepGraph -> Node -> ArrayTransform -> DepGraph
appendTransformToNode g n tr =
  case context g n of
    (ins, n', SNode stm itrs otrs, outs) -> 
      (&) (ins, n', SNode stm itrs (otrs |> tr), outs) (delNode n g)
    _ -> g

inputTransforms :: Input -> ArrayTransforms
inputTransforms (Input trs _ _) = trs

nullInputTransforms :: [Input] -> Bool
nullInputTransforms = all (nullTransforms . inputTransforms)

-- appendTransform :: DepNode -> DepGraphAug
-- appendTransform node_to_fuse g =
--   if gelem (nodeFromLNode node_to_fuse) g
--   then applyAugs (map (appendT node_to_fuse_id) fuses_to) g
--   else pure g
--   where
--     fuses_to = map nodeFromLNode $ input g node_to_fuse
--     node_to_fuse_id = nodeFromLNode node_to_fuse

-- -- Given two nodes, if the nodes are (MapNest depends on ArrayTransform)
-- -- add the ArrayTransform to the input transforms of MapNest
-- -- Delete the transformNode, keep the mapNode
-- appendT :: Node -> Node -> DepGraphAug
-- appendT merge_into input_transform g
--   | not (gelem input_transform g && gelem merge_into g) = pure g
--   -- outdeg g merge_into == 1 =
--   | otherwise = 
--     case mapT (lFromNode g) (input_transform, merge_into) of
--       (SNode (Let _ aux_1 exp_1) _ _, -- ArrayTransform
--         SNode s@(Let _ aux_2 (Op (Futhark.Screma _ _ scremaform))) transforms ots) ->
--         case (transformFromExp (stmAuxCerts aux_1) exp_1, isMapSOAC scremaform) of
--           (Just (vn,transform), Just _) -> do
--             let newNodeL = SNode s (addTransform transforms vn transform) ots
--             let newContext = mergedContext newNodeL (context g merge_into) (context g input_transform)
--             contractEdge input_transform newContext g
--           _ -> pure g
--       _ -> pure g
--   where
--     addTransform :: InputTransforms -> VName -> ArrayTransform -> InputTransforms
--     addTransform trs vn tr = 
--       case M.lookup vn trs of
--         Nothing  -> M.insert vn (tr <| noTransforms) trs
--         Just seq -> M.insert vn (tr <| seq) trs



--- Graph Construction ---

emptyG2 :: [Stm SOACS] -> [VName] -> [VName] -> DepGraph
emptyG2 stms res inputs = mkGraph (label_nodes (snodes ++ rnodes ++ inNodes)) []
  where
    label_nodes = zip [0..]
    snodes = map (\s -> SNode s [] noTransforms) stms
    rnodes = map RNode res
    inNodes= map InNode inputs

isArray :: FParam SOACS -> Bool
isArray p = case paramDec p of
  Array {} -> True
  _ -> False

mkDepGraph :: [Stm SOACS] -> [VName] -> [VName] -> FusionEnvM DepGraph
mkDepGraph stms res inputs = do
  let g = emptyG2 stms res inputs
  _ <- makeMapping g
  addDepEdges g

addDepEdges :: DepGraphAug
addDepEdges = applyAugs
  [addDeps2, makeScanInfusible, addInfDeps, addCons, addExtraCons, addResEdges, addAliases, addTransforms]


makeMapping :: DepGraphAug
makeMapping g = do
  let mapping = M.fromList $ concatMap gen_dep_list (labNodes g)
  modify (\s -> s{producerMapping = mapping})
  pure g
    where
      gen_dep_list :: DepNode -> [(VName, Node)]
      gen_dep_list (i, node) = [(name, i) | name <- getOutputs node]

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

depGraphInsertEdges :: [DepEdge] -> DepGraphAug
depGraphInsertEdges edgs g = return $ mkGraph (labNodes g) (edgs ++ labEdges g)

applyAugs :: [DepGraphAug] -> DepGraphAug
applyAugs augs g = foldlM (flip ($)) g augs


--- Extracting Nodes/Edges ---

label :: DepNode -> NodeT
label = snd

stmFromNode :: NodeT -> [Stm SOACS]
--stmFromNode (SNode x inputTransforms outputTransforms) = [inputTransforms, x, outputTransforms]

stmFromNode (SNode x [] _) = [x]
stmFromNode (FinalNode x) = x
stmFromNode _ = []

nodeFromLNode :: DepNode -> Node
nodeFromLNode = fst

lNodeFromNode :: DepGraph -> Node -> DepNode
lNodeFromNode g n = labNode' (context g n)

lFromNode :: DepGraph -> Node -> NodeT
lFromNode g n = label $ lNodeFromNode g n

-- nodeToTransforms :: DepGraph -> Node -> Maybe ArrayTransforms -- might need a modification
-- nodeToTransforms g n = 
--   case lFromNode g n of
--     SNode _ trs -> Just trs
--     _ -> Nothing

labFromEdge :: DepGraph -> DepEdge -> DepNode
labFromEdge g (n1, _, _) = lNodeFromNode g n1

depsFromEdgeT :: EdgeT -> [VName]
depsFromEdgeT e = case e of
  Dep name    -> [name]
  TrDep name  -> [name]
  InfDep name -> [name]
  Res name    -> [name]
  Cons name   -> [name]
  Fake name   -> [name]
  Alias name  -> [name]

depsFromEdge ::  DepEdge -> [VName]
depsFromEdge = depsFromEdgeT . edgeLabel

-- List of Nodes that node depends on, i.e. inputs to the label Stm
input :: DepGraph -> DepNode -> [DepNode]
input g node = map (labNode' . context g) $ suc g $ nodeFromLNode node

-- List of Nodes depending on node, i.e. outputs of the label Stm
output :: DepGraph -> DepNode -> [DepNode]
output g node = map (labNode' . context g) $ pre g $ nodeFromLNode node

edgesBetween :: DepGraph -> Node -> Node -> [DepEdge]
edgesBetween g n1 n2 = labEdges $ subgraph [n1,n2] g


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

addCons :: DepGraphAug
addCons = augWithFun getStmCons

-- Merges two contexts
mergedContext :: (Eq b) => a -> Context a b -> Context a b -> Context a b
mergedContext mergedlabel (inp1, n1, _, out1) (inp2, n2, _, out2) =
  let new_inp = L.nub $ filter (\n -> snd n /= n1 && snd n /= n2) (inp1  `L.union` inp2) in
  let new_out = L.nub $ filter (\n -> snd n /= n1 && snd n /= n2) (out1 `L.union` out2)
  in (new_inp, n1, mergedlabel, new_out)
  -- update keys of gen n2 with n1

-- Contracts the edge between n1 and n2, n1 remains
contractEdge :: Node -> DepContext -> DepGraphAug
contractEdge n2 cxt g = do
  let n1 = node' cxt
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
      && cname `elem` depsFromEdgeT toedge
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
      then InfDep name
      else Dep name
    change_node_to_idep e = e


-- Utils for fusibility/infusibility
-- find dependencies - either fusable or infusable. edges are generated based on these

fusableInputs :: Stm SOACS -> [VName]
fusableInputs (Let _ _ expr) = fusableInputsFromExp expr

fusableInputsFromExp :: Exp SOACS -> [VName]
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
-- infusableInputsFromExp op@If {} = namesToList $ freeIn op
-- infusableInputsFromExp op@DoLoop {} = namesToList $ freeIn op
infusableInputsFromExp op = namesToList $ freeIn op

aliasInputs :: Stm SOACS -> [VName]
aliasInputs op = case op of
  Let _ _ expr -> concatMap namesToList $ expAliases $ Alias.analyseExp mempty expr


--- Inspecting Stms ---

getStmNames :: Stm SOACS -> [VName]
getStmNames s = case s of
  Let pat _ _ -> patNames pat


getStmCons :: EdgeGenerator
getStmCons (SNode s _ _) = zip names (map Cons names)
  where
    names =  namesToList . consumedInStm . Alias.analyseStm mempty $ s
getStmCons _ = []

getStmRes :: EdgeGenerator
getStmRes (RNode name) = [(name, Res name)]
getStmRes _ = []

getOutputs :: NodeT -> [VName]
getOutputs node = case node of
  (SNode stm _ _) -> getStmNames stm
  (RNode _)   -> []
  (InNode name) -> [name]
  (FinalNode stms) -> concatMap getStmNames stms


--- Other ---
mapT :: (a -> b) -> (a,a) -> (b,b)
mapT f (a,b) = (f a, f b)

-- TODO: Figure out where to put this
namesFromRes :: [SubExpRes] -> [VName]
namesFromRes = concatMap ((\case
     Var z -> [z]
     Constant _ -> []
  ) . resSubExp)
-- THIS IS BUGGY!!!! Constants are yeeted from lambda outputs after fusion