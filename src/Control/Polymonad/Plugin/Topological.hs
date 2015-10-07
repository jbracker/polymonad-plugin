
module Control.Polymonad.Plugin.Topological
  ( topologicalTyConOrder ) where

import Data.List ( nubBy, find )
import Data.Graph.Inductive
  ( Graph(..), Gr
  , Node, LNode, LEdge )
import Data.Graph.Inductive.Graph
  ( delNode, indeg )

import Type ( Type, eqType, mkTyConTy )
import TcRnTypes ( Ct(..) )

import Control.Polymonad.Plugin.Utils ( removeDup )
import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , getIdentityTyCon
  , throwPluginError )
import Control.Polymonad.Plugin.Constraint ( WantedCt, constraintPolymonadTyArgs' )

-- | Calculate the topological order of the type constructors involved with
--   the given polymonad constraints. The given constraints should be the
--   wanted polymonad constraints.
--   The returned list of types contains the types from least to greatest type,
--   where the bind operation of the wanted constraints is used as ordering:
--
--   @M a -> (a -> N b) -> P b@ ==> @M < P@ and @N < P@.
topologicalTyConOrder :: [WantedCt] -> PmPluginM [Type]
topologicalTyConOrder wantedCts = orderNodes topoGraph
  where
    -- Involved type constructors
    constraintTys :: [(Ct, Type, Type, Type)]
    constraintTys = constraintPolymonadTyArgs' wantedCts

    nodes :: [LNode Type]
    nodes = zip [0..] -- with node ids added
          $ nubBy eqType -- without duplicates
          $ concatMap (\(_, t0, t1, t2) -> [t0, t1, t2]) constraintTys -- as a list

    nodeForTy :: Type -> Node
    nodeForTy ty = case find (\(_, ty') -> eqType ty ty') nodes of
      Just (n, _) -> n
      Nothing -> error "nodeForTy: Impossible, we should always find a node by construction."

    edges :: [LEdge ()]
    edges = filter (\(n, n', _) -> n /= n') $ removeDup
          $ concatMap (\(_, t0, t1, t2)
                -> [(nodeForTy t0, nodeForTy t2, ()), (nodeForTy t1, nodeForTy t2, ())]) constraintTys

    topoGraph :: Gr Type ()
    topoGraph = mkGraph nodes edges

    orderNodes :: Gr Type () -> PmPluginM [Type]
    orderNodes gr = if isEmpty gr
      then return []
      else case filter (\(n, _) -> indeg gr n == 0) $ labNodes gr of
        [] -> throwPluginError "topologicalTyConOrder: No nodes with zero in-degree. There was a cycle!"
        ns -> do
          restTys <- orderNodes $ foldr delNode gr (fmap fst ns)
          -- If identity is among other smallest types, put it at
          -- the smallest position. (The functor law allows us to apply this
          -- ordering among these types.)
          bottomNs <- idToBottom $ fmap snd ns
          return $ bottomNs ++ restTys

    -- If the given list contains the identity type constructor, then move it
    -- to the beginning of the list.
    idToBottom :: [Type] -> PmPluginM [Type]
    idToBottom ts = do
      idTC <- mkTyConTy <$> getIdentityTyCon
      return $ case find (eqType idTC) ts of
        Just _ -> idTC : filter (not . eqType idTC) ts
        Nothing -> ts

{-
-- | Calculate the topological order of the type constructors involved with
--   the given polymonad constraints. The given constraints should be the
--   wanted polymonad constraints.
topologicalTyConOrder :: GraphView -> PmPluginM [Type]
topologicalTyConOrder gv = printObj (labNodes collapsedGraph, labEdges collapsedGraph) >> orderNodes collapsedGraph
  where
    collapsedGraph = removeReflEdges -- Now we have a lot of loop that need removing.
                   $ collapseUnifEdges -- Collapse all nodes linked by unification edges into a single node
                   $ convNodeTypes -- Label nodes with their type
                   $ gvGraph gv -- Look at the graph

    orderNodes :: Gr Type EdgeType -> PmPluginM [Type]
    orderNodes gr = if isEmpty gr
      then return []
      else case find (\(n, _) -> indeg gr n == 0) $ labNodes gr of
        Just (n, ty) -> do
          restTys <- orderNodes $ delNode n gr
          return $ ty : restTys
        Nothing -> throwPluginError "topologicalTyConOrder: No nodes with zero in-degree. There was a cycle!"

    removeReflEdges :: Gr a b -> Gr a b
    removeReflEdges g = delEdges (filter (uncurry (==)) $ edges g) g

    convNodeTypes :: Gr PiNode e -> Gr Type e
    convNodeTypes = nmap (fromJust . piNodeType gv)

    collapseUnifEdges :: Gr Type EdgeType -> Gr Type EdgeType
    collapseUnifEdges gr = foldr collapseUnifEdge gr (labEdges gr)

    collapseUnifEdge :: LEdge EdgeType -> Gr Type EdgeType -> Gr Type EdgeType
    collapseUnifEdge (_, _, Bind) g = g
    collapseUnifEdge (n, m, Unif) g = if gelem n g && gelem m g
      then
        let mEdges = out g m ++ inn g m -- All adjacent edges of m
            -- Replace all occurences of m in the adjacent edges with n.
            newNEdges = (\(k, l, e) -> (if k == m then n else l, if l == m then n else l, e)) <$> mEdges
        in delNode m -- At last, remove m and with it all adjacent edges.
         $ insEdges newNEdges -- Then link all nodes currently linked with m to n
         $ delEdge (n, m) g -- First, remove the unification edge
      else g
-}
