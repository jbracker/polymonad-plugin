
-- | Graph structure given by the "Polymonad Programming"
--   paper (Hicks 2014) used for coherence.
module Control.Polymonad.Plugin.GraphView
  ( GraphView(..)
  , EdgeType(..)
  , PiNode(..)
  , piNodeType
  , mkGraphView
  , isFlowEdge
  , getPath
  , noPathExists
  , getAmbiguousConstraintTyVars
  , tyVarIsIn
  , flowEdgeCountAtNode
  , isUnificationEdge
  , isFlowLEdge
  , isAdjToAmbiguousNodes
  , removeLEdge
  , piNodeToNode
  , nodeToPiNode
  , isEdge
  , getLEdges
  , isBindEdge
  , getLEdge
  ) where

import Data.Maybe ( catMaybes, listToMaybe )
import Data.List ( sort )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Graph.Inductive
  ( Graph(..), Gr
  , Node, LNode, LEdge
  , out, inn
  , esp
  , hasLEdge )
import Data.Graph.Inductive.Graph ( delLEdge )

import Type ( Type, TyVar, getTyVar_maybe )
import TcRnTypes ( Ct(..) )
import TcType ( isAmbiguousTyVar )
import Outputable ( Outputable(..) )
import qualified Outputable as O

import Control.Polymonad.Plugin.Utils ( eqTyVar )
import Control.Polymonad.Plugin.Constraint
  ( constraintPolymonadTyArgs' )

type PiNodeId = Int

type PiNodeConstraints = Map PiNodeId (Ct, Type, Type, Type)

-- | A node in the 'GraphView'.
data PiNode
  = Pi0 PiNodeId -- ^ Node for the first argument of a polymonad constraint.
  | Pi1 PiNodeId -- ^ Node for the second argument of a polymonad constraint.
  | Pi2 PiNodeId -- ^ Node for the third argument of a polymonad constraint.
  deriving ( Eq, Ord, Show )

-- | Type of an edge in a 'GraphView'.
data EdgeType
  = Unif -- ^ Unification edge. This means the connected nodes contain
         --   the same variable.
  | Bind -- ^ Bind edge. This means the connected nodes are part of the
         --   same bind constraints.
  deriving ( Eq, Ord, Show )

-- | Graph-view of a constraint bag.
--   See 'mkGraphView' and definition 5 of the paper
--   "Polymonad Programming" (Hicks 2014).
data GraphView = GraphView
  { gvPiNodeConstraints :: PiNodeConstraints
  , gvPiNodes :: Set PiNode
  , gvGraph :: Gr PiNode EdgeType
  , gvNextPiNodeId :: Int
  , gvUnificationEdges :: Set (Set PiNode)
  }

-- | Retrieves the assigned type of the given node in the 'GraphView',
--   if the node exists.
piNodeType :: GraphView -> PiNode -> Maybe Type
piNodeType gv = piNodeType' (gvPiNodeConstraints gv)

-- | Retrieve the type associated with the given 'PiNode' from the map
--   of associations, if there is one.
piNodeType' :: PiNodeConstraints -> PiNode -> Maybe Type
piNodeType' constr (Pi0 i) = (\(_, t, _, _) -> t) <$> M.lookup i constr
piNodeType' constr (Pi1 i) = (\(_, _, t, _) -> t) <$> M.lookup i constr
piNodeType' constr (Pi2 i) = (\(_, _, _, t) -> t) <$> M.lookup i constr

getLEdges :: GraphView -> [LEdge EdgeType]
getLEdges = labEdges . gvGraph

-- | Create a 'GraphView' for solving the given constraints.
mkGraphView :: [Ct] -> GraphView
mkGraphView cts =
  let -- Map out the arguments of the given constraints so they are accessible
      vs :: [(Int, (Ct, Type, Type, Type))]
      vs = zip [0..] (constraintPolymonadTyArgs' cts)
      -- The indices associated with the arguments
      ids :: [Int]
      ids = fst <$> vs
      -- The graphs nodes based on the ids.
      newPiNodes :: Set PiNode
      newPiNodes = S.unions [ S.fromList [Pi0 i, Pi1 i, Pi2 i] | i <- ids ]
      -- The 'PiNode' constraints. Assigment between ids and constraints
      piNodeConstr :: PiNodeConstraints
      piNodeConstr = M.fromList vs
      -- The undirected unification edges of the graph
      protoUnificationEdges :: [[PiNode]]
      protoUnificationEdges = removeDup
        [ sort [v , v'] -- Order does not matter, needed to detect duplicates correctly
        | v <- S.toList newPiNodes
        , v' <- S.toList newPiNodes
        , v /= v'
        , isSameTyVar piNodeConstr v v' ]
      unifEdges :: [LEdge EdgeType]
      unifEdges = concatMap (\[v,v'] -> mkUnifEdge v v') protoUnificationEdges
      -- The directed bind edges
      bindEdges :: [LEdge EdgeType]
      bindEdges =  [ mkEdge (Pi0 i) (Pi2 i) Bind | i <- ids ]
                ++ [ mkEdge (Pi1 i) (Pi2 i) Bind | i <- ids ]
  in GraphView
    { gvPiNodeConstraints = piNodeConstr
    , gvPiNodes = newPiNodes
    , gvGraph = mkGraph (fmap piNodeToLNode (S.toList newPiNodes))
            $ unifEdges ++ bindEdges
    , gvNextPiNodeId = length vs
    , gvUnificationEdges = S.fromList $ fmap S.fromList protoUnificationEdges
    }

-- | Correctly remove the given edge from the given 'GraphView'.
--   If the edge does not exists in the graph, nothing is changed.
removeLEdge :: LEdge EdgeType -> GraphView -> GraphView
removeLEdge e@(n, n', Unif) gv = gv
  { gvGraph = delLEdge (n', n, Unif) $ delLEdge e (gvGraph gv)
  , gvUnificationEdges = S.delete (S.fromList [nodeToPiNode n, nodeToPiNode n']) (gvUnificationEdges gv)
  }
removeLEdge e@(_n, _n', Bind) gv = gv
  { gvGraph = delLEdge e (gvGraph gv)
  }

-- -----------------------------------------------------------------------------
-- Local Utility Functions
-- -----------------------------------------------------------------------------

-- | Returns the incoming edges of the given node.
inEdges :: GraphView -> PiNode -> [LEdge EdgeType]
inEdges gv node = inn (gvGraph gv) (piNodeToNode node)

-- | Returns the outgoing edges of the given node.
outEdges :: GraphView -> PiNode -> [LEdge EdgeType]
outEdges gv node = out (gvGraph gv) (piNodeToNode node)

isAdjToAmbiguousNodes :: GraphView -> LEdge EdgeType -> Bool
isAdjToAmbiguousNodes gv (n, n', _) = isAmbiguousNode gv (nodeToPiNode n) || isAmbiguousNode gv (nodeToPiNode n')

isAmbiguousNode :: GraphView -> PiNode -> Bool
isAmbiguousNode gv piN = maybe False isAmbiguousTyVar
  $ piNodeType gv piN >>= getTyVar_maybe

isEdge :: GraphView -> PiNode -> PiNode -> EdgeType -> Bool
isEdge gv a b t = hasLEdge (gvGraph gv) (piNodeToNode a, piNodeToNode b, t)

-- | Checks if there is a flow edge (Definition 6 in "Polymonad Programming")
--   between the given two nodes. Only returns true if there is a unification
--   edge between the nodes that has the characteristics of a flow edge.
isFlowEdge :: GraphView -> PiNode -> PiNode -> Bool
isFlowEdge gv p@(Pi2 i) q@(Pi0 j) =  i /= j && isEdge gv p q Unif
isFlowEdge gv p@(Pi2 i) q@(Pi1 j) =  i /= j && isEdge gv p q Unif
isFlowEdge gv p@(Pi0 j) q@(Pi2 i) =  i /= j && isEdge gv p q Unif
isFlowEdge gv p@(Pi1 j) q@(Pi2 i) =  i /= j && isEdge gv p q Unif
isFlowEdge _gv _p _q = False

-- | Check if the given edge of the graph is a flow edge.
--   See 'isFlowEdge'.
isFlowLEdge :: GraphView -> LEdge EdgeType -> Bool
isFlowLEdge gv (from, to, _) = isFlowEdge gv (nodeToPiNode from) (nodeToPiNode to)

-- | Check if the given edge is a 'Unif'ication edge.
isUnificationEdge :: LEdge EdgeType -> Bool
isUnificationEdge (_, _, Unif) = True
isUnificationEdge _ = False

-- | Check if the given edge is a 'Bind' edge.
isBindEdge :: LEdge EdgeType -> Bool
isBindEdge (_, _, Bind) = True
isBindEdge _ = False

-- | Counts the number of flow edges adjacent to the given node.
--   This number is corrected such that the same edge in different directions
--   is not counted as several edges.
flowEdgeCountAtNode :: GraphView -> PiNode -> Int
flowEdgeCountAtNode gv = length . removeDupUndirectedEdges . flowEdgesAtNode gv

-- | Checks if there are any flow edges going in or out of the given node.
flowEdgesAtNode :: GraphView -> PiNode -> [LEdge EdgeType]
flowEdgesAtNode gv node =
  filter (isFlowLEdge gv) (inEdges gv node) ++ filter (isFlowLEdge gv) (outEdges gv node)

-- | Check if there is an edge between the given nodes and, if so, return
--   that edge.
getLEdge :: GraphView -> PiNode -> PiNode -> Maybe (LEdge EdgeType)
getLEdge gv p q = listToMaybe [ e | e@(_np, nq, _et) <- outEdges gv p, nq == piNodeToNode q ]

-- | Calculate the actual graph node from the given 'PiNode'.
piNodeToLNode :: PiNode -> LNode PiNode
piNodeToLNode v = ( piNodeToNode v, v )

-- | Calculate the graph 'Node' of a 'PiNode'.
--   Note: @piNodeToNode . nodeToPiNode = id@
piNodeToNode :: PiNode -> Node
piNodeToNode (Pi0 i) = i * 3 + 0
piNodeToNode (Pi1 i) = i * 3 + 1
piNodeToNode (Pi2 i) = i * 3 + 2

-- | Calculate the 'PiNode' from the given 'Node'.
--   Note: @nodeToPiNode . piNodeToNode = id@
nodeToPiNode :: Node -> PiNode
nodeToPiNode n = case divMod n 3 of
  (i, 0) -> Pi0 i
  (i, 1) -> Pi1 i
  (i, 2) -> Pi2 i

-- | Check if the two given nodes contain a type variable and if it is
--   the same type variable in both nodes. Uses the given association map
--   to lookup the contents of the nodes.
isSameTyVar :: PiNodeConstraints -> PiNode -> PiNode -> Bool
isSameTyVar constr p q = case (piNodeType' constr p, piNodeType' constr q) of
  (Just tp, Just tq) -> eqTyVar tp tq
  _ -> False

-- | Get the top-level type variable associated with the given node, if
--   the node is associated with a type variable.
piNodeTyVar' :: PiNodeConstraints -> PiNode -> Maybe TyVar
piNodeTyVar' constr node = piNodeType' constr node >>= getTyVar_maybe

-- | Get the top-level type variable associated with the given node, if
--   the node is associated with a type variable.
piNodeTyVar :: GraphView -> PiNode -> Maybe TyVar
piNodeTyVar = piNodeTyVar' . gvPiNodeConstraints

-- | Check if the given 'PiNode' is a type variable and, if so, if it
--   is inside the given set of type variables.
tyVarIsIn :: GraphView -> PiNode -> Set TyVar -> Bool
tyVarIsIn gv node tvs = case piNodeTyVar gv node of
  Just tv -> tv `S.member` tvs
  Nothing -> False

-- | Create and 'LEdge' from the given data.
mkEdge :: PiNode -> PiNode -> EdgeType -> LEdge EdgeType
mkEdge p q e = (piNodeToNode p, piNodeToNode q, e)

-- | Create an undirected unification edge. That is
--   two edges in a list.
mkUnifEdge :: PiNode -> PiNode -> [LEdge EdgeType]
mkUnifEdge p q = [ mkEdge p q Unif, mkEdge q p Unif]

-- | Efficient removal of duplicate elements in O(n * log(n)).
--   The result list is ordered in ascending order.
removeDup :: (Ord a) => [a] -> [a]
removeDup = S.toAscList . S.fromList

removeDupUndirectedEdges :: [LEdge EdgeType] -> [LEdge EdgeType]
removeDupUndirectedEdges [] = []
removeDupUndirectedEdges (e@(p, q, Unif):es) = e : removeDupUndirectedEdges (filter (\e' -> e' /= e && e' /= (q, p, Unif)) es)
removeDupUndirectedEdges (e:es) = e : removeDupUndirectedEdges es

getAmbiguousConstraintTyVars :: GraphView -> Set TyVar
getAmbiguousConstraintTyVars = collectAmbiguousTyVars . gvPiNodeConstraints

-- | Collectes all ambiguous type variables from the associated constraints.
--   Only collect type variables that are at the top-level.
--   Top-level variables are enough, because the test in 'isUnambiguous'
--   only checks if the associated type of a node is in the set of
--   ambiguous type variables (A(v) in ftv(P) | ftv(Gamma, t)) and
--   A(v) can only be a top-level type variable.
collectAmbiguousTyVars :: PiNodeConstraints -> Set TyVar
collectAmbiguousTyVars cts = S.unions $ collectAmbTVs <$> M.elems cts
  where
    collectAmbTVs :: (Ct, Type, Type, Type) -> Set TyVar
    collectAmbTVs (_ct, t0, t1, t2) = S.fromList $ catMaybes [getAmbTV t0, getAmbTV t1, getAmbTV t2]

    getAmbTV :: Type -> Maybe TyVar
    getAmbTV t = case getTyVar_maybe t of
      Just tv -> if isAmbiguousTyVar tv then Just tv else Nothing
      Nothing -> Nothing

-- | Check if _no_ path between the two given nodes in the 'GraphView'
--   exists. If the nodes are not part of the graph this function will
--   also return 'False'.
noPathExists :: GraphView -> PiNode -> PiNode -> Bool
noPathExists gv p q = null $ getPath gv p q

getPath :: GraphView -> PiNode -> PiNode -> Maybe [PiNode]
getPath gv p q = if null path then Nothing else Just path
  where path = nodeToPiNode <$> esp (piNodeToNode p) (piNodeToNode q) (gvGraph gv)


-- -----------------------------------------------------------------------------
-- Unimportant Instances
-- -----------------------------------------------------------------------------

instance Outputable PiNode where
  ppr = O.text . show

instance Outputable GraphView where
  ppr gv = O.text "GraphView {" O.$$
       O.nest 2 ( ppr (gvPiNodeConstraints gv)
         O.$$ ppr (gvPiNodes gv)
         O.$$ O.text (show $ gvGraph gv)
         O.$$ O.int (gvNextPiNodeId gv)
       )
       O.$$ O.text "}"
