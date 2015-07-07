
-- | Graph structure given by the "Polymonad Programming"
--   paper (Hicks 2014) used for coherence.
module Control.Polymonad.Plugin.Graph
  ( GraphView
  , EdgeType(..)
  , PiNode(..)
  , vertexAssignment
  , mkGraphView
  , isUnambiguous
  , isFlowEdge
  ) where

import Data.Maybe ( isJust, catMaybes, listToMaybe )
import Data.List ( sort )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Graph.Inductive
  ( Graph(..), Gr, Node, LNode, LEdge
  , out, inn
  , esp )

import Type ( Type, TyVar, getTyVar_maybe )
import TcRnTypes ( Ct(..) )
import TcType ( isAmbiguousTyVar )
import Outputable ( Outputable(..) )
import qualified Outputable as O

import Control.Polymonad.Plugin.Constraint ( constraintClassTyArgs )

-- | A node in the 'GraphView'.
--   The arguments refers to the constraint the node was generated for.
data PiNode a
  = Pi0 a -- ^ Node for the first argument of a polymonad constraint.
  | Pi1 a -- ^ Node for the second argument of a polymonad constraint.
  | Pi2 a -- ^ Node for the third argument of a polymonad constraint.
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
  { vertexConstraints :: Map Int (Ct, Type, Type, Type)
  , vertices :: Set (PiNode Int)
  , graph :: Gr (PiNode Int) EdgeType
  , nextVertexIndex :: Int
  }

-- | Retrieves the assigned type of the given node in the 'GraphView',
--   if the node exists.
vertexAssignment :: GraphView -> PiNode Int -> Maybe Type
vertexAssignment gv = vertexAssignment' (vertexConstraints gv)

-- | Create a 'GraphView' for solving the given constraints.
mkGraphView :: [Ct] -> GraphView
mkGraphView cts =
  let -- Map out the arguments of the given constraints so they are accessible
      vs :: [(Int, (Ct, Type, Type, Type))]
      vs = zip [0..]
         $ fmap (\(ct, Just (p0 : p1 : p2 : _)) -> (ct, p0, p1, p2))
         $ filter (\(_, ts) -> isJust ts)
         $ fmap (\ct -> (ct, constraintClassTyArgs ct)) cts
      -- The indices associated with the arguments
      is :: [Int]
      is = [0..]
      -- The graphs nodes based on the indices.
      verts :: Set (PiNode Int)
      verts = S.unions [ S.fromList [Pi0 i, Pi1 i, Pi2 i] | i <- is ]
      -- The vertex constraints. Assigment between indices and constraints
      vertConstr :: Map Int (Ct, Type, Type, Type)
      vertConstr = M.fromList vs
      -- The undirected unification edges of the graph
      unifEdges :: [LEdge EdgeType]
      unifEdges = concatMap (\[v,v'] -> mkUnifEdge v v')
                $ removeDup
                [ sort [v , v'] -- Order does not matter, needed to detect duplicates correctly
                | v <- S.toList verts
                , v' <- S.toList verts
                , v /= v'
                , isSameTyVar vertConstr v v' ]
      -- The directed bind edges
      bindEdges :: [LEdge EdgeType]
      bindEdges =  [ mkEdge (Pi0 i) (Pi2 i) Bind | i <- is ]
                ++ [ mkEdge (Pi1 i) (Pi2 i) Bind | i <- is ]
  in GraphView
    { vertexConstraints = vertConstr
    , vertices = verts
    , graph = mkGraph (fmap piNodeToLNode (S.toList verts))
            $ unifEdges ++ bindEdges
    , nextVertexIndex = length vs
    }

-- | Check if the given 'GraphView' is unambiguous in sense of
--   definition 7 in the "Polymonad Programming" paper. This
--   does look at subgraphes; it only checks if the given graph
--   fulfills the criteria.
isUnambiguous :: GraphView -> Bool
isUnambiguous gv =
  let -- Check of there are an paths from a 'Pi2' to a 'Pi0' or a 'Pi1'.
      noPaths :: Bool
      noPaths = and
              [ noPathExists gv (Pi2 i) (Pi0 i) &&
                noPathExists gv (Pi2 i) (Pi1 i)
              | Pi2 i <- S.toList $ vertices gv ]
      -- Collect all top-level ambiguous type variables in the constraints.
      -- Top-level is enough, because A(v) can only be a top-level variable.
      ambTvs :: Set TyVar
      ambTvs = collectAmbiguousTyVars $ vertexConstraints gv
      -- Get nodes of ambiguous type variables.
      ambNodes :: Set (PiNode Int)
      ambNodes = S.filter (\node -> tyVarIsIn gv node ambTvs) (vertices gv)
  -- Check the ambiguity conditions:
  --   1. No paths from a Pi.2 to a Pi.0 or Pi.1.
  --   2. For all nodes with an ambiguous type variable there exists a connected flow edge.
  in noPaths && all (flowEdgeAtNodeExists gv) ambNodes



-- -----------------------------------------------------------------------------
-- Local Utility Functions
-- -----------------------------------------------------------------------------

-- | Returns the incoming edges of the given node.
inEdges :: GraphView -> PiNode Int -> [LEdge EdgeType]
inEdges gv node = inn (graph gv) (piNodeToNode node)

-- | Returns the outgoing edges of the given node.
outEdges :: GraphView -> PiNode Int -> [LEdge EdgeType]
outEdges gv node = out (graph gv) (piNodeToNode node)

-- | Checks if there is a flow edge (Definition 6 in "Polymonad Programming")
--   between the given two nodes. Only returns true if there is a unification
--   edge between the nodes that has the characteristics of a flow edge.
isFlowEdge :: GraphView -> PiNode Int -> PiNode Int -> Bool
isFlowEdge gv p@(Pi2 i) q@(Pi0 j) =  i /= j
                                  && (isUnificationEdge <$> getLEdge gv p q) == Just True
isFlowEdge gv p@(Pi2 i) q@(Pi1 j) =  i /= j
                                  && (isUnificationEdge <$> getLEdge gv p q) == Just True
isFlowEdge _gv _p _q = False

-- | Check if the given edge is a 'Unif'ication edge.
isUnificationEdge :: LEdge EdgeType -> Bool
isUnificationEdge (_, _, Unif) = True
isUnificationEdge _ = False

-- | Checks if there are any flow edges going in or out of the given node.
flowEdgeAtNodeExists :: GraphView -> PiNode Int -> Bool
flowEdgeAtNodeExists gv node
  =  any flowEdgePred (inEdges  gv node)
  || any flowEdgePred (outEdges gv node)
  where
    flowEdgePred :: LEdge EdgeType -> Bool
    flowEdgePred (from, to, _) = isFlowEdge gv (nodeToPiNode from) (nodeToPiNode to)

-- | Check if there is an edge between the given nodes and, if so, return
--   that edge.
getLEdge :: GraphView -> PiNode Int -> PiNode Int -> Maybe (LEdge EdgeType)
getLEdge gv p q = listToMaybe [ e | e@(_np, nq, _et) <- out (graph gv) (piNodeToNode p), nq == piNodeToNode q ]

-- | Retrieve the type associated with the given 'PiNode' from the map
--   of associations, if there is one.
vertexAssignment' :: Map Int (Ct, Type, Type, Type) -> PiNode Int -> Maybe Type
vertexAssignment' vAssign (Pi0 i) = (\(_, t, _, _) -> t) <$> M.lookup i vAssign
vertexAssignment' vAssign (Pi1 i) = (\(_, _, t, _) -> t) <$> M.lookup i vAssign
vertexAssignment' vAssign (Pi2 i) = (\(_, _, _, t) -> t) <$> M.lookup i vAssign

-- | Calculate the actual graph node from the given 'PiNode'.
piNodeToLNode :: PiNode Int -> LNode (PiNode Int)
piNodeToLNode v = ( piNodeToNode v, v )

-- | Calculate the graph 'Node' of a 'PiNode'.
--   Note: @piNodeToNode . nodeToPiNode = id@
piNodeToNode :: PiNode Int -> Node
piNodeToNode (Pi0 i) = i * 3 + 0
piNodeToNode (Pi1 i) = i * 3 + 1
piNodeToNode (Pi2 i) = i * 3 + 2

-- | Calculate the 'PiNode' from the given 'Node'.
--   Note: @nodeToPiNode . piNodeToNode = id@
nodeToPiNode :: Node -> PiNode Int
nodeToPiNode n = case divMod n 3 of
  (i, 0) -> Pi0 i
  (i, 1) -> Pi1 i
  (i, 2) -> Pi2 i

-- | Check if the two given nodes contain a type variable and if it is
--   the same type variable in both nodes. Uses the given association map
--   to lookup the contents of the nodes.
isSameTyVar :: Map Int (Ct, Type, Type, Type) -> PiNode Int -> PiNode Int -> Bool
isSameTyVar vAssign p q = case (piNodeTyVar' vAssign p, piNodeTyVar' vAssign q) of
  (Just tp, Just tq) -> tp == tq
  _ -> False

-- | Get the top-level type variable associated with the given node, if
--   the node is associated with a type variable.
piNodeTyVar' :: Map Int (Ct, Type, Type, Type) -> PiNode Int -> Maybe TyVar
piNodeTyVar' vAssign node = vertexAssignment' vAssign node >>= getTyVar_maybe

-- | Get the top-level type variable associated with the given node, if
--   the node is associated with a type variable.
piNodeTyVar :: GraphView -> PiNode Int -> Maybe TyVar
piNodeTyVar = piNodeTyVar' . vertexConstraints

-- | Check if the given 'PiNode' is a type variable and, if so, if it
--   is inside the given set of type variables.
tyVarIsIn :: GraphView -> PiNode Int -> Set TyVar -> Bool
tyVarIsIn gv node tvs = case piNodeTyVar gv node of
  Just tv -> tv `S.member` tvs
  Nothing -> False

-- | Create and 'LEdge' from the given data.
mkEdge :: PiNode Int -> PiNode Int -> EdgeType -> LEdge EdgeType
mkEdge p q e = (piNodeToNode p, piNodeToNode q, e)

-- | Create an undirected unification edge. That is
--   two edges in a list.
mkUnifEdge :: PiNode Int -> PiNode Int -> [LEdge EdgeType]
mkUnifEdge p q = [ mkEdge p q Unif, mkEdge q p Unif]

-- | Efficient removal of duplicate elements in O(n * log(n)).
--   The result list is ordered in ascending order.
removeDup :: (Ord a) => [a] -> [a]
removeDup = S.toAscList . S.fromList

-- | Collectes all ambiguous type variables from the associated constraints.
--   Only collect type variables that are at the top-level.
--   Top-level variables are enough, because the test in 'isUnambiguous'
--   only checks if the associated type of a node is in the set of
--   ambiguous type variables (A(v) in ftv(P) | ftv(Gamma, t)) and
--   A(v) can only be a top-level type variable.
collectAmbiguousTyVars :: Map Int (Ct, Type, Type, Type) -> Set TyVar
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
noPathExists :: GraphView -> PiNode Int -> PiNode Int -> Bool
noPathExists gv p q = null
                    $ esp (piNodeToNode p) (piNodeToNode q) (graph gv)

-- -----------------------------------------------------------------------------
-- Unimportant Instances
-- -----------------------------------------------------------------------------

instance (Show a) => Outputable (PiNode a) where
  ppr = O.text . show

instance Outputable GraphView where
  ppr gv = O.text "GraphView {" O.$$
       O.nest 2 ( ppr (vertexConstraints gv)
         O.$$ ppr (vertices gv)
         O.$$ O.text (show $ graph gv)
         O.$$ O.int (nextVertexIndex gv)
       )
       O.$$ O.text "}"
