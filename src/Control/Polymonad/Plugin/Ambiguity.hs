
module Control.Polymonad.Plugin.Ambiguity
  ( isAllUnambigious ) where

import Data.Maybe ( catMaybes )
import Data.Set ( Set )
import qualified Data.Set as S

import Type ( TyVar )

import Control.Polymonad.Plugin.GraphView

-- | Check if the given 'GraphView' is unambiguous in sense of
--   definition 7 in the "Polymonad Programming" paper. This
--   does /not/ look at subgraphes; it only checks if the given graph
--   fulfills the criteria.
isUnambiguous :: GraphView -> Bool
isUnambiguous gv =
  let -- Check of there are an paths from a 'Pi2' to a 'Pi0' or a 'Pi1'.
      noPaths :: Bool
      noPaths = and
              [ noPathExists gv (Pi2 i) (Pi0 i) &&
                noPathExists gv (Pi2 i) (Pi1 i)
              | Pi2 i <- S.toList $ gvPiNodes gv ]
      -- Collect all ambiguous type variables in the constraints.
      ambTvs :: Set TyVar
      ambTvs = getAmbiguousConstraintTyVars gv
      -- Get nodes of ambiguous type variables.
      ambNodes :: Set PiNode
      ambNodes = S.filter (\node -> tyVarIsIn gv node ambTvs) (gvPiNodes gv)
  -- Check the ambiguity conditions:
  --   1. No paths from a Pi.2 to a Pi.0 or Pi.1.
  --   2. For all nodes with an ambiguous type variable there exists a connected flow edge.
  in noPaths && all ((>= 1) . flowEdgeCountAtNode gv) ambNodes

-- | Find all of the paths in the given graph that are part of the
--   reason why it is ambiguous.
ambigiousBadPaths :: GraphView -> [[PiNode]]
ambigiousBadPaths gv = catMaybes
  $  [ getPath gv (Pi2 i) (Pi0 i) | Pi2 i <- S.toList $ gvPiNodes gv ]
  ++ [ getPath gv (Pi2 i) (Pi1 i) | Pi2 i <- S.toList $ gvPiNodes gv ]

-- Check if the given graph view is unambigious as described in
-- definition 7 in the "Polymonad Programming" paper by looking
-- at all subgraphs with fewer unification edges.
isAllUnambigious :: GraphView -> Bool
isAllUnambigious gvOrig = isAllUnambigious' gvSmall
  where
    -- The graph we want to work with in the rest of the algorithm.
    -- We can safely remove all unification edges that are not
    -- flow edges, because removing an edge can not create a
    -- new path and we are only removing non-flow-edges.
    gvSmall :: GraphView
    gvSmall = foldr (\e g -> if isUnificationEdge e && not (isFlowLEdge g e && isAdjToAmbiguousNodes g e)
                                then removeLEdge e g
                                else g)
                    gvOrig (getLEdges gvOrig)

    -- Assumes the graph has already been minified as in 'gvSmall'.
    isAllUnambigious' :: GraphView -> Bool
    isAllUnambigious' gv = isUnambiguous gv || maybe False isAllUnambigious' reduceBadPaths
      where
        -- Look at all the paths from a pi.2 to a pi.0 or pi.1 node.
        -- They cause the graph to be ambigious. Try to break up those
        -- paths without removing flow edges that are essential for its
        -- unambigiuity.
        reduceBadPaths :: Maybe GraphView
        reduceBadPaths = do
            gvReduced <- foldr f (Just gv) (ambigiousBadPaths gv)
            if gvGraph gv == gvGraph gvReduced then Nothing else return gvReduced
          where f :: [PiNode] -> Maybe GraphView -> Maybe GraphView
                f _ Nothing = Nothing -- We failed in reducing, so we remain failing.
                f [] _g = Nothing -- We could not break up the path: Fail
                f [_] _g = Nothing -- We could not break up the path: Fail
                f (p:q:ps) (Just g) = case (isEdge gv p q Unif, isFlowEdge gv p q) of
                  -- We found a flow edge. We may only remove it if the number of flow edges at each node is big enough.
                  (True, True) -> case (flowEdgeCountAtNode gv p, flowEdgeCountAtNode gv q) of
                    (i, j) | i > 1 && j > 1 -> Just $ removeLEdge (piNodeToNode p, piNodeToNode q, Unif) gv
                    (_, _) -> f (q:ps) (Just g)
                  -- A unification but no flow edge: We can remove it safly to interrupt the path.
                  -- This case probably is never used because we work on gvSmall from the beginning.
                  (True, False) -> Just $ removeLEdge (piNodeToNode p, piNodeToNode q, Unif) gv
                  -- This is a bind edge or no edge at all, either way we can't remove it
                  (False, _) -> f (q:ps) (Just g)
