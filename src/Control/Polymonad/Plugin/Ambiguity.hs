
module Control.Polymonad.Plugin.Ambiguity
  ( isAllUnambiguous ) where

import Data.Maybe ( catMaybes )
import Data.Set ( Set )
import qualified Data.Set as S

import Type ( TyVar )

--import Control.Polymonad.Plugin.Log ( printTrace, printObjTrace )
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
  -- Check the ambiguity conditions:https://www.magickartenmarkt.de/Products/Storage/Magic+2013+Storage+box+for+2000+cards
  --   1. No paths from a Pi.2 to a Pi.0 or Pi.1.
  --   2. For all nodes with an ambiguous type variable there exists a connected flow edge.
  in noPaths && all ((>= 1) . flowEdgeCountAtNode gv) ambNodes

-- | Find all of the paths in the given graph that are part of the
--   reason why it is ambiguous.
ambiguousBadPaths :: GraphView -> [[PiNode]]
ambiguousBadPaths gv = catMaybes
  $  [ getPath gv (Pi2 i) (Pi0 i) | Pi2 i <- S.toList $ gvPiNodes gv ]
  ++ [ getPath gv (Pi2 i) (Pi1 i) | Pi2 i <- S.toList $ gvPiNodes gv ]

-- Check if the given graph view is unambiguous as described in
-- definition 7 in the "Polymonad Programming" paper by looking
-- at all subgraphs with fewer unification edges.
isAllUnambiguous :: GraphView -> Bool
isAllUnambiguous gvOrig = isAllUnambiguous' gvSmall
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
    isAllUnambiguous' :: GraphView -> Bool
    isAllUnambiguous' gv = isUnambiguous gv || reduceBadPaths ambBadPaths
      where
        ambBadPaths :: [[PiNode]]
        ambBadPaths = ambiguousBadPaths gv

        -- Try to break up the given ambiguous path in the graph view. If
        -- we are able to remove one edge of the path (looking through the
        -- path from beginning to end), we return the reduced graph view
        -- together with the rest of the path that was not looked at.
        tryReduceAmbGraph :: [PiNode] -> GraphView -> Maybe (GraphView, [PiNode])
        tryReduceAmbGraph [] _g = Nothing -- We could not break up the path: Fail
        tryReduceAmbGraph [_] _g = Nothing -- We could not break up the path: Fail
        tryReduceAmbGraph (p:q:ps) g =
          case (isEdge gv p q Unif, isFlowEdge gv p q) of
            -- We found a flow edge. We may only remove it if the number of flow edges at each node is big enough.
            (True, True) -> case (flowEdgeCountAtNode gv p, flowEdgeCountAtNode gv q) of
              (i, j) | i > 1 && j > 1 -> Just (removeLEdge (piNodeToNode p, piNodeToNode q, Unif) gv, q : ps)
              (_, _) -> tryReduceAmbGraph (q:ps) g
            -- A unification but no flow edge: We can remove it safly to interrupt the path.
            -- This case probably is never used because we work on gvSmall from the beginning.
            (True, False) -> Just (removeLEdge (piNodeToNode p, piNodeToNode q, Unif) gv, q : ps)
            -- This is a bind edge or no edge at all, either way we can't remove it
            (False, _) -> tryReduceAmbGraph (q:ps) g

        -- Look at all the paths from a pi.2 to a pi.0 or pi.1 node.
        -- They cause the graph to be ambiguous. Try to break up those
        -- paths without removing flow edges that are essential for its
        -- unambiguity.
        reduceBadPaths :: [[PiNode]] -> Bool -- Maybe GraphView
        -- There are no bad paths, just check if the graph is unambiguous
        reduceBadPaths [] = isUnambiguous gv
        -- There is at least on bad path, try to reduce the graph on it.
        reduceBadPaths (p : ps) = case tryReduceAmbGraph p gv of
          -- We are not able to break up this path, the graph remain ambiguous.
          Nothing -> False
          Just (reducedGv, restP)
            -> isAllUnambiguous' reducedGv -- If the reduced GV is unambiguous we are done.
            || reduceBadPaths (restP : ps) -- If breaking up one edge
                                           -- does not work, we can try to
                                           -- remove a different edge of the path.
