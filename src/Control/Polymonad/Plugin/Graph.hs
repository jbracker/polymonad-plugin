
-- | Graph structure given by the "Polymonad Programming"
--   paper (Hicks 2014) used for coherence.
module Control.Polymonad.Plugin.Graph
  ( GraphView
  , vertexAssignment
  , mkGraphView
  ) where

import Data.Maybe ( isJust )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Graph.Inductive ( Graph(..), Gr, LNode, LEdge )

import Type ( Type, isTyVarTy, getTyVar_maybe )
import TcRnTypes ( Ct(..) )
import Outputable ( Outputable(..) )
import qualified Outputable as O

import Control.Polymonad.Plugin.Constraint ( constraintClassTyArgs )

data PiNode a
  = Pi0 a
  | Pi1 a
  | Pi2 a
  deriving ( Eq, Ord, Show )

instance (Show a) => Outputable (PiNode a) where
  ppr = O.text . show

data EdgeType = Unif | Bind deriving ( Eq, Ord, Show )

data GraphView = GraphView
  { vertexConstraints :: Map Int (Ct, Type, Type, Type)
  , vertices :: Set (PiNode Int)
  , graph :: Gr (PiNode Int) EdgeType
  , nextVertexIndex :: Int
  }

instance Outputable GraphView where
  ppr gv = O.text "GraphView {" O.$$
         ( O.nest 2 $ ppr (vertexConstraints gv)
           O.$$ ppr (vertices gv)
           O.$$ O.text (show $ graph gv)
           O.$$ O.int (nextVertexIndex gv)
         )
         O.$$ O.text "}"

vertexAssignment :: GraphView -> PiNode Int -> Maybe Type
vertexAssignment gv p = vertexAssignment' (vertexConstraints gv) p

vertexAssignment' :: Map Int (Ct, Type, Type, Type) -> PiNode Int -> Maybe Type
vertexAssignment' vAssign (Pi0 i) = fmap (\(_, t, _, _) -> t) $ M.lookup i vAssign
vertexAssignment' vAssign (Pi1 i) = fmap (\(_, _, t, _) -> t) $ M.lookup i vAssign
vertexAssignment' vAssign (Pi2 i) = fmap (\(_, _, _, t) -> t) $ M.lookup i vAssign

vertexToNode :: PiNode Int -> LNode (PiNode Int)
vertexToNode (Pi0 i) = ( i * 3 + 0, Pi0 i )
vertexToNode (Pi1 i) = ( i * 3 + 1, Pi1 i )
vertexToNode (Pi2 i) = ( i * 3 + 2, Pi2 i )

isSameTyVar :: Map Int (Ct, Type, Type, Type) -> PiNode Int -> PiNode Int -> Bool
isSameTyVar vAssign p q = case (vertexAssignment' vAssign p, vertexAssignment' vAssign q) of
    (Just tp, Just tq) -> isTyVarTy tp && isTyVarTy tq && getTyVar_maybe tp == getTyVar_maybe tq
    _ -> False

mkEdge :: PiNode Int -> PiNode Int -> EdgeType -> LEdge EdgeType
mkEdge p q e = (fst $ vertexToNode p, fst $ vertexToNode q, e)

mkUnifEdge :: PiNode Int -> PiNode Int -> [LEdge EdgeType]
mkUnifEdge p q = [ mkEdge p q Unif, mkEdge q p Unif]

mkGraphView :: [Ct] -> GraphView
mkGraphView cts =
  let vs = fmap (\(ct, Just (p0 : p1 : p2 : _)) -> (ct, p0, p1, p2))
         $ filter (\(_, ts) -> isJust ts)
         $ fmap (\ct -> (ct, constraintClassTyArgs ct)) cts
      is = [0 .. length vs - 1]
      verts = S.unions [ S.fromList [Pi0 i, Pi1 i, Pi2 i] | i <- is ]
      vertConstr = M.fromList $ zip is vs
      unifEdges = S.toList
                $ S.fromList
                [ S.fromList [v , v']
                | v <- S.toList verts
                , v' <- S.toList verts
                , v /= v'
                , isSameTyVar vertConstr v v' ]
  in GraphView
    { vertexConstraints = vertConstr
    , vertices = verts
    , graph = mkGraph (fmap vertexToNode (S.toList verts))
            $ concat [ mkUnifEdge v v' | [v,v'] <- fmap S.toList unifEdges]
            ++ [ mkEdge (Pi0 i) (Pi2 i) Bind | i <- is ]
            ++ [ mkEdge (Pi1 i) (Pi2 i) Bind | i <- is ]
    , nextVertexIndex = length vs
    }

-- mkGraph :: [LNode a] -> [LEdge b] -> gr a b
