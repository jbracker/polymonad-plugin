
-- | Graph structure given by the "Polymonad Programming" 
--   paper (Hicks 2014) used for coherence.
module Control.Polymonad.Plugin.Graph 
  ( GraphView(..)
  , mkGraphView
  ) where

import Type ( Type )
import TcRnTypes ( Ct(..) )
import Outputable ( Outputable(..) )
import qualified Outputable as O

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Graph.Inductive ( Gr )

data PiNode a
  = Pi0 a
  | Pi1 a
  | Pi2 a
  deriving ( Eq, Ord, Show )

instance (Show a) => Outputable (PiNode a) where
  ppr = O.text . show


data GraphView = GraphView
  { vertexConstraints :: Map Int (Ct, Type, Type, Type)
  , vertices :: Set (PiNode Int)
  , vertexAssignment :: Map Int Type
  , unificationGraph :: Gr (PiNode Int) ()
  , bindGraph :: Gr (PiNode Int) ()
  }

mkGraphView :: GraphView
mkGraphView = undefined