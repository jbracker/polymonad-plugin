
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoin
  ) where

import Data.Set ( Set )
import qualified Data.Set as S

import Type ( Type )
import InstEnv ( ClsInst(..) )

import Control.Polymonad.Plugin.Utils ( collectTopTyCons )
import Control.Polymonad.Plugin.Instance ( instanceTyCons )

-- | Calculate the principal join of a set of type constructors.
--   For this to work properly all of the given types need to be
--   type constructors or partially applied type constructors.
--   The principal join is defined in definition 4 of the
--   "Polymonad Programming" paper.
--   TODO: UNFINISHED
--   @principalJoin insts f ms@
--   insts - Available polymonad instances
--   f     - The set to calculate the join for
--   ms    - The target constructors.
principalJoin :: [ClsInst] -> [(Type, Type)] -> [Type] -> Maybe Type
principalJoin insts f ms = undefined -- TODO: IMPLEMENT - How?
  where
    availTyCons = S.unions (instanceTyCons <$> insts)
                `S.union` collectTopTyCons ms
                `S.union` collectTopTyCons (concatMap (\(a,b) -> [a,b]) f)

isPrincipalJoin :: [ClsInst] -> [(Type, Type)] -> [Type] -> Type -> Bool
isPrincipalJoin insts f ms m = undefined
  where
    
