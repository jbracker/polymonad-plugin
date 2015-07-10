
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoin
  ) where

import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( forM )

import Type ( Type, mkTyConTy )
import InstEnv ( ClsInst(..) )
import TcRnTypes ( TcPluginM )

import Control.Polymonad.Plugin.Utils ( collectTopTyCons )
import Control.Polymonad.Plugin.Instance ( instanceTyCons )
import Control.Polymonad.Plugin.Core ( pickPolymonadInstance )
import Control.Polymonad.Plugin.Detect ( getIdentityTyCon )

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

    isPrincipalJoin :: Type -> TcPluginM Bool
    isPrincipalJoin m = do
        hasOutMorphs <- and <$> forM ms (isMorphismBetween m)
        hasInMorphs  <- and <$> forM f (`isBind` m)
        return $ hasOutMorphs && hasInMorphs
      where
        isMorphismBetween :: Type -> Type -> TcPluginM Bool
        isMorphismBetween t0 t2 = do
          mIdTC <- getIdentityTyCon
          case mIdTC of
            Just idTC -> isJust <$> pickPolymonadInstance (t0, mkTyConTy idTC, t2)
            Nothing -> return False

        isBind :: (Type, Type) -> Type -> TcPluginM Bool
        isBind (t0, t1) t2 = isJust <$> pickPolymonadInstance (t0, t1, t2)
