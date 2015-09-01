
-- | Core functions the plugin relies on to interact with GHCs API.
module Control.Polymonad.Plugin.Core
  ( isInstanceOf
  ) where

import InstEnv ( ClsInst )
import Type ( Type )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runTcPlugin
  , getGivenConstraints
  , throwPluginError )
import Control.Polymonad.Plugin.Instance ( isInstantiatedBy )

-- | Checks if the given arguments types to the free variables in the
--   class instance actually form a valid instantiation of that instance.
--   The given arguments need to match up with the list of free type variables
--   given for the class instance ('is_tvs').
--
--   Caveat: This currently only matches class constraints, but not type
--   equality or type function constraints properly.
isInstanceOf :: [Type] -> ClsInst -> PmPluginM Bool
isInstanceOf tys inst = do
  givenCts <- getGivenConstraints
  res <- runTcPlugin $ isInstantiatedBy givenCts tys inst
  case res of
    Left err -> throwPluginError err
    Right b -> return b
