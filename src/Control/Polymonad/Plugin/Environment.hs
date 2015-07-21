
-- | Provides the polymonad plugin monadic envionment,
--   access to the environment and message printing capabilities.
module Control.Polymonad.Plugin.Environment
  ( -- * Polymonad Plugin Monad
    PmPluginM
  , runPmPlugin
    -- * Polymonad Plugin Environment Access
  , getPolymonadClass, getPolymonadModule
  , getPolymonadInstances
  , getIdentityTyCon, getIdentityModule
  , getInstEnvs
    -- * Debug and Error Output
  , printErr, printMsg, printObj, pprToStr
  ) where

import Control.Monad.Trans.Reader ( ReaderT, runReaderT, asks )
import Control.Monad.Trans.Class ( lift )

import Class ( Class )
import Module ( Module )
import InstEnv ( ClsInst, InstEnvs, classInstances )
import TyCon ( TyCon )
import TcPluginM ( TcPluginM, tcPluginIO )
import qualified TcPluginM
import Outputable
  ( Outputable( ppr )
  --, text, parens, (<>)
  , showSDocUnsafe )

import Control.Polymonad.Plugin.Detect
  ( polymonadModuleName, polymonadClassName
  , identityModuleName, identityTyConName
  , findPolymonadModule, findPolymonadClass
  , findIdentityModule, findIdentityTyCon )

-- -----------------------------------------------------------------------------
-- Plugin Monad
-- -----------------------------------------------------------------------------

type PmPluginM = ReaderT PmPluginEnv TcPluginM

data PmPluginEnv = PmPluginEnv
  { pmEnvPolymonadModule    :: Module
  , pmEnvPolymonadClass     :: Class
  , pmEnvPolymonadInstances :: [ClsInst]
  , pmEnvIdentityModule :: Module
  , pmEnvIdentityTyCon  :: TyCon
  }

runPmPlugin :: PmPluginM a -> TcPluginM (Either String a)
runPmPlugin pmM = do
  mPmMdl <- findPolymonadModule
  mPmCls <- findPolymonadClass
  case (mPmMdl, mPmCls) of
    (Just pmMdl, Just pmCls) -> do
      mIdMdl <- findIdentityModule
      mIdTyCon <- findIdentityTyCon
      case (mIdMdl, mIdTyCon) of
        (Just idMdl, Just idTyCon) -> do
          pmInsts <- getPolymonadInstancesInScope
          result <- runReaderT pmM PmPluginEnv
            { pmEnvPolymonadModule = pmMdl
            , pmEnvPolymonadClass  = pmCls
            , pmEnvPolymonadInstances = pmInsts
            , pmEnvIdentityModule = idMdl
            , pmEnvIdentityTyCon  = idTyCon
            }
          return $ Right result
        _ -> return $ Left $ pmErrMsg
          $ "Could not find " ++ identityModuleName
          ++ " module and " ++ identityTyConName ++ " type constructor!"
    _ -> return $ Left $ pmErrMsg
      $ "Could not find " ++ polymonadModuleName
      ++ " module and " ++ polymonadClassName ++ " class!"

-- -----------------------------------------------------------------------------
-- Plugin Environment Access
-- -----------------------------------------------------------------------------

-- | Returns the 'Control.Polymonad' class.
getPolymonadClass :: PmPluginM Class
getPolymonadClass = asks pmEnvPolymonadClass

-- | Returns the module containing the 'Control.Polymonad' class.
getPolymonadModule :: PmPluginM Module
getPolymonadModule = asks pmEnvPolymonadModule

-- | Returns all instances of the 'Control.Polymonad' class that are in scope.
getPolymonadInstances :: PmPluginM [ClsInst]
getPolymonadInstances = asks pmEnvPolymonadInstances

-- | Returns the module that contains the 'Data.Functor.Identity' data type.
getIdentityModule :: PmPluginM Module
getIdentityModule = asks pmEnvIdentityModule

-- | Returns the type constructor of the 'Data.Functor.Identity' data type.
getIdentityTyCon :: PmPluginM TyCon
getIdentityTyCon = asks pmEnvIdentityTyCon

-- | Shortcut to access the instance environments.
getInstEnvs :: PmPluginM InstEnvs
getInstEnvs = lift TcPluginM.getInstEnvs

-- -----------------------------------------------------------------------------
-- Plugin internal utility
-- -----------------------------------------------------------------------------

-- | Returns a list of all 'Control.Polymonad' instances that are currently in scope.
getPolymonadInstancesInScope :: TcPluginM [ClsInst]
getPolymonadInstancesInScope = do
  mPolymonadClass <- findPolymonadClass
  case mPolymonadClass of
    Just polymonadClass -> do
      instEnvs <- TcPluginM.getInstEnvs
      return $ classInstances instEnvs polymonadClass
    Nothing -> return []

-- -----------------------------------------------------------------------------
-- Plugin debug and error printing
-- -----------------------------------------------------------------------------

-- | Print some generic outputable object from the plugin (Unsafe).
printObj :: Outputable o => o -> PmPluginM ()
printObj = printMsg . pprToStr

-- | Print a message from the plugin.
printMsg :: String -> PmPluginM ()
printMsg = internalPrint . pmDebugMsg

-- | Print a error message from the plugin.
printErr :: String -> PmPluginM ()
printErr = internalPrint . pmErrMsg

-- | Internal function for printing from within the monad.
internalPrint :: String -> PmPluginM ()
internalPrint = lift . tcPluginIO . putStrLn

-- | Convert some generic outputable to a string (Unsafe).
pprToStr :: Outputable o => o -> String
pprToStr = showSDocUnsafe . ppr

-- | @prefixMsg prefix msg@ prefixes a message with the given string.
prefixMsg :: String -> String -> String
prefixMsg prefix = unlines . fmap (prefix ++) . lines

-- | Message prefix of the polymonad plugin.
pluginMsgPrefix :: String
pluginMsgPrefix = "[Polymonad]"

-- | Prefix a message with the error prefix.
pmErrMsg :: String -> String
pmErrMsg = prefixMsg $ pluginMsgPrefix ++ " ERROR: "

-- | Prefix a message with the standard debug prefix.
pmDebugMsg :: String -> String
pmDebugMsg = prefixMsg $ pluginMsgPrefix ++ " "
