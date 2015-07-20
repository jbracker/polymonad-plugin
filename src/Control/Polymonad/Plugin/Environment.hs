
module Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , runPmPlugin
  , getPolymonadClass, getPolymonadModule
  , getPolymonadInstances
  , getIdentityTyCon, getIdentityModule
  , getInstEnvs
  , pmErrMsg, pmDebugMsg
  ) where

import Control.Monad.Trans.Reader ( ReaderT, runReaderT, asks )
import Control.Monad.Trans.Class ( lift )

import Class ( Class )
import Module ( Module )
import InstEnv ( ClsInst, InstEnvs, classInstances )
import TyCon ( TyCon )
import TcPluginM ( TcPluginM )
import qualified TcPluginM

import Control.Polymonad.Plugin.Detect
  ( polymonadModuleName, polymonadClassName
  , identityModuleName, identityTyConName
  , findPolymonadModule, findPolymonadClass
  , findIdentityModule, findIdentityTyCon )

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

getPolymonadClass :: PmPluginM Class
getPolymonadClass = asks pmEnvPolymonadClass

getPolymonadModule :: PmPluginM Module
getPolymonadModule = asks pmEnvPolymonadModule

getPolymonadInstances :: PmPluginM [ClsInst]
getPolymonadInstances = asks pmEnvPolymonadInstances

getIdentityModule :: PmPluginM Module
getIdentityModule = asks pmEnvIdentityModule

getIdentityTyCon :: PmPluginM TyCon
getIdentityTyCon = asks pmEnvIdentityTyCon

getInstEnvs :: PmPluginM InstEnvs
getInstEnvs = lift TcPluginM.getInstEnvs

prefixMsg :: String -> String -> String
prefixMsg prefix = unlines . fmap (prefix ++) . lines

pluginMsgPrefix :: String
pluginMsgPrefix = "[Polymonad]"

pmErrMsg :: String -> String
pmErrMsg = prefixMsg $ pluginMsgPrefix ++ " ERROR: "

pmDebugMsg :: String -> String
pmDebugMsg = prefixMsg $ pluginMsgPrefix ++ " "

-- | Returns a list of all 'Control.Polymonad' instances that are currently in scope.
getPolymonadInstancesInScope :: TcPluginM [ClsInst]
getPolymonadInstancesInScope = do
  mPolymonadClass <- findPolymonadClass
  case mPolymonadClass of
    Just polymonadClass -> do
      instEnvs <- TcPluginM.getInstEnvs
      return $ classInstances instEnvs polymonadClass
    Nothing -> return []
