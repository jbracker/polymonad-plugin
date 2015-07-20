
module Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , runPmPlugin
  , getPolymonadClass, getPolymonadModule
  , getPolymonadInstances
  , getIdentityTyCon, getIdentityModule
  , pmErrMsg, pmDebugMsg
  ) where

import Control.Monad.Trans.Reader ( ReaderT, runReaderT, asks )

import Class ( Class )
import Module ( Module )
import InstEnv ( ClsInst )
import TyCon ( TyCon )
import TcPluginM ( TcPluginM )

import Control.Polymonad.Plugin.Detect
  ( polymonadModuleName, polymonadClassName
  , identityModuleName, identityTyConName
  , findPolymonadModule, findPolymonadClass
  , findIdentityModule, findIdentityTyCon )

import Control.Polymonad.Plugin.Core
  ( getPolymonadInstancesInScope )

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

prefixMsg :: String -> String -> String
prefixMsg prefix = unlines . fmap (prefix ++) . lines

pluginMsgPrefix :: String
pluginMsgPrefix = "[Polymonad]"

pmErrMsg :: String -> String
pmErrMsg = prefixMsg $ pluginMsgPrefix ++ " ERROR: "

pmDebugMsg :: String -> String
pmDebugMsg = prefixMsg $ pluginMsgPrefix ++ " "
