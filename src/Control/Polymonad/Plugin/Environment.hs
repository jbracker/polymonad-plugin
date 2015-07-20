
module Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , runPmPlugin
  , getPolymonadClass, getPolymonadModule, getPolymonadInstances
  , pmErrMsg, pmDebugMsg
  ) where

import Control.Monad.Trans.Reader ( ReaderT, runReaderT, asks )

import Class ( Class )
import Module ( Module )
import InstEnv ( ClsInst )
import TcPluginM ( TcPluginM )

import Control.Polymonad.Plugin.Detect
  ( polymonadModuleName, polymonadClassName
  , findPolymonadModule, findPolymonadClass )

import Control.Polymonad.Plugin.Core
  ( getPolymonadInstancesInScope )

type PmPluginM = ReaderT PmPluginEnv TcPluginM

data PmPluginEnv = PmPluginEnv
  { pmEnvPolymonadModule    :: Module
  , pmEnvPolymonadClass     :: Class
  , pmEnvPolymonadInstances :: [ClsInst]
  }

runPmPlugin :: PmPluginM a -> TcPluginM (Either String a)
runPmPlugin pmM = do
  mPmMdl <- findPolymonadModule
  mPmCls <- findPolymonadClass
  case (mPmMdl, mPmCls) of
    (Just pmMdl, Just pmCls) -> do
      pmInsts <- getPolymonadInstancesInScope
      result <- runReaderT pmM PmPluginEnv
        { pmEnvPolymonadModule = pmMdl
        , pmEnvPolymonadClass  = pmCls
        , pmEnvPolymonadInstances = pmInsts
        }
      return $ Right result
    _ -> return $ Left $ pmErrMsg
      $ "Could not find "
      ++ polymonadModuleName ++ " module and " ++ polymonadClassName ++ " class!"

getPolymonadClass :: PmPluginM Class
getPolymonadClass = asks pmEnvPolymonadClass

getPolymonadModule :: PmPluginM Module
getPolymonadModule = asks pmEnvPolymonadModule

getPolymonadInstances :: PmPluginM [ClsInst]
getPolymonadInstances = asks pmEnvPolymonadInstances

prefixMsg :: String -> String -> String
prefixMsg prefix = unlines . fmap (prefix ++) . lines

pmErrMsg :: String -> String
pmErrMsg = prefixMsg "[Polymonad] ERROR: "

pmDebugMsg :: String -> String
pmDebugMsg = prefixMsg "[Polymonad] "
