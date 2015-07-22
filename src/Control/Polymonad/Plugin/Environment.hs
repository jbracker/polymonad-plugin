
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
  , getGivenConstraints, getWantedConstraints
  , getCurrentPolymonad
  , getInstEnvs
    -- * Debug and Error Output
  , printErr, printMsg, printObj, pprToStr
    -- * Other Utilities
  , isClassConstraint
  ) where

import Data.Set ( Set )

import Control.Monad.Trans.Reader ( ReaderT, runReaderT, asks )
import Control.Monad.Trans.Class ( lift )

import Class ( Class )
import Module ( Module )
import InstEnv ( ClsInst, InstEnvs )
import Type ( TyVar, getClassPredTys_maybe )
import TyCon ( TyCon )
import TcRnTypes
  ( Ct(..), CtEvidence(..)
  , isGivenCt, isWantedCt )
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
  , findIdentityModule, findIdentityTyCon
  , findPolymonadInstancesInScope )

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
  , pmEnvGivenConstraints  :: [Ct]
  , pmEnvWantedConstraints :: [Ct]
  , pmEnvCurrentPolymonad  :: (Set TyCon, Set TyVar, [ClsInst], [Ct])
  }

-- | @runPmPlugin given wanted m@ runs the given polymonad plugin solver @m@
--   within the type checker plugin monad. The _given_ constraints are
--   passed in through @given@ and the _wanted_ constraints are passed in
--   through @wanted@.
--
--   The function will make sure that only the polymonad constraints
--   and actually _given_ or _wanted_ constraints
--   are kept, respectivly.
runPmPlugin :: [Ct] -> [Ct] -> PmPluginM a -> TcPluginM (Either String a)
runPmPlugin givenCts wantedCts pmM = do
  mPmMdl <- findPolymonadModule
  mPmCls <- findPolymonadClass
  case (mPmMdl, mPmCls) of
    (Just pmMdl, Just pmCls) -> do
      mIdMdl <- findIdentityModule
      mIdTyCon <- findIdentityTyCon
      case (mIdMdl, mIdTyCon) of
        (Just idMdl, Just idTyCon) -> do
          pmInsts <- findPolymonadInstancesInScope
          let givenPmCts  = filter (\ct -> isGivenCt ct  && isClassConstraint pmCls ct) givenCts
          let wantedPmCts = filter (\ct -> isWantedCt ct && isClassConstraint pmCls ct) wantedCts
          let currPm = (undefined, undefined, undefined, givenPmCts) -- TODO
          result <- runReaderT pmM PmPluginEnv
            { pmEnvPolymonadModule = pmMdl
            , pmEnvPolymonadClass  = pmCls
            , pmEnvPolymonadInstances = pmInsts
            , pmEnvIdentityModule = idMdl
            , pmEnvIdentityTyCon  = idTyCon
            , pmEnvGivenConstraints = givenPmCts
            , pmEnvWantedConstraints = wantedPmCts
            , pmEnvCurrentPolymonad = currPm
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

-- | Returns the given constraints of this plugin solver call.
--   All of the returned constraints are guarenteed to be _given_ constraints
--   and actual 'Control.Polymonad' constraints.
getGivenConstraints :: PmPluginM [Ct]
getGivenConstraints = asks pmEnvGivenConstraints

-- | Returns the wanted constraints of this plugin solver call.
--   All of the returned constraints are guarenteed to be _wanted_ constraints
--   and actual 'Control.Polymonad' constraints.
getWantedConstraints :: PmPluginM [Ct]
getWantedConstraints = asks pmEnvWantedConstraints

-- | Returns the polymonad that the wanted constraints need solving for.
--
--   The available type constructors are given by the first and second elements
--   of the triple. They can be not-applied type constructors, e.g. 'Identity',
--   or type variables in case there are given constraints that involve them.
--
--   The available bind operations are given by the thrid and fourth elements
--   of the triple. They come as class instances that provide bind operations
--   or given constraints that need to be assumed to be existing bind
--   operations.
getCurrentPolymonad :: PmPluginM (Set TyCon, Set TyVar, [ClsInst], [Ct])
getCurrentPolymonad = asks pmEnvCurrentPolymonad

-- | Shortcut to access the instance environments.
getInstEnvs :: PmPluginM InstEnvs
getInstEnvs = lift TcPluginM.getInstEnvs

-- -----------------------------------------------------------------------------
-- Plugin utility
-- -----------------------------------------------------------------------------

-- | Check if the given constraint is a class constraint of the given class.
isClassConstraint :: Class -> Ct -> Bool
isClassConstraint wantedClass ct =
  case ct of
    CDictCan { cc_class = cls } -> cls == wantedClass
    CNonCanonical { cc_ev = ev } -> case getClassPredTys_maybe (ctev_pred ev) of
      Just (cls, _args) -> cls == wantedClass
      _ -> False
    _ -> False

-- -----------------------------------------------------------------------------
-- Plugin debug and error printing
-- -----------------------------------------------------------------------------

-- | Print some generic outputable object from the plugin (Unsafe).
printObj :: Outputable o => o -> PmPluginM ()
printObj = internalPrint . pmObjMsg . pprToStr

-- | Print a message from the plugin.
printMsg :: String -> PmPluginM ()
printMsg = internalPrint . pmDebugMsg

-- | Print a error message from the plugin.
printErr :: String -> PmPluginM ()
printErr = internalPrint . pmErrMsg

-- | Internal function for printing from within the monad.
internalPrint :: String -> PmPluginM ()
internalPrint = lift . tcPluginIO . putStr

-- | Convert some generic outputable to a string (Unsafe).
pprToStr :: Outputable o => o -> String
pprToStr = showSDocUnsafe . ppr

-- | @prefixMsg prefix msg@ prefixes a message with the given string.
prefixMsg :: String -> String -> String
prefixMsg prefix = unlines . fmap (prefix ++) . lines

-- | Message prefix of the polymonad plugin.
pluginMsgPrefix :: String
pluginMsgPrefix = "[PM]"

-- | Prefix a message with the error prefix.
pmErrMsg :: String -> String
pmErrMsg = prefixMsg $ pluginMsgPrefix ++ " ERROR: "

-- | Prefix a message with the standard debug prefix.
pmDebugMsg :: String -> String
pmDebugMsg = prefixMsg $ pluginMsgPrefix ++ " "

-- | Prefix a message with the debug prefix and a note that this is a
--   printed object.
pmObjMsg :: String -> String
pmObjMsg = prefixMsg $ pluginMsgPrefix ++ "> "
