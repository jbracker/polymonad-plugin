
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
  , getGivenPolymonadConstraints, getWantedPolymonadConstraints
  , getGivenConstraints, getWantedConstraints
  , getCurrentPolymonad
  , getInstEnvs
  , isDebugEnabled
  , withDebug, withoutDebug
  , throwPluginError
    -- * Debug and Error Output
  , assert
  , printErr, printMsg, printObj
  , printDebug, printDebugObj
  , printConstraints
  ) where

import Data.Set ( Set )
import Data.List ( nubBy, groupBy )

import Control.Monad ( when, unless, forM_ )
import Control.Monad.Trans.Reader ( ReaderT, runReaderT, asks, local )
import Control.Monad.Trans.Except ( ExceptT, runExceptT, throwE )
import Control.Monad.Trans.Class ( lift )

import Class ( Class )
import Module ( Module )
import InstEnv ( ClsInst, InstEnvs )
import Type ( Type, eqType )
import TyCon ( TyCon )
import TcRnTypes
  ( Ct
  , isGivenCt, isWantedCt, isDerivedCt )
import TcPluginM ( TcPluginM, tcPluginIO )
import qualified TcPluginM
import Outputable ( Outputable )
import SrcLoc ( srcSpanFileName_maybe )
import FastString ( unpackFS )

import Control.Polymonad.Plugin.Log
  ( pmErrMsg, pmDebugMsg, pmObjMsg
  , pprToStr
  , formatConstraint )
import Control.Polymonad.Plugin.Constraint
  ( isClassConstraint, constraintSourceLocation )
import Control.Polymonad.Plugin.Detect
  ( polymonadModuleName, polymonadClassName
  , identityModuleName, identityTyConName
  , findPolymonadModule, findPolymonadClass
  , findIdentityModule, findIdentityTyCon
  , findPolymonadInstancesInScope
  , selectPolymonadSubset )

-- -----------------------------------------------------------------------------
-- Plugin Monad
-- -----------------------------------------------------------------------------

type PmPluginM = ReaderT PmPluginEnv (ExceptT String TcPluginM)

data PmPluginEnv = PmPluginEnv
  { pmEnvPolymonadModule    :: Module
  , pmEnvPolymonadClass     :: Class
  , pmEnvPolymonadInstances :: [ClsInst]
  , pmEnvIdentityModule :: Module
  , pmEnvIdentityTyCon  :: TyCon
  , pmEnvGivenConstraints  :: [Ct]
  , pmEnvGivenPolymonadConstraints :: [Ct]
  , pmEnvWantedConstraints :: [Ct]
  , pmEnvWantedPolymonadConstraints :: [Ct]
  , pmEnvCurrentPolymonad  :: (Set TyCon, [Type], [ClsInst], [Ct])
  , pmEnvDebugEnabled :: Bool
  }

-- | @runPmPlugin givenAndDerived wanted m@ runs the given polymonad plugin solver @m@
--   within the type checker plugin monad. The /given/ and /derived/ constraints are
--   passed in through @givenAndDerived@ and the /wanted/ constraints are passed in
--   through @wanted@.
--
--   The function will make sure that only the polymonad constraints
--   and actually /given/, /derived/ or /wanted/ constraints
--   are kept, respectivly.
runPmPlugin :: [Ct] -> [Ct] -> PmPluginM a -> TcPluginM (Either String a)
runPmPlugin givenCts wantedCts pmM = do
  mPmMdl <- findPolymonadModule
  mPmCls <- findPolymonadClass
  case (mPmMdl, mPmCls) of
    (Right pmMdl, Just pmCls) -> do
      mIdMdl <- findIdentityModule
      mIdTyCon <- findIdentityTyCon
      case (mIdMdl, mIdTyCon) of
        (Right idMdl, Just idTyCon) -> do
          pmInsts <- findPolymonadInstancesInScope
          let givenPmCts  = filter (\ct -> (isGivenCt ct || isDerivedCt ct) && isClassConstraint pmCls ct) givenCts
          let wantedPmCts = filter (\ct -> isWantedCt ct && isClassConstraint pmCls ct) wantedCts
          (pmTcs, pmTvs, pmBindClsInsts) <- selectPolymonadSubset idTyCon pmCls pmInsts (givenPmCts, wantedPmCts)
          let currPm = (pmTcs, nubBy eqType pmTvs, pmBindClsInsts, givenPmCts)
          runExceptT $ runReaderT pmM PmPluginEnv
            { pmEnvPolymonadModule = pmMdl
            , pmEnvPolymonadClass  = pmCls
            , pmEnvPolymonadInstances = pmInsts
            , pmEnvIdentityModule = idMdl
            , pmEnvIdentityTyCon  = idTyCon
            , pmEnvGivenConstraints = givenCts
            , pmEnvWantedConstraints = wantedCts
            , pmEnvGivenPolymonadConstraints = givenPmCts
            , pmEnvWantedPolymonadConstraints = wantedPmCts
            , pmEnvCurrentPolymonad = currPm
            , pmEnvDebugEnabled = False
            }
        (Left errId, _) -> return $ Left
          $ pmErrMsg ("Could not find " ++ identityModuleName ++ " module:\n")
          ++ errId
        _ -> return $ Left
          $ pmErrMsg ("Could not find " ++ identityTyConName ++ " type constructor.")
    (Left errPm, _) -> return $ Left
      $ pmErrMsg ("Could not find " ++ polymonadModuleName
        ++ " module:\n")
      ++ errPm
    _ -> return $ Left
      $ pmErrMsg ("Could not find " ++ polymonadClassName ++ " class:")

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

-- | Returns the /given/ and /derived/ constraints of this plugin solver call.
--   All of the returned constraints are guarenteed to be /given/ or /derived/ constraints
--   and actual 'Control.Polymonad' constraints. The derived constraints
--   are included since they are constraints that result from the given constraints
--   and therefore can also be seen as given.
--   The list of /given/ and /derived/ constraints may be empty.
getGivenPolymonadConstraints :: PmPluginM [Ct]
getGivenPolymonadConstraints = asks pmEnvGivenPolymonadConstraints

-- | Returns the wanted constraints of this plugin solver call.
--   All of the returned constraints are guarenteed to be /wanted/ constraints
--   and actual 'Control.Polymonad' constraints.
--   The list of /wanted/ constraints will never be empty.
getWantedPolymonadConstraints :: PmPluginM [Ct]
getWantedPolymonadConstraints = asks pmEnvWantedPolymonadConstraints

-- | Returns all of the /given/ and /derived/ constraints of this plugin call.
--   This will also include the polymonad constraints that are
--   delivered by 'getGivenPolymonadConstraints'.
getGivenConstraints :: PmPluginM [Ct]
getGivenConstraints = asks pmEnvGivenConstraints

-- | Returns all of the wanted constraints of this plugin call.
--   This will also include the polymonad constraints that are
--   delivered by 'getWantedPolymonadConstraints'.
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
getCurrentPolymonad :: PmPluginM (Set TyCon, [Type], [ClsInst], [Ct])
getCurrentPolymonad = asks pmEnvCurrentPolymonad

-- | Shortcut to access the instance environments.
getInstEnvs :: PmPluginM InstEnvs
getInstEnvs = lift $ lift TcPluginM.getInstEnvs

-- | Checks wether debugging mode is enabled.
--   Debug mode allows debug messages to be printed.
isDebugEnabled :: PmPluginM Bool
isDebugEnabled = asks pmEnvDebugEnabled

withDebug :: PmPluginM a -> PmPluginM a
withDebug = local (\env -> env { pmEnvDebugEnabled = True })

withoutDebug :: PmPluginM a -> PmPluginM a
withoutDebug = local (\env -> env { pmEnvDebugEnabled = False })

-- -----------------------------------------------------------------------------
-- Plugin debug and error printing
-- -----------------------------------------------------------------------------

assert :: Bool -> String -> PmPluginM ()
assert cond msg = unless cond $ throwPluginError msg

throwPluginError :: String -> PmPluginM a
throwPluginError = lift . throwE

-- | Print some generic outputable object from the plugin (Unsafe).
printObj :: Outputable o => o -> PmPluginM ()
printObj = internalPrint . pmObjMsg . pprToStr

-- | Print a message from the plugin.
printMsg :: String -> PmPluginM ()
printMsg = internalPrint . pmDebugMsg

-- | Print a error message from the plugin.
printErr :: String -> PmPluginM ()
printErr = internalPrint . pmErrMsg

printDebug :: String -> PmPluginM ()
printDebug msg = do
  debug <- isDebugEnabled
  when debug $ internalPrint $ pmDebugMsg msg

printDebugObj :: (Outputable o) => o -> PmPluginM ()
printDebugObj obj = do
  debug <- isDebugEnabled
  when debug $ internalPrint $ pmObjMsg $ pprToStr obj

-- | Internal function for printing from within the monad.
internalPrint :: String -> PmPluginM ()
internalPrint = lift . lift . tcPluginIO . putStr

printFormattedObj :: Bool -> String -> PmPluginM ()
printFormattedObj isDebug obj = do
  debug <- isDebugEnabled
  when (not isDebug || debug) $ internalPrint $ pmObjMsg obj

printConstraints :: Bool -> [Ct] -> PmPluginM ()
printConstraints debug cts = do
  forM_ groupedCts $ \(file, ctGroup) -> do
    printFormattedObj debug $ maybe "From unknown file:" (("From " ++) . (++":") . unpackFS) file
    mapM_ (printFormattedObj debug . formatConstraint) ctGroup
  where
    groupedCts = (\ctGroup -> (getCtFile $ head ctGroup, ctGroup)) <$> groupBy eqFileName cts
    eqFileName ct1 ct2 = getCtFile ct1 == getCtFile ct2
    getCtFile = srcSpanFileName_maybe . constraintSourceLocation
