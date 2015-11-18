
-- | Provides the polymonad plugin monadic envionment,
--   access to the environment and message printing capabilities.
module Control.Polymonad.Plugin.Environment
  ( -- * Polymonad Plugin Monad
    PmPluginM, PmPluginEnv
  , runPmPlugin
  , runTcPlugin
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
  , assert, assertM
  , printErr, printMsg, printObj
  , printDebug, printDebugObj
  , printConstraints
  ) where

import Data.Maybe ( catMaybes, isNothing )
import Data.List ( groupBy, partition )

import Control.Monad ( when, unless, forM_, forM )
import Control.Monad.Trans.Reader ( ReaderT, runReaderT, asks, local )
import Control.Monad.Trans.Except ( ExceptT, runExceptT, throwE )
import Control.Monad.Trans.Class ( lift )

import Class ( Class )
import Module ( Module )
import InstEnv ( ClsInst, InstEnvs )
import Type ( TyVar )
import TyCon ( TyCon )
import Kind ( Kind )
import TcRnTypes
  ( Ct, TcPluginResult(..) )
import TcPluginM
  ( TcPluginM
  , tcPluginIO )
import qualified TcPluginM
import Outputable ( Outputable )
import SrcLoc ( srcSpanFileName_maybe )
import FastString ( unpackFS )

import Control.Polymonad.Plugin.Log
  ( pmErrMsg, pmDebugMsg, pmObjMsg
  , pprToStr
  , formatConstraint )
import Control.Polymonad.Plugin.Constraint
  ( GivenCt, WantedCt
  , isClassConstraint, constraintSourceLocation
  , isFullyAppliedClassConstraint )
import Control.Polymonad.Plugin.Detect
  ( polymonadModuleName, polymonadClassName
  , identityModuleName, identityTyConName
  , findPolymonadModule, findPolymonadClass
  , findIdentityModule, findIdentityTyCon
  , findPolymonadInstancesInScope
  , selectPolymonadByConnectedComponent
  , pickInstanceForAppliedConstraint )

-- -----------------------------------------------------------------------------
-- Plugin Monad
-- -----------------------------------------------------------------------------

-- | The plugin monad.
type PmPluginM = ReaderT PmPluginEnv (ExceptT String TcPluginM)

-- | The read-only environent of the plugin.
data PmPluginEnv = PmPluginEnv
  { pmEnvPolymonadModule    :: Module
  -- ^ The 'Control.Polymonad' module.
  , pmEnvPolymonadClass     :: Class
  -- ^ The 'Polymonad' class.
  , pmEnvPolymonadInstances :: [ClsInst]
  -- ^ All available polymonad instances
  --   (that are related to the currently selected polymonad).
  , pmEnvIdentityModule :: Module
  -- ^ The 'Data.Functor.Identity' module (TODO: don't use this).
  , pmEnvIdentityTyCon  :: TyCon
  -- ^ The 'Identity' type constructor.
  , pmEnvGivenConstraints  :: [GivenCt]
  -- ^ The given and derived constraints (all of them).
  , pmEnvGivenPolymonadConstraints :: [GivenCt]
  -- ^ The given and derived polymonad constraints
  --   (that are related to the currently selected polymonad).
  , pmEnvWantedConstraints :: [WantedCt]
  -- ^ The wanted constraints (all of them).
  , pmEnvWantedPolymonadConstraints :: [WantedCt]
  -- ^ The wanted polymonad constraints
  --   (that are related to the currently selected polymonad).
  , pmEnvCurrentPolymonad  :: ([(Either TyCon TyVar, [Kind])], [ClsInst], [GivenCt])
  -- ^ The currently selected polymonad.
  , pmEnvDebugEnabled :: Bool
  -- ^ If debugging messages are enabled or not.
  }

-- | @runPmPlugin givenAndDerived wanted m@ runs the given polymonad plugin solver @m@
--   within the type checker plugin monad. The /given/ and /derived/ constraints are
--   passed in through @givenAndDerived@ and the /wanted/ constraints are passed in
--   through @wanted@.
--
--   The function will make sure that only the polymonad constraints
--   and actually /given/, /derived/ or /wanted/ constraints
--   are kept, respectivly.
runPmPlugin :: [GivenCt] -> [WantedCt] -> PmPluginM TcPluginResult -> TcPluginM (Either String [TcPluginResult])
runPmPlugin givenCts allWantedCts pmM = do
  mPmMdl <- findPolymonadModule
  mPmCls <- findPolymonadClass
  case (mPmMdl, mPmCls) of
    (Right pmMdl, Just pmCls) -> do
      mIdMdl <- findIdentityModule
      mIdTyCon <- findIdentityTyCon
      case (mIdMdl, mIdTyCon) of
        (Right idMdl, Just idTyCon) -> do
          pmInsts <- findPolymonadInstancesInScope
          -- All fully applied constraints are given evidence and removed from
          -- the set of constraints we pass on to the solver.
          -- This is done here (one single time), so it is not done in every
          -- run of the solver on another polymonad.
          let (wantedApplied, wantedCts') = partition isFullyAppliedClassConstraint allWantedCts
          -- Now pick instances.
          mWantedEvidence <- forM wantedApplied $ \wAppCt -> do
            instEv <- pickInstanceForAppliedConstraint givenCts pmCls wAppCt
            return (wAppCt, instEv)
          -- If some of these does not produce good evidence, because there are overlapping instances
          -- sort those out and hand them to the plugin as usual.
          let (wantedAppliedUnsolved, wantedAppliedSolved) = partition (isNothing . snd) mWantedEvidence
          let wantedCts = fmap fst wantedAppliedUnsolved ++ wantedCts'
          -- Now select the different polymonads...
          foundPms <- selectPolymonadByConnectedComponent idTyCon pmCls pmInsts (givenCts, wantedCts)
          -- ...and run the solver on each one of them.
          results <- nestedSequence $ flip fmap foundPms $ \(currPm@(_pmTcs, pmRelevantInsts, gPmCts), wPmCts) ->
            runExceptT $ runReaderT pmM PmPluginEnv
              { pmEnvPolymonadModule = pmMdl
              , pmEnvPolymonadClass  = pmCls
              , pmEnvPolymonadInstances = pmRelevantInsts
              , pmEnvIdentityModule = idMdl
              , pmEnvIdentityTyCon  = idTyCon
              , pmEnvGivenConstraints = filter (not . isClassConstraint pmCls) givenCts ++ gPmCts
              , pmEnvWantedConstraints = filter (not . isClassConstraint pmCls) wantedCts ++ wPmCts
              , pmEnvGivenPolymonadConstraints = gPmCts
              , pmEnvWantedPolymonadConstraints = wPmCts
              , pmEnvCurrentPolymonad = currPm
              , pmEnvDebugEnabled = False
              }
          -- Add the evidence for fully applied constraints to the results of all solvers.
          return $ fmap (TcPluginOk (catMaybes $ fmap snd wantedAppliedSolved) [] :) results
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

nestedSequence :: [TcPluginM (Either String a)] -> TcPluginM (Either String [a])
nestedSequence [] = return $ Right []
nestedSequence (m : ms) = do
  eitherA <- m
  case eitherA of
    Left err -> return $ Left err
    Right a -> do
      eitherAs <- nestedSequence ms
      case eitherAs of
        Left err -> return $ Left err
        Right as -> return $ Right $ a : as

-- | Execute the given 'TcPluginM' computation within the polymonad plugin monad.
runTcPlugin :: TcPluginM a -> PmPluginM a
runTcPlugin = lift . lift

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
--   The available type constructors are given by the first element
--   of the triple. They can be not-applied type constructors, e.g. 'Identity',
--   or type variables in case there are given constraints that involve them.
--   A list of its arguments kinds is supplied with each type constructor.
--
--   The available bind operations are given by the second and third elements
--   of the triple. They come as class instances that provide bind operations
--   or given constraints that need to be assumed to be existing bind
--   operations.
getCurrentPolymonad :: PmPluginM ([(Either TyCon TyVar, [Kind])], [ClsInst], [GivenCt])
getCurrentPolymonad = asks pmEnvCurrentPolymonad

-- | Shortcut to access the instance environments.
getInstEnvs :: PmPluginM InstEnvs
getInstEnvs = runTcPlugin TcPluginM.getInstEnvs

-- | Checks wether debugging mode is enabled.
--   Debug mode allows debug messages to be printed.
isDebugEnabled :: PmPluginM Bool
isDebugEnabled = asks pmEnvDebugEnabled

-- | Enable debug mode for the given computation.
withDebug :: PmPluginM a -> PmPluginM a
withDebug = local (\env -> env { pmEnvDebugEnabled = True })

-- | Disable debug mode for the given computation.
withoutDebug :: PmPluginM a -> PmPluginM a
withoutDebug = local (\env -> env { pmEnvDebugEnabled = False })

-- -----------------------------------------------------------------------------
-- Plugin debug and error printing
-- -----------------------------------------------------------------------------

-- | Assert the given condition. If the condition does not
--   evaluate to 'True', an error with the given message will
--   be thrown the plugin aborts.
assert :: Bool -> String -> PmPluginM ()
assert cond msg = unless cond $ throwPluginError msg

-- | Assert the given condition. Same as 'assert' but with
--   a monadic condition.
assertM :: PmPluginM Bool -> String -> PmPluginM ()
assertM condM msg = do
  cond <- condM
  assert cond msg

-- | Throw an error with the given message in the plugin.
--   This will abort all further actions.
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

-- | Print a message from the plugin. It is only displayed if debugging is enabled.
printDebug :: String -> PmPluginM ()
printDebug msg = do
  debug <- isDebugEnabled
  when debug $ internalPrint $ pmDebugMsg msg

-- | Print an object. If is only displayed if debugging is enabled.
printDebugObj :: (Outputable o) => o -> PmPluginM ()
printDebugObj obj = do
  debug <- isDebugEnabled
  when debug $ internalPrint $ pmObjMsg $ pprToStr obj

-- | Internal function for printing from within the monad.
internalPrint :: String -> PmPluginM ()
internalPrint = runTcPlugin . tcPluginIO . putStr

-- | Print the given string as if it was an object. This allows custom
--   formatting of object. The boolean indicates wether the debug mode
--   is ignored or this message only appears when debugging.
printFormattedObj :: Bool -> String -> PmPluginM ()
printFormattedObj isDebug obj = do
  debug <- isDebugEnabled
  when (not isDebug || debug) $ internalPrint $ pmObjMsg obj

-- | Print the given constraints in the plugins custom format.
--   The boolean indicates wether the debug mode
--   is ignored or this message only appears when debugging.
printConstraints :: Bool -> [Ct] -> PmPluginM ()
printConstraints debug cts =
  forM_ groupedCts $ \(file, ctGroup) -> do
    printFormattedObj debug $ maybe "From unknown file:" (("From " ++) . (++":") . unpackFS) file
    mapM_ (printFormattedObj debug . formatConstraint) ctGroup
  where
    groupedCts = (\ctGroup -> (getCtFile $ head ctGroup, ctGroup)) <$> groupBy eqFileName cts
    eqFileName ct1 ct2 = getCtFile ct1 == getCtFile ct2
    getCtFile = srcSpanFileName_maybe . constraintSourceLocation
