module MinimalPlugin ( plugin ) where

import Data.Set ( Set )
import Data.List ( partition, find )
import Data.Maybe ( isJust, catMaybes, listToMaybe, maybeToList, fromMaybe )
import qualified Data.Set as S

import Control.Monad ( unless, forM, liftM )

import Type
 ( TyThing(..), TyVar, Type
  , eqType
  , isTyVarTy
  , getTyVar, getTyVar_maybe
  , getClassPredTys_maybe, getEqPredTys_maybe
  , splitTyConApp_maybe, splitAppTy_maybe, splitFunTy_maybe
  , mkTyConTy, mkTyVarTy
  , substTys)
import Plugins ( Plugin(tcPlugin), defaultPlugin )
import InstEnv
  ( ClsInst(..)
  , instanceBindFun, instanceSig
  , instEnvElts, ie_global )
import Class
  ( Class(..)
  , className, classArity )
import Unify ( BindFlag(..), tcUnifyTys )
import TyCon ( TyCon )
import RdrName ( GlobalRdrElt(..), lookupGlobalRdrEnv )
import OccName ( occNameString, mkTcOcc )
import Name ( getOccName )
import TcRnTypes
  ( Ct(..), CtEvidence(..)
  , TcGblEnv(..), TcTyThing(..)
  , TcPlugin(..), TcPluginResult(..)
  , mkNonCanonical )
import TcType ( mkTcEqPred, isAmbiguousTyVar )
import TcPluginM
 ( TcPluginM
  , tcPluginIO, tcLookup
  , getEnvs, getInstEnvs )
import TcEvidence ( EvTerm )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runPmPlugin
  , getCurrentPolymonad
  , getGivenConstraints
  , getWantedPolymonadConstraints
  , printDebug, printMsg
  --, printObj
  --, printConstraints
  , runTcPlugin)
import Control.Polymonad.Plugin.Simplification
  ( simplifyAllUpDown )
import Control.Polymonad.Plugin.Evidence
  ( isInstantiatedBy, produceEvidenceFor, matchInstanceTyVars )
import qualified Control.Polymonad.Plugin.Log as L
import qualified Control.Polymonad.Plugin.Debug as D

-- -----------------------------------------------------------------------------
-- The Plugin
-- -----------------------------------------------------------------------------

-- | The polymonad type checker plugin for GHC.
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = \_clOpts -> Just polymonadPlugin }

-- -----------------------------------------------------------------------------
-- Actual Plugin Code
-- -----------------------------------------------------------------------------
type GivenCt = Ct
type DerivedCt = Ct
type WantedCt = Ct

type PolymonadState = ()

polymonadPlugin :: TcPlugin
polymonadPlugin = TcPlugin
  { tcPluginInit  = polymonadInit
  , tcPluginSolve = polymonadSolve
  , tcPluginStop  = polymonadStop
  }

polymonadInit :: TcPluginM PolymonadState
polymonadInit = return ()

polymonadStop :: PolymonadState -> TcPluginM ()
polymonadStop _s = return ()

polymonadSolve :: PolymonadState -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
polymonadSolve _s _g _d [] = return $ TcPluginOk [] []
polymonadSolve s given derived wanted = do
  res <- runPmPlugin (given ++ derived) wanted $
    if not $ null wanted
      then do
        printMsg "Invoke polymonad plugin..."
        polymonadSolve' s
      else return noResult
  case res of
    Left errMsg -> do
      tcPluginIO $ putStrLn errMsg
      return noResult
    Right slv -> do
      let mergedRes = mergeResults slv
      case mergedRes of
        TcPluginOk solved derive -> do
          L.printObj wanted
          L.printObj derive
          L.printObj $ fmap snd solved
      return $ mergedRes

polymonadSolve' :: PolymonadState -> PmPluginM TcPluginResult
polymonadSolve' _s = do
  -- Simplification ------------------------------------------------------------
  printDebug "Try simplification of constraints..."
  allWanted <- getWantedPolymonadConstraints
  let (tyConAppCts, wanted) = partition isTyConAppliedClassConstraint allWanted

  solvedOverlaps <- fmap catMaybes $ forM tyConAppCts $ \tyConAppCt -> do
      mEv <- detectOverlappingInstancesAndTrySolve' tyConAppCt
      return $ (\ev -> (ev, tyConAppCt)) <$> mEv

  let ambTvs = S.unions $ constraintTopAmbiguousTyVars <$> wanted
  eqUpDownCtData <- simplifyAllUpDown wanted ambTvs
  let eqUpDownCts = simplifiedTvsToConstraints eqUpDownCtData
  
  return $ TcPluginOk solvedOverlaps eqUpDownCts

deriveConstraints :: TyCon -> WantedCt -> TcPluginM [DerivedCt]
deriveConstraints idTyCon wCt = case constraintPolymonadTyArgs wCt of
  Just (m, n, p) -> return $ case () of
    () | eqType m idTy && eqType n idTy && isTyVarTy p
       -> [mkDerivedTypeEqCt wCt (getTyVar "IMPOSSIBLE_1" p) idTy]
    () | not (isTyVarTy m) && eqType n idTy && isTyVarTy p
       -> [mkDerivedTypeEqCt wCt (getTyVar "IMPOSSIBLE_2" p) m]
    () -> []
  Nothing -> return []
  where
    idTy = mkTyConTy idTyCon

evidentConstraints :: ([ClsInst], [GivenCt]) -> [GivenCt] -> WantedCt -> TcPluginM [(EvTerm, WantedCt)]
evidentConstraints (pmInsts, pmCts) givenCts wCt | isTyConAppliedClassConstraint wCt = do
  mEv <- detectOverlappingInstancesAndTrySolve (pmInsts, pmCts) givenCts wCt
  return $ (\ev -> (ev, wCt)) <$> maybeToList mEv
evidentConstraints _ _ _ = return []

-- ===========================================================================================================================

detectOverlappingInstancesAndTrySolve :: ([ClsInst], [GivenCt]) -> [GivenCt] -> WantedCt -> TcPluginM (Maybe EvTerm)
detectOverlappingInstancesAndTrySolve (pmInsts, pmCts) givenCts ct =
  case fmap snd $ constraintClassType ct of
    Just tyArgs -> do
      -- Collect variables that are to be seen as constants.
      -- The first batch of these are the non ambiguous type variables in the constraint arguments...
      let dontBind =  filter (not . isAmbiguousTyVar) (S.toList $ S.unions $ fmap collectTyVars tyArgs)
                   -- and the second batch are the type variables in given constraints.
                   ++ S.toList (S.unions $ concat $ fmap (maybe [] (fmap collectTyVars) . fmap snd . constraintClassType) pmCts)
      instMatches <- forM pmInsts $ \pmInst -> do
        let (_, _, _, instArgs) = instanceSig pmInst
        case tcUnifyTys (skolemVarsBindFun dontBind) tyArgs instArgs of
          Just subst -> case matchInstanceTyVars pmInst (substTys subst tyArgs) of
            Just args -> do
              isInst <- isInstanceOf givenCts args pmInst
              return $ if isInst then Just (pmInst, args) else Nothing
            Nothing -> return Nothing
          Nothing -> return Nothing
      case catMaybes instMatches of
        [instWithArgs] -> uncurry (produceEvidenceForPM givenCts) instWithArgs
        _ -> return Nothing
    _ -> return Nothing
    
detectOverlappingInstancesAndTrySolve' :: WantedCt -> PmPluginM (Maybe EvTerm)
detectOverlappingInstancesAndTrySolve' ct = do
  (_, pmInsts, pmCts) <- getCurrentPolymonad
  givenCts <- getGivenConstraints
  runTcPlugin $ detectOverlappingInstancesAndTrySolve (pmInsts, pmCts) givenCts ct

-- ================================================================================================

isInstanceOf :: [GivenCt] -> [Type] -> ClsInst -> TcPluginM Bool
isInstanceOf givenCts instArgs inst = do
  res <- isInstantiatedBy givenCts inst instArgs
  case res of
    Left err -> return False
    Right b -> return b

produceEvidenceForPM :: [GivenCt] -> ClsInst -> [Type] -> TcPluginM (Maybe EvTerm)
produceEvidenceForPM givenCts inst args = do
  eEvTerm <- produceEvidenceFor givenCts inst args
  return $ case eEvTerm of
    Left _err -> Nothing
    Right evTerm -> Just evTerm

-- -----------------------------------------------------------------------------
-- Detection
-- -----------------------------------------------------------------------------

polymonadClassName :: String
polymonadClassName = "Polymonad"

identityTyConName :: String
identityTyConName = "Identity"

isPolymonadClass :: Class -> Bool
isPolymonadClass cls
  =  (occNameString $ getOccName $ className cls) == polymonadClassName
  && classArity cls == 3

findPolymonadClass :: TcPluginM (Maybe Class)
findPolymonadClass = do
  let isPmCls = isPolymonadClass . is_cls
  envs <- fst <$> getEnvs
  let foundInstsLcl =  (filter isPmCls . instEnvElts . tcg_inst_env $ envs)
                    ++ (filter isPmCls . tcg_insts $ envs)
  foundInstsGbl <- filter isPmCls . instEnvElts . ie_global <$> getInstEnvs
  return $ case foundInstsLcl ++ foundInstsGbl of
    (inst : _) -> Just $ is_cls inst
    [] -> Nothing

findIdentityTyCon :: TcPluginM (Maybe TyCon)
findIdentityTyCon = do
  let idOccName = mkTcOcc identityTyConName
  rdrEnv <- tcg_rdr_env . fst <$> getEnvs
  let envResultElem = lookupGlobalRdrEnv rdrEnv idOccName
  mTyCons <- forM envResultElem $ liftM tcTyThingToTyCon . tcLookup . gre_name
  return $ listToMaybe $ catMaybes mTyCons

tcTyThingToTyCon :: TcTyThing -> Maybe TyCon
tcTyThingToTyCon (AGlobal (ATyCon tc)) = Just tc
tcTyThingToTyCon _ = Nothing

-- -----------------------------------------------------------------------------
-- Utility Functions
-- -----------------------------------------------------------------------------

noResult :: TcPluginResult
noResult = TcPluginOk [] []

mergeResults :: [TcPluginResult] -> TcPluginResult
mergeResults [] = noResult
mergeResults (TcPluginOk evidence derived : rest) = case mergeResults rest of
  TcPluginOk restEv restDe -> TcPluginOk (evidence ++ restEv) (derived ++ restDe)
  TcPluginContradiction cts -> TcPluginContradiction cts
mergeResults (TcPluginContradiction cts : _) = TcPluginContradiction cts

getEvidence :: TcPluginResult -> [EvTerm]
getEvidence (TcPluginOk evs _dc) = fmap fst evs
getEvidence _ = []

-- | Create a derived type equality constraint. The constraint
--   will be located at the location of the given constraints
--   and equate the given variable with the given type.
mkDerivedTypeEqCt :: Ct -> TyVar -> Type -> DerivedCt
mkDerivedTypeEqCt ct tv ty = mkNonCanonical CtDerived
    { ctev_pred = mkTcEqPred (mkTyVarTy tv) ty
    , ctev_loc = ctev_loc $ cc_ev ct }

constraintClassType :: Ct -> Maybe (Class, [Type])
constraintClassType ct = case ct of
  CDictCan {} -> Just (cc_class ct, cc_tyargs ct)
  CNonCanonical evdnc -> getClassPredTys_maybe $ ctev_pred evdnc
  _ -> Nothing

-- | Extracts the type arguments of the given constraint.
--   Only works if the given constraints is a type class constraint
--   and has exactly three arguments.
constraintPolymonadTyArgs :: Ct -> Maybe (Type, Type, Type)
constraintPolymonadTyArgs ct = case fmap snd $ constraintClassType ct of
    Just [t0, t1, t2] -> Just (t0, t1, t2)
    _ -> Nothing

-- | Collects the top-level ambiguous type variables in the constraints
--   arguments. Only returns non-empty sets if the constraint is a class
--   constraint and actually has arguments.
constraintTopAmbiguousTyVars :: Ct -> Set TyVar
constraintTopAmbiguousTyVars ct = ambTvs
  where tyArgs = fromMaybe [] (fmap snd $ constraintClassType ct)
        tvArgs = catMaybes $ getTyVar_maybe <$> tyArgs
        ambTvs = S.fromList $ filter isAmbiguousTyVar tvArgs

-- | Check if the given constraint is a class constraint and all arguments
--   consist of non-variable type constructor (partially) applied to their
--   arguments.
--
--   /Examples/:
--
-- >>> isTyConAppliedClassConstraint (Polymonad m Identity Maybe)
-- False -- because of 'm'
--
-- >>> isTyConAppliedClassConstraint (Polymonad (Session a b) (Session () ()) Maybe)
-- True -- because 'a' and 'b' are not the top level type-constructor
--
-- >>> isTyConAppliedClassConstraint (Polymonad Maybe (m () ()) (m () ()))
-- False -- because of 'm'
isTyConAppliedClassConstraint :: Ct -> Bool
isTyConAppliedClassConstraint ct = case fmap snd $ constraintClassType ct of
  Just tyArgs -> all isJust $ splitTyConApp_maybe <$> tyArgs
  Nothing -> False

-- | Try to collect all type variables in a given expression.
--   Does not work for Pi or ForAll types.
--   If the given type is not supported an empty set is returned.
collectTyVars :: Type -> Set TyVar
collectTyVars t =
  case getTyVar_maybe t of
    Just tv -> S.singleton tv
    Nothing -> case splitTyConApp_maybe t of
      Just (_tc, args) -> S.unions $ fmap collectTyVars args
      Nothing -> case splitFunTy_maybe t of
        Just (ta, tb) -> collectTyVars ta `S.union` collectTyVars tb
        Nothing -> case splitAppTy_maybe t of
          Just (ta, tb) -> collectTyVars ta `S.union` collectTyVars tb
          Nothing -> case getEqPredTys_maybe t of
            Just (_r, ta, tb) -> collectTyVars ta `S.union` collectTyVars tb
            Nothing -> S.empty

-- | Override the standard bind flag of a given list of variables to 'Skolem'.
--   The standard bind flad is determined using 'instanceBindFun'.
--   This can be used to keep 'tcUnifyTys' from unifying the given variables
--   and to view them as constants.
skolemVarsBindFun :: [TyVar] -> TyVar -> BindFlag
skolemVarsBindFun tvs var = case find (var ==) tvs of
  Just _ -> Skolem
  Nothing -> instanceBindFun var

-- | Converts the associations of type variables to their simplifications to
--   derived type equality constraints that are located at the position of the
--   constraints that led to the simplification.
simplifiedTvsToConstraints :: [(TyVar, (Ct, Type))] -> [Ct]
simplifiedTvsToConstraints tvs = (\(tv, (ct, t)) -> mkDerivedTypeEqCt ct tv t) <$> tvs