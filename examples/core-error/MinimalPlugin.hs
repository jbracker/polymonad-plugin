module MinimalPlugin ( plugin ) where

import Data.List ( partition, find )
import Data.Maybe 
  ( isJust, catMaybes
  , listToMaybe, maybeToList
  , fromMaybe, fromJust )
import Data.Either ( isLeft, isRight )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( unless, guard, forM, liftM )

import Type
  ( TyThing(..), TyVar, Type
  , eqType
  , isTyVarTy
  , getTyVar, getTyVar_maybe
  , getClassPredTys_maybe, getClassPredTys
  , getEqPredTys_maybe, getEqPredTys, getEqPredRole
  , splitTyConApp_maybe, splitAppTy_maybe, splitFunTy_maybe
  , mkTyConTy, mkTyVarTy
  , mkTopTvSubst, substTy, substTys)
import Plugins ( Plugin(tcPlugin), defaultPlugin )
import InstEnv
  ( ClsInst(..)
  , instanceBindFun, instanceSig
  , instEnvElts, ie_global
  , lookupUniqueInstEnv
  , classInstances)
import Class
  ( Class(..)
  , className, classArity )
import Unify ( BindFlag(..), tcUnifyTys )
import TyCon ( TyCon, isTupleTyCon, isTypeFamilyTyCon, isTypeSynonymTyCon )
import RdrName ( GlobalRdrElt(..), lookupGlobalRdrEnv )
import OccName ( occNameString, mkTcOcc )
import Name ( getOccName )
import CoAxiom ( Role(..) )
import FamInstEnv ( normaliseType )
import TcRnTypes
  ( Ct(..), CtEvidence(..)
  , TcGblEnv(..), TcTyThing(..)
  , TcPlugin(..), TcPluginResult(..)
  , isGivenCt
  , ctPred, ctEvidence, ctEvTerm
  , mkNonCanonical )
import TcType ( mkTcEqPred, isAmbiguousTyVar )
import TcPluginM
  ( TcPluginM
  , tcPluginIO, tcLookup
  , getEnvs, getInstEnvs
  , getFamInstEnvs )
import TcEvidence ( EvTerm(..), TcCoercion(..) )
import Coercion ( Coercion )
import Outputable ( ($$), SDoc )
import qualified Outputable as O

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runPmPlugin
  , getCurrentPolymonad
  , getIdentityTyCon
  , getGivenConstraints
  , getWantedPolymonadConstraints
  , printDebug, printMsg
  , printObj
  --, printConstraints
  , runTcPlugin)
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
  instEnvs <- TcPluginM.getInstEnvs
  mIdTyCon <- findIdentityTyCon
  mPmCls <- findPolymonadClass
  case (mIdTyCon, mPmCls) of
    (Just idTyCon, Just pmCls) -> do
      let pmInsts = classInstances instEnvs pmCls
      let pmGivenCts = filter (isClassConstraint pmCls) (given ++ derived)
      let pmWantedCts = filter (isClassConstraint pmCls) wanted
      return ()
    _ -> return ()
  
  L.printMsg "Invoke polymonad plugin..."
  res <- runPmPlugin (given ++ derived) wanted $ polymonadSolve' s
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
        _ -> return ()
      return $ mergedRes

polymonadSolve' :: PolymonadState -> PmPluginM TcPluginResult
polymonadSolve' _s = do
  allWanted <- getWantedPolymonadConstraints
  let (tyConAppCts, wanted) = partition isTyConAppliedClassConstraint allWanted
  
  -- Assign ambiguous variables
  let ambTvs = S.unions $ constraintTopAmbiguousTyVars <$> wanted
  eqUpDownCtData <- assignAmbiguousTyVars wanted ambTvs -- simplifyAllUp wanted ambTvs -- 
  let eqUpDownCts = simplifiedTvsToConstraints eqUpDownCtData
  
  -- Solve overlapping instances
  solvedOverlaps <- fmap catMaybes $ forM tyConAppCts $ \tyConAppCt -> do
      mEv <- detectOverlappingInstancesAndTrySolve' tyConAppCt
      return $ (\ev -> (ev, tyConAppCt)) <$> mEv
  
  return $ TcPluginOk solvedOverlaps eqUpDownCts

-- ===========================================================================================================================

detectOverlappingInstancesAndTrySolve :: ([ClsInst], [GivenCt]) -> [GivenCt] -> WantedCt -> TcPluginM (Maybe EvTerm)
detectOverlappingInstancesAndTrySolve (pmInsts, pmCts) givenCts ct = do
  let ctTyArgs = constraintClassArgs ct
  -- Only select an instance if all arguments of the constraint don't contain variables
  if all S.null (collectTyVars <$> ctTyArgs)
    then do
      instMatches <- forM pmInsts $ \pmInst -> do
        case matchInstanceTyVars pmInst ctTyArgs of
          Just args -> do
            isInst <- isInstanceOf givenCts args pmInst
            return $ if isInst then Just (pmInst, args) else Nothing
          Nothing -> return Nothing
      case catMaybes instMatches of
        [instWithArgs] -> uncurry (produceEvidenceForPM givenCts) instWithArgs
        _ -> return Nothing
    else return Nothing
    
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
-- Assign Ambiguous Type Variables
-- -----------------------------------------------------------------------------

matchAssign :: [WantedCt] -> Set TyVar -> (Set TyVar -> (Type, Type, Type) -> Maybe (TyVar, Type)) -> Maybe (TyVar, (Ct, Type))
matchAssign wantedCts tvs matchRule =
  case find (\(ct, m1, m2, m3) -> isJust $ matchRule tvs (m1, m2, m3)) (constraintPolymonadTyArgs' wantedCts) of
    Just (ct, m1, m2, m3) -> (\(tv, t) -> (tv, (ct, t))) <$> matchRule tvs (m1, m2, m3)
    Nothing -> Nothing

-- | An uncomplicated version of the simplification process.
assignAmbiguousTyVars :: [WantedCt] -> Set TyVar -> PmPluginM [(TyVar, (Ct, Type))]
assignAmbiguousTyVars wantedCts tyVars = do
  idTyCon <- mkTyConTy <$> getIdentityTyCon
  let idIdSimpl = matchAssign wantedCts tyVars $ \tvs (m1, m2, m3) -> 
        if m1 `eqType` idTyCon && m2 `eqType` idTyCon
           then (\tv -> (tv, idTyCon)) <$> (m3 `tyVarAndInSet` tvs)
           else Nothing
  let funcSimpl = matchAssign wantedCts tyVars $ \tvs (m1, m2, m3) -> 
        if S.null (collectTyVars m1) && m2 `eqType` idTyCon
           then (\tv -> (tv, m1)) <$> (m3 `tyVarAndInSet` tvs) 
           else Nothing
  return $ case (idIdSimpl, funcSimpl) of
    (Just simpl, _) -> [simpl]
    (_, Just simpl) -> [simpl]
    _ -> []

tyVarAndInSet :: Type -> Set TyVar -> Maybe TyVar
tyVarAndInSet t tvs = do 
  tv <- getTyVar_maybe t
  guard $ tv `S.member` tvs
  return tv

-- -----------------------------------------------------------------------------
-- Evidence Production
-- -----------------------------------------------------------------------------

-- | Trys to see if the given arguments match the class instance
--   arguments by unification. This only works if the number of arguments
--   given is equal to the arguments taken by the class the instance is of.
--   If the given arguments match the class arguments, a list with a type for
--   each free variable in the instance is returned. This list is in the same
--   order as the list of free variables that can be retrieved from the instance.
--
--   This function is meant for use in conjunction with 'isInstanceOf',
--   'isInstantiatedBy' and 'produceEvidenceFor'.
matchInstanceTyVars :: ClsInst -> [Type] -> Maybe [Type]
matchInstanceTyVars inst instArgs = do
  let (instVars, _cts, _cls, tyArgs) = instanceSig inst
  -- Old Version:
  -- let instVarSet = printObjTrace $ mkVarSet instVars
  -- subst <- printObjTrace $ tcMatchTys instVarSet tyArgs instArgs
  let ctVars = filter (not . isAmbiguousTyVar) $ S.toList $ S.unions $ fmap collectTyVars instArgs
  subst <- tcUnifyTys (skolemVarsBindFun ctVars) tyArgs instArgs
  return $ substTy subst . mkTyVarTy <$> instVars

-- | Checks if the given arguments types to the free variables in the
--   class instance actually form a valid instantiation of that instance.
--   The given arguments need to match up with the list of free type variables
--   given for the class instance ('is_tvs').
--
--   The instance argument types can be created using 'matchInstanceTyVars'.
--
--   The list of given constraints that can be used to check of they
--   fulfill the instance constraints, in case there are no instances
--   that can fulfill them.
--
--   For details on the accepted arguments and support of type extensions,
--   see 'produceEvidenceFor'.
isInstantiatedBy :: [GivenCt] -> ClsInst -> [Type] -> TcPluginM (Either String Bool)
isInstantiatedBy givenCts inst instArgs = do
  eEvTerm <- produceEvidenceFor givenCts inst instArgs
  case eEvTerm of
    Left _err -> return $ Right False
    Right _ev -> return $ Right True

-- | Apply the given instance dictionary to the given type arguments
--   and try to produce evidence for the application.
--
--   The list of types has to match the number of open variables of the
--   given instance dictionary in length. They need to match up with
--   the list of free type variables given for the class instance ('is_tvs').
--   The list can be created using 'matchInstanceTyVars'.
--
--   The first argument is a list of given constraints that can be used
--   to produce evidence for otherwise not fulfilled constraints. Be aware that
--   only actually /given/ constraints (as in 'isGivenCt') are useful here,
--   because only those produce evidence for themselves. All other constraints
--   will be ignored.
--
--   This function should properly work with type synonyms and type functions.
--   It only produces evidence for type equalities if they are trivial, i.e., @a ~ a@.
produceEvidenceFor :: [GivenCt] -> ClsInst -> [Type] -> TcPluginM (Either SDoc EvTerm)
produceEvidenceFor givenCts inst instArgs = do
  -- Get the instance type variables and constraints (by that we know the
  -- number of type arguments and dictionart arguments for the EvDFunApp)
  let (tyVars, instCts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
  -- How the instance variables for the current instance are bound.
  let varSubst = mkTopTvSubst $ zip tyVars instArgs
  -- Now go over each constraint and find a suitable instance and evidence.
  -- Don't forget to substitute all variables for their actual values,
  ctEvTerms <- forM (substTys varSubst instCts) $ produceEvidenceForCt givenCts
  -- If we found a good instance and evidence for every constraint,
  -- we can create the evidence for this instance.
  return $ if any isLeft ctEvTerms
    then Left
      $ O.text "Can't produce evidence for instance:"
      $$ O.ppr inst
      $$ O.text "Reason:"
      $$ O.vcat (fromLeft <$> filter isLeft ctEvTerms)
    else Right $ EvDFunApp (is_dfun inst) instArgs (fromRight <$> ctEvTerms)

produceEvidenceForCt :: [GivenCt] -> Type -> TcPluginM (Either SDoc EvTerm)
produceEvidenceForCt givenCts ct =
  case splitTyConApp_maybe ct of
    -- Do we have a tuple of constraints?
    Just (tc, tcArgs) | isTupleTyCon tc -> do
      -- Produce evidence for each element of the tuple
      tupleEvs <- mapM (produceEvidenceForCt checkedGivenCts) tcArgs
      return $ if any isLeft tupleEvs
        then Left
          $ O.text "Can't find evidence for this tuple constraint:"
          $$ O.ppr ct
          $$ O.text "Reason:"
          $$ O.vcat (fromLeft <$> filter isLeft tupleEvs)
        -- And put together evidence for the complete tuple.
        else Right $ EvTupleMk $ fmap fromRight tupleEvs
    -- Do we have a type family application?
    Just (tc, _tcArgs) | isTyFunCon tc -> do
      -- Evaluate it...
      (coer, evalCt) <- evaluateType Representational ct
      -- Produce evidence for the evaluated term
      eEvEvalCt <- produceEvidenceForCt checkedGivenCts evalCt
      -- Add the appropriate cast to the produced evidence
      return $ (\ev -> EvCast ev (TcSymCo $ TcCoercion coer)) <$> eEvEvalCt
    -- Do we have a type equality constraint?
    _ -> case getEqPredTys_maybe ct of
      -- If there is a synonym or type function in the equality...
      Just _ | containsTyFunApp ct -> do
          -- Evaluate it...
          (coer, evalCt) <- evaluateType Representational ct
          -- Produce evidence for the evaluated term and
          -- add the appropriate cast to the produced evidence
          let (ta, tb) = getEqPredTys evalCt
          let r = getEqPredRole evalCt
          return $ (\ev -> EvCast ev (TcSymCo $ TcCoercion coer)) <$> produceTypeEqEv r ta tb
      -- If there isn't we can just proceed...
      Just (r, ta, tb) -> return $ produceTypeEqEv r ta tb
      -- Do we have a class constraint?
      _ -> case getClassPredTys_maybe ct of
        Just _ | containsTyFunApp ct -> do
          -- Evaluate it...
          (coer, evalCt) <- evaluateType Representational ct
          -- Produce evidence for the evaluated term and
          -- add the appropriate cast to the produced evidence
          let (cls, args) = getClassPredTys evalCt
          fmap (\ev -> EvCast ev (TcSymCo $ TcCoercion coer)) <$> produceClassCtEv cls args
        Just (ctCls, ctArgs) -> produceClassCtEv ctCls ctArgs
        -- In any other case, lets try if one of the given constraints can help...
        _ | containsTyFunApp ct -> do
          -- Evaluate it...
          (coer, evalCt) <- evaluateType Representational ct
          -- and produce the appropriate cast
          return $ (\ev -> EvCast ev (TcCoercion coer)) <$> produceGivenCtEv evalCt
        -- In any other case, lets try if one of the given constraints can help...
        _ -> return $ produceGivenCtEv ct
  where
    -- Ensure there are only given constraints there.
    checkedGivenCts = filter isGivenCt givenCts

    -- We only do the simplest kind of equality constraint solving and
    -- evidence construction.
    produceTypeEqEv :: Role -> Type -> Type -> Either SDoc EvTerm
    produceTypeEqEv r ta tb = if eqType ta tb
      then Right $ EvCoercion $ TcRefl r ta
      else Left
        $ O.text "Can't produce evidence for this type equality constraint:"
        $$ O.ppr ct

    -- Produce evidence of a class constraint.
    produceClassCtEv :: Class -> [Type] -> TcPluginM (Either SDoc EvTerm)
    produceClassCtEv cls args = do
      -- Get global instance environment
      instEnvs <- getInstEnvs
      -- Look for suitable instance. Since we are not necessarily working
      -- with polymonads anymore we need to find a unique one.
      case lookupUniqueInstEnv instEnvs cls args of -- (snd <$> normCtArgs)
        -- No instance found, too bad...
        Left err ->
          return $ Left
            $ O.text "Can't produce evidence for this class constraint:"
            $$ O.ppr ct
            $$ O.text "Lookup error:"
            $$ err
        -- We found one: Now we can produce evidence for the found instance.
        Right (clsInst, instArgs) -> produceEvidenceFor checkedGivenCts clsInst instArgs

    -- Try to find a given constraint that matches and use its evidence.
    produceGivenCtEv :: Type -> Either SDoc EvTerm
    produceGivenCtEv cnstrnt = case find (eqType cnstrnt . ctPred) checkedGivenCts of
      -- Check if there is some given constraint that provides evidence
      -- for our constraint.
      Just foundGivenCt -> Right $ ctEvTerm (ctEvidence foundGivenCt)
      -- Nothing delivered a result, give up...
      Nothing -> Left
        $ O.text "Can't produce evidence for this constraint:"
        $$ O.ppr cnstrnt

    -- Is this type constructor something that requires evaluation?
    isTyFunCon :: TyCon -> Bool
    isTyFunCon tc = isTypeFamilyTyCon tc || isTypeSynonymTyCon tc

    -- | Check of the given type is the application of a type family data constructor.
    isTyFunApp :: Type -> Bool
    isTyFunApp t = case splitTyConApp_maybe t of
      Just (tc, _args) -> isTyFunCon tc
      Nothing -> False

    -- | Find out if there is a type function application somewhere inside the type.
    containsTyFunApp :: Type -> Bool
    containsTyFunApp t = isTyFunApp t ||
      case getTyVar_maybe t of
        Just _tv -> False
        Nothing -> case splitTyConApp_maybe t of
          Just (_tc, args) -> any containsTyFunApp args
          Nothing -> case splitFunTy_maybe t of
            Just (ta, tb) -> containsTyFunApp ta || containsTyFunApp tb
            Nothing -> case splitAppTy_maybe t of
              Just (ta, tb) -> containsTyFunApp ta || containsTyFunApp tb
              Nothing -> case getEqPredTys_maybe t of
                Just (_r, ta, tb) -> containsTyFunApp ta || containsTyFunApp tb
                Nothing -> False

-- | Try to evaluate the given type as far as possible by evaluating contained
--   type families and expanding type synonyms.
evaluateType :: Role -> Type -> TcPluginM (Coercion, Type)
evaluateType r t = do
  famInstEnvs <- getFamInstEnvs
  return $ normaliseType famInstEnvs r t

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

-- | Check if the given constraint is a class constraint of the given class.
isClassConstraint :: Class -> Ct -> Bool
isClassConstraint wantedClass ct =
  case ct of
    CDictCan { cc_class = cls } -> cls == wantedClass
    CNonCanonical { cc_ev = ev } -> case getClassPredTys_maybe (ctev_pred ev) of
      Just (cls, _args) -> cls == wantedClass
      _ -> False
    _ -> False
    
constraintClassType :: Ct -> Maybe (Class, [Type])
constraintClassType ct = case ct of
  CDictCan {} -> Just (cc_class ct, cc_tyargs ct)
  CNonCanonical evdnc -> getClassPredTys_maybe $ ctev_pred evdnc
  _ -> Nothing

constraintClassArgs :: Ct -> [Type]
constraintClassArgs ct = case constraintClassType ct of
  Just (_cls, args) -> args
  Nothing -> []

-- | Extracts the type arguments of the given constraint.
--   Only works if the given constraints is a type class constraint
--   and has exactly three arguments.
constraintPolymonadTyArgs :: Ct -> Maybe (Type, Type, Type)
constraintPolymonadTyArgs ct = case fmap snd $ constraintClassType ct of
    Just [t0, t1, t2] -> Just (t0, t1, t2)
    _ -> Nothing

-- | Extracts the type arguments of the given constraints.
--   Only keeps those constraints that are type class constraints
--   and have exactly three arguments.
constraintPolymonadTyArgs' :: [Ct] -> [(Ct, Type, Type, Type)]
constraintPolymonadTyArgs' cts
  = fmap (\(ct, Just (p0, p1, p2)) -> (ct, p0, p1, p2))
  $ filter (\(_, ts) -> isJust ts)
  $ fmap (\ct -> (ct, constraintPolymonadTyArgs ct)) cts

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

-- | Return the 'Left' value. If no 'Left' value is given, an error is raised.
fromLeft :: Either a b -> a
fromLeft (Left a) = a
fromLeft (Right _) = error "fromLeft: Applied to 'Right'"

-- | Return the 'Right' value. If no 'Right' value is given, an error is raised.
fromRight :: Either a b -> b
fromRight (Left _) = error "fromRight: Applied to 'Left'"
fromRight (Right b) = b