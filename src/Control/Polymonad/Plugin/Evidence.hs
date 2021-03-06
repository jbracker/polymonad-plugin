
-- | Provides functions to check if a given instance together with some
--   arguments to instantiate it, is actually instantiated by those arguments.
--   Also provides functions to produce evidence for the instantiations if
--   necessary.
module Control.Polymonad.Plugin.Evidence
  ( matchInstanceTyVars
  , isInstantiatedBy
  , isPotentiallyInstantiatedPolymonad
  , produceEvidenceFor
  ) where

import Data.Either ( isLeft, isRight )
import Data.Maybe ( catMaybes, isJust, fromMaybe )
import Data.List ( find )
import qualified Data.Set as S

import Control.Monad ( forM )
import Control.Arrow ( first )

import Type
  ( Type, TyVar, Kind
  , mkTopTvSubst, mkTyVarTy
  , substTy, substTys
  , eqType
  , getClassPredTys_maybe, getClassPredTys
  , getEqPredTys_maybe, getEqPredTys, getEqPredRole
  , getTyVar_maybe
  , splitTyConApp_maybe, splitFunTy_maybe, splitAppTy_maybe )
import TyCon
  ( TyCon
  , isTupleTyCon, isTypeFamilyTyCon, isTypeSynonymTyCon )
import Class ( Class, classTyCon )
import Coercion ( Coercion(..) )
import InstEnv
  ( ClsInst(..)
  , instanceSig
  , lookupUniqueInstEnv )
import Unify ( tcUnifyTys )
import CoAxiom ( Role(..) )
import TcRnTypes ( isGivenCt, ctPred, ctEvidence, ctEvTerm )
import TcType ( isAmbiguousTyVar )
import TcEvidence ( EvTerm(..), TcCoercion(..) )
import TcPluginM
  ( TcPluginM
  , getInstEnvs )
import Outputable ( ($$), SDoc )
import qualified Outputable as O

import Control.Polymonad.Plugin.Evaluate ( evaluateType )
import Control.Polymonad.Plugin.Constraint
  ( GivenCt
  , constraintTyVars )
import Control.Polymonad.Plugin.Utils
  ( fromLeft, fromRight
  , collectTyVars
  , skolemVarsBindFun
  , applyTyCon
  , associations )
--import Control.Polymonad.Plugin.Log ( printObj, printMsg )
--import Control.Polymonad.Plugin.Debug ( containsAllOf, containsNoneOf )

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

-- | Check if a given polymonad constraint can potentially be instantiated using the given
--   type constructors. By potentially we mean: First, check if the
--   polymonad instance can actually be applied to some combination of
--   the type constructors. Then check if all resulting constraints that
--   do not contain free variables actually can be instantiated.
isPotentiallyInstantiatedPolymonad :: [GivenCt] -> ClsInst -> [(Either TyCon TyVar, [Kind])] -> TcPluginM Bool
isPotentiallyInstantiatedPolymonad givenCts pmInst tyCons = do
  -- Get the type constructors partially applied to some new variables to find potential matches
  mAppliedTyCons <- mapM applyTyCon tyCons
  case (catMaybes mAppliedTyCons, all isJust mAppliedTyCons) of
    -- Only proceed if all type constructors are now indeed unary
    (appliedTyCons, True) -> do
      -- Create argument triplets
      let tyConAssocs = fmap snd <$> associations [ (pos, appliedTyCons) | pos <- [0..2 :: Int]]
      -- Now look at the instance and see if unification with any of our
      -- triplets of arguments delivers a match.
      fmap or $ forM tyConAssocs $ \tyConAssoc ->
        case matchInstanceTyVars pmInst (fst <$> tyConAssoc) of
          Just instArgMatches -> do
            -- Create a substitution from our map.
            let (instTyVars, instCts, _cls, _tyArgs) = instanceSig pmInst
            let subst = mkTopTvSubst $ zip instTyVars instArgMatches
            -- Substitute the matchings into the instance constraints.
            let substInstCts = substTys subst instCts
            -- Collect all instance constraints that do not contain variables.
            let appliedInstCts = filter isFullyAppliedConstraint substInstCts
            -- Check if we can produce evidence for them.
            appliedInstCtEv <- mapM (produceEvidenceForCt givenCts) appliedInstCts
            -- If so this instance is potentially instantiated.
            return $ all isRight appliedInstCtEv
          Nothing -> return False
    _ -> return False
  where
    -- | The constraint is fully applied if it does not contain variables,
    --   except for those contained in the given constraints.
    isFullyAppliedConstraint :: Type -> Bool
    isFullyAppliedConstraint t = collectTyVars t `S.isSubsetOf` S.unions (constraintTyVars <$> givenCts)


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
