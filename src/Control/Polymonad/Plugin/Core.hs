
-- | Core functions the plugin relies on to interact with GHCs API.
module Control.Polymonad.Plugin.Core
  ( pickInstanceForAppliedConstraint
  , findInstanceTopTyCons
  , findConstraintTopTyCons
  , findConstraintOrInstanceTyCons
  , isInstanceOf
  ) where

import Data.Maybe ( isJust, isNothing, fromJust, catMaybes )
import Data.List ( partition, find )
import Data.Set ( Set )
import qualified Data.Set as S
import Control.Monad ( forM, unless, when )
import Control.Monad.Trans.Class ( lift )

import InstEnv
  ( ClsInst(..)
  , instanceBindFun, instanceSig
  , lookupInstEnv
  , lookupUniqueInstEnv )
import TyCon ( TyCon )
import Type
  ( Type, TyVar
  , getClassPredTys_maybe
  , mkTopTvSubst, mkTyVarTy
  , substTys, substTy
  , splitTyConApp_maybe
  , getTyVar
  , eqTypes
  , tyConAppTyCon )
import Unify ( tcUnifyTys )
import Class ( Class(..) )
import Name ( getName )
import TcRnTypes ( Ct(..) )
import TcPluginM ( tcLookupClass )
import TcEvidence ( EvTerm(..) )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , getPolymonadClass, getInstEnvs
  , getGivenConstraints
  , throwPluginError
  , printObj )
import Control.Polymonad.Plugin.Constraint
  ( constraintClassType, constraintClassTyArgs
  , constraintTyCons, constraintTcVars
  , isClassConstraint, isFullyAppliedClassConstraint )
import Control.Polymonad.Plugin.Instance
  ( instanceTyCons, instanceTcVars )
import Control.Polymonad.Plugin.Utils
  ( splitTyConApps )

-- | Search for all possible type constructors that could be
--   used in the top-level position of the constraint arguments.
--   Delivers a set of type constructors.
findConstraintTopTyCons :: Ct -> PmPluginM (Set TyCon)
findConstraintTopTyCons ct = case constraintClassType ct of
  Just (cls, tyArgs) -> do
    let tyCon = classTyCon cls
    let tcs = constraintTyCons ct
    foundTcs <- findConstraintOrInstanceTyCons (constraintTcVars ct) (tyCon, tyArgs)
    return $ tcs `S.union` foundTcs
  Nothing -> return S.empty

-- | Search for all possible type constructors that could be
--   used in the top-level position of the instance arguments.
--   Delivers a set of type constructors.
findInstanceTopTyCons :: ClsInst -> PmPluginM (Set TyCon)
findInstanceTopTyCons clsInst = do
  -- Top level type constructors of the instance arguments
  let instTcs = instanceTyCons clsInst
  -- Type constructor variables of the instance arguments
  let instTcvs = instanceTcVars clsInst
  -- Get the constraints of the given instance
  let (_vars, cts, _cls, _instArgs) = instanceSig clsInst
  -- For each constraint find the type constructors in its instances as
  -- long as they are substitutes for the type constructor variables in
  -- this instance
  foundTcs <- mapM (findConstraintOrInstanceTyCons instTcvs) (splitTyConApps cts)
  -- Collect all results
  return $ instTcs `S.union` S.unions foundTcs


-- | @findConstraintOrInstanceTyCons tvs ctOrInst@ delivers the set of type
--   constructors that can be substituted for the type variables in @tvs@
--   which are part of the given constraint or instance @ctOrInst@.
--   Only works properly if the given type variables are a subset of
--   @collectTopTcVars (snd ctOrInst)@.
findConstraintOrInstanceTyCons :: Set TyVar -> (TyCon, [Type]) -> PmPluginM (Set TyCon)
findConstraintOrInstanceTyCons tcvs (ctTyCon, ctTyConAppArgs)
  -- There are no relevant type variables to substitute. We are done
  | S.null tcvs = return S.empty
  | otherwise = do
    -- Find the type class this constraint is about
    ctCls <- lift . lift $ tcLookupClass (getName ctTyCon)
    -- Get our instance environment
    instEnvs <- getInstEnvs
    -- Find all instances that match the given constraint
    let (otherFoundClsInsts, foundClsInsts, _) = lookupInstEnv instEnvs ctCls ctTyConAppArgs
    -- ([(ClsInst, [DFunInstType])], [ClsInst], Bool)
    -- TODO: So far this was always empty. Alert when there actually is something in there:
    unless (null otherFoundClsInsts) $ printObj otherFoundClsInsts
    -- Now look at each found instance and collect the type constructor for the relevant variables
    collectedTyCons <- forM foundClsInsts $ \foundInst ->
      -- Unify the constraint arguments with the instance arguments.
      case tcUnifyTys instanceBindFun ctTyConAppArgs (is_tys foundInst) of
        -- The instance is applicable
        Just subst -> do
          -- Get substitutions for variables that we are searching for
          let substTcvs = fmap (substTy subst . mkTyVarTy) (S.toList tcvs)
          -- Sort the substitutions into type constructors and type variables
          let (substTcs, substTvs) = partition (isJust . splitTyConApp_maybe) substTcvs
          -- Get the constraints of this instance
          let (_vars, cts, _cls, _instArgs) = instanceSig foundInst
          -- Search for further instantiations of type constructors in
          -- the constraints of this instance. Search is restricted to
          -- variables that are relevant for the original search.
          -- Relevant means that the variables are substitutes for the original ones.
          collectedTcs <- forM (splitTyConApps cts)
                        $ findConstraintOrInstanceTyCons (S.fromList $ fmap (getTyVar "This should never happen") substTvs)
          -- Union everthing we found so far together
          return $ S.fromList (fmap tyConAppTyCon substTcs) `S.union` S.unions collectedTcs
        -- The instance is not applicable for our constraint. We are done here.
        Nothing -> return S.empty
    -- Union all collected type constructors
    return $ S.unions collectedTyCons

-- | Given a fully applied polymonad constraint it will pick the first instance
--   that matches it. This is ok to do, because for polymonads it does
--   not make a difference which bind-operation we pick if the type is equal.
pickInstanceForAppliedConstraint :: Ct -> PmPluginM (Maybe (EvTerm, Ct))
pickInstanceForAppliedConstraint ct = do
  -- Get the polymonad class constructor.
  pmCls <- getPolymonadClass
  case constraintClassTyArgs ct of
    -- We found the polymonad class constructor and the given constraint
    -- is a instance constraint.
    Just tyArgs
        -- Be sure to only proceed if the constraint is a polymonad constraint
        -- and is fully applied to concrete types.
        |  isClassConstraint pmCls ct
        && isFullyAppliedClassConstraint ct -> do
      -- Get the instance environment
      instEnvs <- getInstEnvs
      -- Find matching instance for our constraint.
      let (matches, _, _) = lookupInstEnv instEnvs pmCls tyArgs
      -- Only keep those matches that actually found a type for every argument.
      case filter (\(_, args) -> all isJust args) matches of
        -- If we found more then one instance, just use the first.
        -- Because we are talking about polymonad we can freely choose.
        (foundInst, foundInstArgs) : _ -> do
          -- Try to produce evidence for the instance we want to use.
          evTerm <- produceEvidenceFor foundInst (fromJust <$> foundInstArgs)
          return $ (\ev -> (ev, ct)) <$> evTerm
        _ -> return Nothing
    _ -> return Nothing
  where
    -- | Apply the given instance dictionary to the given type arguments
    --   and try to produce evidence for the application.
    produceEvidenceFor :: ClsInst -> [Type] -> PmPluginM (Maybe EvTerm)
    produceEvidenceFor inst tys = do
      -- Get the instance type variables and constraints (by that we know the
      -- number of type arguments and dictionart arguments for the EvDFunApp)
      let (tyVars, cts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
      -- How the instance variables for the current instance are bound.
      let varSubst = mkTopTvSubst $ zip tyVars tys
      -- Global instance environment.
      instEnvs <- getInstEnvs
      -- Split the constraints into their class and arguments.
      -- We ignore constraints where this is not possible.
      -- Don't know if this is the right thing to do.
      let instCts = catMaybes $ fmap getClassPredTys_maybe cts
      -- Now go over each constraint and find a suitable instance and evidence.
      ctEvTerms <- forM instCts $ \(ctCls, ctArgs) -> do
        -- Substitute the variables to know what instance we are looking for.
        let substArgs = substTys varSubst ctArgs
        -- Look for suitable instance. Since we are not necessarily working
        -- with polymonads anymore we need to find a unique one.
        case lookupUniqueInstEnv instEnvs ctCls substArgs of
          -- No instance found, too bad...
          Left _err -> return Nothing
          -- We found one: Now we can produce evidence for the found instance.
          Right (clsInst, instArgs) -> produceEvidenceFor clsInst instArgs
      -- If we found a good instance and evidence for every constraint,
      -- we can create the evidence for this instance.
      return $ if any isNothing ctEvTerms
        then Nothing
        else Just $ EvDFunApp (is_dfun inst) tys (fromJust <$> ctEvTerms)

-- | Checks if the given arguments types to the free variables in the
--   class instance actually from a valid instantiation of that instance.
--   The given arguments need to match up with the list of free type variables
--   given for the class instance ('is_tvs').
--
--   Caveat: This currently only matches class constraints, but not type
--   equality or type function constraints properly.
isInstanceOf :: [Type] -> ClsInst -> PmPluginM Bool
isInstanceOf tys inst = do
  -- Get the instance type variables and constraints (by that we know
  -- the numner of type arguments)
  let (instVars, cts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
  -- Assert: We have a type for each variable in the instance.
  when (length tys /= length instVars) $
    throwPluginError "isInstanceOf: Number of type arguments does not match number of variables in instance"
  -- How the instance variables for the current instance are bound.
  let varSubst = mkTopTvSubst $ zip instVars tys
  -- Split the constraints into their class and arguments.
  -- FIXME: We ignore constraints where this is not possible.
  -- Don't know if this is the right thing to do.
  let instCts = catMaybes $ fmap getClassPredTys_maybe cts
  -- Now go over each constraint and find a suitable instance.
  fmap and $ forM instCts $ \(ctCls, ctArgs) -> do
    -- Substitute the variables to know what instance we are looking for.
    let substArgs = substTys varSubst ctArgs
    -- Get the current instance environment
    instEnvs <- getInstEnvs
    -- Look for suitable instance. Since we are not necessarily working
    -- with polymonads anymore we need to find a unique one.
    case lookupUniqueInstEnv instEnvs ctCls substArgs of
      -- No instance found, but maybe a given constraint will do the deed...
      Left _err -> do
        givenCts <- getGivenConstraints
        -- Split the given constraints into their class and arguments.
        -- FIXME: We ignore constraints where this is not possible.
        let givenInstCts = catMaybes $ fmap constraintClassType givenCts
        -- Define the predicate to check if a given constraint matches
        -- the constraint we want to fulfill.
        let eqInstCt (givenCls, givenArgs) = ctCls == givenCls && eqTypes substArgs givenArgs
        -- If we find a given constraint that fulfills the constraint we are
        -- searching for, return true, otherwise false.
        return $ isJust $ find eqInstCt givenInstCts
      -- We found one: Now we also need to check the found instance for
      -- its preconditions.
      Right (clsInst, instArgs) -> instArgs `isInstanceOf` clsInst
