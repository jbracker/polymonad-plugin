
-- | A collection of functions that did not fit anywhere else.
module Control.Polymonad.Plugin.Core
  ( isInstanceOf
  , trySolveAmbiguousForAppliedTyConConstraint
  , detectOverlappingInstancesAndTrySolve
  ) where

import Data.Maybe ( fromJust, catMaybes )
import qualified Data.Set as S

import Control.Monad ( forM )

import InstEnv ( ClsInst )
import Type
  ( Type, TyVar
  , substTyVar, substTys )
import Unify ( tcUnifyTys )
import TcType ( isAmbiguousTyVar )
import TcEvidence ( EvTerm )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runTcPlugin
  , getGivenConstraints
  , getPolymonadClass, getCurrentPolymonad
  --, printObj, printMsg
  , throwPluginError )
import Control.Polymonad.Plugin.Instance
  ( isInstantiatedBy
  , instanceTyArgs
  , matchInstanceTyVars )
import Control.Polymonad.Plugin.Constraint
  ( WantedCt
  , constraintClassTyArgs
  , isClassConstraint
  , isTyConAppliedClassConstraint )
import Control.Polymonad.Plugin.Evidence
  ( produceEvidenceFor )
import Control.Polymonad.Plugin.Utils
  ( collectTyVars
  , skolemVarsBindFun )

-- | Checks if the given arguments types to the free variables in the
--   class instance actually form a valid instantiation of that instance.
--   The given arguments need to match up with the list of free type variables
--   given for the class instance ('is_tvs'). See 'matchInstanceTyVars' for
--   matching up the arguments.
--
--   Caveat: This currently only matches class constraints, but not type
--   equality or type function constraints properly.
isInstanceOf :: [Type] -> ClsInst -> PmPluginM Bool
isInstanceOf tys inst = do
  givenCts <- getGivenConstraints
  res <- runTcPlugin $ isInstantiatedBy givenCts tys inst
  case res of
    Left err -> throwPluginError err
    Right b -> return b

produceEvidenceForPM :: ClsInst -> [Type] -> PmPluginM (Maybe EvTerm)
produceEvidenceForPM inst args = runTcPlugin $ produceEvidenceFor inst args


-- | Tries to solve ambiguous type variables in polymonad constraints using
--   the available polymonad instances. Only unification is applied. This
--   only delivers a result if there is exactly one instance that matches
--   the given constraint and all type constructors of the given constraint
--   are concrete (see 'isTyConAppliedClassConstraint').
--
--   __Note__: This means that ambiguous type variables in the type
--   constructors arguments will be assigned and therefore this may not
--   be applicable if those indices do not influence the runtime behaviour.
trySolveAmbiguousForAppliedTyConConstraint :: WantedCt -> PmPluginM (Maybe [(TyVar, Type)])
trySolveAmbiguousForAppliedTyConConstraint ct = do
  pmCls <- getPolymonadClass
  (_, pmInsts, pmCts) <- getCurrentPolymonad
  case constraintClassTyArgs ct of
    -- We found the polymonad class constructor and the given constraint
    -- is a instance constraint.
    Just tyArgs
        -- Be sure to only proceed if the constraint is a polymonad constraint
        -- and is fully applied to concrete type constructors.
        |  isClassConstraint pmCls ct
        && isTyConAppliedClassConstraint ct -> do
      -- Collect all ambiguous variables that appear in the constraint.
      let ambTyVars = filter isAmbiguousTyVar (S.toList $ S.unions $ fmap collectTyVars tyArgs)
      -- Collect variables that are to be seen as constants.
      -- The first batch of these are the non ambiguous type variables in the constraint arguments...
      let dontBind =  filter (not . isAmbiguousTyVar) (S.toList $ S.unions $ fmap collectTyVars tyArgs)
                   -- and the second batch are the type variables in given constraints.
                   ++ S.toList (S.unions $ concat $ fmap (maybe [] (fmap collectTyVars) . constraintClassTyArgs) pmCts)
      -- Now look at all instances and see if they match our constraint by unification.
      instMatches <- forM pmInsts $ \pmInst -> do
        let instArgs = instanceTyArgs pmInst
        case tcUnifyTys (skolemVarsBindFun dontBind) tyArgs instArgs of
          Just subst ->
            -- If so, we return the mapping of ambiguous variabels to specific types.
            return $ Just $ zip ambTyVars (substTyVar subst <$> ambTyVars)
          Nothing -> return Nothing
      -- We repeat the process for the given constraints.
      ctMatches <- forM pmCts $ \pmCt -> do
        let ctArgs = fromJust $ constraintClassTyArgs pmCt
        case tcUnifyTys (skolemVarsBindFun dontBind) tyArgs ctArgs of
          Just subst ->
            return $ Just $ zip ambTyVars (substTyVar subst <$> ambTyVars)
          Nothing -> return Nothing
      -- Finally, we collect all association we found. If there is no
      -- ambiguity (only one possible association, as concluded through available instances)
      -- we can use that association.
      return $ case catMaybes (instMatches ++ ctMatches) of
        [binds] -> Just binds
        _ -> Nothing
    _ -> return Nothing

-- | Determines if there are two overlapping instances for a given constraint.
--   If so, try to solve them and see if there if there is a single instance that
--   fulfills all requirements.
detectOverlappingInstancesAndTrySolve :: WantedCt -> PmPluginM (Maybe EvTerm)
detectOverlappingInstancesAndTrySolve ct =
  case constraintClassTyArgs ct of
    Just tyArgs -> do
      (_, pmInsts, pmCts) <- getCurrentPolymonad
      -- Collect variables that are to be seen as constants.
      -- The first batch of these are the non ambiguous type variables in the constraint arguments...
      let dontBind =  filter (not . isAmbiguousTyVar) (S.toList $ S.unions $ fmap collectTyVars tyArgs)
                   -- and the second batch are the type variables in given constraints.
                   ++ S.toList (S.unions $ concat $ fmap (maybe [] (fmap collectTyVars) . constraintClassTyArgs) pmCts)
      instMatches <- forM pmInsts $ \pmInst -> do
        let instArgs = instanceTyArgs pmInst
        case tcUnifyTys (skolemVarsBindFun dontBind) tyArgs instArgs of
          Just subst -> case matchInstanceTyVars (substTys subst tyArgs) pmInst of
            Just args -> do
              isInst <- args `isInstanceOf` pmInst
              return $ if isInst then Just (pmInst, args) else Nothing
            Nothing -> return Nothing
          Nothing -> return Nothing
      case catMaybes instMatches of
        [instWithArgs] -> uncurry produceEvidenceForPM instWithArgs
        _ -> return Nothing
    _ -> return Nothing
