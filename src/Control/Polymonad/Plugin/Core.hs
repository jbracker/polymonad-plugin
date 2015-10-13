
-- | A collection of functions that did not fit anywhere else.
module Control.Polymonad.Plugin.Core
  ( isInstanceOf
  , trySolveAmbiguousForAppliedTyConConstraint
  ) where

import Data.Maybe ( fromJust, catMaybes )
import qualified Data.Set as S

import Control.Monad ( forM )

import InstEnv ( ClsInst )
import Type
  ( Type, TyVar
  , substTyVar )
import Unify ( tcUnifyTys )
import TcType ( isAmbiguousTyVar )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runTcPlugin
  , getGivenConstraints
  , getPolymonadClass, getCurrentPolymonad
  , throwPluginError
  , printObj )
import Control.Polymonad.Plugin.Instance
  ( isInstantiatedBy
  , instanceTyArgs )
import Control.Polymonad.Plugin.Constraint
  ( WantedCt
  , constraintClassTyArgs
  , isClassConstraint
  , isTyConAppliedClassConstraint )
import Control.Polymonad.Plugin.Utils
  ( collectTyVars
  , skolemVarsBindFun )

-- | Checks if the given arguments types to the free variables in the
--   class instance actually form a valid instantiation of that instance.
--   The given arguments need to match up with the list of free type variables
--   given for the class instance ('is_tvs').
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
        -- and is fully applied to concrete types.
        |  isClassConstraint pmCls ct
        && isTyConAppliedClassConstraint ct -> do
      let ambTyVars = filter isAmbiguousTyVar $ S.toList $ S.unions $ fmap collectTyVars tyArgs
      let dontBind =  (filter (not . isAmbiguousTyVar) $ S.toList $ S.unions $ fmap collectTyVars tyArgs)
                   ++ (S.toList $ S.unions $ concat $ fmap (maybe [] (fmap collectTyVars) . constraintClassTyArgs) pmCts)

      instMatches <- forM pmInsts $ \pmInst -> do
        printObj pmInst
        let instArgs = instanceTyArgs pmInst
        case tcUnifyTys (skolemVarsBindFun dontBind) tyArgs instArgs of
          Just subst ->
            return $ Just $ zip ambTyVars (substTyVar subst <$> ambTyVars)
          Nothing -> return Nothing

      ctMatches <- forM pmCts $ \pmCt -> do
        printObj pmCt
        let ctArgs = fromJust $ constraintClassTyArgs pmCt
        case tcUnifyTys (skolemVarsBindFun dontBind) tyArgs ctArgs of
          Just subst ->
            return $ Just $ zip ambTyVars (substTyVar subst <$> ambTyVars)
          Nothing -> return Nothing

      return $ case catMaybes (instMatches ++ ctMatches) of
        [binds] -> Just binds
        _ -> Nothing
    _ -> return Nothing
