
-- | Core functions the plugin relies on to interact with GHCs API.
module Control.Polymonad.Plugin.Core
  ( findInstanceTopTyCons
  , findConstraintTopTyCons
  , findConstraintOrInstanceTyCons
  , isInstanceOf
  ) where

import Data.Maybe ( isJust )
import Data.List ( partition )
import Data.Set ( Set )
import qualified Data.Set as S
import Control.Monad ( forM, unless )

import InstEnv
  ( ClsInst(..)
  , instanceBindFun, instanceSig
  , lookupInstEnv )
import TyCon ( TyCon )
import Type
  ( Type, TyVar
  , mkTyVarTy
  , substTy
  , splitTyConApp_maybe
  , getTyVar
  , tyConAppTyCon )
import Unify ( tcUnifyTys )
import Class ( Class(..) )
import Name ( getName )
import TcRnTypes ( Ct(..) )
import TcPluginM ( tcLookupClass )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runTcPlugin
  , getInstEnvs
  , getGivenConstraints
  , throwPluginError
  , printObj )
import Control.Polymonad.Plugin.Constraint
  ( constraintClassType
  , constraintTyCons, constraintTcVars )
import Control.Polymonad.Plugin.Instance
  ( instanceTyCons, instanceTcVars
  , isInstantiatedBy )
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
    ctCls <- runTcPlugin $ tcLookupClass (getName ctTyCon)
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
