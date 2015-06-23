
-- | Functions and utilities to work with and inspect class instances
--   of the GHC API. 
module Control.Polymonad.Plugin.Instance
  ( instanceTyCons
  , instanceTcVars
  , findInstanceTopTyCons
  , findMatchingInstances
  ) where

import Data.Maybe ( catMaybes )
import Data.List ( partition )
import Data.Set ( Set )
import qualified Data.Set as S

import Name ( getName )
import InstEnv 
  ( ClsInst(..), ClsInstLookupResult
  , instanceHead
  , instanceSig
  , lookupInstEnv
  , instanceBindFun )
import Type 
  ( Type, TyVar, TvSubst
  , splitTyConApp_maybe
  , mkTyVarTy, getTyVar
  , tyConAppTyCon
  , substTys 
  , substTy )
import TyCon ( TyCon )
import Unify ( tcUnifyTys )
import TcPluginM

import Control.Polymonad.Plugin.Utils 
  ( printppr
  , collectTopTyCons
  , collectTopTcVars )
  


-- | Retrieve the type constructors involved in the instance head of the 
--   given instance. This only selects the top level type constructors 
--   (See 'collectTopTyCons').
--   /Example:/
--   
--   > instance Polymonad Identity m Identity where
--   > > { Identity }
instanceTyCons :: ClsInst -> Set TyCon
instanceTyCons inst = 
  let (_tvs, _cls, args) = instanceHead inst 
  in collectTopTyCons args

-- | Retrieve the type constructor variables involved in the instance head of the 
--   given instance. This only selects the top level type variables (See 'collectTopTcVars').
--   /Example:/
--   
--   > instance Polymonad (m a b) n Identity where
--   > > { m , n }
instanceTcVars :: ClsInst -> Set TyVar
instanceTcVars inst = 
  let (_tvs, _cls, args) = instanceHead inst
  in collectTopTcVars args

-- | Search for all possible type constructors that could be 
--   used in the top-level position of the instance arguments.
--   Delivers a set of type constructors together with their arity.
findInstanceTopTyCons :: ClsInst -> TcPluginM (Set TyCon)
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
      foundTcs <- mapM (findConstraintTyCons instTcvs) (splitTyConApps cts)
      -- Collect all results
      return $ instTcs `S.union` S.unions foundTcs
  where
    findConstraintTyCons :: Set TyVar -> (TyCon, [Type]) -> TcPluginM (Set TyCon)
    findConstraintTyCons tcvs (ctTyCon, ctTyConAppArgs)
      -- There are no relevant type variables to substitute. We are done
      | S.null tcvs = return $ S.empty 
      | otherwise = do
        -- Find the type class this constraint is about
        ctCls <- tcLookupClass (getName ctTyCon)
        -- Get our instance environment
        instEnvs <- getInstEnvs
        -- Find all instances that match the given constraint
        let (otherFoundClsInsts, foundClsInsts, _) = lookupInstEnv instEnvs ctCls ctTyConAppArgs
        -- ([(ClsInst, [DFunInstType])], [ClsInst], Bool)
        -- TODO: So far this was always empty. Alert when there actually is something in there:
        if null otherFoundClsInsts then return () else printppr otherFoundClsInsts
        -- Now look at each found instance and collect the type constructor for the relevant variables
        collectedTyCons <- (flip mapM) foundClsInsts $ \foundInst -> do
          -- Unify the constraint arguments with the instance arguments.
          case tcUnifyTys instanceBindFun ctTyConAppArgs (is_tys foundInst) of
            -- The instance is applicable
            Just subst -> do
              -- Get substitutions for variables that we are searching for
              let substTcvs = fmap (substTy subst . mkTyVarTy) (S.toList tcvs)
              -- Sort the substitutions into type constructors and type variables
              let (substTcs, substTvs) = partition (\t -> maybe False (const True) (splitTyConApp_maybe t)) substTcvs
              -- Get the constraints of this instance
              let (_vars, cts, _cls, _instArgs) = instanceSig foundInst
              -- Search for further instantiations of type constructors in
              -- the constraints of this instance. Search is restricted to 
              -- variables that are relevant for the original search.
              -- Relevant means that the variables are substitutes for the original ones.
              collectedTcs <- (flip mapM) (splitTyConApps cts) 
                            $ findConstraintTyCons (S.fromList $ fmap (getTyVar "This should never happen") substTvs)
              -- Union everthing we found so far together
              return $ (S.fromList $ fmap tyConAppTyCon substTcs) `S.union` S.unions collectedTcs
            -- The instance is not applicable for our constraint. We are done here.
            Nothing -> return $ S.empty
        -- Union all collected type constructors
        return $ S.unions $ collectedTyCons

-- | Split type constructor applications into their type constructor and arguments. Only
--   keeps those in the result list where this split actually worked.
splitTyConApps :: [Type] -> [(TyCon, [Type])]
splitTyConApps = catMaybes . fmap splitTyConApp_maybe

-- | Substitute some type variables in the head of the given instance and 
--   look if you can find instances that provide and implementation for the 
--   substituted type.
findMatchingInstances :: TvSubst -> ClsInst -> TcPluginM ClsInstLookupResult
findMatchingInstances subst clsInst = do
  instEnvs <- getInstEnvs
  let cls = is_cls clsInst
  let tys = substTys subst $ is_tys clsInst
  return $ lookupInstEnv instEnvs cls tys