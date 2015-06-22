
-- | Provides all kinds of functions that are needed by the plugin.
module Control.Polymonad.Plugin.Utils ( 
  -- * Plugin printing and debugging
    printppr
  , printM
  , pprToStr
  -- * Polymonad module and class recognition
  , getPolymonadModule
  , isPolymonadClass
  , getPolymonadClass
  , getPolymonadInstancesInScope
  , getRelevantPolymonadTyCons
  -- * Constraint and type inspection
  , isClassConstraint
  , instanceTyCons
  , instanceTcVars
  , constraintTyCons
  , constraintTcVars
  , constraintClassTyCon
  , collectTyVars
  , mkTcVarSubst
  , findMatchingInstances
  -- * General Utilities
  , atIndex
  , associations
  ) where

import Data.Maybe ( listToMaybe, catMaybes )
import Data.Set ( Set )
import qualified Data.Set as S
import Control.Monad ( filterM )
import Control.Monad ( guard, MonadPlus(..) )

import Var (varUnique)
import TcRnTypes
  ( Ct(..), CtEvidence(..)
  , isCDictCan_Maybe
  , isCNonCanonical
  , isWantedCt
  , imp_mods
  , ctev_pred
  , tcg_imports, tcg_inst_env )
import TcPluginM
import Name 
  ( nameModule
  , getOccName, getName )
import OccName ( occNameString )
import Module 
  ( Module(..)
  , mainPackageKey
  , moduleEnvKeys
  , moduleNameString )
import Class
  ( Class(..)
  , className, classArity )
import InstEnv 
  ( ClsInst(..), ClsInstLookupResult
  , instEnvElts
  , instanceHead
  , classInstances
  , lookupInstEnv
  , instanceSig
  , instanceBindFun )
import Unify ( tcUnifyTys )
import Type 
  ( Type, TyVar, TvSubst
  , getTyVar_maybe
  , tyConAppTyCon_maybe
  , tyConAppArgs
  , splitTyConApp_maybe
  , splitAppTys
  , mkTyConTy
  , mkTopTvSubst
  , substTys
  )
import TyCon ( TyCon )
import Outputable 
  ( Outputable( ppr )
  --, text, parens, (<>)
  , showSDocUnsafe )
  
-- -----------------------------------------------------------------------------
-- Plugin debug primitives
-- -----------------------------------------------------------------------------

-- | Print some generic outputable from the plugin (Unsafe).
printppr :: Outputable o => o -> TcPluginM ()
printppr = tcPluginIO . putStrLn . pprToStr

-- | Print a message from the plugin.
printM :: String -> TcPluginM ()
printM = tcPluginIO . putStrLn

-- | Convert some generic outputable to a string (Unsafe).
pprToStr :: Outputable o => o -> String
pprToStr = showSDocUnsafe . ppr

-- -----------------------------------------------------------------------------
-- Polymonad module and class recognition
-- -----------------------------------------------------------------------------

polymonadModuleName :: String
polymonadModuleName = "Control.Polymonad"

polymonadClassName :: String
polymonadClassName = "Polymonad"

-- | Checks of the module containing the 'Control.Polymonad' type class 
--   is imported and, if so, return the module.
getPolymonadModule :: TcPluginM (Maybe Module)
getPolymonadModule = do
  impMdls <- fmap (moduleEnvKeys . imp_mods . tcg_imports . fst) getEnvs
  foundMdls <- (flip filterM) impMdls $ \m -> do
    let pkgKey = modulePackageKey m
    let mdlName = moduleNameString $ moduleName m
    return $ pkgKey == mainPackageKey && mdlName == polymonadModuleName
  return $ case foundMdls of
    [m] -> Just m
    _ -> Nothing

-- | Checks if the given class matches the shape of the 'Control.Polymonad'
--   type class and is defined in the given module. Usually the given module 
--   should be the one delivered from 'getPolymonadModule'.
isPolymonadClass :: Module -> Class -> Bool
isPolymonadClass polymonadModule cls = 
  let clsName = className cls
      clsMdl = nameModule clsName
      clsNameStr = occNameString $ getOccName clsName
      clsArity = classArity cls
  in    clsMdl == polymonadModule 
     && clsNameStr == polymonadClassName
     && clsArity == 3

-- | Checks if a type class matching the shape and name of the 
--   'Control.Polymonad' type class is in scope and if it is part of the
--   polymonad module ('getPolymonadModule'). If so returns the class.
getPolymonadClass :: TcPluginM (Maybe Class)
getPolymonadClass = do
  mModule <- getPolymonadModule
  case mModule of
    Just polymonadModule -> do
      visibleInsts <- fmap (instEnvElts . tcg_inst_env . fst) getEnvs
      let foundInsts = (flip filter) visibleInsts $ isPolymonadClass polymonadModule . is_cls
      return $ case foundInsts of
        (inst : _) -> Just $ is_cls inst
        [] -> Nothing
    Nothing -> return Nothing

-- | Returns a list of all 'Control.Polymonad' instances that are currently in scope.
getPolymonadInstancesInScope :: TcPluginM [ClsInst]
getPolymonadInstancesInScope = do
  mPolymonadClass <- getPolymonadClass
  case mPolymonadClass of
    Just polymonadClass -> do
      instEnvs <- getInstEnvs
      return $ classInstances instEnvs polymonadClass
    Nothing -> return []

-- | TODO
getRelevantPolymonadTyCons :: [Ct] -> TcPluginM (Set TyCon)
getRelevantPolymonadTyCons cts = do
  pmInsts <- getPolymonadInstancesInScope
  return $ S.unions $ fmap constraintTyCons cts

-- | Find all instances that could possible be applied for a given constraint.
--   Returns the applicable instance together with the necessary substitution
--   for unification.
findMatchingInstancesForConstraint :: [ClsInst] -> Ct -> [(ClsInst, TvSubst)]
findMatchingInstancesForConstraint insts ct = do
  inst <- insts
  let ctTys = constraintTyParams ct
  guard $ classTyCon (is_cls inst) == constraintClassTyCon ct
  case tcUnifyTys instanceBindFun (is_tys inst) ctTys of
    Just subst -> do
      return (inst, subst)
    Nothing -> mzero

-- -----------------------------------------------------------------------------
-- Constraint and type inspection
-- -----------------------------------------------------------------------------

-- | Check if the given constraint is a class constraint of the given class.
isClassConstraint :: Class -> Ct -> Bool
isClassConstraint wantedClass ct = 
  case isCDictCan_Maybe ct of
    Just cls -> cls == wantedClass && isWantedCt ct
    Nothing -> False

-- | Retrieves the arguments of the given type class constraints.
--   Unclear what happens if the given evidence does not contain a type 
--   application.
constraintEvidenceTyParams :: CtEvidence -> [Type]
constraintEvidenceTyParams evdnc = case splitTyConApp_maybe $ ctev_pred evdnc of
  Just (_tc, args) -> args
  Nothing -> missingCaseError "constraintEvidenceTyParams" $ Just (ctev_pred evdnc)

-- | Retrieves the arguments of the given constraints.
--   Only works if the constraint is a type class constraint.
--   Emits and error in case the constraint is not supported.
constraintTyParams :: Ct -> [Type]
constraintTyParams ct = case ct of
  CDictCan _ _ _ -> cc_tyargs ct
  CNonCanonical evdnc -> constraintEvidenceTyParams evdnc
  v -> missingCaseError "constraintTyParams" $ Just v

-- | Retrieves the type constructor of the given type class constraint.
--   Only works if the constraint is a type class constraint.
--   Emits and error in case the constraint is not supported.
constraintClassTyCon :: Ct -> TyCon
constraintClassTyCon ct = case ct of
  CDictCan _ _ _ -> classTyCon (cc_class ct)
  CNonCanonical evdnc -> constraintEvidenceClassTyCon evdnc
  v -> missingCaseError "constraintTyCon" $ Just v

-- | Retrieves the type constructor of the given type class constraints.
--   Only works if the constraint is a type class constraint.
--   Emits and error in case the constraint is not supported.
constraintEvidenceClassTyCon :: CtEvidence -> TyCon
constraintEvidenceClassTyCon evdnc = case splitTyConApp_maybe $ ctev_pred evdnc of
  Just (tc, _args) -> tc
  Nothing -> missingCaseError "constraintEvidenceClassTyCon" $ Just (ctev_pred evdnc)

-- | Retrieve the type constructors at top level involved in the given types.
--   If there are type constructors nested within the type they are ignored.
--   /Example:/
--   
--   > collectTopTyCons [Maybe (Identity ())]
--   > > { Maybe }
collectTopTyCons :: [Type] -> Set TyCon
collectTopTyCons tys = S.fromList $ catMaybes $ fmap tyConAppTyCon_maybe tys

-- | Retrieve the type constructor variables at the top level involved in the 
--   given types. If there are nested type variables they are ignored. 
--   There is no actual check if the returned type variables are actually type
--   constructor variables.
--   /Example:/
--   
--   > collectTopTcVars [m a b, Identity c, n]
--   > > { m, n }
collectTopTcVars :: [Type] -> Set TyVar
collectTopTcVars tys = S.fromList $ catMaybes $ fmap (getTyVar_maybe . fst . splitAppTys) tys

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

-- | Collects the type constructors in the arguments of the constraint. 
--   Only works if the given constraint is a type class constraint. 
--   Only collects those on the top level (See 'collectTopTyCons').
constraintTyCons :: Ct -> Set TyCon
constraintTyCons ct = collectTopTyCons $ constraintTyParams ct
  

-- | Collects the type variables in the arguments of the constraint. 
--   Only works if the given constraint is a type class constraint.
--   Only collects those on the top level (See 'collectTopTcVars').
constraintTcVars :: Ct -> Set TyVar
constraintTcVars ct = collectTopTcVars $ constraintTyParams ct

-- | Try to collect all type variables in a given expression.
--   Only works for nested type constructor applications and type variables.
--   If the given type is not supported an empty set is returned.
collectTyVars :: Type -> Set TyVar
collectTyVars t =
  case getTyVar_maybe t of
    Just tv -> S.singleton tv
    Nothing -> case splitTyConApp_maybe t of
      Just (_tc, args) -> S.unions $ fmap collectTyVars args
      Nothing -> S.empty

-- | Create a substitution that replaces the given type variables with their
--   associated type constructors.
mkTcVarSubst :: [(TyVar, TyCon)] -> TvSubst
mkTcVarSubst substs = mkTopTvSubst $ fmap (\(tv, tc) -> (tv, mkTyConTy tc)) substs

-- | Substitute some type variables in the head of the given instance and 
--   look if you can find instances that provide and implementation for the 
--   substituted type.
findMatchingInstances :: TvSubst -> ClsInst -> TcPluginM ClsInstLookupResult
findMatchingInstances subst clsInst = do
  instEnvs <- getInstEnvs
  let cls = is_cls clsInst
  let tys = substTys subst $ is_tys clsInst
  return $ lookupInstEnv instEnvs cls tys

-- -----------------------------------------------------------------------------
-- General utilities
-- -----------------------------------------------------------------------------

-- | Get the element of a list at a given index (If that element exists).
atIndex :: [a] -> Int -> Maybe a
atIndex xs i = listToMaybe $ drop i xs

-- | Takes a list of keys and all of their possible values and returns a list
--   of all possible associations between keys and values
--   /Example:/
--   
--   > associations [('a', [1,2,3]), ('b', [4,5])]
--   > > [ [('a', 1), ('b', 4)], [('a', 1), ('b', 5)]
--   > > , [('a', 2), ('b', 4)], [('a', 2), ('b', 5)]
--   > > , [('a', 3), ('b', 4)], [('a', 3), ('b', 5)] ]
associations :: [(key , [value])] -> [[(key, value)]]
associations [] = [[]]
associations ((_x, []) : _xys) = []
associations ((x, (y : ys)) : xys) = (fmap ((x, y) :) (associations xys)) ++ associations ((x, ys) : xys)

missingCaseError :: (Outputable o) => String -> Maybe o -> a
missingCaseError funName (Just val) = error $ "Missing case in '" ++ funName ++ "' for " ++ pprToStr val
missingCaseError funName Nothing    = error $ "Missing case in '" ++ funName ++ "'"