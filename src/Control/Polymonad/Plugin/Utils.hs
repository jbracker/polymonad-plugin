
-- | Provides all kinds of functions that are needed by the plugin.
module Control.Polymonad.Plugin.Utils ( 
  -- * Plugin printing and debugging
    printppr
  , printM
  , pprToStr
  -- * Constraint and type inspection
  , collectTopTyCons
  , collectTopTcVars
  , instanceTyCons
  , instanceTcVars
  , collectTyVars
  , mkTcVarSubst
  , findMatchingInstances
  -- * General Utilities
  , atIndex
  , associations
  , missingCaseError
  ) where

import Data.Maybe ( listToMaybe, catMaybes )
import Data.Set ( Set )
import qualified Data.Set as S

import TcPluginM
import InstEnv 
  ( ClsInst(..), ClsInstLookupResult
  , instanceHead
  , lookupInstEnv )
import Type 
  ( Type, TyVar, TvSubst
  , getTyVar_maybe
  , tyConAppTyCon_maybe
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
-- Constraint and type inspection
-- -----------------------------------------------------------------------------

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