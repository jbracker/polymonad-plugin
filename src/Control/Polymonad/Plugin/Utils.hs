
-- | Provides all kinds of functions that are needed by the plugin.
module Control.Polymonad.Plugin.Utils (
  -- * Type inspection
    collectTopTyCons
  , collectTopTcVars
  , collectTyVars
  , mkTcVarSubst
  , splitTyConApps
  , isGroundUnaryTyCon
  -- * General Utilities
  , eqTyVar, eqTyVar'
  , eqTyCon
  , isAmbiguousType
  , atIndex
  , associations
  , subsets
  , removeDup
  ) where

import Data.Maybe ( listToMaybe, catMaybes )
import Data.Set ( Set )
import qualified Data.Set as S

import Type
  ( Type, TyVar, TvSubst
  , getTyVar_maybe
  , tyConAppTyCon_maybe
  , splitTyConApp_maybe
  , splitAppTys
  , mkTyConTy
  , mkTopTvSubst
  , eqType )
import TyCon ( TyCon, tyConArity )
import TcType ( isAmbiguousTyVar )

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

-- | Split type constructor applications into their type constructor and arguments. Only
--   keeps those in the result list where this split actually worked.
splitTyConApps :: [Type] -> [(TyCon, [Type])]
splitTyConApps = catMaybes . fmap splitTyConApp_maybe

-- | Check if the given type is a type constructor that is partially applied
--   such that it now is a unary type constructor.
isGroundUnaryTyCon :: Type -> Bool
isGroundUnaryTyCon t = case splitTyConApp_maybe t of
  Just (tc, args) -> tyConArity tc == length args + 1
  Nothing -> False

-- -----------------------------------------------------------------------------
-- General utilities
-- -----------------------------------------------------------------------------

-- | Check if both types contain type variables and if those type
--   variables are equal.
eqTyVar :: Type -> Type -> Bool
eqTyVar ty ty' = case getTyVar_maybe ty of
  Just tv -> eqTyVar' tv ty'
  _ -> False

-- | Check if the given type constrains a type variable and it is equal to
--   the given type variable.
eqTyVar' :: TyVar -> Type -> Bool
eqTyVar' tv ty = case getTyVar_maybe ty of
  Just tv' -> tv == tv'
  Nothing  -> False

-- | Checks if the given type constructors equals the given type.
-- TODO: Test!
eqTyCon :: TyCon -> Type -> Bool
eqTyCon tc = eqType (mkTyConTy tc)

-- | Get the element of a list at a given index (If that element exists).
atIndex :: [a] -> Int -> Maybe a
atIndex xs i = listToMaybe $ drop i xs

-- | Checks if the given type is an ambiguous type variable.
isAmbiguousType :: Type -> Bool
isAmbiguousType ty = maybe False isAmbiguousTyVar $ getTyVar_maybe ty

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
associations ((x, y : ys) : xys) = fmap ((x, y) :) (associations xys) ++ associations ((x, ys) : xys)

-- | Generates the set of all subsets of a given set.
subsets :: (Ord a) => Set a -> Set (Set a)
subsets s = case S.size s of
  0 -> S.singleton S.empty
  _ -> let (x, s') = S.deleteFindMin s
           subs = subsets s'
       in S.map (S.insert x) subs `S.union` subs

-- | Efficient removal of duplicate elements in O(n * log(n)).
--   The result list is ordered in ascending order.
removeDup :: (Ord a) => [a] -> [a]
removeDup = S.toAscList . S.fromList
