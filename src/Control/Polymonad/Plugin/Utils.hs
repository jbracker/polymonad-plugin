
-- | Provides all kinds of functions that are needed by the plugin.
module Control.Polymonad.Plugin.Utils (
  -- * Plugin printing and debugging
    printppr
  , printM
  , pprToStr
  -- * Type inspection
  , collectTopTyCons
  , collectTopTcVars
  , collectTyVars
  , mkTcVarSubst
  , findConstraintOrInstanceTyCons
  , splitTyConApps
  -- * General Utilities
  , eqTyVar, eqTyVar'
  , eqTyCon
  , atIndex
  , associations
  , subsets
  , missingCaseError
  ) where

import Data.List ( partition )
import Data.Maybe ( listToMaybe, catMaybes, isJust )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( unless, forM )

import Type
  ( Type, TyVar, TvSubst
  , getTyVar_maybe
  , tyConAppTyCon_maybe
  , splitTyConApp_maybe
  , splitAppTys
  , mkTyConTy
  , mkTopTvSubst
  , mkTyVarTy, getTyVar
  , tyConAppTyCon
  , substTy
  , eqType )
import TyCon ( TyCon )
import Name ( getName )
import InstEnv
  ( ClsInst(..)
  , instanceSig
  , lookupInstEnv
  , instanceBindFun )
import Unify ( tcUnifyTys )
import TcPluginM
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

-- | @findConstraintOrInstanceTyCons tvs ctOrInst@ delivers the set of type
--   constructors that can be substituted for the type variables in @tvs@
--   which are part of the given constraint or instance @ctOrInst@.
--   Only works properly if the given type variables are a subset of
--   @collectTopTcVars (snd ctOrInst)@.
findConstraintOrInstanceTyCons :: Set TyVar -> (TyCon, [Type]) -> TcPluginM (Set TyCon)
findConstraintOrInstanceTyCons tcvs (ctTyCon, ctTyConAppArgs)
  -- There are no relevant type variables to substitute. We are done
  | S.null tcvs = return S.empty
  | otherwise = do
    -- Find the type class this constraint is about
    ctCls <- tcLookupClass (getName ctTyCon)
    -- Get our instance environment
    instEnvs <- getInstEnvs
    -- Find all instances that match the given constraint
    let (otherFoundClsInsts, foundClsInsts, _) = lookupInstEnv instEnvs ctCls ctTyConAppArgs
    -- ([(ClsInst, [DFunInstType])], [ClsInst], Bool)
    -- TODO: So far this was always empty. Alert when there actually is something in there:
    unless (null otherFoundClsInsts) $ printppr otherFoundClsInsts
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

-- | Split type constructor applications into their type constructor and arguments. Only
--   keeps those in the result list where this split actually worked.
splitTyConApps :: [Type] -> [(TyCon, [Type])]
splitTyConApps = catMaybes . fmap splitTyConApp_maybe

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

-- | Used to emit an error with a message describing the missing case.
--   The string is the function that misses the case and the 'Outputable'
--   is the object being matched.
missingCaseError :: (Outputable o) => String -> Maybe o -> a
missingCaseError funName (Just val) = error $ "Missing case in '" ++ funName ++ "' for " ++ pprToStr val
missingCaseError funName Nothing    = error $ "Missing case in '" ++ funName ++ "'"
