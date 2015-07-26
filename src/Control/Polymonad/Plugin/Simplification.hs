
-- This is a workaround of a cabal/haddock bug:
-- http://trac.haskell.org/haddock/ticket/187
{-# LANGUAGE TemplateHaskell #-}

-- | Implementation of the simplification rules for polymonad constraints
--   described in section 5 of the "Polymonad Programming" paper (Hicks 2014).
module Control.Polymonad.Plugin.Simplification
  ( -- * Base Simplification Rules
    simplifyUp
  , simplifyDown
  , simplifyJoin
    -- * Application of Simplification Rules
  , simplifyAllUpDown
  , simplifyAllJoin
    -- * Utility Functions
  , simplifiedTvsToConstraints
  ) where

import Data.Maybe ( isJust, catMaybes )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Applicative ( Alternative(..) )
import Control.Monad ( guard )

import Type
  ( Type, TyVar
  , tyConAppTyCon_maybe
  , eqType
  , mkTyVarTy )
import TcRnTypes ( Ct )

import Control.Polymonad.Plugin.Log ( pprToStr )
import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , getIdentityTyCon, getPolymonadInstances
  , getGivenConstraints, getWantedConstraints
  , printErr, printObj, printMsg )
import Control.Polymonad.Plugin.Utils
  ( eqTyVar', eqTyCon )
import Control.Polymonad.Plugin.Constraint
  ( constraintPolymonadTyArgs, constraintPolymonadTyArgs'
  , mkDerivedTypeEqCt )
import Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoin )

-- HLint: Please, ignore the unused template haskell pragma at the beginning.
-- For some reason this needs to be added here:
-- https://github.com/ndmitchell/hlint/issues/103
-- {-# ANN module "HLint: ignore Unused LANGUAGE pragma" #-}
-- This causes issues with ghc-mod...

-- -----------------------------------------------------------------------------
-- Base Simplification Rules
-- -----------------------------------------------------------------------------

-- | @simplifyUp (psl, p, psr) rho@ tries to simplify the type variable @rho@
--   in the wanted constraint @p@ using the S-Up rule. The context of the
--   wanted polymonad constraints is given by @psl@ and @psr@.
--   The result is a new equality constraint between @rho@ and the type it
--   should be bound to, to simplify @psl ++ [p] ++ psr@. If the simplification cannot
--   be applied 'Nothing' is returned.
--
--   See figure 7 of the the "Polymonad Programming" paper for more information.
simplifyUp :: ([Ct], Ct, [Ct]) -> TyVar -> PmPluginM (Maybe (TyVar, (Ct, Type)))
simplifyUp (psl, p, psr) rho = do
  idTyCon <- getIdentityTyCon
  return $ do
    (t0, t1, t2) <- constraintPolymonadTyArgs p
    guard $ eqTyVar' rho t2 && (eqTyCon idTyCon t0 || eqTyCon idTyCon t1)
    guard $ not . null $ flowsFrom (psl ++ psr) rho
    guard $ null $ flowsTo (psl ++ psr) rho
    let m = if eqTyCon idTyCon t0 then t1 else t0
    -- It does not help to say some type variables equals itself.
    if eqType (mkTyVarTy rho) m
      then Nothing
      else return (rho, (p, m))

-- | @simplifyDown (psl, p, psr) rho@ tries to simplify the type variable @rho@
--   in the wanted constraint @p@ using the S-Down rule. The context of
--   the wanted polymonad constraints is given by @psl@ and @psr@.
--   The result is a new equality constraint between @rho@ and the type it
--   should be bound to, to simplify @psl ++ [p] ++ psr@. If the simplification cannot
--   be applied 'Nothing' is returned.
--
--   See figure 7 of the the "Polymonad Programming" paper for more information.
simplifyDown :: ([Ct], Ct, [Ct]) -> TyVar -> PmPluginM (Maybe (TyVar, (Ct, Type)))
simplifyDown (psl, p, psr) rho = do
  idTyCon <- getIdentityTyCon
  return $ do
    (t0, t1, t2) <- constraintPolymonadTyArgs p
    guard $  ( eqTyVar' rho t0 && eqTyCon idTyCon t1 )
          || ( eqTyVar' rho t1 && eqTyCon idTyCon t0 )
    guard $ null $ flowsFrom (psl ++ psr) rho
    guard $ not . null $ flowsTo (psl ++ psr) rho
    -- It does not help to say some type variables equals itself.
    if eqType (mkTyVarTy rho) t2
      then Nothing
      else return (rho, (p, t2))

-- | @simplifyJoin rho@ tries to simplify the type variable @rho@ using
--   the S-Join rule.
--   The result is a new equality constraint between @rho@ and the type it
--   should be bound to. If the simplification cannot
--   be applied 'Nothing' is returned.
--
--   See figure 7 of the the "Polymonad Programming" paper for more information.
simplifyJoin :: [Ct] -> TyVar -> PmPluginM (Maybe (TyVar, (Ct, Type)))
simplifyJoin [] rho = return Nothing
simplifyJoin ps rho = do
  let f = flowsTo ps rho
  if (not . null $ f) && all (\(t0,t1) -> isConcreteTyConApp t0 && isConcreteTyConApp t1) f
    then do
      -- TODO: We might have to restrict the set of instances we look at.
      pmInsts <- getPolymonadInstances
      -- TODO: This is the only possibility I can think of to get targets.
      let ms = flowsFrom ps rho
      if length ms == 2 || length ms == 1
        then do
          givenCts <- getGivenConstraints
          mJoinM <- principalJoin (pmInsts, givenCts) f ms
          printMsg "Apply simplifyJoin:"
          printObj (pmInsts, givenCts)
          printObj f
          printObj ms
          printObj mJoinM
          -- It does not help to say some type variables equals itself.
          return $ if maybe True (eqType (mkTyVarTy rho)) mJoinM
            then Nothing
            else fmap (\t -> (rho, (head ps, t))) mJoinM
        else do
          printErr $ "simplifyJoin: There are more then 2 principal join targets: " ++ pprToStr ms
          return Nothing
    else
      return Nothing

-- -----------------------------------------------------------------------------
-- Simplification Application
-- -----------------------------------------------------------------------------

-- | Tries to find a simplification for the given type variable using the
--   given simplification rule on the given set of constraints.
trySimplifyUntil :: [Ct] -> TyVar
                 -> (([Ct], Ct, [Ct]) -> TyVar -> PmPluginM (Maybe (TyVar, (Ct, Type))))
                 -> PmPluginM (Maybe (TyVar, (Ct, Type)))
trySimplifyUntil [] _rho _simp = return empty
trySimplifyUntil (ct:cts) rho simp = trySimplifyUntil' ([], ct, cts)
  where
    trySimplifyUntil' z@(_psl, _p, []) = simp z rho
    trySimplifyUntil' z@(psl, p, p' : psr') = do
      r <- simp z rho
      rs <- trySimplifyUntil' (p : psl, p', psr')
      return $ r <|> rs

-- | Try to simplify as many type variables as possible in the given set of
--   constraints using
--   the 'simplifyUp' and 'simplifyDown' rule (in that order).
simplifyAllUpDown :: [Ct] -> Set TyVar -> PmPluginM [(TyVar, (Ct, Type))]
simplifyAllUpDown ps tvs = do
  let tvList = S.toList tvs
  upSimps <- catMaybes <$> mapM (\rho -> trySimplifyUntil ps rho simplifyUp) tvList
  let tvList' = S.toList $ tvs S.\\ S.fromList (fst <$> upSimps)
  downSimps <- catMaybes <$> mapM (\rho -> trySimplifyUntil ps rho simplifyDown) tvList'
  return $ upSimps ++ downSimps

-- | @simplifyAllJoin ps rhos@ tries to apply the S-Join rule to all
--   of the type variables in @rho@ to simplify the given constraints.
simplifyAllJoin :: [Ct] -> Set TyVar -> PmPluginM [(TyVar, (Ct, Type))]
simplifyAllJoin [] _tvs = return []
simplifyAllJoin ps tvs = catMaybes <$> mapM (simplifyJoin ps) (S.toList tvs)

-- -----------------------------------------------------------------------------
-- Utility Functions
-- -----------------------------------------------------------------------------

-- | Converts the associations of type variables to their simplifications to
--   derived type equality constraints that are located at the position of the
--   constraints that led to the simplification.
simplifiedTvsToConstraints :: [(TyVar, (Ct, Type))] -> [Ct]
simplifiedTvsToConstraints tvs = (\(tv, (ct, t)) -> mkDerivedTypeEqCt ct tv t) <$> tvs

-- -----------------------------------------------------------------------------
-- Local Utility Functions
-- -----------------------------------------------------------------------------

-- | Check if the given type is a type constructor (not a type constructor
--   variable) or a partial application of such.
isConcreteTyConApp :: Type -> Bool
isConcreteTyConApp = isJust . tyConAppTyCon_maybe

-- | @flowsTo p rho@ implementats the function from Figure 7 in the paper.
--   Returns the pairs of types that form a bind operator in @p@ together
--   with @rho@ as result.
flowsTo :: [Ct] -> TyVar -> [(Type, Type)]
flowsTo p rho = do
  (_ct, t0, t1, t2) <- constraintPolymonadTyArgs' p
  guard $ eqTyVar' rho t2
  return (t0, t1)

-- | @flowsFrom p rho@ implements the function from Figure 7 in the paper.
--   Returns the result types of those bind operators in @p@ that take
--   @rho@ as one of their parameters.
flowsFrom :: [Ct] -> TyVar -> [Type]
flowsFrom p rho = do
  (_ct, t0, t1, t2) <- constraintPolymonadTyArgs' p
  guard $ eqTyVar' rho t0 || eqTyVar' rho t1
  return t2
