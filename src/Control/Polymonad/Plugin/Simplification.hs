
-- | Implementation of the simplification rules for polymonad constraints
--   described in section 5 of the "Polymonad Programming" paper (Hicks 2014).
module Control.Polymonad.Plugin.Simplification
  ( simplifyUp
  , simplifyDown
  , simplifyJoin
  ) where

import Data.Maybe ( isJust )

import Control.Monad ( guard )

import Type
  ( Type, TyVar
  , tyConAppTyCon_maybe )
import TyCon ( TyCon )
import TcRnTypes ( Ct )

import Control.Polymonad.Plugin.Utils
  ( eqTyVar', eqTyCon )
import Control.Polymonad.Plugin.Constraint
  ( constraintPolymonadTyArgs, constraintPolymonadTyArgs'
  , mkDerivedTypeEqCt )

-- | @simplifyUp idTc (psl, p, psr) rho@ tries to simplify the type variable @rho@
--   in the constraint @p@ using the S-Up rule. The context of polymonad
--   constraints is given by @psl@ and @psr@. The 'Identity' type constructor has to be
--   passed in for @idTc@.
--   The result is a new equality constraint between @rho@ and the type it
--   should be bound to, to simplify @psl ++ [p] ++ psr@. If the simplification cannot
--   be applied 'Nothing' is returned.
--
--   See figure 7 of the the "Polymonad Programming" paper for more information.
simplifyUp :: TyCon -> ([Ct], Ct, [Ct]) -> TyVar -> Maybe Ct
simplifyUp idTyCon (psl, p, psr) rho = do
  (t0, t1, t2) <- constraintPolymonadTyArgs p
  guard $ eqTyVar' rho t2 && (eqTyCon idTyCon t0 || eqTyCon idTyCon t1)
  guard $ not . null $ flowsFrom (psl ++ psr) rho
  guard $ null $ flowsTo (psl ++ psr) rho
  let m = if eqTyCon idTyCon t0 then t1 else t0
  return $ mkDerivedTypeEqCt p rho m

-- | @simplifyDown idTc (psl, p, psr) rho@ tries to simplify the type variable @rho@
--   in the constraint @p@ using the S-Down rule. The context of polymonad
--   constraints is given by @psl@ and @psr@. The 'Identity' type constructor has to be
--   passed in for @idTc@.
--   The result is a new equality constraint between @rho@ and the type it
--   should be bound to, to simplify @psl ++ [p] ++ psr@. If the simplification cannot
--   be applied 'Nothing' is returned.
--
--   See figure 7 of the the "Polymonad Programming" paper for more information.
simplifyDown :: TyCon -> ([Ct], Ct, [Ct]) -> TyVar -> Maybe Ct
simplifyDown idTc (psl, p, psr) rho = do
  (t0, t1, t2) <- constraintPolymonadTyArgs p
  guard $  ( eqTyVar' rho t0 && eqTyCon idTc t1 )
        || ( eqTyVar' rho t1 && eqTyCon idTc t0 )
  guard $ null $ flowsFrom (psl ++ psr) rho
  guard $ not . null $ flowsTo (psl ++ psr) rho
  return $ mkDerivedTypeEqCt p rho t2

-- | @simplifyJoin ps rho@ tries to simplify the type variable @rho@
--   in the constraints @ps@ using the S-Join rule.
--   The result is a new equality constraint between @rho@ and the type it
--   should be bound to, to simplify @ps@. If the simplification cannot
--   be applied 'Nothing' is returned.
--
--   See figure 7 of the the "Polymonad Programming" paper for more information.
simplifyJoin :: [Ct] -> TyVar -> Maybe Ct
simplifyJoin [] _rho = Nothing
simplifyJoin ps rho = do
  let f = concatMap (\(t,s) -> [t,s]) $ flowsTo ps rho
  guard $ all isConcreteTyConApp f
  return $ mkDerivedTypeEqCt (head ps) rho (principalJoin f)

isConcreteTyConApp :: Type -> Bool
isConcreteTyConApp = isJust . tyConAppTyCon_maybe

-- | Calculate the principal join of a set of type constructors.
--   For this to work properly all of the given types need to be
--   type constructors or partially applied type constructors.
--   The principal join is defined in definition 4 of the
--   "Polymonad Programming" paper.
principalJoin :: [Type] -> Type
principalJoin ts = undefined -- TODO: IMPLEMENT - How?

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
