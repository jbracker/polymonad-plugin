
-- | Implementation of the simplification rules for polymonad constraints
--   described in section 5 of the "Polymonad Programming" paper (Hicks 2014).
module Control.Polymonad.Plugin.Simplification
  ( simplifyUp
  , simplifyDown
  , simplifyJoin
  ) where

import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( guard )

import Type ( Type, TyVar )
import TcRnTypes ( Ct )

import Control.Polymonad.Plugin.Utils
  ( eqTyVar' )
import Control.Polymonad.Plugin.Constraint
  ( constraintPolymonadTyArgs )

-- | Try to simplify the type variable in the given bag of constraints
--   using the S-Up rule. Deliver the additional constraints created by
--   the simplification.
--   The new constraints will only be type equality constraints with the
--   given variable on the right hand side.
simplifyUp :: [Ct] -> TyVar -> [Ct]
simplifyUp cts tv = undefined

simplifyDown :: [Ct] -> TyVar -> [Ct]
simplifyDown cts tv = undefined

simplifyJoin :: [Ct] -> TyVar  -> [Ct]
simplifyJoin cts tv = undefined

-- | @flowsTo p rho@ implementats the function from Figure 7 in the paper.
--   Returns the pairs of types that form a bind operator in @p@ together
--   with @rho@ as result.
flowsTo :: [Ct] -> TyVar -> [(Type, Type)]
flowsTo p rho = do
  (_ct, t0, t1, t2) <- constraintPolymonadTyArgs p
  guard $ eqTyVar' rho t2
  return (t0, t1)

-- | @flowsFrom p rho@ implements the function from Figure 7 in the paper.
--   Returns the result types of those bind operators in @p@ that take
--   @rho@ as one of their parameters.
flowsFrom :: [Ct] -> TyVar -> [Type]
flowsFrom p rho = do
  (_ct, t0, t1, t2) <- constraintPolymonadTyArgs p
  guard $ eqTyVar' rho t0 || eqTyVar' rho t1
  return t2
