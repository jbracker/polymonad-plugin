
module Control.Polymonad.Plugin.Simplification
  ( simplifyUp
  , simplifyDown
  , simplifyJoin
  ) where

import Data.Set ( Set )
import qualified Data.Set as S

import Type ( TyVar )
import TcRnTypes ( Ct )

-- | Try to simplify the type variable in the given bag of constraints
--   and deliver the additional constraints created by the simplification.
--   The new constraints will only be type equality constraints with the
--   given variable on the right hand side.
simplifyUp :: [Ct] -> TyVar -> [Ct]
simplifyUp cts tv = undefined

simplifyDown :: [Ct] -> TyVar -> [Ct]
simplifyDown cts tv = undefined

simplifyJoin :: [Ct] -> TyVar  -> [Ct]
simplifyJoin cts tv = undefined
