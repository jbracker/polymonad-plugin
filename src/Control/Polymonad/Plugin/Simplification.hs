
module Control.Polymonad.Plugin.Simplification
  ( simplifyUp
  , simplifyDown
  , simplifyJoin
  ) where

import Data.Set ( Set )
import qualified Data.Set as S

import Type ( TyVar )
import TcRnTypes ( Ct )

simplifyUp :: [Ct] -> TyVar -> [Ct]
simplifyUp cts tv = undefined

simplifyDown :: [Ct] -> TyVar -> [Ct]
simplifyDown cts tv = undefined

simplifyJoin :: [Ct] -> TyVar  -> [Ct]
simplifyJoin cts tv = undefined
