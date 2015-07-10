
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoin
  ) where

import Type ( Type )

-- | Calculate the principal join of a set of type constructors.
--   For this to work properly all of the given types need to be
--   type constructors or partially applied type constructors.
--   The principal join is defined in definition 4 of the
--   "Polymonad Programming" paper.
--   TODO: UNFINISHED
principalJoin :: [Type] -> Type
principalJoin ts = undefined -- TODO: IMPLEMENT - How?
