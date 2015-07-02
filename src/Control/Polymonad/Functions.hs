
-- To defer errors of ambiguity in utility function to their use-sight.
{-# LANGUAGE AllowAmbiguousTypes #-}
-- Not sure if this is needed yet. Sometimes useful.
{-# LANGUAGE ScopedTypeVariables #-}

-- Plugin ----------------------------------------------------------------------

{-# OPTIONS_GHC -fplugin Control.Polymonad.Plugin #-}

-- -----------------------------------------------------------------------------
-- | Collection of the ported monad-based prelude functions for polymonads.
module Control.Polymonad.Functions 
  ( (=<<)
  , mapM
  ) where

import Prelude 
  ( String
  , (.), ($)
  , error
  )
import qualified Prelude as P

import Control.Polymonad

-- | Same as '>>=', but with the arguments interchanged.
(=<<) :: Polymonad m n p => (a -> n b) -> m a -> p b
f =<< ma = ma >>= f

mapM :: forall m n a b. (Polymonad m n n) => (a -> m b) -> [a] -> n [b]
mapM f xs = P.foldr k (return []) xs
  where
    k :: a -> n [b] -> n [b]
    k a r = f a >>= \x -> r >>= \xs -> (return (x : xs) :: n [b])