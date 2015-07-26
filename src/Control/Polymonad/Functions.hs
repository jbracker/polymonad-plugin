
-- Needed to specify constraint context that contain 'Identity'.
{-# LANGUAGE FlexibleContexts #-}
-- Needed to use polymonads instead of standard monads.
{-# LANGUAGE RebindableSyntax #-}
-- To defer errors of ambiguity in utility function to their use-sight.
--{-# LANGUAGE AllowAmbiguousTypes #-}
-- Not sure if this is needed yet. Sometimes useful.
{-# LANGUAGE ScopedTypeVariables #-}

-- Plugin ----------------------------------------------------------------------

{-# OPTIONS_GHC -fplugin Control.Polymonad.Plugin #-}

-- -----------------------------------------------------------------------------
-- | Collection of the ported monad-based prelude functions for polymonads.
module Control.Polymonad.Functions
  ( (=<<)
  , mapM, mapM_
  , sequence, sequence_
  , when
  , liftM
  , join
  ) where
{-
import Prelude
  ( String
  , (.), ($)
  , error
  )-}
import qualified Prelude as P
import Prelude
  ( Bool(..)
  , (.), ($)
  , id, const )
import Data.Functor.Identity ( Identity )

import Control.Polymonad

-- | Same as '>>=', but with the arguments interchanged.
(=<<) :: Polymonad m n p => (a -> n b) -> m a -> p b
f =<< ma = ma >>= f

when :: (Polymonad Identity Identity m) => Bool -> m () -> m ()
when p s = case p of
  True -> s
  False -> return ()

mapM :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => (a -> m b) -> [a] -> n [b]
mapM f = P.foldr k (return [])
  where
    k a r = do
      x <- f a
      xs <- r
      return (x : xs)

sequence :: ( Polymonad Identity Identity n, Polymonad n Identity n
            , Polymonad m n n, Polymonad n n n)
         => [m b] -> n [b]
sequence = mapM id

liftM :: (Polymonad m Identity n) => (a -> r) -> m a -> n r
liftM f m = m >>= (return . f)

join :: (Polymonad m n p) => m (n a) -> p a
join k = k >>= id

void :: (Polymonad m Identity n) => m a -> n ()
void = (>>= const (return ()))

mapM_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
         , Polymonad m n n, Polymonad n n n)
      => (a -> m b) -> [a] -> n ()
mapM_ f = void . mapM f

sequence_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
             , Polymonad m n n, Polymonad n n n)
          => [m b] -> n ()
sequence_ = void . sequence
