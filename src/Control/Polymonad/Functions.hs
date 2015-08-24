
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
  , (>=>), (<=<)
  , mapM, mapM_
  , forM, forM_
  , sequence, sequence_
  , when
  , liftM
  , join
  , forever
  , filterM
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
  , id, const, flip
  , otherwise, not )
import Data.Foldable ( Foldable(..) )
import Data.Functor.Identity ( Identity )

import Control.Polymonad

infixr 1 =<<
infixr 1 >=>
infixr 1 <=<

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _f = t
ifThenElse False _t f = f

-- | Same as '>>=', but with the arguments interchanged.
(=<<) :: Polymonad m n p => (a -> n b) -> m a -> p b
f =<< ma = ma >>= f

(>=>) :: Polymonad m n p => (a -> m b) -> (b -> n c) -> a -> p c
(>=>) f g x = f x >>= g

(<=<) :: Polymonad m n p => (b -> n c) -> (a -> m b) -> a -> p c
(<=<) g f x = f x >>= g

when :: (Polymonad n Identity m, Polymonad Identity Identity m) => Bool -> n () -> m ()
when True  s = void s
when False _ = return ()

unless :: (Polymonad n Identity m, Polymonad Identity Identity m) => Bool -> n () -> m ()
unless b = when (not b)

mapM :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => (a -> m b) -> [a] -> n [b]
mapM f = P.foldr k (return [])
  where
    k a r = do
      x <- f a
      xs <- r
      return (x : xs)

forM :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => [a] -> (a -> m b) -> n [b]
forM = flip mapM

sequence :: ( Polymonad Identity Identity n, Polymonad n Identity n
            , Polymonad m n n, Polymonad n n n)
         => [m b] -> n [b]
sequence = mapM id

liftM :: (Polymonad m Identity n) => (a -> r) -> m a -> n r
liftM f m = m >>= (return . f)

join :: (Polymonad m n p) => m (n a) -> p a
join k = k >>= id

void :: (Polymonad m Identity n) => m a -> n ()
void = (>> return ())

mapM_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
         , Polymonad m n n, Polymonad n n n)
      => (a -> m b) -> [a] -> n ()
mapM_ f = void . mapM f

forM_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => [a] -> (a -> m b) -> n ()
forM_ xs = void . forM xs

sequence_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
             , Polymonad m n n, Polymonad n n n)
          => [m b] -> n ()
sequence_ = void . sequence

forever :: Polymonad m m m => m a -> m b
forever ma = ma >> forever ma


filterM :: forall n m a b. ( Polymonad n m m, Polymonad m m m
           , Polymonad m Identity m, Polymonad Identity Identity m)
        => (a -> n Bool) -> [a] -> m [a]
filterM f [] = return []
filterM f (x : xs) = do
  keep <- f x
  if keep
    then filterM f xs >>= (return . (x :))
    else filterM f xs

-- TODO: Generalize all the other functions in Control.Monad.
