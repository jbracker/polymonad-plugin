
-- General Polymomnads ---------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}

-- -----------------------------------------------------------------------------

module Control.Polymonad
  ( Polymonad(..)
  , fail
  , return
  ) where

import Prelude 
  ( Functor(..), String
  , (.), error
  )
import qualified Prelude as P

import Data.Functor.Identity ( Identity( Identity, runIdentity ) )

fail :: String -> m a
fail = error

-- -----------------------------------------------------------------------------
-- Polymonad Type Class
-- -----------------------------------------------------------------------------

class Polymonad m n p where
  (>>=) :: m a -> (a -> n b) -> p b
  (>>) :: m a -> n b -> p b
  ma >> mb = ma >>= \_ -> mb

-- -----------------------------------------------------------------------------
-- Identity Instance
-- -----------------------------------------------------------------------------

instance Polymonad Identity Identity Identity where
  (Identity a) >>= f = f a

-- -----------------------------------------------------------------------------
-- Functor Instances
-- -----------------------------------------------------------------------------

-- | Standard functor instance
instance Functor f => Polymonad f Identity f where
  m >>= f = fmap (runIdentity . f) m

-- | Apply instance. Technically does not need the functor prerequisite
instance Functor f => Polymonad Identity f f where
  (Identity a) >>= f = f a
  
-- -----------------------------------------------------------------------------
-- Monad Instances
-- -----------------------------------------------------------------------------

-- | Standard monadic bind
instance P.Monad m => Polymonad m m m where
  m >>= f = m P.>>= f

-- | Standard monadic return
instance P.Monad m => Polymonad Identity Identity m where
  (Identity a) >>= f = let Identity b = f a in P.return b

-- -----------------------------------------------------------------------------
-- Units / Returns
-- -----------------------------------------------------------------------------

-- | Polymonad return function as a handy wrapper for the return bind operation.
return :: (Polymonad Identity Identity m) => a -> m a
return x = Identity x >>= Identity

{- For now remove these additional classes 
-- and instances to simplify the plugin.
class Unit m where
  return :: a -> m a

-- We want the chain of instances for backwards compatability.
-- P.Applicative would be enough for this, once it is an actual 
-- dependency of the P.Monad class.
instance P.Monad m => Unit m where
  return = P.return

instance Unit m => Polymonad Identity Identity m where
  (Identity a) >>= f = (return . runIdentity . f) a
-}

{- The other way around would also work.
instance (Polymonad Identity Identity p) => Unit p where
  -- (Polymonad Identity Identity p) => a -> p a
  return x = Identity x >>= Identity
-}

-- -----------------------------------------------------------------------------
-- Applicative
-- -----------------------------------------------------------------------------
{-
getFun :: (Polymonad f Identity f) => f (a -> b) -> (a -> f b)
getFun ff a = ff >>= (\f -> Identity (f a))

ap :: (Polymonad f Identity f, Polymonad f f f) => f (a -> b) -> f a -> f b
ap ff fa = fa >>= \a -> getFun ff a
-}


