
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Provides a generalized monad that models Hoare triples. This is well
--   known from the indexed monads presented by Edward Kmett in his package
--   <https://hackage.haskell.org/package/indexed indexed> (@Control.Monad.Indexed@).
--
--   __Note:__
--   There are orphan instances that this modules provides:
--
--     * __@'HoareMonad' m => 'Polymonad' (m i j)  (m j k)  (m i k)@__ - Monadic bind instance.
--     * __@'HoareMonad' m => 'Polymonad' 'Identity' 'Identity' (m i i)@__ - Return bind instance.
--     * __@'HoareMonad' m => 'Polymonad' (m i j) 'Identity' (m i j)@__ - Functor bind instance.
--     * __@'HoareMonad' m => 'Polymonad' 'Identity' (m i j) (m i j)@__ - Apply bind instance.
--
--   These will provide a suitable polymonad for any given 'HoareMonad'
--   instance.
module Control.Polymonad.Hoare
  ( HoareMonad(..)
  ) where

import Control.Polymonad

-- | A generalized monad that models hoare triples.
--   The laws that a Hoare monad needs to abide are very similar
--   to those of standard 'Monad's:
--
--   __TODO__
--
--   Also see the module description.
class HoareMonad m where
  -- | Bind operation (Composition).
  hoareBind :: m i j a -> (a -> m j k b) -> m i k b
  -- | Return operation (Skip)
  hoareRet  :: a -> m i i a

-- | Monad bind instance.
instance HoareMonad m => Polymonad (m i j) (m j k) (m i k) where
  (>>=) = hoareBind

-- | Return bind instance.
instance HoareMonad m => Polymonad Identity Identity (m i i) where
  (>>=) ma f = hoareRet $ runIdentity . f $ runIdentity ma

-- | Functor bind instance.
instance HoareMonad m => Polymonad (m i j) Identity (m i j) where
  (>>=) ma f = hoareBind ma (hoareRet . runIdentity . f)

-- | Apply bind instance.
instance HoareMonad m => Polymonad Identity (m i j) (m i j) where
  (>>=) ma f = f (runIdentity ma)
