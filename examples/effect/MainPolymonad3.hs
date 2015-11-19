
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE UndecidableInstances #-}

-- Ignore our orphan instance in this file.
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- Use the polymonad plugin.
{-# OPTIONS_GHC -fplugin Control.Polymonad.Plugin #-}

import Control.Polymonad.Prelude

import qualified Control.Effect as E
import Control.Effect ( Effect, Plus, Unit )
import Control.Effect.CounterNat

import GHC.TypeLits ( Nat )

instance (Effect m, h ~ Plus m f g, E.Inv m f g) => Polymonad (m (f :: Nat)) (m (g :: Nat)) (m (h :: Nat)) where
  (>>=) = (E.>>=)

instance (Effect m, h ~ Unit m) => Polymonad Identity Identity (m (h :: Nat)) where
  a >>= f = (E.return . runIdentity . f . runIdentity) a

instance ( Effect m, E.Inv m f (Unit m), f ~ Plus m f (Unit m))
        => Polymonad (m (f :: Nat)) Identity (m (f :: Nat)) where
  ma >>= f = ma E.>>= (E.return . runIdentity . f)

instance (Effect m) => Polymonad Identity (m (g :: Nat)) (m (g :: Nat)) where
  a >>= f = f (runIdentity a)

main :: IO ()
main = do
  print $ forget (limitedOp 1 2 3 4)

specialOp :: Int -> Int -> Counter 1 Int
specialOp n m = tick (n + m)

limitedOp :: Int -> Int -> Int -> Int -> Counter 3 Int
limitedOp a b c d = do
  ab <- specialOp a b
  abc <- specialOp ab c
  specialOp abc d
