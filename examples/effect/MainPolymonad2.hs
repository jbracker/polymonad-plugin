
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
import Control.Effect.Reader

instance (Effect m, h ~ Plus m f g, E.Inv m f g) => Polymonad (m (f :: [*])) (m (g :: [*])) (m (h :: [*])) where
  (>>=) = (E.>>=)

instance (Effect m) => Polymonad Identity (m (g :: [*])) (m (g :: [*])) where
  a >>= f = f (runIdentity a)

instance ( Effect m, E.Inv m f (Unit m), f ~ Plus m f (Unit m))
        => Polymonad (m (f :: [*])) Identity (m (f :: [*])) where
  ma >>= f = ma E.>>= (E.return . runIdentity . f)

instance (Effect m, h ~ Unit m) => Polymonad Identity Identity (m (h :: [*])) where
  a >>= f = (E.return . runIdentity . f . runIdentity) a

main :: IO ()
main = do
  let l = runReader (flatFilter tree) (Ext (vThres :-> 3) Empty)
  print l
  print (sum l)

vThres :: Var "thres"
vThres = Var

data Tree = Leaf Int
          | Branch Tree Tree
          deriving Show

tree :: Tree
tree = Branch (Branch (Leaf 1) (Leaf 4)) (Leaf 5)

flatFilter :: Tree -> Reader '["thres" :-> Int] [Int]
flatFilter ( Leaf i ) = do
  thres <- ask vThres
  return (if i < thres then [] else [i])
flatFilter ( Branch l r ) = do
  ls <- flatFilter l
  rs <- flatFilter r
  return (ls ++ rs)
