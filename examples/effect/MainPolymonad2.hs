
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

import Control.Effect ( Effect, Plus, Unit )
import qualified Control.Effect as E
import Control.Effect.State
--import qualified Control.Effect.State as ES

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
  putStrLn $ show $ runState
    ( write "abc" )
    ( Ext (Var :-> 0 :! Eff) (Ext (Var :-> [] :! Eff) Empty) )

-- '["count" :-> Int :! RW, "out" :-> [a] :! RW]

data Tree = Leaf Int
          | Branch Tree Tree

instance Show Tree where
  show (Leaf i) = show i
  show (Branch l r) = "(" ++ show l ++ " | " ++ show r ++ ")"

leavesV :: Var "leaves"
leavesV = Var :: (Var "leaves")

sumV :: Var "sum"
sumV = Var :: (Var "sum")

flattenV :: Var "flatten"
flattenV = Var :: (Var "flatten")

update :: Var n -> (a -> a) -> State '[n :-> a :! 'RW] a
update v f = do
  x <- get v
  let fx = f x
  put v fx
  return fx

type ProcessEffects =
  '[ "flatten" :-> Bool :! 'R
   , "leaves"  :-> Int  :! 'RW
   , "sum"     :-> Int  :! 'RW
   ]

-- Nubable is not exported by Control.Effect.State
--process :: Tree -> State ProcessEffects (Either Tree [Int])
{-
process (Leaf i) = do
  --_ <- update leavesV (+ 1)
  _ <- update sumV (+ i)
  flatten <- get flattenV
  if flatten
    then return $ Right [i]
    else return $ Left $ Leaf i
process (Branch tl tr) = do
  eitherL <- process tl
  eitherR <- process tr
  case (eitherL, eitherR) of
    (Left  l, Left  r) -> return $ Left  $ Branch l r
    (Right l, Right r) -> return $ Right $ l ++ r
-}

varC = Var :: Var "count"
varS = Var :: Var "out"

incC :: State '["count" :-> Int :! RW] ()
incC = do { x <- get varC; put varC (x + 1) }

writeS :: [a] -> State '["out" :-> [a] :! RW] ()
writeS y = do { x <- get varS; put varS (x ++ y) }

write :: [a] -> State '["count" :-> Int :! RW, "out" :-> [a] :! RW] ()
write x = do { writeS x; incC }
