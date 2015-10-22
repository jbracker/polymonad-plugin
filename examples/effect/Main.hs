
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Main ( main, process ) where

import Prelude
import qualified Prelude as P
import qualified Control.Effect as E
import Control.Effect.State

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t e = t
ifThenElse False t e = e

main :: IO ()
main = do
  return ()
  where
    return = P.return

data Tree = Leaf Int
          | Branch Tree Tree

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
  where (>>=) = (E.>>=)
        (>>) = (E.>>)
        return = E.return
        fail = E.fail

type ProcessEffects =
  '[ "flatten" :-> Bool :! 'R
   , "leaves"  :-> Int  :! 'RW
   , "sum"     :-> Int  :! 'RW
   ]
{-
-- Nubable is not exported by Control.Effect.State
process :: (Nubable ProcessEffects)
        => Tree
        -> State ProcessEffects (Either Tree [Int])
-}
process (Leaf i) = do
  _ <- update leavesV (+ 1)
  _ <- update sumV (+ i)
  flatten <- get flattenV
  if flatten
    then return $ Right [i]
    else return $ Left $ Leaf i
  where (>>=) :: (E.Inv State f g) => State f a -> (a -> State g b) -> State (E.Plus State f g) b
        (>>=) = (E.>>=)
        (>>) :: (E.Inv State f g) => State f a -> State g b -> State (E.Plus State f g) b
        (>>) = (E.>>)
        return = E.return
        fail = E.fail
process (Branch tl tr) = do
  eitherL <- process tl
  eitherR <- process tr
  case (eitherL, eitherR) of
    (Left  l, Left  r) -> return $ Left  $ Branch l r
    (Right l, Right r) -> return $ Right $ l ++ r
  where (>>=) :: (E.Inv State f g) => State f a -> (a -> State g b) -> State (E.Plus State f g) b
        (>>=) = (E.>>=)
        (>>) :: (E.Inv State f g) => State f a -> State g b -> State (E.Plus State f g) b
        (>>) = (E.>>)
        return = E.return
        fail = E.fail
