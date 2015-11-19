
{-# LANGUAGE RebindableSyntax #-}

{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

import Prelude
import Prelude as P

import Control.Effect as E
import Control.Effect.CounterNat

import GHC.TypeLits ( Nat )

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t e = t
ifThenElse False t e = e

main :: IO ()
main = do
  print $ forget (limitedOp 1 2 3 4)
  where return :: (Monad m) => a -> m a
        return = P.return

specialOp :: Int -> Int -> Counter 1 Int
specialOp n m = tick (n + m)

limitedOp :: Int -> Int -> Int -> Int -> Counter 3 Int
limitedOp a b c d = do
  ab <- specialOp a b
  abc <- specialOp ab c
  specialOp abc d
  where (>>=) :: (E.Effect e, E.Inv e f g) => e (f :: Nat) a -> (a -> e (g :: Nat) b) -> e (E.Plus e f g) b
        (>>=) = (E.>>=)
        fail = E.fail
        return :: (Effect e) => a -> e (Unit e) a
        return = E.return
