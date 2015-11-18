
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

import Prelude
import Prelude as P

import Control.Effect as E
import Control.Effect.Reader

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t e = t
ifThenElse False t e = e

main :: IO ()
main = P.return ()
