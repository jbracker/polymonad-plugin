

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin Plugin #-}

class A a where
  a :: a

class B b where
  b :: b x

class C c where
  c :: c

instance (A a) => C a where
  c = a

instance (B b) => C (b x) where
  c = b

instance A (Maybe Int) where
  a = Just 0

f :: Maybe Int
f = c

g :: Maybe Int
g = c

h :: Maybe Int
h = c

main :: IO ()
main = putStrLn $ show f