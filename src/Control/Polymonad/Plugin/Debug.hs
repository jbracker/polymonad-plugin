
module Control.Polymonad.Plugin.Debug
  ( containsOneOf
  , containsAllOf
  , pprToStr
  ) where

import Data.List ( isInfixOf )

import Outputable
  ( Outputable(..)
  , showSDocUnsafe )

-- | Convert some generic outputable to a string (Unsafe).
pprToStr :: Outputable o => o -> String
pprToStr = showSDocUnsafe . ppr

containsOneOf :: (Outputable o) => o -> [String] -> Bool
containsOneOf obj = any (`isInfixOf` pprToStr obj)

containsAllOf :: (Outputable o) => o -> [String] -> Bool
containsAllOf obj = all (`isInfixOf` pprToStr obj)
