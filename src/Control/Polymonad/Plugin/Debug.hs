
module Control.Polymonad.Plugin.Debug
  ( containsAnyOf
  , containsAllOf
  , containsNoneOf
  , pprToStr
  ) where

import Data.List ( isInfixOf )

import Outputable
  ( Outputable(..)
  , showSDocUnsafe )

-- | Convert some generic outputable to a string (Unsafe).
pprToStr :: Outputable o => o -> String
pprToStr = showSDocUnsafe . ppr

containsAnyOf :: (Outputable o) => o -> [String] -> Bool
containsAnyOf obj = any (`isInfixOf` pprToStr obj)

containsAllOf :: (Outputable o) => o -> [String] -> Bool
containsAllOf obj = all (`isInfixOf` pprToStr obj)

containsNoneOf :: (Outputable o) => o -> [String] -> Bool
containsNoneOf obj = not . (obj `containsAnyOf`)
