
module Control.Polymonad.Plugin.Evaluate
  ( evaluateTypeEqualities
  ) where

import Type ( Type )
import TcRnTypes ( Ct(..) )

evaluateTypeEqualities :: [Ct] -> Type -> Type
evaluateTypeEqualities = undefined
