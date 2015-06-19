
module Control.Polymonad.Plugin.Types
  ( PolymonadInst(..)
  , SigPart(..)
  , mkPolymonadInst
  , typeToSigPart
  ) where

import Type
  ( Type
  , eqType
  , isTyVarTy, isAlgType )
import InstEnv 
  ( ClsInst(..)
  , instanceSig )
import Outputable 
  ( Outputable( ppr )
  , text, parens, (<>) )

-- -----------------------------------------------------------------------------
-- Solver Types
-- -----------------------------------------------------------------------------

data PolymonadInst = PolymonadInst
  { pmiSignature :: [SigPart]
  , pmiTcInstance :: ClsInst
  }

instance Outputable PolymonadInst where
  ppr pmi = ppr $ pmiSignature pmi

data SigPart
  = SPVar Type
  | SPGround Type

instance Eq SigPart where
  (SPVar    t1) == (SPVar    t2) = eqType t1 t2
  (SPGround t1) == (SPGround t2) = eqType t1 t2
  _ == _ = False

instance Outputable SigPart where
  ppr (SPVar t)    = text "V " <> ppr t
  ppr (SPGround t) = text "G " <> parens (ppr t)

mkPolymonadInst :: ClsInst -> Maybe PolymonadInst
mkPolymonadInst inst = 
  let (_, _, _, sig) = instanceSig inst
  in case mapM typeToSigPart sig of
    Just signat -> Just $ PolymonadInst
      { pmiSignature = signat
      , pmiTcInstance = inst
      }
    Nothing -> Nothing
  

typeToSigPart :: Type -> Maybe SigPart
typeToSigPart t = 
  -- For now a type is ground if it is algebraic.
  -- We might have to refine this at some point.
  case (isTyVarTy t, isAlgType t) of
    (True, _) -> Just $ SPVar t
    (_, True) -> Just $ SPGround t
    _ -> Nothing
