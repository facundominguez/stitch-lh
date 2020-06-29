{-# LANGUAGE DataKinds, TypeOperators, KindSignatures, GADTs,
             TypeFamilies, StandaloneDeriving, DeriveGeneric, DeriveAnyClass #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Type
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Defines types
--
----------------------------------------------------------------------------

module Language.Stitch.Type (
      Ty(..), STy(..), extractResType
    , testEquality, (:~:)(..)
  ) where

import Language.Stitch.Util
import Language.Stitch.Data.Singletons

import Text.PrettyPrint.ANSI.Leijen
import Data.Kind
import Data.Type.Equality
import Data.Hashable
import GHC.Generics

-- | The type of a Stitch expression
data Ty = TInt
        | TBool
        | Ty :-> Ty
  deriving (Show, Eq, Generic, Hashable)
infixr 0 :->

-- | The singleton for a Stitch type
data STy :: Ty -> Type where
  SInt   :: STy TInt
  SBool  :: STy TBool
  (::->) :: STy arg -> STy res -> STy (arg :-> res)
infixr 0 ::->

deriving instance Show (STy ty)

instance Hashable (STy ty) where
  hashWithSalt s = hashWithSalt s . fromSing

instance SingKind Ty where
  type Sing = STy

  fromSing SInt       = TInt
  fromSing SBool      = TBool
  fromSing (a ::-> r) = fromSing a :-> fromSing r

  toSing TInt      cont = cont SInt
  toSing TBool     cont = cont SBool
  toSing (a :-> r) cont = toSing a $ \sa ->
                          toSing r $ \sr ->
                          cont (sa ::-> sr)

instance SingI TInt where
  sing = SInt
instance SingI TBool where
  sing = SBool
instance (SingI a, SingI r) => SingI (a :-> r) where
  sing = sing ::-> sing

-- | Informative equality on types
instance TestEquality STy where
  testEquality SInt SInt   = Just Refl
  testEquality SBool SBool = Just Refl
  testEquality (a1 ::-> r1) (a2 ::-> r2) = do
    Refl <- testEquality a1 a2
    Refl <- testEquality r1 r2
    return Refl
  testEquality _ _ = Nothing

-- | Extract the result type of an STy known to be an arrow
extractResType :: STy (arg :-> res) -> STy res
extractResType (_ ::-> res) = res

-----------------------------------------
-- Pretty-printing

instance Pretty Ty where
  pretty = pretty_ty topPrec

instance Pretty (STy ty) where
  pretty sty = pretty_ty topPrec (fromSing sty)

arrowLeftPrec, arrowRightPrec, arrowPrec :: Prec
arrowLeftPrec  = 5
arrowRightPrec = 4.9
arrowPrec      = 5

pretty_ty :: Prec -> Ty -> Doc
pretty_ty prec (arg :-> res) = maybeParens (prec >= arrowPrec) $
                               hsep [ pretty_ty arrowLeftPrec arg
                                    , text "->"
                                    , pretty_ty arrowRightPrec res ]
pretty_ty _    TInt          = text "Int"
pretty_ty _    TBool         = text "Bool"
