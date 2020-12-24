{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

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
      Ty(..)
  ) where

import Language.Stitch.Util

import Text.PrettyPrint.ANSI.Leijen
import Data.Hashable
import GHC.Generics

-- | The type of a Stitch expression
data Ty = TInt
        | TBool
        | Ty :-> Ty
  deriving (Show, Eq, Generic, Hashable)
infixr 0 :->

instance Pretty Ty where
  pretty = pretty_ty topPrec

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
