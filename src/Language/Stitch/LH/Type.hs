{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Type
-- Copyright   :  (C) 2015 Richard Eisenberg
--                (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- Defines types
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Type where

import Language.Stitch.LH.Util

import Text.PrettyPrint.ANSI.Leijen
import Data.Hashable
import GHC.Generics
import Language.Haskell.Liquid.ProofCombinators (Proof, (==.), (***), QED(..))

-- | The type of a Stitch expression
data Ty = TInt
        | TBool
        | TFun Ty Ty
  deriving (Show, Eq, Generic, Hashable)

{-@
type FunTy = {t : Ty | isFunTy t }
data Ty = TInt
        | TBool
        | TFun Ty Ty
@-}

{-@ measure funResTy @-}
{-@ funResTy :: FunTy -> Ty @-}
funResTy :: Ty -> Ty
funResTy (TFun _ b) = b

{-@ measure funArgTy @-}
{-@ funArgTy :: FunTy -> Ty @-}
funArgTy :: Ty -> Ty
funArgTy (TFun a _) = a

{-@ measure isFunTy @-}
isFunTy :: Ty -> Bool
isFunTy (TFun _ _) = True
isFunTy _ = False

-- XXX: Can't find a way to replace ==. with === in this proof.
{-@
funTypeProjections_prop
  :: ty:FunTy -> { ty = TFun (funArgTy ty) (funResTy ty) }
@-}
funTypeProjections_prop :: Ty -> Proof
funTypeProjections_prop ty@(TFun _ _) =
  ty
  ==.
  TFun (funArgTy ty) (funResTy ty)
  ***
  QED

instance Pretty Ty where
  pretty = pretty_ty topPrec

arrowLeftPrec, arrowRightPrec, arrowPrec :: Prec
arrowLeftPrec  = 5
arrowRightPrec = 4.9
arrowPrec      = 5

pretty_ty :: Prec -> Ty -> Doc
pretty_ty p (TFun arg res) = maybeParens (p >= arrowPrec) $
                               hsep [ pretty_ty arrowLeftPrec arg
                                    , text "->"
                                    , pretty_ty arrowRightPrec res ]
pretty_ty _    TInt        = text "Int"
pretty_ty _    TBool       = text "Bool"
