-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Unchecked
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Defines the AST for un-type-checked expressions
--
----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module Language.Stitch.Unchecked ( UExp(..) ) where

import Language.Stitch.Pretty
import Language.Stitch.Type
import Language.Stitch.Op
import Language.Stitch.Util
import Language.Stitch.Data.Nat as Nat

import Text.PrettyPrint.ANSI.Leijen

{-@
data UExp
  = UVar Nat
  | UGlobal String
  | ULam Ty UExp
  | UApp UExp UExp
  | ULet UExp UExp
  | UArith UExp ArithOp UExp
  | UCond UExp UExp UExp
  | UFix UExp
  | UIntE Int
  | UBoolE Bool
@-}

-- | Unchecked expression
data UExp
  = UVar Nat
  | UGlobal String
  | ULam Ty UExp
  | UApp UExp UExp
  | ULet UExp UExp
  | UArith UExp ArithOp UExp
  | UCond UExp UExp UExp
  | UFix UExp
  | UIntE Int
  | UBoolE Bool
  deriving Show

{-@
instance measure numFreeVars :: UExp -> Nat
  numFreeVars (UVar v) = v + 1
  numFreeVars (UGlobal _) = 0
  numFreeVars (ULam _ body) = Nat.minus (numFreeVars body) 1
  numFreeVars (UApp e1 e2) = Nat.max (numFreeVars e1) (numFreeVars e2)
  numFreeVars (ULet e1 e2) =
    Nat.max (numFreeVars e1) (Nat.minus (numFreeVars e2) 1)
  numFreeVars (UArith e1 _ e2) = Nat.max (numFreeVars e1) (numFreeVars e2)
  numFreeVars (UCond e1 e2 e3) =
    Nat.max (Nat.max (numFreeVars e1) (numFreeVars e2)) (numFreeVars e3)
  numFreeVars (UFix body) = numFreeVars body
  numFreeVars (UIntE _) = 0
  numFreeVars (UBoolE _) = 0
@-}

-- An expression paired with the bound for the valid
-- variable indices
{-@ data ScopedExp = ScopedExp (n :: NumVarsInScope) (VarsSmallerThan UExp n) @-}
data ScopedExp = ScopedExp NumVarsInScope UExp

instance Pretty ScopedExp where
  pretty (ScopedExp n exp) = prettyExp n topPrec exp

instance PrettyExp UExp where
  -- XXX: The preconditions of prettyExp as defined in the class
  -- PrettyExp are not visible in this module for some reason.
  -- Therefore, we tell LH to assume them anyway by calling an
  -- ignored function.
  prettyExp n p e = _prettyExpUExp n p e

{-@ ignore _prettyExpUExp @-}
_prettyExpUExp :: NumVarsInScope -> Prec -> UExp -> Doc
_prettyExpUExp = pretty_exp

{-@ pretty_exp :: n : NumVarsInScope -> Prec -> (VarsSmallerThan UExp n) -> Doc @-}
pretty_exp :: NumVarsInScope -> Prec -> UExp -> Doc
pretty_exp n _    (UVar v)                     = prettyVar (ScopedVar n v)
pretty_exp _ _    (UGlobal name)               = text name
pretty_exp n prec (ULam ty body)               = prettyLam n prec ty body
pretty_exp n prec (UApp e1 e2)                 = prettyApp n prec e1 e2
pretty_exp n prec (ULet e1 e2)                 = prettyLet n prec e1 e2
pretty_exp n prec (UArith e1 op e2)            = prettyArith n prec e1 op e2
pretty_exp n prec (UCond e1 e2 e3)             = prettyIf n prec e1 e2 e3
pretty_exp n prec (UFix body)                  = prettyFix n prec body
pretty_exp _ _    (UIntE i)                    = int i
pretty_exp _ _    (UBoolE True)                = text "true"
pretty_exp _ _    (UBoolE False)               = text "false"
