{-# LANGUAGE TypeInType, FlexibleInstances, TypeFamilies #-}

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

module Language.Stitch.Unchecked ( UExp(..) ) where

import Language.Stitch.Pretty
import Language.Stitch.Type
import Language.Stitch.Op
import Language.Stitch.Util
import Language.Stitch.Data.Fin
import Language.Stitch.Data.Nat
import Language.Stitch.Data.Singletons

import Text.PrettyPrint.ANSI.Leijen

-- | Unchecked expression, indexed by the number of variables in scope
data UExp (n :: Nat)
  = UVar (Fin n)   -- ^ de Bruijn index for a variable
  | UGlobal String
  | ULam Ty (UExp (Succ n))
  | UApp (UExp n) (UExp n)
  | ULet (UExp n) (UExp (Succ n))
  | UArith (UExp n) UArithOp (UExp n)
  | UCond (UExp n) (UExp n) (UExp n)
  | UFix (UExp n)
  | UIntE Int
  | UBoolE Bool
  deriving Show

instance SingI n => Pretty (UExp n) where
  pretty = prettyExp topPrec

instance SingI n => PrettyExp (UExp n) where
  type NumBoundVars (UExp n) = n
  prettyExp = pretty_exp

pretty_exp :: SingI n => Prec -> UExp n -> Doc
pretty_exp _    (UVar n)                       = prettyVar n
pretty_exp _    (UGlobal n)                    = text n
pretty_exp prec (ULam ty body)                 = prettyLam prec ty body
pretty_exp prec (UApp e1 e2)                   = prettyApp prec e1 e2
pretty_exp prec (ULet e1 e2)                   = prettyLet prec e1 e2
pretty_exp prec (UArith e1 (UArithOp _ op) e2) = prettyArith prec e1 op e2
pretty_exp prec (UCond e1 e2 e3)               = prettyIf prec e1 e2 e3
pretty_exp prec (UFix body)                    = prettyFix prec body
pretty_exp _    (UIntE n)                      = int n
pretty_exp _    (UBoolE True)                  = text "true"
pretty_exp _    (UBoolE False)                 = text "false"
