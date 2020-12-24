{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Pretty
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Pretty-printing expressions. This allows reduction of code duplication
-- between unchecked and checked expressions.
--
----------------------------------------------------------------------------

module Language.Stitch.Pretty where
-- XXX: Using an export list causes LH to fail with an obscure error
--
-- (
--  PrettyExp(..), AnExpression(..)
--  prettyVar, prettyLam, prettyApp, prettyLet, prettyArith, prettyIf, prettyFix
--  ) where

import Language.Stitch.Op
import Language.Stitch.Util
import Language.Stitch.Data.Nat

import Text.PrettyPrint.ANSI.Leijen

lamPrec, appPrec, appLeftPrec, appRightPrec, ifPrec :: Prec
lamPrec = 1
appPrec = 9
appLeftPrec = 8.9
appRightPrec = 9
ifPrec = 1

opPrec, opLeftPrec, opRightPrec :: ArithOp -> Prec
opPrec      (precInfo -> (x, _, _)) = x
opLeftPrec  (precInfo -> (_, x, _)) = x
opRightPrec (precInfo -> (_, _, x)) = x

-- | Returns (overall, left, right) precedences for an 'ArithOp'
precInfo :: ArithOp -> (Prec, Prec, Prec)
precInfo Plus     = (5, 4.9, 5)
precInfo Minus    = (5, 4.9, 5)
precInfo Times    = (6, 5.9, 6)
precInfo Divide   = (6, 5.9, 6)
precInfo Mod      = (6, 5.9, 6)
precInfo Less     = (4, 4, 4)
precInfo LessE    = (4, 4, 4)
precInfo Greater  = (4, 4, 4)
precInfo GreaterE = (4, 4, 4)
precInfo Equals   = (4, 4, 4)

-- | A function that changes a 'Doc's color
type ApplyColor = Doc -> Doc

-- | The colors used for all rendered expressions
{-@ coloring :: { v : [ApplyColor] | len v > 0 } @-}
coloring :: [ApplyColor]
coloring = [red, green, yellow, blue, magenta, cyan]

{-@ ignore applyColor @-}
-- LH would need a proof that
-- @len (cycle coloring) > maxIndex v - scopedIndex v@
-- so @!!@ is safe to use.
applyColor :: ScopedVar -> ApplyColor
applyColor v = cycle coloring !! (maxIndex v - scopedIndex v)

{-@
class measure numFreeVars :: forall exp. exp -> Nat
type VarsSmallerThan exp N = { e : exp | numFreeVars e <= N }
@-}

-- | A class for expressions that can be pretty-printed
{-@
class PrettyExp exp where
  prettyExp :: n : NumVarsInScope -> Prec -> VarsSmallerThan exp n -> Doc
@-}
class PrettyExp exp where
  prettyExp :: NumVarsInScope -> Prec -> exp -> Doc

-- The number of variables in scope.
{-@ type NumVarsInScope = Nat @-}
type NumVarsInScope = Nat

{-@
data ScopedVar = ScopedVar
  { maxIndex    :: NumVarsInScope
  , scopedIndex :: { i : Nat | i < maxIndex }
  }
@-}
data ScopedVar = ScopedVar
  { maxIndex    :: NumVarsInScope
  , scopedIndex :: Nat
  }

-- | Print a variable
prettyVar :: ScopedVar -> Doc
prettyVar v = applyColor v (char '#' <> int (scopedIndex v))

-- | Print a lambda expression
{-@
prettyLam
  :: (Pretty ty, PrettyExp exp)
  => n : NumVarsInScope
  -> Prec
  -> ty
  -> VarsSmallerThan exp {(n + 1)}
  -> Doc
@-}
-- XXX: reversing the order of the constraints here,
-- causes a failure in Unchecked.hs.
prettyLam :: (PrettyExp exp, Pretty ty)
          => NumVarsInScope -> Prec -> ty -> exp -> Doc
prettyLam n prec ty body
  = maybeParens (prec >= lamPrec) $
    fillSep [ char 'λ' <> applyColor (ScopedVar (n + 1) 0) (char '#') <>
              text ":" <> pretty ty <> char '.'
            , prettyExp (n + 1) topPrec body ]

-- | Print an application
{-@
prettyApp
  :: (PrettyExp exp1, PrettyExp exp2)
  => n : NumVarsInScope
  -> Prec
  -> VarsSmallerThan exp1 n
  -> VarsSmallerThan exp2 n
  -> Doc
@-}
prettyApp :: (PrettyExp exp1, PrettyExp exp2)
          => NumVarsInScope -> Prec -> exp1 -> exp2 -> Doc
prettyApp n prec e1 e2
  = maybeParens (prec >= appPrec) $
    fillSep [ prettyExp n appLeftPrec  e1
            , prettyExp n appRightPrec e2 ]

-- | Print a let-expression
{-@
prettyLet
  :: (PrettyExp exp1, PrettyExp exp2)
  => n : NumVarsInScope
  -> Prec
  -> VarsSmallerThan exp1 n
  -> VarsSmallerThan exp2 {(n + 1)}
  -> Doc
@-}
prettyLet :: (PrettyExp exp1, PrettyExp exp2)
          => NumVarsInScope -> Prec -> exp1 -> exp2 -> Doc
prettyLet n prec e1 e2
  = maybeParens (prec >= lamPrec) $
    fillSep [ text "let" <+> applyColor (ScopedVar (n + 1) 0) (char '#') <+>
              char '=' <+> prettyExp n topPrec e1 <+> text "in"
            , prettyExp (n + 1) topPrec e2 ]

-- | Print an arithemtic expression
{-@
prettyArith
  :: (PrettyExp exp1, PrettyExp exp2)
  => n : NumVarsInScope
  -> Prec
  -> VarsSmallerThan exp1 n
  -> ArithOp
  -> VarsSmallerThan exp2 n
  -> Doc
@-}
prettyArith :: (PrettyExp exp1, PrettyExp exp2)
            => NumVarsInScope -> Prec -> exp1 -> ArithOp -> exp2 -> Doc
prettyArith n prec e1 op e2
  = maybeParens (prec >= opPrec op) $
    fillSep [ prettyExp n (opLeftPrec op) e1 <+> pretty op
            , prettyExp n (opRightPrec op) e2 ]

-- | Print a conditional
{-@
prettyIf
  :: (PrettyExp exp1, PrettyExp exp2, PrettyExp exp3)
  => n : NumVarsInScope
  -> Prec
  -> VarsSmallerThan exp1 n
  -> VarsSmallerThan exp2 n
  -> VarsSmallerThan exp3 n
  -> Doc
@-}
prettyIf :: ( PrettyExp exp1, PrettyExp exp2, PrettyExp exp3 )
         => NumVarsInScope -> Prec -> exp1 -> exp2 -> exp3 -> Doc
prettyIf n prec e1 e2 e3
  = maybeParens (prec >= ifPrec) $
    fillSep [ text "if" <+> prettyExp n topPrec e1
            , text "then" <+> prettyExp n topPrec e2
            , text "else" <+> prettyExp n topPrec e3 ]

-- | Print a @fix@
{-@
prettyFix
  :: PrettyExp exp => n : NumVarsInScope -> Prec -> VarsSmallerThan exp n -> Doc
@-}
prettyFix :: PrettyExp exp => NumVarsInScope -> Prec -> exp -> Doc
prettyFix n prec e
  = maybeParens (prec >= appPrec) $
    text "fix" <+> prettyExp n topPrec e
