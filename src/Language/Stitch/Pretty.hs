{-# LANGUAGE ViewPatterns, GADTs, TypeInType, TypeFamilies, TypeApplications,
             FlexibleInstances, UndecidableInstances, ScopedTypeVariables,
             FlexibleContexts #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Pretty
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
--
-- Pretty-printing expressions. This allows reduction of code duplication
-- between unchecked and checked expressions.
--
----------------------------------------------------------------------------

module Language.Stitch.Pretty (
  PrettyExp(..),
  Coloring,
  prettyVar, prettyLam, prettyApp, prettyLet, prettyArith, prettyIf, prettyFix
  ) where

import Language.Stitch.Op
import Language.Stitch.Util
import Language.Stitch.Data.Fin
import Language.Stitch.Data.Nat
import Language.Stitch.Data.SNat
import Language.Stitch.Data.Singletons

import Text.PrettyPrint.ANSI.Leijen

lamPrec, appPrec, appLeftPrec, appRightPrec, ifPrec :: Prec
lamPrec = 1
appPrec = 9
appLeftPrec = 8.9
appRightPrec = 9
ifPrec = 1

opPrec, opLeftPrec, opRightPrec :: ArithOp ty -> Prec
opPrec      (precInfo -> (x, _, _)) = x
opLeftPrec  (precInfo -> (_, x, _)) = x
opRightPrec (precInfo -> (_, _, x)) = x

-- | Returns (overall, left, right) precedences for an 'ArithOp'
precInfo :: ArithOp ty -> (Prec, Prec, Prec)
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

-- | An infinite stream of colorings
data Coloring = ApplyColor :&: Coloring
infixr 5 :&:

-- | The stream of colorings used for all rendered expressions
coloring :: Coloring
coloring = red :&: green :&: yellow :&: blue :&: magenta :&: cyan :&: coloring

applyColor :: forall n. SingI n => Fin n -> ApplyColor
applyColor v = go coloring (n `minus` v)
  where
    go (color :&: _) Zero      = color
    go (_ :&: rest)  (Succ n') = go rest n'

    n :: Sing n
    n = sing

-- | A class for expressions that can be pretty-printed
class SingI (NumBoundVars exp) => PrettyExp exp where
  type NumBoundVars exp :: Nat
  prettyExp :: Prec -> exp -> Doc

-- | Print a variable
prettyVar :: forall n. SingI n => Fin n -> Doc
prettyVar v = applyColor v (char '#' <> int (finToInt v))

-- | Print a lambda expression
prettyLam :: forall exp n ty. (Pretty ty, PrettyExp exp, NumBoundVars exp ~ Succ n)
          => Prec -> ty -> exp -> Doc
prettyLam prec ty body
  = maybeParens (prec >= lamPrec) $
    fillSep [ char 'λ' <> applyColor @(NumBoundVars exp) FZ (char '#') <>
              text ":" <> pretty ty <> char '.'
            , prettyExp topPrec body ]

-- | Print an application
prettyApp :: (PrettyExp exp1, PrettyExp exp2)
          => Prec -> exp1 -> exp2 -> Doc
prettyApp prec e1 e2
  = maybeParens (prec >= appPrec) $
    fillSep [ prettyExp appLeftPrec  e1
            , prettyExp appRightPrec e2 ]

-- | Print a let-expression
prettyLet :: forall exp1 exp2 n.
             (PrettyExp exp1, PrettyExp exp2, NumBoundVars exp2 ~ Succ n)
          => Prec -> exp1 -> exp2 -> Doc
prettyLet prec e1 e2
  = maybeParens (prec >= lamPrec) $
    fillSep [ text "let" <+> applyColor @(NumBoundVars exp2) FZ (char '#') <+>
              char '=' <+> prettyExp topPrec e1 <+> text "in"
            , prettyExp topPrec e2 ]

-- | Print an arithemtic expression
prettyArith :: (PrettyExp exp1, PrettyExp exp2)
            => Prec -> exp1 -> ArithOp ty -> exp2 -> Doc
prettyArith prec e1 op e2
  = maybeParens (prec >= opPrec op) $
    fillSep [ prettyExp (opLeftPrec op) e1 <+> pretty op
            , prettyExp (opRightPrec op) e2 ]

-- | Print a conditional
prettyIf :: ( PrettyExp exp1, PrettyExp exp2, PrettyExp exp3 )
         => Prec -> exp1 -> exp2 -> exp3 -> Doc
prettyIf prec e1 e2 e3
  = maybeParens (prec >= ifPrec) $
    fillSep [ text "if" <+> prettyExp topPrec e1
            , text "then" <+> prettyExp topPrec e2
            , text "else" <+> prettyExp topPrec e3 ]

-- | Print a @fix@
prettyFix :: PrettyExp exp => Prec -> exp -> Doc
prettyFix prec e
  = maybeParens (prec >= appPrec) $
    text "fix" <+> prettyExp topPrec e
