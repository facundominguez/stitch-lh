{-# LANGUAGE PolyKinds, DataKinds #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Statement
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Defines the Stitch Statement type, which can either be a bare
-- expression or a global variable assignment.
--
----------------------------------------------------------------------------

module Language.Stitch.Statement ( Statement(..) ) where

import Language.Stitch.Unchecked
import Language.Stitch.Data.Nat

import Text.PrettyPrint.ANSI.Leijen

-- | A statement can either be a bare expression, which will be evaluated,
-- or an assignment to a global variable.
data Statement = BareExp (UExp Zero)
               | NewGlobal String (UExp Zero)
  deriving Show

instance Pretty Statement where
  pretty (BareExp exp)     = pretty exp
  pretty (NewGlobal v exp) = text v <+> char '=' <+> pretty exp
