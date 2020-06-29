{-# LANGUAGE GADTs, TypeInType, RankNTypes, FlexibleContexts,
             StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Globals
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
--
-- Manages the global variables in Stitch
--
----------------------------------------------------------------------------

module Language.Stitch.Globals (
  Globals, emptyGlobals, extend, lookupGlobal ) where

import Language.Stitch.Exp
import Language.Stitch.Type
import Language.Stitch.Data.Vec
import Language.Stitch.Data.Exists

import Text.PrettyPrint.ANSI.Leijen

import Control.Monad.Except

import Data.Map as Map

-- | The global variable environment maps variables to type-checked
-- expressions
newtype Globals = Globals (Map String (SingEx (Exp VNil)))

-- | An empty global variable environment
emptyGlobals :: Globals
emptyGlobals = Globals Map.empty

-- | Extend a 'Globals' with a new binding
extend :: String -> STy ty -> Exp VNil ty -> Globals -> Globals
extend var sty exp (Globals globals)
  = Globals $ Map.insert var (SingEx sty exp) globals

-- | Lookup a global variable. Fails with 'throwError' if the variable
-- is not bound.
lookupGlobal :: MonadError Doc m
             => Globals -> String
             -> (forall ty. STy ty -> Exp VNil ty -> m r)
             -> m r
lookupGlobal (Globals globals) var k
  = case Map.lookup var globals of
      Just exp -> unpackSingEx exp k
      Nothing  -> throwError $
                  text "Global variable not in scope:" <+>
                  squotes (text var)
