{-# LANGUAGE RankNTypes, TypeInType, GADTs, FlexibleContexts, CPP,
             TypeApplications, PatternSynonyms #-}

#ifdef __HADDOCK_VERSION__
{-# OPTIONS_GHC -Wno-unused-imports #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Check
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- The stitch typechecker.
--
----------------------------------------------------------------------------

module Language.Stitch.Check ( check ) where

import Language.Stitch.Exp
import Language.Stitch.Shift
import Language.Stitch.Op
import Language.Stitch.Type
import Language.Stitch.Unchecked
import Language.Stitch.Util
import Language.Stitch.Globals
#ifdef __HADDOCK_VERSION__
import Language.Stitch.Monad ( StitchE )
#endif

import Language.Stitch.Data.Nat
import Language.Stitch.Data.Fin
import Language.Stitch.Data.Singletons
import Language.Stitch.Data.Vec

import Text.PrettyPrint.ANSI.Leijen

import Control.Monad.Reader
import Control.Monad.Except

-- | Abort with a type error in the given expression
typeError :: (MonadError Doc m, SingI n) => UExp n -> Doc -> m a
typeError e doc = throwError $
                  doc $$ text "in the expression" <+> squotes (pretty e)

------------------------------------------------
-- The typechecker

-- | Check the given expression, aborting on type errors. The resulting
-- type and checked expression is given to the provided continuation.
-- This is parameterized over the choice of monad in order to support
-- pure operation during testing. 'StitchE' is the canonical choice for the
-- monad.
check :: (MonadError Doc m, MonadReader Globals m)
      => UExp Zero -> (forall t. STy t -> Exp VNil t -> m r)
      -> m r
check = go SVNil
  where
    -- More general version that supports non-empty contexts.
    -- In a proof, this would be a generalization of the indction principle.
    -- The SingI constraint is needed only for the colorization of pretty-printing.
    go :: (MonadError Doc m, MonadReader Globals m, SingI n)
       => Sing (ctx :: Ctx n) -> UExp n -> (forall t. STy t -> Exp ctx t -> m r)
       -> m r

    go ctx (UVar n) k
      = check_var n ctx $ \ty elem ->
        k ty (Var elem)
      where
        check_var :: Fin n -> Sing (ctx :: Ctx n)
                  -> (forall t. STy t -> Elem ctx t -> m r)
                  -> m r
        check_var FZ     (ty :%> _)   k = k ty EZ
        check_var (FS n) (_  :%> ctx) k = check_var n ctx $ \ty elem ->
                                          k ty (ES elem)

    go _   (UGlobal n) k
      = do globals <- ask
           lookupGlobal globals n $ \ty exp ->
             k ty (shifts0 exp)

    go ctx (ULam ty body) k
      = toSing ty $ \arg_ty ->
        go (arg_ty :%> ctx) body $ \res_ty body' ->
        k (arg_ty ::-> res_ty) (Lam arg_ty body')

    go ctx e@(UApp e1 e2) k
      = go ctx e1 $ \fun_ty e1' ->
        go ctx e2 $ \arg_ty e2' ->
        case fun_ty of
          arg_ty' ::-> res_ty
            |  Just Refl <- arg_ty `testEquality` arg_ty'
            -> k res_ty (App e1' e2')
          _ -> typeError e $
                   text "Bad function application." $$
                   indent 2 (vcat [ text "Function type:" <+> pretty fun_ty
                                  , text "Argument type:" <+> pretty arg_ty ])

    go ctx (ULet rhs body) k
      = go ctx rhs $ \rhs_ty rhs' ->
        go (rhs_ty :%> ctx) body $ \body_ty body' ->
        k body_ty (Let rhs' body')

    go ctx e@(UArith e1 (UArithOp s_op_ty op) e2) k
      = go ctx e1 $ \ty1 e1' ->
        go ctx e2 $ \ty2 e2' ->
        case (testEquality SInt ty1, testEquality SInt ty2) of
          (Just Refl, Just Refl)
            -> k s_op_ty (Arith e1' op e2')
          _ -> typeError e $
               text "Bad arith operand(s)." $$
               indent 2 (vcat [ text " Left-hand type:" <+> pretty ty1
                              , text "Right-hand type:" <+> pretty ty2 ])

    go ctx e@(UCond e1 e2 e3) k
      = go ctx e1 $ \ty1 e1' ->
        go ctx e2 $ \ty2 e2' ->
        go ctx e3 $ \ty3 e3' ->
        case testEquality SBool ty1 of
          Just Refl
            |  Just Refl <- ty2 `testEquality` ty3
            -> k ty2 (Cond e1' e2' e3')
          _ -> typeError e $
               text "Bad conditional." $$
               indent 2 (vcat [ text "Flag type:" <+> pretty ty1
                              , squotes (text "true") <+> text "expression type:"
                                                      <+> pretty ty2
                              , squotes (text "false") <+> text "expression type:"
                                                       <+> pretty ty3 ])

    go ctx e@(UFix e1) k
      = go ctx e1 $ \ty1 e1' ->
        case ty1 of
          arg ::-> res
            |  Just Refl <- arg `testEquality` res
            -> k arg (Fix e1')
          _ -> typeError e $
               text "Bad fix over expression with type:" <+> pretty ty1

    go _   (UIntE n)  k = k sing (IntE n)
    go _   (UBoolE b) k = k sing (BoolE b)
