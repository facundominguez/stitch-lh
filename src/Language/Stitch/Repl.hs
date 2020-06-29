{-# LANGUAGE FlexibleInstances, UndecidableInstances, ViewPatterns,
             NondecreasingIndentation, TypeInType #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Repl
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
--
-- Implements a REPL for stitch.
--
----------------------------------------------------------------------------

module Language.Stitch.Repl ( main ) where

import Prelude hiding ( lex )

import Language.Stitch.Check
import Language.Stitch.Eval
import Language.Stitch.Lex
import Language.Stitch.Parse
import Language.Stitch.Unchecked
import Language.Stitch.Util
import Language.Stitch.Statement
import Language.Stitch.Globals
import Language.Stitch.Monad
import Language.Stitch.Exp
import Language.Stitch.CSE
import Language.Stitch.Type

import Language.Stitch.Data.Nat
import Language.Stitch.Data.Vec

import Text.PrettyPrint.ANSI.Leijen as Pretty hiding ( (<$>) )

import System.Console.Haskeline
import System.Directory

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List as List

-- | The Stitch interpreter
main :: IO ()
main = runInputT defaultSettings $
       runStitch $ do
         helloWorld
         loop

loop :: Stitch ()
loop = do
  m_line <- prompt "λ> "
  case stripWhitespace <$> m_line of
    Nothing          -> quit
    Just (':' : cmd) -> runCommand cmd
    Just str         -> runStmts str
  loop

-- | Prints welcome message
helloWorld :: Stitch ()
helloWorld = do
  printLine $ text "Welcome to the Stitch interpreter, version" <+>
              text version <> char '.'
  printLine $ text "Type `:help` at the prompt for the list of commands."

-- | The current version of stitch
version :: String
version = "1.0"

-------------------------------------------
-- running statements

runStmts :: String -> Stitch ()
runStmts str = stitchE $ do
    toks <- lexM str
    stmts <- parseStmtsM toks
    doStmts stmts

-- | Run a sequence of statements, returning the new global variables
doStmts :: [Statement] -> StitchE Globals
doStmts []     = ask
doStmts (s:ss) = doStmt s $ doStmts ss

-- | Run a 'Statement' and then run another action with the global
-- variables built in the 'Statement'
doStmt :: Statement -> StitchE a -> StitchE a
doStmt (BareExp uexp) thing_inside = check uexp $ \sty exp -> do
  printLine $ printValWithType (eval exp) sty
  thing_inside
doStmt (NewGlobal g uexp) thing_inside = check uexp $ \sty exp -> do
  printLine $ text g <+> char '=' <+> printWithType exp sty
  local (extend g sty exp) thing_inside

-------------------------------------------
-- commands

-- | Interpret a command (missing the initial ':').
runCommand :: String -> Stitch ()
runCommand = dispatchCommand cmdTable

type CommandTable = [(String, String -> Stitch ())]

dispatchCommand :: CommandTable -> String -> Stitch ()
dispatchCommand table line
  = case List.filter ((cmd `List.isPrefixOf`) . fst) table of
      []            -> do printLine $ text "Unknown command:" <+> squotes (text cmd)
      [(_, action)] -> action arg
      many          -> do printLine $ text "Ambiguous command:" <+> squotes (text cmd)
                          printLine $ text "Possibilities:" $$
                                      indent 2 (vcat $ List.map (text . fst) many)
  where (cmd, arg) = List.break isSpace line

cmdTable :: CommandTable
cmdTable = [ ("quit",     quitCmd)
           , ("d-lex",    lexCmd)
           , ("d-parse",  parseCmd)
           , ("load",     loadCmd)
           , ("eval",     evalCmd)
           , ("step",     stepCmd)
           , ("type",     typeCmd)
           , ("all",      allCmd)
           , ("cse",      cseCmd)
           , ("cse-step", cseStepCmd)
           , ("help",     helpCmd)
           ]

quitCmd :: String -> Stitch ()
quitCmd _ = quit

class Reportable a where
  report :: a -> Stitch Globals

instance Reportable Doc where
  report x = printLine x >> get
instance Reportable () where
  report _ = get
instance Reportable Globals where
  report = return
instance {-# OVERLAPPABLE #-} Pretty a => Reportable a where
  report other = printLine (pretty other) >> get

stitchE :: Reportable a => StitchE a -> Stitch ()
stitchE thing_inside = do
  result <- runStitchE thing_inside
  new_globals <- case result of
    Left err -> printLine err >> get
    Right x  -> report x
  put new_globals

parseLex :: String -> StitchE (UExp Zero)
parseLex = parseExpM <=< lexM

printWithType :: (Pretty exp, Pretty ty) => exp -> ty -> Doc
printWithType exp ty
  = pretty exp <+> colon <+> pretty ty

printValWithType :: ValuePair ty -> STy ty -> Doc
printValWithType val sty
  = pretty val <+> colon <+> pretty sty

showSteps :: STy ty -> Exp VNil ty -> StitchE Int
showSteps sty exp = do
  printLine $ printWithType exp sty
  let loop num_steps e = case step e of
        Step e' -> do
          printLine $ text "-->" <+> printWithType e' sty
          loop (num_steps + 1) e'
        Value _ -> return num_steps
  loop 0 exp

lexCmd, parseCmd, evalCmd, stepCmd, typeCmd, allCmd, loadCmd, cseCmd, cseStepCmd
  , helpCmd
  :: String -> Stitch ()
lexCmd expr = stitchE $ lexM expr
parseCmd = stitchE . parseLex

evalCmd expr = stitchE $ do
  uexp <- parseLex expr
  check uexp $ \sty exp ->
    return $ printValWithType (eval exp) sty

stepCmd expr = stitchE $ do
  uexp <- parseLex expr
  check uexp $ \sty exp -> do
    _ <- showSteps sty exp
    return ()

typeCmd expr = stitchE $ do
  uexp <- parseLex expr
  check uexp $ \sty exp -> return (printWithType exp sty)

allCmd expr = do
  printLine (text "Small step:")
  _ <- stepCmd expr

  printLine Pretty.empty
  printLine (text "Big step:")
  evalCmd expr

loadCmd (stripWhitespace -> file) = do
  file_exists <- liftIO $ doesFileExist file
  if not file_exists then file_not_found else do
  contents <- liftIO $ readFile file
  runStmts contents
  where
    file_not_found = do
      printLine (text "File not found:" <+> squotes (text file))
      cwd <- liftIO getCurrentDirectory
      printLine (parens (text "Current directory:" <+> text cwd))

cseCmd expr = stitchE $ do
  uexp <- parseLex expr
  check uexp $ \_sty exp -> do
    printLine $ text "Before CSE:" <+> pretty exp
    printLine $ text "After CSE: " <+> pretty (cse exp)

cseStepCmd expr = stitchE $ do
  uexp <- parseLex expr
  check uexp $ \sty exp -> do
    printLine $ text "Before CSE:" <+> pretty exp
    n <- showSteps sty exp
    printLine $ text "Number of steps:" <+> pretty n

    printLine $ text "----------------------"

    let exp' = cse exp
    printLine $ text "After CSE: " <+> pretty exp'
    n' <- showSteps sty exp'
    printLine $ text "Number of steps:" <+> pretty n'

    return ()

helpCmd _ = do
  printLine $ text "Available commands:"
  printLine $ text " :quit             Quits the interpreter"
  printLine $ text " :load <filename>  Loads a file with ;-separated Stitch statements"
  printLine $ text " :eval <expr>      Evaluates an expression with big-step semantics"
  printLine $ text " :step <expr>      Small-steps an expression until it becomes a value"
  printLine $ text " :type <expr>      Type-check an expression and report the type"
  printLine $ text " :all <expr>       Combination of :eval and :step"
  printLine $ text " :cse <expr>       Performs common-subexpression elimination (CSE)"
  printLine $ text " :cse-step <expr>  Steps an expression both before and after CSE"
  printLine $ text " :help             Shows this help text"
  printLine $ text "You may also type an expression to evaluate it, or assign to a global"
  printLine $ text "variable with `<var> = <expr>`"
