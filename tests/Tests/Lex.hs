module Tests.Lex where

import Language.Stitch.Lex
import Language.Stitch.Token
import Language.Stitch.Op
import Tests.Util

import Prelude hiding ( lex )

import Data.List as List
import Control.Arrow as Arrow ( right )

lexTestCases :: [(String, [Token])]
lexTestCases = [ ("", [])
               , ("  ", [])
               , (" {- hi -}  \n  ", [])
               , (" {----} ", [])
               , (" {- foo {- bar -} blah -}", [])
               , (" {- foo {-- bar -}-}", [])
               , ("{- blah ---}", [])
               , ("{- froggle -} -- blah", [])
               , ("x", [Name "x"])
               , ("(()", [LParen, LParen, RParen])
               , ("++--++", [ArithOp uPlus, ArithOp uPlus])
               , ("->->", [ArrowTok, ArrowTok])
               , ("45+332-89/1*3%xyz", [ IntTok 45, ArithOp uPlus, IntTok 332
                                       , ArithOp uMinus, IntTok 89, ArithOp uDivide
                                       , IntTok 1, ArithOp uTimes, IntTok 3
                                       , ArithOp uMod, Name "xyz" ])
               , ("===", [ArithOp uEquals, Assign])
               , ("if x then y else z", [If, Name "x", Then, Name "y", Else, Name "z"])
               , ("ifs trues falsee true-", [ Name "ifs", Name "trues", Name "falsee"
                                            , BoolTok True, ArithOp uMinus ])
               , (":\\", [Colon, Lambda])
               , (">>==<===<", [ ArithOp uGreater, ArithOp uGreaterE, Assign
                               , ArithOp uLessE, ArithOp uEquals, ArithOp uLess ])
               ]

lexTests :: TestTree
lexTests = testGroup "Lexer" $
  List.map (\(str, out) -> testCase ("`" ++ str ++ "'") $
                           Arrow.right (List.map unLoc)
                                        (lex str) @?= Right out)
           lexTestCases
