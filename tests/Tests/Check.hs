{-# LANGUAGE GADTs, TypeApplications #-}

module Tests.Check where

import Prelude hiding ( lex )

import Language.Stitch.Data.Vec
import Language.Stitch.Exp
import Language.Stitch.Parse
import Language.Stitch.Lex
import Language.Stitch.Check
import Language.Stitch.Type
import Language.Stitch.Eval
import Language.Stitch.Globals
import Language.Stitch.Util
import Language.Stitch.Data.Singletons

import Control.Monad.Trans.Except
import Control.Monad.Reader

import Text.PrettyPrint.ANSI.Leijen

import Data.Maybe
import Data.List as List
import qualified Control.Arrow as Arrow

import Test.Tasty
import Test.Tasty.HUnit

checkTestCases :: [(String, Maybe (String, Ty, String))]
checkTestCases = [ ("1", Just ("1", TInt, "1"))
                 , ("1 + true", Nothing)
                 , ("(\\x:Int.x) 5",
                    Just ("(λ#:Int. #0) 5", TInt, "5"))
                 , ("(\\x:Int.\\y:Int->Int.y x) 4 (\\z:Int.z*2)",
                    Just ("(λ#:Int. λ#:Int -> Int. #0 #1) 4 (λ#:Int. #0 * 2)",
                          TInt, "8"))
                 , ("1 + 2 * 3 / 4 - 10 % 3",
                    Just ("1 + 2 * 3 / 4 - 10 % 3", TInt, "1"))
                 , ("if true then 1 else false", Nothing)
                 , ("if 3 - 1 == 2 then \\x:Int.x else \\x:Int.3",
                    Just ("if 3 - 1 == 2 then λ#:Int. #0 else λ#:Int. 3",
                          TInt :-> TInt, "λ#:Int. #0"))
                 , ("1 > 2", Just ("1 > 2", TBool, "false"))
                 , ("2 > 1", Just ("2 > 1", TBool, "true"))
                 , ("1 > 1", Just ("1 > 1", TBool, "false"))
                 , ("1 >= 1", Just ("1 >= 1", TBool, "true"))
                 , ("1 < 2", Just ("1 < 2", TBool, "true"))
                 , ("1 < 1", Just ("1 < 1", TBool, "false"))
                 , ("1 <= 1", Just ("1 <= 1", TBool, "true"))
                 , ("id_int (id_int 5)", Just ("(λ#:Int. #0) ((λ#:Int. #0) 5)", TInt, "5"))
                 ]

checkTests :: TestTree
checkTests = testGroup "Typechecker" $
  List.map (\(expr_str, m_result) ->
               testCase ("`" ++ expr_str ++ "'") $
               (case flip runReader id_globals $ runExceptT $ do
                       uexp <- hoistEither $ Arrow.left text $ parseExp =<< lex expr_str
                       check uexp $ \sty exp -> return $
                         case m_result of
                           Just result
                             -> (render (plain $ pretty exp), fromSing sty,
                                 render (plain $ pretty (eval exp)))
                                 @?= result
                           _ -> assertFailure "unexpected type-check success"
                  of
                  Left _  -> assertBool "unexpected failure" (isNothing m_result)
                  Right b -> b)) checkTestCases

hoistEither :: Monad m => Either e a -> ExceptT e m a
hoistEither = ExceptT . return

id_globals :: Globals
id_globals = extend "id_int" (SInt ::-> SInt) (Lam SInt (Var EZ)) emptyGlobals
