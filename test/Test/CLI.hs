{-# LANGUAGE OverloadedStrings #-}
module Test.CLI
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Frontend.Run
import Strat.Backend (Value(..))
import Strat.Backend.Concat (CatExpr(..))
import Strat.Kernel.Syntax (OpName(..), Term(..), TermNode(..))
import qualified Data.Text as T
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "CLI"
    [ testCase "end-to-end monoid" testEndToEndMonoid
    , testCase "end-to-end peano" testEndToEndPeano
    , testCase "end-to-end ski" testEndToEndSKI
    , testCase "end-to-end category" testEndToEndCat
    ]


testEndToEndMonoid :: Assertion
testEndToEndMonoid = do
  path <- getDataFileName "examples/monoid.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      rrCatExpr out @?= CatOp (OpName "C.e") []
      rrValue out @?= VString ""
      rrPrintedNormalized out @?= "e"


testEndToEndPeano :: Assertion
testEndToEndPeano = do
  path <- getDataFileName "examples/peano.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> rrValue out @?= VInt 6


testEndToEndSKI :: Assertion
testEndToEndSKI = do
  path <- getDataFileName "examples/ski.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> rrValue out @?= VAtom "SKI.a"


testEndToEndCat :: Assertion
testEndToEndCat = do
  path <- getDataFileName "examples/cat.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (rrNormalized out)
      assertBool "no id in normal form" (OpName "C.id" `notElem` ops)
      case termNode (rrNormalized out) of
        TOp (OpName "C.comp") [_, _, _, Term _ (TOp (OpName "C.h") []), Term _ (TOp (OpName "C.comp") innerArgs)] ->
          case innerArgs of
            [_, _, _, Term _ (TOp (OpName "C.g") []), Term _ (TOp (OpName "C.f") [])] -> pure ()
            _ -> assertFailure "inner composition not in expected form"
        _ -> assertFailure "outer composition not in expected form"

collectOps :: Term -> [OpName]
collectOps tm =
  case termNode tm of
    TVar _ -> []
    TOp op args -> op : concatMap collectOps args
