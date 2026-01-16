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
    , testCase "end-to-end monoid alt syntax/model" testEndToEndMonoidAlt
    , testCase "end-to-end peano" testEndToEndPeano
    , testCase "end-to-end ski" testEndToEndSKI
    , testCase "end-to-end category" testEndToEndCat
    , testCase "end-to-end STLC surface" testEndToEndSTLCSurface
    , testCase "end-to-end STLC surface lam" testEndToEndSTLCLam
    , testCase "end-to-end STLC surface lam nested x" testEndToEndSTLCLamNestedX
    , testCase "end-to-end STLC surface lam nested y" testEndToEndSTLCLamNestedY
    , testCase "end-to-end STLC surface pair/fst" testEndToEndSTLCPair
    , testCase "end-to-end STLC surface unknown identifier" testEndToEndSTLCBadIdent
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

testEndToEndMonoidAlt :: Assertion
testEndToEndMonoidAlt = do
  path <- getDataFileName "examples/monoid.alt.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      rrValue out @?= VInt 0
      rrPrintedNormalized out @?= "unit"


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

testEndToEndSTLCSurface :: Assertion
testEndToEndSTLCSurface = do
  path <- getDataFileName "examples/ccc_surface/stlc.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      assertBool "surface input printed" (maybe False (not . T.null) (rrPrintedInput out))
      case termNode (rrNormalized out) of
        TOp _ _ -> pure ()
        _ -> assertFailure "expected normalized core term"

testEndToEndSTLCLam :: Assertion
testEndToEndSTLCLam = do
  path <- getDataFileName "examples/ccc_surface/stlc.lam1.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (rrNormalized out)
      assertBool "expected CCC.curry in core term" (OpName "CCC.curry" `elem` ops)

testEndToEndSTLCLamNestedX :: Assertion
testEndToEndSTLCLamNestedX = do
  path <- getDataFileName "examples/ccc_surface/stlc.lam2.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (rrNormalized out)
      assertBool "expected CCC.curry in core term" (OpName "CCC.curry" `elem` ops)

testEndToEndSTLCLamNestedY :: Assertion
testEndToEndSTLCLamNestedY = do
  path <- getDataFileName "examples/ccc_surface/stlc.lam3.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (rrNormalized out)
      assertBool "expected CCC.curry in core term" (OpName "CCC.curry" `elem` ops)

testEndToEndSTLCPair :: Assertion
testEndToEndSTLCPair = do
  path <- getDataFileName "examples/ccc_surface/stlc.pair.run.llang"
  result <- runFile path
  case result of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testEndToEndSTLCBadIdent :: Assertion
testEndToEndSTLCBadIdent = do
  path <- getDataFileName "examples/ccc_surface/stlc.bad.run.llang"
  result <- runFile path
  case result of
    Left _ -> pure ()
    Right _ -> assertFailure "expected failure for unknown identifier"

collectOps :: Term -> [OpName]
collectOps tm =
  case termNode tm of
    TVar _ -> []
    TOp op args -> op : concatMap collectOps args
