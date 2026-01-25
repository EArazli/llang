{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Basic
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram


tests :: TestTree
tests =
  testGroup
    "Poly.Basic"
    [ testCase "diagram dom/cod" testDiagramDomCod
    , testCase "compD rejects boundary mismatch" testCompMismatch
    , testCase "tensorD rejects mode mismatch" testTensorModeMismatch
    ]


testDiagramDomCod :: Assertion
testDiagramDomCod = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  let ctx = [a]
  case genD mode ctx ctx (GenName "f") of
    Left err -> assertFailure (T.unpack err)
    Right diag -> do
      diagramDom diag @?= ctx
      diagramCod diag @?= ctx


testCompMismatch :: Assertion
testCompMismatch = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  let b = TCon (TypeName "B") []
  let g = idD mode [a]
  let f = idD mode [b]
  case compD g f of
    Left _ -> pure ()
    Right _ -> assertFailure "expected boundary mismatch"


testTensorModeMismatch :: Assertion
testTensorModeMismatch = do
  let modeA = ModeName "A"
  let modeB = ModeName "B"
  let a = TCon (TypeName "A") []
  let d1 = idD modeA [a]
  let d2 = idD modeB [a]
  case tensorD d1 d2 of
    Left _ -> pure ()
    Right _ -> assertFailure "expected mode mismatch"
