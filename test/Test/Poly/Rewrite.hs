{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Rewrite
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.Diagram
import Strat.Poly.Graph
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..))
import Strat.Poly.Rewrite
import Strat.Poly.Normalize (normalize, NormalizationStatus(..))
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Pretty (renderDiagram)


tests :: TestTree
tests =
  testGroup
    "Poly.Rewrite"
    [ testCase "simple local rewrite" testSimpleRewrite
    , testCase "subdiagram rewrite across composition" testSubdiagramRewrite
    , testCase "dangling condition rejects match" testDanglingReject
    , testCase "normalize deterministic" testNormalizeDeterminism
    ]

modeName :: ModeName
modeName = ModeName "M"

aTy :: TypeExpr
aTy = TCon (TypeName "A") []

mkGen :: Text -> [TypeExpr] -> [TypeExpr] -> Either Text Diagram
mkGen name dom cod = genD modeName dom cod (GenName name)

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

assocRule :: Either Text RewriteRule
assocRule = do
  mul <- mkGen "mul" [aTy, aTy] [aTy]
  id1 <- pure (idD modeName [aTy])
  left <- tensorD mul id1
  lhs <- compD mul left
  right <- tensorD id1 mul
  rhs <- compD mul right
  pure RewriteRule
    { rrName = "assoc"
    , rrLHS = lhs
    , rrRHS = rhs
    , rrTyVars = []
    }

testSimpleRewrite :: Assertion
testSimpleRewrite = do
  rule <- either (assertFailure . T.unpack) pure assocRule
  let lhs = rrLHS rule
  res <- case rewriteOnce [rule] lhs of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> assertFailure "expected rewrite"
    Just d -> renderDiagram d @?= renderDiagram (rrRHS rule)

testSubdiagramRewrite :: Assertion
testSubdiagramRewrite = do
  rule <- either (assertFailure . T.unpack) pure assocRule
  let lhs = rrLHS rule
  extra <- require (mkGen "mul" [aTy, aTy] [aTy])
  host <- require (tensorD lhs extra)
  res <- case rewriteOnce [rule] host of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> assertFailure "expected subdiagram rewrite"
    Just _ -> pure ()

testDanglingReject :: Assertion
testDanglingReject = do
  f <- require (mkGen "f" [aTy] [aTy])
  let lhs = f { dOut = [] }
  let rhs = lhs
  let rule = RewriteRule
        { rrName = "dangling"
        , rrLHS = lhs
        , rrRHS = rhs
        , rrTyVars = []
        }
  g <- require (mkGen "g" [aTy] [aTy])
  host0 <- require (tensorD lhs g)
  let internalPort = head (filter (`notElem` dIn lhs) (diagramPortIds lhs))
  let gIn = dIn host0 !! length (dIn lhs)
  host1 <- case mergePorts host0 internalPort gIn of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  res <- case rewriteOnce [rule] host1 of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> pure ()
    Just _ -> assertFailure "expected dangling match rejection"

testNormalizeDeterminism :: Assertion
testNormalizeDeterminism = do
  rule <- either (assertFailure . T.unpack) pure assocRule
  mul <- require (mkGen "mul" [aTy, aTy] [aTy])
  id1 <- pure (idD modeName [aTy])
  d1 <- require (tensorD mul id1)
  d2 <- require (compD mul d1)
  let rules = [rule]
  r1 <- require (normalize 10 rules d2)
  r2 <- require (normalize 10 rules d2)
  case (r1, r2) of
    (Finished a, Finished b) -> a @?= b
    (OutOfFuel a, OutOfFuel b) -> a @?= b
    _ -> assertFailure "expected same normalization status"
