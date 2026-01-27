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
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..))
import Strat.Poly.Rewrite
import Strat.Poly.Normalize (normalize, NormalizationStatus(..))
import Strat.Poly.Match (findFirstMatchNoDoc)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Pretty (renderDiagram)
import qualified Data.IntMap.Strict as IM


tests :: TestTree
tests =
  testGroup
    "Poly.Rewrite"
    [ testCase "simple local rewrite" testSimpleRewrite
    , testCase "subdiagram rewrite across composition" testSubdiagramRewrite
    , testCase "dangling condition rejects match" testDanglingReject
    , testCase "matching requires injective host mapping" testInjectiveMatch
    , testCase "non-injective match does not trigger rewrite" testNonInjectiveRewrite
    , testCase "rewrite inside box" testRewriteInsideBox
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
    Just d -> do
      got <- require (renderDiagram d)
      expected <- require (renderDiagram (rrRHS rule))
      got @?= expected

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
  g <- require (mkGen "g" [aTy] [aTy])
  lhs <- require (compD g f)
  let rhs = lhs
  let rule = RewriteRule
        { rrName = "dangling"
        , rrLHS = lhs
        , rrRHS = rhs
        , rrTyVars = []
        }
  extra <- require (mkGen "h" [aTy] [aTy])
  host0 <- require (tensorD lhs extra)
  let boundary = dIn lhs <> dOut lhs
  let internalPort = head (filter (`notElem` boundary) (diagramPortIds lhs))
  let host1 = host0 { dOut = internalPort : dOut host0 }
  res <- case rewriteOnce [rule] host1 of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> pure ()
    Just _ -> assertFailure "expected dangling match rejection"

testInjectiveMatch :: Assertion
testInjectiveMatch = do
  g <- require (mkGen "f" [aTy] [aTy])
  pat <- require (tensorD g g)
  let host = g
  res <- case findFirstMatchNoDoc pat host of
    Left err -> assertFailure (T.unpack err)
    Right m -> pure m
  case res of
    Nothing -> pure ()
    Just _ -> assertFailure "expected no match due to non-injective mapping"

testNonInjectiveRewrite :: Assertion
testNonInjectiveRewrite = do
  g <- require (mkGen "f" [aTy] [aTy])
  lhs <- require (tensorD g g)
  let rule = RewriteRule
        { rrName = "dup"
        , rrLHS = lhs
        , rrRHS = lhs
        , rrTyVars = []
        }
  res <- case rewriteOnce [rule] g of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> pure ()
    Just _ -> assertFailure "expected no rewrite due to non-injective match"

testRewriteInsideBox :: Assertion
testRewriteInsideBox = do
  f <- require (mkGen "f" [aTy] [aTy])
  g <- require (mkGen "g" [aTy] [aTy])
  let rule = RewriteRule
        { rrName = "boxrule"
        , rrLHS = f
        , rrRHS = g
        , rrTyVars = []
        }
  let (inP, d0) = freshPort aTy (emptyDiagram modeName)
  let (outP, d1) = freshPort aTy d0
  let boxEdge = PBox (BoxName "B") f
  d2 <- require (addEdgePayload boxEdge [inP] [outP] d1)
  let host = d2 { dIn = [inP], dOut = [outP] }
  res <- case rewriteOnce [rule] host of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> assertFailure "expected rewrite inside box"
    Just d -> do
      let edges = IM.elems (dEdges d)
      case edges of
        [edge] ->
          case ePayload edge of
            PBox _ inner -> do
              got <- require (renderDiagram inner)
              expected <- require (renderDiagram g)
              got @?= expected
            _ -> assertFailure "expected box edge"
        _ -> assertFailure "expected single box edge"

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
