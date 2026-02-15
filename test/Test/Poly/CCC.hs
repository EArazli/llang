{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.CCC
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Paths_llang (getDataFileName)
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env (meDoctrines)
import Strat.Poly.Doctrine (Doctrine(..), doctrineTypeTheory)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Normalize (normalize, NormalizationStatus(..))
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.Graph (canonDiagramRaw)
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Diagram (Diagram)
import Strat.Common.Rules (RewritePolicy(..))


tests :: TestTree
tests =
  testGroup
    "Poly.CCC"
    [ testCase "beta reduces under computational policy" testBetaReduces
    , testCase "beta_app reduces under computational policy" testBetaAppReduces
    ]

testBetaReduces :: Assertion
testBetaReduces = do
  doc <- loadCCC
  cell <- requireCell "beta" doc
  assertCellReduces doc cell

testBetaAppReduces :: Assertion
testBetaAppReduces = do
  doc <- loadCCC
  cell <- requireCell "beta_app" doc
  assertCellReduces doc cell

loadCCC :: IO Doctrine
loadCCC = do
  path <- getDataFileName "examples/lib/surfaces/ccc_surface/ccc.llang"
  envResult <- loadModule path
  env <- case envResult of
    Left err -> assertFailure (T.unpack err)
    Right env -> pure env
  case M.lookup "CCC" (meDoctrines env) of
    Nothing -> assertFailure "doctrine CCC not found"
    Just doc -> pure doc

requireCell :: Text -> Doctrine -> IO Cell2
requireCell name doc =
  case filter ((== name) . c2Name) (dCells2 doc) of
    [cell] -> pure cell
    [] -> assertFailure ("cell not found: " <> T.unpack name)
    _ -> assertFailure ("duplicate cell name: " <> T.unpack name)

assertCellReduces :: Doctrine -> Cell2 -> IO ()
assertCellReduces doc cell = do
  let rules = rulesFromPolicy UseOnlyComputationalLR (dCells2 doc)
  tt <- case doctrineTypeTheory doc of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right tt -> pure tt
  status <- case normalize tt 200 rules (c2LHS cell) of
    Left err -> assertFailure (T.unpack err)
    Right st -> pure st
  rhs <- case canonDiagramRaw (c2RHS cell) of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  case status of
    Finished d -> assertIso d rhs
    OutOfFuel d -> do
      ok <- case diagramIsoEq d rhs of
        Left err -> assertFailure (T.unpack err)
        Right v -> pure v
      if ok
        then assertFailure "normalize ran out of fuel despite reaching RHS"
        else assertFailure "normalize ran out of fuel before reaching RHS"

assertIso :: Diagram -> Diagram -> IO ()
assertIso d1 d2 = do
  ok <- case diagramIsoEq d1 d2 of
    Left err -> assertFailure (T.unpack err)
    Right v -> pure v
  if ok
    then pure ()
    else assertFailure "expected diagrams to be isomorphic"
