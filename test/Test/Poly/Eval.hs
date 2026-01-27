{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Eval
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..))
import Strat.Poly.Graph (Diagram(..), emptyDiagram, freshPort, addEdgePayload, EdgePayload(..), validateDiagram)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Eval (evalDiagram)
import Strat.Model.Spec (ModelSpec(..), DefaultBehavior(..))
import Strat.Backend (Value(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Eval"
    [ testCase "eval fails when generator is undeclared" testEvalUnknownGen
    , testCase "eval fails when model is missing and default is error" testEvalMissingModel
    ]


testEvalUnknownGen :: Assertion
testEvalUnknownGen = do
  let mode = ModeName "M"
  let a = TCon (TypeName "A") []
  diag <- case mkDupDiagram mode a of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let doc = Doctrine
        { dName = "NoDup"
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", 0)])]
        , dGens = M.empty
        , dCells2 = []
        }
  let model = ModelSpec "Empty" [] DefaultSymbolic
  case evalDiagram doc model diag [VInt 1] of
    Left _ -> pure ()
    Right _ -> assertFailure "expected eval failure for unknown generator"


testEvalMissingModel :: Assertion
testEvalMissingModel = do
  let mode = ModeName "M"
  let a = TCon (TypeName "A") []
  diag <- case mkDupDiagram mode a of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let dupGen = GenDecl
        { gdName = GenName "dup"
        , gdMode = mode
        , gdTyVars = []
        , gdDom = [a]
        , gdCod = [a, a]
        }
  let doc = Doctrine
        { dName = "WithDup"
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", 0)])]
        , dGens = M.fromList [(mode, M.fromList [(GenName "dup", dupGen)])]
        , dCells2 = []
        }
  let model = ModelSpec "NoDupModel" [] (DefaultError "missing")
  case evalDiagram doc model diag [VInt 1] of
    Left _ -> pure ()
    Right _ -> assertFailure "expected eval failure for missing model clause"


mkDupDiagram :: ModeName -> TypeExpr -> Either T.Text Diagram
mkDupDiagram mode a = do
  let (p0, d0) = freshPort a (emptyDiagram mode)
  let (p1, d1) = freshPort a d0
  let (p2, d2) = freshPort a d1
  d3 <- addEdgePayload (PGen (GenName "dup")) [p0] [p1, p2] d2
  let diag = d3 { dIn = [p0], dOut = [p1, p2] }
  validateDiagram diag
  pure diag
