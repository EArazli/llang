{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Feedback
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Strat.Frontend.Env (emptyEnv)
import Strat.Pipeline (FragmentDecl(..), defaultQuotePolicy)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (Edge(..), EdgePayload(..), ePayload, emptyDiagram, freshPort, addEdgePayload, validateDiagram)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
import Strat.Poly.Quote (SharedBinding(..), SharedProgram(..), quoteProgram)
import Test.Poly.Helpers (mkModes, withSelfClassifiedCtors)


tests :: TestTree
tests =
  testGroup
    "Poly.Feedback"
    [ testCase "loop elaborates to explicit feedback payload" testFeedbackElab
    , testCase "trace elaborates to feedback payload with outer inputs" testTraceElab
    , testCase "trace rejects zero arity" testTraceRejectsZeroArity
    , testCase "trace rejects body arity smaller than k" testTraceRejectsInsufficientBoundary
    , testCase "trace rejects suffix feedback object mismatch" testTraceRejectsSuffixMismatch
    , testCase "trace parser rejects oversized arity literal" testTraceParserRejectsOversizedArity
    , testCase "kernel validation rejects feedback with zero inferred wires" testKernelRejectsZeroInferredFeedbackWires
    ]


testFeedbackElab :: Assertion
testFeedbackElab = do
  let doc = mkDoctrine
  raw <- require (parseDiagExpr "loop { step }")
  diag <- require (elabDiagExpr emptyEnv doc modeM [] raw)
  assertBool "expected feedback edge in outer graph" (hasFeedback diag)
  program <- require (quoteProgram defaultQuotePolicy doc modeM fragmentResidual diag)
  assertBool "expected BindFeedback in quoted program" (any isFeedbackBinding (spBindings program))
  where
    isFeedbackBinding binding =
      case binding of
        BindFeedback {} -> True
        _ -> False

testTraceElab :: Assertion
testTraceElab = do
  let doc = mkDoctrine
  raw <- require (parseDiagExpr "trace 1 { step2 }")
  diag <- require (elabDiagExpr emptyEnv doc modeM [] raw)
  assertBool "expected feedback edge with one outer input and one outer output" (hasFeedbackWithIO 1 1 diag)
  program <- require (quoteProgram defaultQuotePolicy doc modeM fragmentResidual diag)
  assertBool "expected BindFeedback with one input and one output" (any isFeedbackBinding (spBindings program))
  where
    isFeedbackBinding binding =
      case binding of
        BindFeedback { sbIns = ins, sbOuts = outs } -> length ins == 1 && length outs == 1
        _ -> False

testTraceRejectsZeroArity :: Assertion
testTraceRejectsZeroArity = do
  let doc = mkDoctrine
  raw <- require (parseDiagExpr "trace 0 { step2 }")
  expectLeftContains "trace: expected k > 0" (elabDiagExpr emptyEnv doc modeM [] raw)

testTraceRejectsInsufficientBoundary :: Assertion
testTraceRejectsInsufficientBoundary = do
  let doc = mkDoctrine
  raw <- require (parseDiagExpr "trace 3 { step2 }")
  expectLeftContains "trace: body has fewer inputs than k" (elabDiagExpr emptyEnv doc modeM [] raw)

testTraceRejectsSuffixMismatch :: Assertion
testTraceRejectsSuffixMismatch = do
  let doc = mkDoctrine
  raw <- require (parseDiagExpr "trace 1 { step_bad }")
  expectLeftContains "trace: feedback input/output objects must match (suffix convention)" (elabDiagExpr emptyEnv doc modeM [] raw)

testTraceParserRejectsOversizedArity :: Assertion
testTraceParserRejectsOversizedArity =
  case parseDiagExpr "trace 999999999999999999999999999999999999 { step2 }" of
    Left err ->
      assertBool "expected parse error to mention oversized trace arity" ("trace arity is too large" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected parser to reject oversized trace arity"

testKernelRejectsZeroInferredFeedbackWires :: Assertion
testKernelRejectsZeroInferredFeedbackWires = do
  let inner = idD modeM [tyT]
  let (pIn, d0) = freshPort tyT (emptyDiagram modeM [])
  let (pOut, d1) = freshPort tyT d0
  d2 <- require (addEdgePayload (PFeedback inner) [pIn] [pOut] d1)
  let bad = d2 { dIn = [pIn], dOut = [pOut] }
  expectLeftContains "feedback: expected at least one feedback wire" (validateDiagram bad)


hasFeedback :: Diagram -> Bool
hasFeedback diag =
  any isFeedback (IM.elems (dEdges diag))
  where
    isFeedback edge =
      case ePayload edge of
        PFeedback _ -> True
        _ -> False

hasFeedbackWithIO :: Int -> Int -> Diagram -> Bool
hasFeedbackWithIO inCount outCount diag =
  any isFeedback (IM.elems (dEdges diag))
  where
    isFeedback edge =
      case ePayload edge of
        PFeedback _ -> length (eIns edge) == inCount && length (eOuts edge) == outCount
        _ -> False


mkDoctrine :: Doctrine
mkDoctrine =
  withSelfClassifiedCtors
    [(modeM, [(ObjName "T", []), (ObjName "U", [])])]
    Doctrine
      { dName = "D"
      , dModes = mkModes [modeM]
      , dAcyclicModes = S.singleton modeM
      , dAttrSorts = M.empty
      , dGens =
          M.fromList
            [ ( modeM
              , M.fromList
                  [ (GenName "step", genStep)
                  , (GenName "step2", genStep2)
                  , (GenName "step_bad", genStepBad)
                  ]
              )
            ]
      , dCells2 = []
      , dActions = M.empty
      , dObligations = []
      }


genStep :: GenDecl
genStep =
  GenDecl
    { gdName = GenName "step"
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT]
    , gdCod = [tyT, tyT]
    , gdAttrs = []
    }

genStep2 :: GenDecl
genStep2 =
  GenDecl
    { gdName = GenName "step2"
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT, InPort tyT]
    , gdCod = [tyT, tyT]
    , gdAttrs = []
    }

genStepBad :: GenDecl
genStepBad =
  GenDecl
    { gdName = GenName "step_bad"
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT, InPort tyU]
    , gdCod = [tyT, tyT]
    , gdAttrs = []
    }


modeM :: ModeName
modeM = ModeName "M"


tyT :: Obj
tyT = mkCon (ObjRef modeM (ObjName "T")) []

tyU :: Obj
tyU = mkCon (ObjRef modeM (ObjName "U")) []


fragmentResidual :: FragmentDecl
fragmentResidual =
  FragmentDecl
    { frName = "Frag"
    , frBase = "D"
    , frMode = "M"
    , frGenRoles = M.empty
    , frProducts = []
    , frRecurseBinders = False
    , frRecurseBoxes = False
    , frRecurseFeedback = True
    }


expectLeftContains :: Text -> Either Text a -> Assertion
expectLeftContains needle result =
  case result of
    Left err ->
      assertBool
        ("expected error to contain: " <> T.unpack needle <> ", got: " <> T.unpack err)
        (needle `T.isInfixOf` err)
    Right _ ->
      assertFailure ("expected failure containing: " <> T.unpack needle)


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
