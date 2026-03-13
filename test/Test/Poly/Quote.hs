{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Quote
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Pipeline (FragmentDecl(..))
import Strat.Poly.Doctrine
  ( BinderSig(..)
  , Doctrine(..)
  , GenDecl(..)
  , InputShape(..)
  )
import Strat.Poly.Graph
  ( BinderArg(..)
  , Diagram(..)
  , EdgePayload(..)
  , addEdgePayload
  , emptyDiagram
  , freshPort
  , validateDiagram
  )
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
import Strat.Poly.Quote
  ( SharedBinding(..)
  , SharedBindingKind(..)
  , SharedProgram(..)
  , quoteProgram
  )
import Test.Poly.Helpers (mkModes, withSelfClassifiedCtors)


tests :: TestTree
tests =
  testGroup
    "Poly.Quote"
    [ testCase "quotation is deterministic" testDeterminism
    , testCase "included generators are memoized structurally" testIncludedMemoized
    , testCase "excluded generators stay residual and duplicated" testExcludedDuplicated
    , testCase "cross binders false leaves nested syntax residual" testCrossBindersFalse
    , testCase "cross binders true recursively quotes nested syntax" testCrossBindersTrue
    ]


testDeterminism :: Assertion
testDeterminism = do
  let doc = mkDoctrine
  diag <- require mkRepeatedNullaryDiag
  q1 <- require (quoteProgram doc modeM (mkFragment ["a", "f"] False) diag)
  q2 <- require (quoteProgram doc modeM (mkFragment ["a", "f"] False) diag)
  q1 @?= q2


testIncludedMemoized :: Assertion
testIncludedMemoized = do
  let doc = mkDoctrine
  diag <- require mkRepeatedNullaryDiag
  quoted <- require (quoteProgram doc modeM (mkFragment ["a", "f"] False) diag)
  assertEqual "expected one included a binding" 1 (countBinding SBIncluded "a" quoted)
  assertEqual "expected one included f binding" 1 (countBinding SBIncluded "f" quoted)
  assertEqual "expected no residual f bindings" 0 (countBinding SBResidual "f" quoted)


testExcludedDuplicated :: Assertion
testExcludedDuplicated = do
  let doc = mkDoctrine
  diag <- require mkRepeatedNullaryDiag
  quoted <- require (quoteProgram doc modeM (mkFragment ["a"] False) diag)
  assertEqual "expected one included a binding" 1 (countBinding SBIncluded "a" quoted)
  assertEqual "expected two residual f bindings" 2 (countBinding SBResidual "f" quoted)


testCrossBindersFalse :: Assertion
testCrossBindersFalse = do
  let doc = mkDoctrine
  diag <- require mkWrapDiag
  quoted <- require (quoteProgram doc modeM (mkFragment ["a"] False) diag)
  inner <- requireInnerProgram quoted
  assertEqual "expected nested a binding to stay residual" 1 (countBinding SBResidual "a" inner)
  assertEqual "expected nested a binding not to be included" 0 (countBinding SBIncluded "a" inner)


testCrossBindersTrue :: Assertion
testCrossBindersTrue = do
  let doc = mkDoctrine
  diag <- require mkWrapDiag
  quoted <- require (quoteProgram doc modeM (mkFragment ["a"] True) diag)
  inner <- requireInnerProgram quoted
  assertEqual "expected nested a binding to be included" 1 (countBinding SBIncluded "a" inner)
  assertEqual "expected no residual nested a binding" 0 (countBinding SBResidual "a" inner)


countBinding :: SharedBindingKind -> Text -> SharedProgram -> Int
countBinding kind name program =
  length
    [ ()
    | BindGen { sbKind = bindingKind, sbGen = GenName gen } <- spBindings program
    , bindingKind == kind
    , gen == name
    ]


requireInnerProgram :: SharedProgram -> IO SharedProgram
requireInnerProgram program =
  case spBindings program of
    [BindGen { sbGen = GenName "wrap", sbBinders = [inner] }] -> pure inner
    other -> assertFailure ("expected one residual wrap binding, got " <> show other) >> fail "unreachable"


mkRepeatedNullaryDiag :: Either Text Diagram
mkRepeatedNullaryDiag = do
  let (pA1, d0) = freshPort tyT (emptyDiagram modeM [])
  let (pF1, d1) = freshPort tyT d0
  let (pA2, d2) = freshPort tyT d1
  let (pF2, d3) = freshPort tyT d2
  d4 <- addEdgePayload (PGen (GenName "a") [] []) [] [pA1] d3
  d5 <- addEdgePayload (PGen (GenName "f") [] []) [pA1] [pF1] d4
  d6 <- addEdgePayload (PGen (GenName "a") [] []) [] [pA2] d5
  d7 <- addEdgePayload (PGen (GenName "f") [] []) [pA2] [pF2] d6
  let diag = d7 { dIn = [], dOut = [pF1, pF2] }
  validateDiagram diag
  pure diag


mkWrapDiag :: Either Text Diagram
mkWrapDiag = do
  let (pOut, d0) = freshPort tyT (emptyDiagram modeM [])
  inner <- mkInnerA
  d1 <- addEdgePayload (PGen (GenName "wrap") [] [BAConcrete inner]) [] [pOut] d0
  let diag = d1 { dIn = [], dOut = [pOut] }
  validateDiagram diag
  pure diag


mkInnerA :: Either Text Diagram
mkInnerA = do
  let (pOut, d0) = freshPort tyT (emptyDiagram modeM [])
  d1 <- addEdgePayload (PGen (GenName "a") [] []) [] [pOut] d0
  let diag = d1 { dIn = [], dOut = [pOut] }
  validateDiagram diag
  pure diag


mkDoctrine :: Doctrine
mkDoctrine =
  withSelfClassifiedCtors
    [(modeM, [(ObjName "T", [])])]
    Doctrine
      { dName = "D"
      , dModes = mkModes [modeM]
      , dAcyclicModes = S.singleton modeM
            , dGens =
          M.fromList
            [ ( modeM
              , M.fromList
                  [ (GenName "a", genNullary "a")
                  , (GenName "f", genUnary "f")
                  , (GenName "wrap", genWrap)
                  ]
              )
            ]
      , dCells2 = []
      , dActions = M.empty
      , dObligations = []
      }


genNullary :: Text -> GenDecl
genNullary name =
  GenDecl
    { gdName = GenName name
    , gdMode = modeM
    , gdParams = []
    , gdDom = []
    , gdCod = [tyT]
    , gdLiteralKind = Nothing
    }


genUnary :: Text -> GenDecl
genUnary name =
  GenDecl
    { gdName = GenName name
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT]
    , gdCod = [tyT]
    , gdLiteralKind = Nothing
    }


genWrap :: GenDecl
genWrap =
  GenDecl
    { gdName = GenName "wrap"
    , gdMode = modeM
    , gdParams = []
    , gdDom =
        [ InBinder
            BinderSig
              { bsTmCtx = []
              , bsDom = []
              , bsCod = [tyT]
              }
        ]
    , gdCod = [tyT]
    , gdLiteralKind = Nothing
    }


mkFragment :: [Text] -> Bool -> FragmentDecl
mkFragment included crossBinders =
  FragmentDecl
    { frName = "Frag"
    , frBase = "D"
    , frMode = "M"
    , frIncludedGens = S.fromList [ GenName name | name <- included ]
    , frCrossBinders = crossBinders
    , frCrossBoxes = False
    , frCrossFeedback = False
    }


modeM :: ModeName
modeM = ModeName "M"


tyT :: Obj
tyT = mkCon (ObjRef modeM (ObjName "T")) []


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
