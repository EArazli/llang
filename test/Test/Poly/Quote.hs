{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Quote
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Pipeline (FragmentDecl(..), FragmentProduct(..), FragmentRole(..), defaultQuotePolicy)
import Strat.Poly.Doctrine
import Strat.Poly.Graph (Diagram(..), EdgePayload(..), PortId, addEdgePayload, emptyDiagram, freshPort, validateDiagram)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
import Strat.Poly.Quote (SharedBinding(..), SharedProgram(..), canonicalizeDiagram, quoteProgram)
import Test.Poly.Helpers (mkModes, withSelfClassifiedCtors)


tests :: TestTree
tests =
  testGroup
    "Poly.Quote"
    [ testCase "quotation is deterministic" testDeterminism
    , testCase "port naming keeps unsuffixed boundary/internal names" testUnsuffixedPortNames
    , testCase "duplicate role is internalized" testDuplicateRoleInternalized
    , testCase "exact repeated shareable subterms are memoized" testExactShareMemoized
    , testCase "residual repeated subterms stay duplicated" testResidualRepeatedDuplicated
    , testCase "declared product witnesses eliminate pack-then-project churn" testProductWitnessEliminatesProjectionChurn
    ]


testDeterminism :: Assertion
testDeterminism = do
  let doc = mkDoctrine
  diag <- require (mkTwoStepDiag)
  q1 <- require (quoteProgram defaultQuotePolicy doc modeM fragmentResidual diag)
  q2 <- require (quoteProgram defaultQuotePolicy doc modeM fragmentResidual diag)
  q1 @?= q2


testUnsuffixedPortNames :: Assertion
testUnsuffixedPortNames = do
  let doc = mkDoctrine
  diag <- require mkTwoStepDiag
  quoted <- require (quoteProgram defaultQuotePolicy doc modeM fragmentResidual diag)
  let names = M.elems (spPortNames quoted)
  assertBool "expected boundary name p0" ("p0" `elem` names)
  assertBool "expected boundary name p1" ("p1" `elem` names)
  assertBool "expected internal name t0" ("t0" `elem` names)
  assertBool "did not expect suffixed t0_1" ("t0_1" `notElem` names)


testDuplicateRoleInternalized :: Assertion
testDuplicateRoleInternalized = do
  let doc = mkDoctrine
  diag <- require mkRepeatedFDiag
  quoted <- require (quoteProgram defaultQuotePolicy doc modeM fragmentShare diag)
  assertEqual "expected no binding for duplicate role" 0 (countBinding "dup" quoted)


testExactShareMemoized :: Assertion
testExactShareMemoized = do
  let doc = mkDoctrine
  diag <- require mkRepeatedFDiag
  quoted <- require (quoteProgram defaultQuotePolicy doc modeM fragmentShare diag)
  assertEqual "expected one shared binding_f" 1 (countBinding "f" quoted)


testResidualRepeatedDuplicated :: Assertion
testResidualRepeatedDuplicated = do
  let doc = mkDoctrine
  diag <- require mkRepeatedFDiag
  quoted <- require (quoteProgram defaultQuotePolicy doc modeM fragmentResidualizedF diag)
  assertEqual "expected repeated residual binding_f" 2 (countBinding "f" quoted)


testProductWitnessEliminatesProjectionChurn :: Assertion
testProductWitnessEliminatesProjectionChurn = do
  let doc = mkDoctrine
  diag <- require mkPackProjectDiag
  quoted <- require (quoteProgram defaultQuotePolicy doc modeM fragmentProduct diag)
  assertEqual "expected pack-then-project to disappear" [] (spBindings quoted)
  assertEqual "expected final outputs to alias original inputs" ["p0", "p1"] (map (refName (spPortNames quoted)) (spOutputs quoted))


countBinding :: Text -> SharedProgram -> Int
countBinding name program =
  length
    [ ()
    | BindGen { sbGen = GenName gen } <- spBindings program
    , gen == name
    ]


mkTwoStepDiag :: Either Text Diagram
mkTwoStepDiag = do
  let (pIn, d0) = freshPort tyT (emptyDiagram modeM [])
  let (pMid, d1) = freshPort tyT d0
  let (pOut, d2) = freshPort tyT d1
  d3 <- addEdgePayload (PGen (GenName "b") M.empty []) [pIn] [pMid] d2
  d4 <- addEdgePayload (PGen (GenName "b") M.empty []) [pMid] [pOut] d3
  let diag = d4 { dIn = [pIn], dOut = [pOut] }
  validateDiagram diag
  pure diag


mkRepeatedFDiag :: Either Text Diagram
mkRepeatedFDiag = do
  let (pIn, d0) = freshPort tyT (emptyDiagram modeM [])
  let (pDupL, d1) = freshPort tyT d0
  let (pDupR, d2) = freshPort tyT d1
  let (pOutL, d3) = freshPort tyT d2
  let (pOutR, d4) = freshPort tyT d3
  d5 <- addEdgePayload (PGen (GenName "dup") M.empty []) [pIn] [pDupL, pDupR] d4
  d6 <- addEdgePayload (PGen (GenName "f") M.empty []) [pDupL] [pOutL] d5
  d7 <- addEdgePayload (PGen (GenName "f") M.empty []) [pDupR] [pOutR] d6
  let diag = d7 { dIn = [pIn], dOut = [pOutL, pOutR] }
  diag' <- canonicalizeDiagram diag
  validateDiagram diag'
  pure diag'


mkDoctrine :: Doctrine
mkDoctrine =
  withSelfClassifiedCtors
    [(modeM, [(ObjName "T", [])])]
    Doctrine
      { dName = "D"
      , dModes = mkModes [modeM]
      , dAcyclicModes = S.singleton modeM
      , dAttrSorts = M.empty
      , dGens =
          M.fromList
            [ ( modeM
              , M.fromList
                  [ (GenName "b", genUnary "b")
                  , (GenName "dup", genDup)
                  , (GenName "f", genUnary "f")
                  , (GenName "mkPair", genPair)
                  , (GenName "fst", genFst)
                  , (GenName "snd", genSnd)
                  ]
              )
            ]
      , dCells2 = []
      , dActions = M.empty
      , dObligations = []
      }


genUnary :: Text -> GenDecl
genUnary name =
  GenDecl
    { gdName = GenName name
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT]
    , gdCod = [tyT]
    , gdAttrs = []
    }


genDup :: GenDecl
genDup =
  GenDecl
    { gdName = GenName "dup"
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT]
    , gdCod = [tyT, tyT]
    , gdAttrs = []
    }


genPair :: GenDecl
genPair =
  GenDecl
    { gdName = GenName "mkPair"
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT, InPort tyT]
    , gdCod = [tyT]
    , gdAttrs = []
    }


genFst :: GenDecl
genFst =
  GenDecl
    { gdName = GenName "fst"
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT]
    , gdCod = [tyT]
    , gdAttrs = []
    }


genSnd :: GenDecl
genSnd =
  GenDecl
    { gdName = GenName "snd"
    , gdMode = modeM
    , gdParams = []
    , gdDom = [InPort tyT]
    , gdCod = [tyT]
    , gdAttrs = []
    }


fragmentResidual :: FragmentDecl
fragmentResidual =
  FragmentDecl
    { frName = "FragResidual"
    , frBase = "D"
    , frMode = "M"
    , frGenRoles = M.empty
    , frProducts = []
    , frRecurseBinders = False
    , frRecurseBoxes = False
    , frRecurseFeedback = False
    }


fragmentResidualizedF :: FragmentDecl
fragmentResidualizedF =
  fragmentResidual
    { frName = "FragResidualizedF"
    , frGenRoles = M.fromList [(GenName "dup", FragDuplicate)]
    }


fragmentShare :: FragmentDecl
fragmentShare =
  fragmentResidual
    { frName = "FragShare"
    , frGenRoles =
        M.fromList
          [ (GenName "dup", FragDuplicate)
          , (GenName "f", FragShare)
          ]
    }


fragmentProduct :: FragmentDecl
fragmentProduct =
  fragmentResidual
    { frName = "FragProduct"
    , frGenRoles = M.fromList [(GenName "dup", FragDuplicate)]
    , frProducts =
        [ FragmentProduct
            { fpPairCtor = GenName "mkPair"
            , fpProjLeft = GenName "fst"
            , fpProjRight = GenName "snd"
            }
        ]
    }


modeM :: ModeName
modeM = ModeName "M"


tyT :: Obj
tyT = mkCon (ObjRef modeM (ObjName "T")) []


mkPackProjectDiag :: Either Text Diagram
mkPackProjectDiag = do
  let (pInL, d0) = freshPort tyT (emptyDiagram modeM [])
  let (pInR, d1) = freshPort tyT d0
  let (pPair, d2) = freshPort tyT d1
  let (pDupL, d3) = freshPort tyT d2
  let (pDupR, d4) = freshPort tyT d3
  let (pOutL, d5) = freshPort tyT d4
  let (pOutR, d6) = freshPort tyT d5
  d7 <- addEdgePayload (PGen (GenName "mkPair") M.empty []) [pInL, pInR] [pPair] d6
  d8 <- addEdgePayload (PGen (GenName "dup") M.empty []) [pPair] [pDupL, pDupR] d7
  d9 <- addEdgePayload (PGen (GenName "fst") M.empty []) [pDupL] [pOutL] d8
  d10 <- addEdgePayload (PGen (GenName "snd") M.empty []) [pDupR] [pOutR] d9
  let diag = d10 { dIn = [pInL, pInR], dOut = [pOutL, pOutR] }
  validateDiagram diag
  pure diag


refName :: M.Map PortId Text -> PortId -> Text
refName names pid =
  case M.lookup pid names of
    Nothing -> error "missing quoted port name in test"
    Just name -> name


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
