{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.NBE
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , BinderSig(..)
  , InputShape(..)
  , GenParam(..)
  , GenDecl(..)
  , deriveCtorTables
  , doctrineTypeTheory
  )
import Strat.Poly.ModeTheory
  ( ModeTheory
  , ModeName(..)
  , DefEqEngine(..)
  , ClassificationDecl(..)
  , emptyModeTheory
  , addMode
  , addClassification
  , setModeDefEqEngine
  )
import Strat.Poly.TypeTheory (TypeTheory, defEqEngineForMode)
import Strat.Poly.Obj
  ( Obj
  , ObjName(..)
  , ObjRef(..)
  , TmVar(..)
  , TermDiagram(..)
  , CodeArg(..)
  , mkCon
  )
import Strat.Poly.DefEq (normalizeTermDiagram)
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram, diagramToTermExpr)
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , BinderArg(..)
  , BinderMetaVar(..)
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , validateDiagram
  )
import Strat.Poly.Diagram (idDTm)
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Names (GenName(..))


tests :: TestTree
tests =
  testGroup
    "Poly.NBE"
    [ testCase "mode defeq nbe selects NbE fragment" testModeDeclSelectsNBE
    , testCase "NbE beta: app(lam(\\x. x), t) normalizes to t" testNBEBeta
    , testCase "NbE eta: function variable normalizes to eta-long form" testNBEEta
    , testCase "NbE nested binders avoid capture" testNBENestedBinders
    , testCase "NbE mode missing lam is rejected at doctrine build" testNBEMissingLamRejected
    , testCase "NbE rejects splice payloads in definitional normalization" testNBERejectsSplice
    , testCase "deriveCtorTables uses NbE for constructor eligibility" testCtorEligibilityUsesNBE
    , testCase "deriveCtorTables surfaces eligibility defeq failures with context" testCtorEligibilityDefEqErrorContext
    , testCase "deriveCtorTables rejects malformed NbE lam config at eligibility validation time" testCtorEligibilityLamShapeRejected
    , testCase "doctrineTypeTheory rejects NbE mode missing Arr constructor" testCtorEligibilityMissingArrRejected
    , testCase "NbE normalization accepts definitionally equal output sorts" testNBEOutputSortDefEq
    , testCase "meta spines support non-prefix arguments and remain stable through NbE" testMetaSpineNonPrefixStable
    , testCase "TRS mode still enforces termination checks" testTRSStillChecked
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

lookupDoctrineByName :: Text -> ModuleEnv -> IO Doctrine
lookupDoctrineByName name env =
  case M.lookup name (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> fail "unreachable"
    Just d -> pure d

modeM :: ModeName
modeM = ModeName "M"

arrTy :: Obj -> Obj -> Obj
arrTy domTy codTy =
  mkCon
    (ObjRef modeM (ObjName "Arr"))
    [ CAObj domTy
    , CAObj codTy
    ]

mkNbeTypeTheory :: IO (TypeTheory, Obj, Obj)
mkNbeTypeTheory = do
  env <- require (parseRawFile nbeDoctrineSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "NBEMode" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let bTy = mkCon (ObjRef modeM (ObjName "B")) []
  pure (tt, aTy, bTy)

mkLamIdBody :: Obj -> Either Text Diagram
mkLamIdBody aTy = do
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let body = d0 { dIn = [x], dOut = [x] }
  validateDiagram body
  pure body

mkBetaInput :: Obj -> Either Text TermDiagram
mkBetaInput aTy = do
  body <- mkLamIdBody aTy
  let aToA = arrTy aTy aTy
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let (lamOut, d1) = freshPort aToA d0
  let (y, d2) = freshPort aTy d1
  d3 <- addEdgePayload (PGen (GenName "lam") M.empty [BAConcrete body]) [] [lamOut] d2
  d4 <- addEdgePayload (PGen (GenName "app") M.empty []) [lamOut, x] [y] d3
  let diag = d4 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure (TermDiagram diag)

mkNestedInput :: Obj -> Either Text TermDiagram
mkNestedInput aTy = do
  let aToA = arrTy aTy aTy
  let aToAToA = arrTy aTy aToA

  let (yPort, c0) = freshPort aTy (emptyDiagram modeM [])
  let (xPort, c1) = freshPort aTy c0
  c2 <- addEdgePayload PInternalDrop [yPort] [] c1
  let body2 = c2 { dIn = [yPort, xPort], dOut = [xPort] }
  validateDiagram body2

  let (xOuter, b0) = freshPort aTy (emptyDiagram modeM [])
  let (lam2Out, b1) = freshPort aToA b0
  b2 <- addEdgePayload (PGen (GenName "lam") M.empty [BAConcrete body2]) [] [lam2Out] b1
  b3 <- addEdgePayload PInternalDrop [xOuter] [] b2
  let body1 = b3 { dIn = [xOuter], dOut = [lam2Out] }
  validateDiagram body1

  let (t1, d0) = freshPort aTy (emptyDiagram modeM [])
  let (t2, d1) = freshPort aTy d0
  let (lam1Out, d2) = freshPort aToAToA d1
  let (mid, d3) = freshPort aToA d2
  let (out, d4) = freshPort aTy d3
  d5 <- addEdgePayload (PGen (GenName "lam") M.empty [BAConcrete body1]) [] [lam1Out] d4
  d6 <- addEdgePayload (PGen (GenName "app") M.empty []) [lam1Out, t1] [mid] d5
  d7 <- addEdgePayload (PGen (GenName "app") M.empty []) [mid, t2] [out] d6
  let diag = d7 { dIn = [t1, t2], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

testModeDeclSelectsNBE :: Assertion
testModeDeclSelectsNBE = do
  (tt, _aTy, _bTy) <- mkNbeTypeTheory
  defEqEngineForMode tt modeM @?= DefEqNBE

testNBEBeta :: Assertion
testNBEBeta = do
  (tt, aTy, _bTy) <- mkNbeTypeTheory
  tm <- require (mkBetaInput aTy)
  norm <- require (normalizeTermDiagram tt [aTy] aTy tm)
  let want = idDTm modeM [aTy] [aTy]
  ok <- require (diagramIsoEq (unTerm norm) want)
  assertBool "expected beta normal form to be the input variable" ok

testNBEEta :: Assertion
testNBEEta = do
  (tt, aTy, bTy) <- mkNbeTypeTheory
  let aToB = arrTy aTy bTy
  let tm = TermDiagram (idDTm modeM [aToB] [aToB])
  norm <- require (normalizeTermDiagram tt [aToB] aToB tm)
  let normDiag = unTerm norm
  let topEdges = IM.elems (dEdges normDiag)
  let lamBodies =
        [ body
        | Edge _ (PGen g _ [BAConcrete body]) _ _ <- topEdges
        , g == GenName "lam"
        ]
  assertBool "expected exactly one top-level lam in eta normal form" (length lamBodies == 1)
  assertBool "expected top-level eta normal form to drop unused outer function input" (any isDrop topEdges)
  case lamBodies of
    [body] ->
      let bodyEdges = IM.elems (dEdges body)
       in assertBool "expected lambda body to contain app node" (any isApp bodyEdges)
    _ ->
      pure ()
  where
    isDrop edge =
      case ePayload edge of
        PInternalDrop -> True
        _ -> False

    isApp edge =
      case ePayload edge of
        PGen g _ [] -> g == GenName "app"
        _ -> False

testNBENestedBinders :: Assertion
testNBENestedBinders = do
  (tt, aTy, _bTy) <- mkNbeTypeTheory
  tm <- require (mkNestedInput aTy)
  norm <- require (normalizeTermDiagram tt [aTy, aTy] aTy tm)
  let normDiag = unTerm norm
  case (dIn normDiag, dOut normDiag) of
    (in0:in1:[], [out0]) -> do
      out0 @?= in0
      let dropped =
            [ ()
            | Edge _ PInternalDrop [pid] [] <- IM.elems (dEdges normDiag)
            , pid == in1
            ]
      assertBool "expected second boundary input to be dropped after nested beta" (length dropped == 1)
    _ ->
      assertFailure ("unexpected normalized boundary shape: " <> show normDiag)

testNBEMissingLamRejected :: Assertion
testNBEMissingLamRejected =
  case parseRawFile nbeMissingLamSrc >>= elabRawFile of
    Left err ->
      assertBool
        ("expected missing-lam NbE validation error, got: " <> T.unpack err)
        (  "NbE mode" `T.isInfixOf` err
        && "cannot infer NbE primitives (lambda/application/arrow type) from generator signatures" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrine elaboration to reject NbE mode without lam"

testNBERejectsSplice :: Assertion
testNBERejectsSplice = do
  (tt, aTy, _bTy) <- mkNbeTypeTheory
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let (y, d1) = freshPort aTy d0
  d2 <- require (addEdgePayload (PSplice (BinderMetaVar "b0")) [x] [y] d1)
  let diag = d2 { dIn = [x], dOut = [y] }
  _ <- require (validateDiagram diag)
  let tm = TermDiagram diag
  case normalizeTermDiagram tt [aTy] aTy tm of
    Left err ->
      assertBool
        ("expected unsupported splice error, got: " <> T.unpack err)
        ("splice nodes are unsupported" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected NbE normalization to reject splice payload"

testMetaSpineNonPrefixStable :: Assertion
testMetaSpineNonPrefixStable = do
  (tt, aTy, _bTy) <- mkNbeTypeTheory
  let tmCtx = [aTy, aTy, aTy]
      mv =
        TmVar
          { tmvName = "m"
          , tmvSort = aTy
          , tmvScope = 3
          , tmvOwnerMode = Just modeM
          }
      tmExpr = TMMeta mv [0, 2]
  tm0 <- require (termExprToDiagram tt tmCtx aTy tmExpr)
  expr0 <- require (diagramToTermExpr tt tmCtx aTy tm0)
  expr0 @?= tmExpr
  norm <- require (normalizeTermDiagram tt tmCtx aTy tm0)
  exprNorm <- require (diagramToTermExpr tt tmCtx aTy norm)
  exprNorm @?= tmExpr
  tm1 <- require (termExprToDiagram tt tmCtx aTy exprNorm)
  ok <- require (diagramIsoEq (unTerm norm) (unTerm tm1))
  assertBool "expected meta-spine term->graph roundtrip stability after NbE" ok

testTRSStillChecked :: Assertion
testTRSStillChecked =
  case parseRawFile mixedNbeTrsSrc >>= elabRawFile of
    Left err ->
      assertBool
        ("expected TRS termination failure, got: " <> T.unpack err)
        (  "termination not proven" `T.isInfixOf` err
        && "ModeName \"I\"" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrine elaboration to reject non-terminating TRS mode"

modeTy :: ModeName
modeTy = ModeName "Ty"

modeTm :: ModeName
modeTm = ModeName "Tm"

mkEligibilityModeTheory :: Obj -> Either Text ModeTheory
mkEligibilityModeTheory tmUniverse = do
  mt0 <- addMode modeTy emptyModeTheory
  mt1 <- addMode modeTm mt0
  mt2 <- setModeDefEqEngine modeTy DefEqNBE mt1
  let tyUniverse = mkCon (ObjRef modeTy (ObjName "U_Ty")) []
  mt3 <-
    addClassification
      modeTy
      ClassificationDecl
        { cdClassifier = modeTy
        , cdUniverse = tyUniverse
        
        , cdComp = Nothing
        }
      mt2
  addClassification
    modeTm
    ClassificationDecl
      { cdClassifier = modeTy
      , cdUniverse = tmUniverse
      
      , cdComp = Nothing
      }
    mt3

mkConstClosedTerm :: ModeName -> Obj -> GenName -> Either Text TermDiagram
mkConstClosedTerm mode sortTy g = do
  let (out, d0) = freshPort sortTy (emptyDiagram mode [])
  d1 <- addEdgePayload (PGen g M.empty []) [] [out] d0
  let diag = d1 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkLamIdBodyFor :: ModeName -> Obj -> Either Text Diagram
mkLamIdBodyFor mode aTy = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let body = d0 { dIn = [x], dOut = [x] }
  validateDiagram body
  pure body

mkClosedBetaTerm
  :: ModeName
  -> Obj
  -> Obj
  -> GenName
  -> GenName
  -> GenName
  -> Either Text TermDiagram
mkClosedBetaTerm mode natTy arrNatNat lamName appName zName = do
  body <- mkLamIdBodyFor mode natTy
  let (lamOut, d0) = freshPort arrNatNat (emptyDiagram mode [])
  let (zOut, d1) = freshPort natTy d0
  let (out, d2) = freshPort natTy d1
  d3 <- addEdgePayload (PGen lamName M.empty [BAConcrete body]) [] [lamOut] d2
  d4 <- addEdgePayload (PGen zName M.empty []) [] [zOut] d3
  d5 <- addEdgePayload (PGen appName M.empty []) [lamOut, zOut] [out] d4
  let diag = d5 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkClosedSpliceTerm :: ModeName -> Obj -> GenName -> Either Text TermDiagram
mkClosedSpliceTerm mode sortTy seedGen = do
  let (mid, d0) = freshPort sortTy (emptyDiagram mode [])
  let (out, d1) = freshPort sortTy d0
  d2 <- addEdgePayload (PGen seedGen M.empty []) [] [mid] d1
  d3 <- addEdgePayload (PSplice (BinderMetaVar "s0")) [mid] [out] d2
  let diag = d3 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkEligibilityDoctrine :: Bool -> Either Text Doctrine
mkEligibilityDoctrine includeBad = do
  let uTyRef = ObjRef modeTy (ObjName "U_Ty")
  let natRef = ObjRef modeTy (ObjName "Nat")
  let wrapRef = ObjRef modeTy (ObjName "Wrap")
  let arrRef = ObjRef modeTy (ObjName "Arr")
  let uTy = mkCon uTyRef []
  let natTy = mkCon natRef []
  let arrNatNat = mkCon arrRef [CAObj natTy, CAObj natTy]

  zTm <- mkConstClosedTerm modeTy natTy (GenName "z")
  betaTm <- mkClosedBetaTerm modeTy natTy arrNatNat (GenName "lam") (GenName "app") (GenName "z")
  badTm <- mkClosedSpliceTerm modeTy natTy (GenName "z")
  let tmUniverse = mkCon wrapRef [CATm zTm]
  mt <- mkEligibilityModeTheory tmUniverse

  let aTyVar = TmVar { tmvName = "a", tmvSort = uTy, tmvScope = 0, tmvOwnerMode = Just modeTy }
  let bTyVar = TmVar { tmvName = "b", tmvSort = uTy, tmvScope = 0, tmvOwnerMode = Just modeTy }
  let nTmVar = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Just modeTy }

  let mkCtor name cod =
        GenDecl
          { gdName = GenName name
          , gdMode = modeTy
          , gdParams = []
          , gdDom = []
          , gdCod = [cod]
          , gdAttrs = []
          }

  let gUTy = mkCtor "U_Ty" uTy
  let gNat = mkCtor "Nat" uTy
  let gZ = mkCtor "z" natTy
  let gBeta = mkCtor "Beta" (mkCon wrapRef [CATm betaTm])

  let gWrap =
        GenDecl
          { gdName = GenName "Wrap"
          , gdMode = modeTy
          , gdParams = [GP_Tm nTmVar]
          , gdDom = []
          , gdCod = [uTy]
          , gdAttrs = []
          }

  let gArr =
        GenDecl
          { gdName = GenName "Arr"
          , gdMode = modeTy
          , gdParams = [GP_Ty aTyVar, GP_Ty bTyVar]
          , gdDom = []
          , gdCod = [uTy]
          , gdAttrs = []
          }

  let lamBody = BinderSig { bsTmCtx = [], bsDom = [natTy], bsCod = [natTy] }
  let gLam =
        GenDecl
          { gdName = GenName "lam"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = [InBinder lamBody]
          , gdCod = [arrNatNat]
          , gdAttrs = []
          }

  let gApp =
        GenDecl
          { gdName = GenName "app"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = [InPort arrNatNat, InPort natTy]
          , gdCod = [natTy]
          , gdAttrs = []
          }

  let gBad =
        GenDecl
          { gdName = GenName "Bad"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = []
          , gdCod = [mkCon wrapRef [CATm badTm]]
          , gdAttrs = []
          }

  let gens =
        [ gUTy
        , gNat
        , gWrap
        , gArr
        , gLam
        , gApp
        , gZ
        , gBeta
        ]
          <> [gBad | includeBad]
  pure
    Doctrine
      { dName = "CtorEligibilityNBE"
      , dModes = mt
      , dAcyclicModes = S.empty
      , dAttrSorts = M.empty
      , dGens = M.fromList [(modeTy, M.fromList [(gdName gd, gd) | gd <- gens])]
      , dCells2 = []
      , dActions = M.empty
      , dObligations = []
      }

mkMissingArrDoctrine :: Either Text Doctrine
mkMissingArrDoctrine = do
  mt0 <- addMode modeTy emptyModeTheory
  mt1 <- setModeDefEqEngine modeTy DefEqNBE mt0
  let uTy = mkCon (ObjRef modeTy (ObjName "U_Ty")) []
  mt <-
    addClassification
      modeTy
      ClassificationDecl
        { cdClassifier = modeTy
        , cdUniverse = uTy
        
        , cdComp = Nothing
        }
      mt1
  let natTy = mkCon (ObjRef modeTy (ObjName "Nat")) []
  let gUTy =
        GenDecl
          { gdName = GenName "U_Ty"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = []
          , gdCod = [uTy]
          , gdAttrs = []
          }
  let gNat =
        GenDecl
          { gdName = GenName "Nat"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = []
          , gdCod = [uTy]
          , gdAttrs = []
          }
  let arrNatNat = mkCon (ObjRef modeTy (ObjName "Arr")) [CAObj natTy, CAObj natTy]
  let lamBody = BinderSig { bsTmCtx = [], bsDom = [natTy], bsCod = [natTy] }
  let gLam =
        GenDecl
          { gdName = GenName "lam"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = [InBinder lamBody]
          , gdCod = [arrNatNat]
          , gdAttrs = []
          }
  let gApp =
        GenDecl
          { gdName = GenName "app"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = [InPort arrNatNat, InPort natTy]
          , gdCod = [natTy]
          , gdAttrs = []
          }
  pure
    Doctrine
      { dName = "MissingArrInEligibility"
      , dModes = mt
      , dAcyclicModes = S.empty
      , dAttrSorts = M.empty
      , dGens = M.fromList [(modeTy, M.fromList [(gdName gd, gd) | gd <- [gUTy, gNat, gLam, gApp]])]
      , dCells2 = []
      , dActions = M.empty
      , dObligations = []
      }

testCtorEligibilityUsesNBE :: Assertion
testCtorEligibilityUsesNBE = do
  doc <- require (mkEligibilityDoctrine False)
  tables <- require (deriveCtorTables doc)
  let tmTable = M.findWithDefault M.empty modeTm tables
  assertBool "expected Beta constructor in Tm owner vocabulary under NbE eligibility" (M.member (ObjName "Beta") tmTable)

testCtorEligibilityDefEqErrorContext :: Assertion
testCtorEligibilityDefEqErrorContext = do
  doc <- require (mkEligibilityDoctrine True)
  case deriveCtorTables doc of
    Left err ->
      assertBool
        ("expected contextual ctor eligibility error, got: " <> T.unpack err)
        (  "constructor eligibility defeq failed" `T.isInfixOf` err
        && "Ty.Bad" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected deriveCtorTables to surface eligibility defeq failure for Bad constructor"

mkEligibilityDoctrineMalformedLam :: Either Text Doctrine
mkEligibilityDoctrineMalformedLam = do
  doc <- mkEligibilityDoctrine False
  modeGens <-
    case M.lookup modeTy (dGens doc) of
      Just gs -> Right gs
      Nothing -> Left "missing Ty mode generator table"
  lamDecl <-
    case M.lookup (GenName "lam") modeGens of
      Just gd -> Right gd
      Nothing -> Left "missing lam generator declaration"
  let lamDecl2 = lamDecl { gdName = GenName "lam2" }
  let modeGens' = M.insert (gdName lamDecl2) lamDecl2 modeGens
  pure doc { dGens = M.insert modeTy modeGens' (dGens doc) }

testCtorEligibilityLamShapeRejected :: Assertion
testCtorEligibilityLamShapeRejected = do
  doc <- require mkEligibilityDoctrineMalformedLam
  case deriveCtorTables doc of
    Left err ->
      assertBool
        ("expected malformed lam config error during ctor eligibility validation, got: " <> T.unpack err)
        ("has ambiguous NbE primitives" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected deriveCtorTables to reject malformed NbE lam config"

testCtorEligibilityMissingArrRejected :: Assertion
testCtorEligibilityMissingArrRejected = do
  doc <- require mkMissingArrDoctrine
  case doctrineTypeTheory doc of
    Left err ->
      assertBool
        ("expected missing Arr NbE validation error, got: " <> T.unpack err)
        (  "missing arrow type constructor" `T.isInfixOf` err
        && "Arr" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrineTypeTheory to reject NbE mode without Arr constructor"

testNBEOutputSortDefEq :: Assertion
testNBEOutputSortDefEq = do
  doc <- require (mkEligibilityDoctrine False)
  tt <- require (doctrineTypeTheory doc)
  let natTy = mkCon (ObjRef modeTy (ObjName "Nat")) []
  let arrNatNat = mkCon (ObjRef modeTy (ObjName "Arr")) [CAObj natTy, CAObj natTy]
  let wrapRef = ObjRef modeTy (ObjName "Wrap")
  zTm <- require (mkConstClosedTerm modeTy natTy (GenName "z"))
  betaTm <- require (mkClosedBetaTerm modeTy natTy arrNatNat (GenName "lam") (GenName "app") (GenName "z"))
  let expectedSort = mkCon wrapRef [CATm zTm]
  let metaSort = mkCon wrapRef [CATm betaTm]
  let v = TmVar { tmvName = "w", tmvSort = metaSort, tmvScope = 0, tmvOwnerMode = Just modeTy }
  let (out, d0) = freshPort metaSort (emptyDiagram modeTy [])
  d1 <- require (addEdgePayload (PTmMeta v) [] [out] d0)
  let diag = d1 { dIn = [], dOut = [out] }
  _ <- require (validateDiagram diag)
  _ <- require (normalizeTermDiagram tt [] expectedSort (TermDiagram diag))
  pure ()

nbeDoctrineSrc :: Text
nbeDoctrineSrc =
  T.unlines
    [ "doctrine NBEMode where {"
    , "  mode M defeq nbe classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen B : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

nbeMissingLamSrc :: Text
nbeMissingLamSrc =
  T.unlines
    [ "doctrine NBEMissingLam where {"
    , "  mode M defeq nbe classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

mixedNbeTrsSrc :: Text
mixedNbeTrsSrc =
  T.unlines
    [ "doctrine MixedNbeTrs where {"
    , "  mode M defeq nbe classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen m_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen m_var(a@M) : [a] -> [a] @M;"
    , "  gen m_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = m_ctx_ext; var = m_var; reindex = m_reindex; };"
    , ""
    , "  mode I defeq trs classifiedBy I via I.U_I;"
    , "  gen i_ctx_ext(a@I) : [a] -> [a] @I;"
    , "  gen i_var(a@I) : [a] -> [a] @I;"
    , "  gen i_reindex(a@I) : [a] -> [a] @I;"
    , "  comprehension I where { ctx_ext = i_ctx_ext; var = i_var; reindex = i_reindex; };"
    , "  gen U_I : [] -> [I.U_I] @I;"
    , "  gen Nat : [] -> [I.U_I] @I;"
    , "  gen f : [Nat] -> [Nat] @I;"
    , "  rule computational loop -> : [Nat] -> [Nat] @I ="
    , "    id[Nat] ; f == id[Nat] ; f"
    , "}"
    ]
