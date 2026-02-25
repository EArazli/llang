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
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.Doctrine (Doctrine, doctrineTypeTheory)
import Strat.Poly.ModeTheory (ModeName(..), DefEqEngine(..))
import Strat.Poly.TypeTheory (TypeTheory, defEqEngineForMode)
import Strat.Poly.Obj
  ( Obj
  , ObjName(..)
  , ObjRef(..)
  , TermDiagram(..)
  , CodeArg(..)
  , mkCon
  )
import Strat.Poly.DefEq (normalizeTermDiagram)
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
        && "missing required lam generator" `T.isInfixOf` err
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
