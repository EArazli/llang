{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Test.Poly.Dependent
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
import Strat.Frontend.Env (meDoctrines)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.ModeTheory (ModeName(..), ModExpr(..), addMode, emptyModeTheory)
import Strat.Poly.Doctrine (doctrineTypeTheory)
import Strat.Poly.Obj
  ( Obj(..)
  , mkModeMetaVar
  , mkCon
  , ObjArg
  , pattern OAObj
  , pattern OATm
  , TmVar
  , tmvName
  , tmVarOwner
  , ObjName(..)
  , ObjRef(..)
  , TmVar(..)
  , TermDiagram(..)
  , boundTmIndicesTerm
  )
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TmHeadSig(..)
  , TmRule(..)
  , modeOnlyTypeTheory
  , setModeTermHeads
  , setModeTermRules
  , setModeTermTRS
  )
import Strat.Poly.Tele (CtorSig(..), GenParam(..))
import Test.Poly.CtorSigCompat (TypeParamSig(..), flatParamsToCtorSig)
import Strat.Poly.DefEq (normalizeObjDeep, normalizeTermDiagram, validateTermDiagram)
import qualified Strat.Poly.DefEq as DE
import Strat.Poly.UnifyObj (unifyTm, unifyObjFlex, emptySubst, lookupTmMeta)
import Strat.Poly.Match (MatchConfig(..), findAllMatches)
import Strat.Poly.Graph
  ( Diagram(..)
  , BinderMetaVar(..)
  , BinderArg(..)
  , EdgePayload(..)
  , canonDiagramRaw
  , dIn
  , dOut
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , validateDiagram
  )
import Strat.Poly.DiagramIso (diagramIsoEq, diagramIsoMatchWithVars)
import Strat.Poly.Diagram (idD, genDTm, compD, freeVarsDiagram)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Rewrite (RewriteRule(..), rewriteOnce)
import Strat.Poly.Term.AST (TermHeadArg(..))
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram, diagramToTermExpr, diagramGraphToTermExpr)
import Strat.Poly.Term.RewriteCompile (compileAllTermRules)
import Test.Poly.Helpers (mkModes, withZeroParamGenArgSigs)


tests :: TestTree
tests =
  testGroup
    "Poly.Dependent"
    [ testCase "term normalization from doctrine rules reduces add(S(Z),S(Z))" testDoctrineNormalizeTypeArg
    , testCase "term normalization reduces add(S(Z),S(Z))" testNormalizeTm
    , testCase "term normalization is idempotent" testNormalizeTmIdempotent
    , testCase "doctrine rejects non-terminating term rewrite system" testRejectNonTerminatingTermTRS
    , testCase "doctrine rejects non-confluent term rewrite system" testRejectNonConfluentTermTRS
    , testCase "mixed-mode unlabeled tmctx inputs resolve to global indices" testMixedModeTmCtxResolution
    , testCase "bound index survives canonization without labels" testBoundIndexSurvivesCanonization
    , testCase "validateTermDiagram rejects sparse boundaries" testValidateTermDiagramRejectsSparseBoundary
    , testCase "scoped term unification rejects escapes" testScopedTmUnify
    , testCase "dependent unification normalizes term arguments" testDependentUnify
    , testCase "bound term sort checks apply current substitution" testBoundSortUsesSubstitution
    , testCase "matching applies current substitution to bound term sorts" testMatchBoundSortUsesCurrentSubst
    , testCase "dependent composition respects definitional term equality" testDependentCompDefEq
    , testCase "object defeq reduces term indices inside code terms" testDefEqObjTermIndexReduction
    , testCase "matching requires term-context compatibility" testMatchTmCtxCompatibility
    , testCase "matching accepts term-context compatibility up to defeq" testMatchTmCtxDefEqCompatibility
    , testCase "iso matching drops candidates when dependent substitution fails" testIsoMatchDropsSubstFailure
    , testCase "checked term conversion accepts definitional sort equality" testCheckedTermConversionDefEq
    , testCase "checked term conversion rejects bad generalized head sorts" testCheckedTermConversionRejectsBadHeadSort
    , testCase "binder metas + splice rewrite" testBinderMetaSplice
    , testCase "explicit binder term args can reference bound term vars" testExplicitBinderTermArg
    , testCase "rule head type args elaborate in surrounding type-variable scope" testRuleHeadTypeArgsSeeTyVars
    , testCase "generated comprehension laws terminate on dependent Id codomains" testDependentIdCompLaws
    , testCase "nested dependent term-head arguments elaborate without self-capture" testNestedDependentHeadArgElaborates
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

testDoctrineNormalizeTypeArg :: Assertion
testDoctrineNormalizeTypeArg = do
  let src = T.unlines
        [ "doctrine DepNorm where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen comp_var(a@M) : [a] -> [a] @M;"
        , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  mode I classifiedBy I via I.U_I;"
        , "  gen comp_ctx_ext(a@I) : [a] -> [a] @I;"
        , "  gen comp_var(a@I) : [a] -> [a] @I;"
        , "  gen comp_reindex(a@I) : [a] -> [a] @I;"
        , "  comprehension I where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  gen U_I : [] -> [I.U_I] @I;"
        , "  gen Nat : [] -> [I.U_I] @I;"
        , "  gen A : [] -> [M.U_M] @M;"
        , "  gen Vec(n : Nat, a@M) : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @I;"
        , "  gen S : [Nat] -> [Nat] @I;"
        , "  gen add : [Nat, Nat] -> [Nat] @I;"
        , "  rule computational addZ -> : [Nat] -> [Nat] @I ="
        , "    (Z * id[Nat]) ; add == id[Nat]"
        , "  rule computational addS -> : [Nat, Nat] -> [Nat] @I ="
        , "    (S * id[Nat]) ; add == add ; S"
        , "}"
        ]
  env <- require (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "DepNorm" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine DepNorm" >> fail "unreachable"
      Just d -> pure d
  tt <- require (doctrineTypeTheory doc)
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let vecRef = ObjRef modeM (ObjName "Vec")
  let natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
  let z = TMGen (GenName "Z") []
  let s x = TMGen (GenName "S") [THATm x]
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  tmArg <- require (termExprToDiagram tt [] natTy (add (s z) (s z)))
  wantTm <- require (termExprToDiagram tt [] natTy (s (s z)))
  let ty = mkCon vecRef [OATm tmArg, OAObj aTy]
  let want = mkCon vecRef [OATm wantTm, OAObj aTy]
  got <- require (normalizeObjDeep tt ty)
  case (got, want) of
    (OCon gotRef [OATm gotTm, OAObj gotA], OCon wantRef [OATm wantTm', OAObj wantA]) -> do
      gotRef @?= wantRef
      gotA @?= wantA
      gotExpr <- require (diagramToTermExpr tt [] natTy gotTm)
      wantExpr <- require (diagramToTermExpr tt [] natTy wantTm')
      gotExpr @?= wantExpr
    _ -> got @?= want

testNormalizeTm :: Assertion
testNormalizeTm = do
  (tt, natTy, _modeM, _modeI) <- require mkNatTypeTheory
  let z = TMGen (GenName "Z") []
  let s x = TMGen (GenName "S") [THATm x]
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  tm <- require (termExprToDiagram tt [] natTy (add (s z) (s z)))
  norm <- require (normalizeTermDiagram tt [] natTy tm)
  want <- require (termExprToDiagram tt [] natTy (s (s z)))
  normExpr <- require (diagramToTermExpr tt [] natTy norm)
  wantExpr <- require (diagramToTermExpr tt [] natTy want)
  normExpr @?= wantExpr

testNormalizeTmIdempotent :: Assertion
testNormalizeTmIdempotent = do
  (tt, natTy, _modeM, _modeI) <- require mkNatTypeTheory
  let z = TMGen (GenName "Z") []
  let s x = TMGen (GenName "S") [THATm x]
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  tm <- require (termExprToDiagram tt [] natTy (add (s z) (s z)))
  n1 <- require (normalizeTermDiagram tt [] natTy tm)
  n2 <- require (normalizeTermDiagram tt [] natTy n1)
  e1 <- require (diagramToTermExpr tt [] natTy n1)
  e2 <- require (diagramToTermExpr tt [] natTy n2)
  e1 @?= e2

testRejectNonTerminatingTermTRS :: Assertion
testRejectNonTerminatingTermTRS = do
  let src = T.unlines
        [ "doctrine BadLoop where {"
        , "  mode I classifiedBy I via I.U_I;"
        , "  gen comp_ctx_ext(a@I) : [a] -> [a] @I;"
        , "  gen comp_var(a@I) : [a] -> [a] @I;"
        , "  gen comp_reindex(a@I) : [a] -> [a] @I;"
        , "  comprehension I where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  gen U_I : [] -> [I.U_I] @I;"
        , "  gen Nat : [] -> [I.U_I] @I;"
        , "  gen f : [Nat] -> [Nat] @I;"
        , "  rule computational loop -> : [Nat] -> [Nat] @I ="
        , "    id[Nat] ; f == id[Nat] ; f"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected termination failure, got: " <> T.unpack err)
        (  "termination not proven" `T.isInfixOf` err
        && "ModeName \"I\"" `T.isInfixOf` err
        && "root symbols" `T.isInfixOf` err
        && "f" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrine elaboration to reject non-terminating term TRS"

testRejectNonConfluentTermTRS :: Assertion
testRejectNonConfluentTermTRS = do
  let src = T.unlines
        [ "doctrine BadConfluence where {"
        , "  mode I classifiedBy I via I.U_I;"
        , "  gen comp_ctx_ext(a@I) : [a] -> [a] @I;"
        , "  gen comp_var(a@I) : [a] -> [a] @I;"
        , "  gen comp_reindex(a@I) : [a] -> [a] @I;"
        , "  comprehension I where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  gen U_I : [] -> [I.U_I] @I;"
        , "  gen Nat : [] -> [I.U_I] @I;"
        , "  gen a : [] -> [Nat] @I;"
        , "  gen b : [] -> [Nat] @I;"
        , "  gen c : [] -> [Nat] @I;"
        , "  gen f : [Nat] -> [Nat] @I;"
        , "  rule computational r1 -> : [] -> [Nat] @I ="
        , "    a ; f == b"
        , "  rule computational r2 -> : [] -> [Nat] @I ="
        , "    a ; f == c"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected confluence failure, got: " <> T.unpack err)
        (  "confluence failed" `T.isInfixOf` err
        && "overlaps" `T.isInfixOf` err
        && "at [" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrine elaboration to reject non-confluent term TRS"

testMixedModeTmCtxResolution :: Assertion
testMixedModeTmCtxResolution = do
  let modeC = ModeName "C"
  let modeI = ModeName "I"
  let fooRef = ObjRef modeC (ObjName "Foo")
  let natRef = ObjRef modeI (ObjName "Nat")
  let fooTy = mkCon fooRef []
  let natTy = mkCon natRef []
  let tmCtx = [fooTy, natTy]
  let tt =
        withCtorSigs
          (modeOnlyTypeTheory (mkModes [modeC, modeI]))
          [ (fooRef, [])
          , (natRef, [])
          ]
  tm <- require (termExprToDiagram tt tmCtx natTy (TMBound 1))
  let unlabeledTm =
        case tm of
          TermDiagram diag ->
            TermDiagram diag { dPortLabel = IM.map (const Nothing) (dPortLabel diag) }
  boundTmIndicesTerm unlabeledTm @?= S.singleton 1
  _ <- require (unifyTm tt tmCtx S.empty emptySubst natTy unlabeledTm unlabeledTm)
  pure ()

testBoundIndexSurvivesCanonization :: Assertion
testBoundIndexSurvivesCanonization = do
  (tt, natTy, _modeM, _modeI) <- require mkNatTypeTheory
  let tmCtx = [natTy, natTy]
  let tm = TMBound 1
  term <- require (termExprToDiagram tt tmCtx natTy tm)
  let diag = unTerm term
  diagCanon <- require (canonDiagramRaw diag)
  let unlabeled = diagCanon { dPortLabel = IM.map (const Nothing) (dPortLabel diagCanon) }
  boundTmIndicesTerm (TermDiagram unlabeled) @?= S.singleton 1
  decoded <- require (diagramGraphToTermExpr tt tmCtx natTy unlabeled)
  decoded @?= tm

testValidateTermDiagramRejectsSparseBoundary :: Assertion
testValidateTermDiagramRejectsSparseBoundary = do
  let modeI = ModeName "I"
  let natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
  let boolTy = mkCon (ObjRef modeI (ObjName "Bool")) []
  let tmCtx = [natTy, boolTy]
  let (pBool, d0) = freshPort boolTy (emptyDiagram modeI tmCtx)
  let sparse = d0 { dIn = [pBool], dOut = [pBool] }
  _ <- require (validateDiagram sparse)
  case validateTermDiagram sparse of
    Left _ -> pure ()
    Right _ -> assertFailure "expected sparse boundary term diagram to fail validation"

testScopedTmUnify :: Assertion
testScopedTmUnify = do
  (tt, natTy, _modeM, _modeI) <- require mkNatTypeTheory
  let i0 = TmVar { tmvName = "i", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let j1 = TmVar { tmvName = "j", tmvSort = natTy, tmvScope = 1, tmvOwnerMode = Nothing }
  tI0 <- require (termExprToDiagram tt [natTy] natTy (TMMeta i0 []))
  tJ1 <- require (termExprToDiagram tt [natTy] natTy (TMMeta j1 [0]))
  tB0 <- require (termExprToDiagram tt [natTy] natTy (TMBound 0))
  case unifyTm tt [natTy] (S.singleton i0) emptySubst natTy tI0 tB0 of
    Left err ->
      assertBool "expected escape error" ("escape" `T.isInfixOf` err || "scope-0" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected scope-0 metavariable to reject bound term"
  sub <- require (unifyTm tt [natTy] (S.singleton j1) emptySubst natTy tJ1 tB0)
  case lookupTmMeta sub j1 of
    Just tm -> do
      expr <- require (diagramToTermExpr tt [natTy] natTy tm)
      case expr of
        TMBound 0 -> pure ()
        _ -> assertFailure "expected j := ^0"
    _ -> assertFailure "expected j := ^0"

testDependentUnify :: Assertion
testDependentUnify = do
  (tt0, natTy, modeM, _modeI) <- require mkNatTypeTheory
  let vecRef = ObjRef modeM (ObjName "Vec")
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let tt = withCtorSigs tt0 [(vecRef, [TPS_Tm natTy, TPS_Ty modeM])]
  let n = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let z = TMGen (GenName "Z") []
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  lhsTm <- require (termExprToDiagram tt [] natTy (add (TMMeta n []) z))
  rhsTm <- require (termExprToDiagram tt [] natTy (TMMeta n []))
  let lhs = mkCon vecRef [OATm lhsTm, OAObj aTy]
  let rhs = mkCon vecRef [OATm rhsTm, OAObj aTy]
  _ <- require (unifyObjFlex tt [] (S.singleton n) emptySubst lhs rhs)
  pure ()

testBoundSortUsesSubstitution :: Assertion
testBoundSortUsesSubstitution = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let aVar = mkModeMetaVar "a" modeM
  let lenRef = ObjRef modeI (ObjName "Len")
  let concrete = mkCon (ObjRef modeM (ObjName "AConcrete")) []
  let tmCtxSort = mkCon lenRef [OAObj (OVar aVar)]
  let expectedSort = mkCon lenRef [OAObj concrete]
  let tt =
        withCtorSigs
          (modeOnlyTypeTheory (mkModes [modeM, modeI]))
          [(lenRef, [TPS_Ty modeM])]
  bound0 <- require (termExprToDiagram tt [tmCtxSort] tmCtxSort (TMBound 0))
  case unifyTm tt [tmCtxSort] S.empty emptySubst expectedSort bound0 bound0 of
    Left _ -> pure ()
    Right _ -> assertFailure "expected bound sort mismatch before solving substitution"
  subst <- require (unifyObjFlex tt [] (S.singleton (aVar)) emptySubst (OVar aVar) concrete)
  _ <- require (unifyTm tt [tmCtxSort] S.empty subst expectedSort bound0 bound0)
  pure ()

testMatchBoundSortUsesCurrentSubst :: Assertion
testMatchBoundSortUsesCurrentSubst = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let aVar = mkModeMetaVar "a" modeM
  let lenRef = ObjRef modeI (ObjName "Len")
  let fooRef = ObjRef modeM (ObjName "Foo")
  let concrete = mkCon (ObjRef modeM (ObjName "AConcrete")) []
  let tmCtxSort = mkCon lenRef [OAObj (OVar aVar)]
  let expectedSort = mkCon lenRef [OAObj concrete]
  let tt =
        withCtorSigs
          (modeOnlyTypeTheory (mkModes [modeM, modeI]))
          [ (lenRef, [TPS_Ty modeM])
          , (fooRef, [TPS_Tm expectedSort])
          ]
  bound0 <- require (termExprToDiagram tt [tmCtxSort] tmCtxSort (TMBound 0))

  let d0 = emptyDiagram modeM [tmCtxSort]
  let (p1, d1) = freshPort (OVar aVar) d0
  let (p2, d2) = freshPort (mkCon fooRef [OATm bound0]) d1
  d3 <- require (addEdgePayload (PGen (GenName "g") [] []) [p1, p2] [] d2)
  let lhs = d3 { dIn = [p1, p2], dOut = [] }
  _ <- require (validateDiagram lhs)

  let h0 = emptyDiagram modeM [tmCtxSort]
  let (h1, h1d) = freshPort concrete h0
  let (h2, h2d) = freshPort (mkCon fooRef [OATm bound0]) h1d
  h3 <- require (addEdgePayload (PGen (GenName "g") [] []) [h1, h2] [] h2d)
  let host = h3 { dIn = [h1, h2], dOut = [] }
  _ <- require (validateDiagram host)

  tt' <- require (withZeroParamGenArgSigs [lhs, host] tt)
  let cfg = MatchConfig tt' (S.singleton (aVar))
  matches <- require (findAllMatches cfg lhs host)
  assertBool "expected at least one match" (not (null matches))

testDependentCompDefEq :: Assertion
testDependentCompDefEq = do
  (tt0, natTy, modeM, _modeI) <- require mkNatTypeTheory
  let vecRef = ObjRef modeM (ObjName "Vec")
  let outRef = ObjRef modeM (ObjName "Out")
  let z = TMGen (GenName "Z") []
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  let vecTy tmArg = mkCon vecRef [OATm tmArg]
  let outTy = mkCon outRef []
  let tt =
        withCtorSigs
          tt0
          [ (vecRef, [TPS_Tm natTy])
          , (outRef, [])
          ]
  addzz <- require (termExprToDiagram tt [] natTy (add z z))
  zTm <- require (termExprToDiagram tt [] natTy z)
  f <- require (genDTm modeM [] [] [vecTy addzz] (GenName "f"))
  g <- require (genDTm modeM [] [vecTy zTm] [outTy] (GenName "g"))
  _ <- require (compD tt g f)
  pure ()

testDefEqObjTermIndexReduction :: Assertion
testDefEqObjTermIndexReduction = do
  (tt0, natTy, modeM, _modeI) <- require mkNatTypeTheory
  let vecRef = ObjRef modeM (ObjName "Vec")
  let z = TMGen (GenName "Z") []
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  let tt =
        withCtorSigs tt0 [(vecRef, [TPS_Tm natTy])]
  tmAdd <- require (termExprToDiagram tt [] natTy (add z z))
  tmZ <- require (termExprToDiagram tt [] natTy z)
  let lhs = mkCon vecRef [OATm tmAdd]
  let rhs = mkCon vecRef [OATm tmZ]
  lhsCodeN <- require (DE.normalizeCodeTermDeepWithCtx tt [] modeM (objCode lhs))
  rhsCodeN <- require (DE.normalizeCodeTermDeepWithCtx tt [] modeM (objCode rhs))
  lhsCodeN @?= rhsCodeN
  ok <- require (DE.defEqObj tt [] lhs rhs)
  assertBool "expected object defeq to join reducible term-indexed code terms" ok

testMatchTmCtxCompatibility :: Assertion
testMatchTmCtxCompatibility = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
  let boolTy = mkCon (ObjRef modeI (ObjName "Bool")) []
  let tt =
        withCtorSigs
          (modeOnlyTypeTheory (mkModes [modeM, modeI]))
          []
  let lhs = (idD modeM [aTy]) { dTmCtx = [natTy] }
  let host = (idD modeM [aTy]) { dTmCtx = [boolTy] }
  _ <- require (validateDiagram lhs)
  _ <- require (validateDiagram host)
  let cfg = MatchConfig tt S.empty
  matches <- require (findAllMatches cfg lhs host)
  assertBool "expected no matches for incompatible term contexts" (null matches)

testMatchTmCtxDefEqCompatibility :: Assertion
testMatchTmCtxDefEqCompatibility = do
  (tt0, natTy, modeM, _modeI) <- require mkNatTypeTheory
  let vecRef = ObjRef modeM (ObjName "Vec")
  let vecTy tmArg = mkCon vecRef [OATm tmArg]
  let z = TMGen (GenName "Z") []
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  let tt =
        withCtorSigs tt0 [(vecRef, [TPS_Tm natTy])]
  tmAdd <- require (termExprToDiagram tt [] natTy (add z z))
  tmZ <- require (termExprToDiagram tt [] natTy z)
  let lhsTy = vecTy tmAdd
  let rhsTy = vecTy tmZ
  let lhs = (idD modeM [lhsTy]) { dTmCtx = [lhsTy] }
  let rhs = (idD modeM [rhsTy]) { dTmCtx = [rhsTy] }
  _ <- require (validateDiagram lhs)
  _ <- require (validateDiagram rhs)
  matches <- require (diagramIsoMatchWithVars tt S.empty lhs rhs)
  assertBool "expected at least one iso match under definitional tmctx equality" (not (null matches))

testIsoMatchDropsSubstFailure :: Assertion
testIsoMatchDropsSubstFailure = do
  let mode = ModeName "M"
  let goodTy = mkCon (ObjRef mode (ObjName "A")) []
  let badSort = mkCon (ObjRef mode (ObjName "BadSort")) [OAObj goodTy]
  let tt =
        withCtorSigs
          (modeOnlyTypeTheory (mkModes [mode]))
          [(ObjRef mode (ObjName "A"), [])]
  let inner = emptyDiagram mode [badSort]
  _ <- require (validateDiagram inner)
  lhs <- require (mkWrapWithBinder mode goodTy inner)
  rhs <- require (mkWrapWithBinder mode goodTy inner)
  matches <- require (diagramIsoMatchWithVars tt S.empty lhs rhs)
  assertBool "expected no matches when binder substitution normalization fails" (null matches)

testCheckedTermConversionDefEq :: Assertion
testCheckedTermConversionDefEq = do
  (tt0, natTy, modeM, _modeI) <- require mkNatTypeTheory
  let vecRef = ObjRef modeM (ObjName "Vec")
  let tt = withCtorSigs tt0 [(vecRef, [TPS_Tm natTy])]
  let z = TMGen (GenName "Z") []
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  tmAdd <- require (termExprToDiagram tt [] natTy (add z z))
  tmZ <- require (termExprToDiagram tt [] natTy z)
  let sortAdd = mkCon vecRef [OATm tmAdd]
  let sortZ = mkCon vecRef [OATm tmZ]
  let xVar = TmVar { tmvName = "x", tmvSort = sortAdd, tmvScope = 0, tmvOwnerMode = Nothing }
  case termExprToDiagram tt [] sortZ (TMMeta xVar []) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected unchecked conversion to reject structural sort mismatch"
  _ <- require (DE.termExprToDiagramChecked tt [] sortZ (TMMeta xVar []))
  pure ()

testCheckedTermConversionRejectsBadHeadSort :: Assertion
testCheckedTermConversionRejectsBadHeadSort = do
  let mode = ModeName "M"
  let aTy = mkCon (ObjRef mode (ObjName "A")) []
  let bTy = mkCon (ObjRef mode (ObjName "B")) []
  let cTy = mkCon (ObjRef mode (ObjName "C")) []
  let fName = GenName "f"
  let cName = GenName "c"
  let headSigs =
        M.fromList
          [ (fName, TmHeadSig { thsParams = [], thsInputs = [aTy], thsRes = bTy })
          , (cName, TmHeadSig { thsParams = [], thsInputs = [], thsRes = cTy })
          ]
  let tt = setModeTermHeads mode headSigs (modeOnlyTypeTheory (mkModes [mode]))
  let badExpr = TMGen fName [THATm (TMGen cName [])]
  case DE.termExprToDiagramChecked tt [] bTy badExpr of
    Left _ -> pure ()
    Right _ ->
      assertFailure "expected checked term->diagram conversion to reject mismatched generalized head input sort"
  let d0 = emptyDiagram mode []
  let (cOut, d1) = freshPort cTy d0
  d2 <- require (addEdgePayload (PGen cName [] []) [] [cOut] d1)
  let (fOut, d3) = freshPort bTy d2
  badDiag <- require (TermDiagram <$> addEdgePayload (PGen fName [] []) [cOut] [fOut] d3)
  case DE.diagramToTermExprChecked tt [] bTy badDiag of
    Left _ -> pure ()
    Right _ ->
      assertFailure "expected checked diagram->term conversion to reject mismatched generalized head input sort"

testBinderMetaSplice :: Assertion
testBinderMetaSplice = do
  let mode = ModeName "M"
  let aTy = mkCon (ObjRef mode (ObjName "A")) []
  let meta = BinderMetaVar "Body"
  let body = idD mode [aTy]

  lhs <- require (mkBetaInput mode aTy (BAMeta meta))
  host <- require (mkBetaInput mode aTy (BAConcrete body))
  rhs <- require (mkSpliceRHS mode aTy meta)

  let rule = RewriteRule { rrName = "beta", rrLHS = lhs, rrRHS = rhs, rrTyVars = [], rrTmVars = [] }
  tt <- require (withZeroParamGenArgSigs [lhs, rhs, host] (modeOnlyTypeTheory (mkModes [mode])))
  step <- require (rewriteOnce tt [rule] host)
  out <-
    case step of
      Nothing -> assertFailure "expected beta rewrite to fire" >> fail "unreachable"
      Just d -> pure d
  ok <- require (diagramIsoEq out (idD mode [aTy]))
  assertBool "expected splice rewrite to produce identity body" ok

testExplicitBinderTermArg :: Assertion
testExplicitBinderTermArg = do
  let src = T.unlines
        [ "doctrine ImplicitBinderIndex where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  mode I classifiedBy I via I.U_I;"
        , "  gen comp_ctx_ext(a@I) : [a] -> [a] @I;"
        , "  gen comp_var(a@I) : [a] -> [a] @I;"
        , "  gen comp_reindex(a@I) : [a] -> [a] @I;"
        , "  comprehension I where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  gen U_I : [] -> [I.U_I] @I;"
        , "  gen Nat : [] -> [I.U_I] @I;"
        , "  gen Z : [] -> [Nat] @I;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen Out : [] -> [M.U_M] @M;"
        , "  gen use(n : Nat) : [] -> [Vec(n)] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext(a) == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var(a) == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex(a) == id[a]"
        , "  gen wrap : [binder { tm n : Nat } : [Vec(n)]] -> [Out] @M;"
        , "}"
        ]
  env <- require (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "ImplicitBinderIndex" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine ImplicitBinderIndex" >> fail "unreachable"
      Just d -> pure d
  raw <- require (parseDiagExpr "wrap[use(n)]")
  diag <- require (elabDiagExpr env doc (ModeName "M") [] raw)
  assertBool "expected no unresolved metavariables" (S.null (freeVarsDiagram diag))

testRuleHeadTypeArgsSeeTyVars :: Assertion
testRuleHeadTypeArgsSeeTyVars = do
  let src = T.unlines
        [ "doctrine RuleHeadTypeArgs where {"
        , "  mode S classifiedBy S via S.U_S;"
        , "  gen ctx_ext(a@S) : [a] -> [a] @S;"
        , "  gen var(a@S) : [a] -> [a] @S;"
        , "  gen reindex(a@S) : [a] -> [a] @S;"
        , "  comprehension S where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen U_S : [] -> [S.U_S] @S;"
        , "  gen Id(a@S, x : a, y : a) : [] -> [S.U_S] @S;"
        , "  gen refl(a@S, x : a) : [] -> [Id(a, x, x)] @S;"
        , "  gen sym(a@S, x : a, y : a, p : Id(a, x, y)) : [] -> [Id(a, y, x)] @S;"
        , "  rule computational sym_refl -> (a@S, x : a) : [] -> [Id(a, x, x)] @S ="
        , "    sym(a, x, x, refl(a, x)) == refl(a, x)"
        , "}"
        ]
  _ <- require (parseRawFile src >>= elabRawFile)
  pure ()

testDependentIdCompLaws :: Assertion
testDependentIdCompLaws = do
  let src = T.unlines
        [ "doctrine DependentIdComp where {"
        , "  mode S classifiedBy S via S.U_S;"
        , "  gen ctx_ext(a@S) : [a] -> [a] @S;"
        , "  gen var(a@S) : [a] -> [a] @S;"
        , "  gen reindex(a@S) : [a] -> [a] @S;"
        , "  comprehension S where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen U_S : [] -> [S.U_S] @S;"
        , "  gen Id(a@S, x : a, y : a) : [] -> [S.U_S] @S;"
        , "  gen Con : [] -> [S.U_S] @S;"
        , "  gen Ty(g : Con) : [] -> [S.U_S] @S;"
        , "  gen extend(g : Con, a : Ty(g)) : [] -> [Con] @S;"
        , "  gen tri(g : Con, a : Ty(g), b : Ty(extend(g, a))) : [] -> [Con] @S;"
        , "  gen same_tri(g : Con, a : Ty(g), b : Ty(extend(g, a))) : [] -> [Id(Con, tri(g, a, b), tri(g, a, b))] @S;"
        , "}"
        ]
  _ <- require (parseRawFile src >>= elabRawFile)
  pure ()

testNestedDependentHeadArgElaborates :: Assertion
testNestedDependentHeadArgElaborates = do
  let src = T.unlines
        [ "doctrine NestedDependentHeadArg where {"
        , "  mode S classifiedBy S via S.U_S;"
        , "  gen ctx_ext(a@S) : [a] -> [a] @S;"
        , "  gen var(a@S) : [a] -> [a] @S;"
        , "  gen reindex(a@S) : [a] -> [a] @S;"
        , "  comprehension S where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen U_S : [] -> [S.U_S] @S;"
        , "  gen Id(a@S, x : a, y : a) : [] -> [S.U_S] @S;"
        , "  gen Con : [] -> [S.U_S] @S;"
        , "  gen Ty(g : Con) : [] -> [S.U_S] @S;"
        , "  gen empty : [] -> [Con] @S;"
        , "  gen base(g : Con) : [] -> [Ty(g)] @S;"
        , "  gen extend(g : Con, a : Ty(g)) : [] -> [Con] @S;"
        , "  gen sigma(g : Con, a : Ty(g), b : Ty(extend(g, a))) : [] -> [Ty(g)] @S;"
        , "  gen pack(g : Con, a : Ty(g), b : Ty(extend(g, a))) : [] -> [Con] @S;"
        , "  gen mixed(g : Con, a : Ty(g), b : Ty(extend(g, a))) : [] -> [Id(Con, pack(g, a, b), extend(g, sigma(g, a, b)))] @S;"
        , "}"
        ]
  _ <- require (parseRawFile src >>= elabRawFile)
  pure ()

mkBetaInput :: ModeName -> Obj -> BinderArg -> Either Text Diagram
mkBetaInput mode aTy lamArg = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let (lamOut, d1) = freshPort aTy d0
  let (y, d2) = freshPort aTy d1
  d3 <- addEdgePayload (PGen (GenName "lam") [] [lamArg]) [] [lamOut] d2
  d4 <- addEdgePayload (PGen (GenName "app") [] []) [lamOut, x] [y] d3
  let diag = d4 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure diag

mkSpliceRHS :: ModeName -> Obj -> BinderMetaVar -> Either Text Diagram
mkSpliceRHS mode aTy meta = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let (y, d1) = freshPort aTy d0
  let me = ModExpr { meSrc = mode, meTgt = mode, mePath = [] }
  d2 <- addEdgePayload (PSplice meta me) [x] [y] d1
  let diag = d2 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure diag

mkWrapWithBinder :: ModeName -> Obj -> Diagram -> Either Text Diagram
mkWrapWithBinder mode outTy inner = do
  let (outPort, d0) = freshPort outTy (emptyDiagram mode [])
  d1 <- addEdgePayload (PGen (GenName "wrap") [] [BAConcrete inner]) [] [outPort] d0
  let diag = d1 { dOut = [outPort] }
  validateDiagram diag
  pure diag

mkNatTypeTheory :: Either Text (TypeTheory, Obj, ModeName, ModeName)
mkNatTypeTheory = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  mt0 <- addMode modeM emptyModeTheory
  mt1 <- addMode modeI mt0
  let natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
  let z = TMGen (GenName "Z") []
  let s x = TMGen (GenName "S") [THATm x]
  let add x y = TMGen (GenName "add") [THATm x, THATm y]
  let vM = TmVar { tmvName = "m", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let vN = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let funSigs =
        M.fromList
          [ (GenName "Z", TmHeadSig [] [] natTy)
          , (GenName "S", TmHeadSig [] [natTy] natTy)
          , (GenName "add", TmHeadSig [] [natTy, natTy] natTy)
          ]
  let ttSig =
        setModeTermHeads modeI funSigs $
          withCtorSigs
            (modeOnlyTypeTheory mt1)
            []
  r1L <- termExprToDiagram ttSig [] natTy (add z (TMMeta vN []))
  r1R <- termExprToDiagram ttSig [] natTy (TMMeta vN [])
  r2L <- termExprToDiagram ttSig [] natTy (add (s (TMMeta vM [])) (TMMeta vN []))
  r2R <- termExprToDiagram ttSig [] natTy (s (add (TMMeta vM []) (TMMeta vN [])))
  r3L <- termExprToDiagram ttSig [] natTy (add (TMMeta vN []) z)
  r3R <- termExprToDiagram ttSig [] natTy (TMMeta vN [])
  let rules =
        [ TmRule { trVars = [vN], trLHS = r1L, trRHS = r1R }
        , TmRule { trVars = [vM, vN], trLHS = r2L, trRHS = r2R }
        , TmRule { trVars = [vN], trLHS = r3L, trRHS = r3R }
        ]
  let tt1 = setModeTermRules modeI rules ttSig
  trsMap <- compileAllTermRules tt1
  trsMode <-
    case M.lookup modeI trsMap of
      Nothing -> Left "mkNatTypeTheory: missing compiled TRS for mode I"
      Just trs -> Right trs
  let tt = setModeTermTRS modeI trsMode tt1
  pure (tt, natTy, modeM, modeI)

withCtorSigs :: TypeTheory -> [(ObjRef, [TypeParamSig])] -> TypeTheory
withCtorSigs tt entries =
  tt
    { ttCtorSigs = table
    , ttUniverseCtors = M.map (S.fromList . M.keys) table
    }
  where
    table =
      foldl
        (\acc (ref, sig) -> M.insertWith M.union (orMode ref) (M.singleton (orName ref) (flatParamsToCtorSig (orMode ref) sig)) acc)
        M.empty
        entries
