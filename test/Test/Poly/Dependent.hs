{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Dependent
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy(..))

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (meDoctrines)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.ModeTheory (ModeName(..), addMode, emptyModeTheory)
import Strat.Poly.Doctrine (doctrineTypeTheory)
import Strat.Poly.TypeExpr
  ( TypeExpr(..)
  , TypeArg(..)
  , TyVar(..)
  , TypeName(..)
  , TypeRef(..)
  , TmFunName(..)
  , TmVar(..)
  )
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , TmRule(..)
  , defaultTmFuel
  , modeOnlyTypeTheory
  )
import Strat.Poly.TypeNormalize (normalizeTypeDeep, normalizeTermDiagram)
import Strat.Poly.UnifyTy (unifyTm, unifyTyFlex, emptySubst, sTm)
import Strat.Poly.Match (MatchConfig(..), findAllMatches)
import Strat.Poly.Graph
  ( Diagram(..)
  , BinderMetaVar(..)
  , BinderArg(..)
  , EdgePayload(..)
  , diagramIsoMatchWithVars
  , dIn
  , dOut
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , validateDiagram
  , diagramIsoEq
  )
import Strat.Poly.Diagram (idD, genDTm, compD, freeTmVarsDiagram)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Rewrite (RewriteRule(..), rewriteOnce)
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram, diagramToTermExpr)
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.Dependent"
    [ testCase "term normalization from doctrine rules reduces add(S(Z),S(Z))" testDoctrineNormalizeTypeArg
    , testCase "term normalization reduces add(S(Z),S(Z))" testNormalizeTm
    , testCase "scoped term unification rejects escapes" testScopedTmUnify
    , testCase "dependent unification normalizes term arguments" testDependentUnify
    , testCase "bound term sort checks apply current substitution" testBoundSortUsesSubstitution
    , testCase "matching applies current substitution to bound term sorts" testMatchBoundSortUsesCurrentSubst
    , testCase "dependent composition respects definitional term equality" testDependentCompDefEq
    , testCase "matching requires term-context compatibility" testMatchTmCtxCompatibility
    , testCase "iso matching drops candidates when dependent substitution fails" testIsoMatchDropsSubstFailure
    , testCase "binder metas + splice rewrite" testBinderMetaSplice
    , testCase "explicit binder term args can reference bound term vars" testExplicitBinderTermArg
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

testDoctrineNormalizeTypeArg :: Assertion
testDoctrineNormalizeTypeArg = do
  let src = T.unlines
        [ "doctrine DepNorm where {"
        , "  mode M;"
        , "  mode I;"
        , "  type Nat @I;"
        , "  type A @M;"
        , "  type Vec(n : Nat, a@M) @M;"
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
  let tt = doctrineTypeTheory doc
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let aTy = TCon (TypeRef modeM (TypeName "A")) []
  let vecRef = TypeRef modeM (TypeName "Vec")
  let natTy = TCon (TypeRef modeI (TypeName "Nat")) []
  let z = TMFun (TmFunName "Z") []
  let s x = TMFun (TmFunName "S") [x]
  let add x y = TMFun (TmFunName "add") [x, y]
  tmArg <- require (termExprToDiagram tt [] natTy (add (s z) (s z)))
  wantTm <- require (termExprToDiagram tt [] natTy (s (s z)))
  let ty = TCon vecRef [TATm tmArg, TAType aTy]
  let want = TCon vecRef [TATm wantTm, TAType aTy]
  got <- require (normalizeTypeDeep tt ty)
  case (got, want) of
    (TCon gotRef [TATm gotTm, TAType gotA], TCon wantRef [TATm wantTm', TAType wantA]) -> do
      gotRef @?= wantRef
      gotA @?= wantA
      gotExpr <- require (diagramToTermExpr tt [] natTy gotTm)
      wantExpr <- require (diagramToTermExpr tt [] natTy wantTm')
      gotExpr @?= wantExpr
    _ -> got @?= want

testNormalizeTm :: Assertion
testNormalizeTm = do
  (tt, natTy, _modeM, _modeI) <- require mkNatTypeTheory
  let z = TMFun (TmFunName "Z") []
  let s x = TMFun (TmFunName "S") [x]
  let add x y = TMFun (TmFunName "add") [x, y]
  tm <- require (termExprToDiagram tt [] natTy (add (s z) (s z)))
  norm <- require (normalizeTermDiagram tt [] natTy tm)
  want <- require (termExprToDiagram tt [] natTy (s (s z)))
  normExpr <- require (diagramToTermExpr tt [] natTy norm)
  wantExpr <- require (diagramToTermExpr tt [] natTy want)
  normExpr @?= wantExpr

testScopedTmUnify :: Assertion
testScopedTmUnify = do
  (tt, natTy, _modeM, _modeI) <- require mkNatTypeTheory
  let i0 = TmVar { tmvName = "i", tmvSort = natTy, tmvScope = 0 }
  let j1 = TmVar { tmvName = "j", tmvSort = natTy, tmvScope = 1 }
  tI0 <- require (termExprToDiagram tt [natTy] natTy (TMVar i0))
  tJ1 <- require (termExprToDiagram tt [natTy] natTy (TMVar j1))
  tB0 <- require (termExprToDiagram tt [natTy] natTy (TMBound 0))
  case unifyTm tt [natTy] (S.singleton i0) emptySubst natTy tI0 tB0 of
    Left err ->
      assertBool "expected escape error" ("escape" `T.isInfixOf` err || "scope-0" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected scope-0 metavariable to reject bound term"
  sub <- require (unifyTm tt [natTy] (S.singleton j1) emptySubst natTy tJ1 tB0)
  case M.lookup j1 (sTm sub) of
    Just tm -> do
      expr <- require (diagramToTermExpr tt [natTy] natTy tm)
      case expr of
        TMBound 0 -> pure ()
        _ -> assertFailure "expected j := ^0"
    _ -> assertFailure "expected j := ^0"

testDependentUnify :: Assertion
testDependentUnify = do
  (tt0, natTy, modeM, _modeI) <- require mkNatTypeTheory
  let vecRef = TypeRef modeM (TypeName "Vec")
  let aTy = TCon (TypeRef modeM (TypeName "A")) []
  let tt = tt0 { ttTypeParams = M.fromList [ (vecRef, [TPS_Tm natTy, TPS_Ty modeM]) ] }
  let n = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0 }
  let z = TMFun (TmFunName "Z") []
  let add x y = TMFun (TmFunName "add") [x, y]
  lhsTm <- require (termExprToDiagram tt [] natTy (add (TMVar n) z))
  rhsTm <- require (termExprToDiagram tt [] natTy (TMVar n))
  let lhs = TCon vecRef [TATm lhsTm, TAType aTy]
  let rhs = TCon vecRef [TATm rhsTm, TAType aTy]
  _ <- require (unifyTyFlex tt [] S.empty (S.singleton n) emptySubst lhs rhs)
  pure ()

testBoundSortUsesSubstitution :: Assertion
testBoundSortUsesSubstitution = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let aVar = TyVar { tvName = "a", tvMode = modeM }
  let lenRef = TypeRef modeI (TypeName "Len")
  let concrete = TCon (TypeRef modeM (TypeName "AConcrete")) []
  let tmCtxSort = TCon lenRef [TAType (TVar aVar)]
  let expectedSort = TCon lenRef [TAType concrete]
  let tt =
        TypeTheory
          { ttModes = mkModes [modeM, modeI]
          , ttTypeParams = M.fromList [(lenRef, [TPS_Ty modeM])]
          , ttTmFuns = M.empty
          , ttTmRules = M.empty
          , ttTmFuel = defaultTmFuel
          , ttTmPolicy = UseOnlyComputationalLR
          }
  bound0 <- require (termExprToDiagram tt [tmCtxSort] tmCtxSort (TMBound 0))
  case unifyTm tt [tmCtxSort] S.empty emptySubst expectedSort bound0 bound0 of
    Left _ -> pure ()
    Right _ -> assertFailure "expected bound sort mismatch before solving substitution"
  subst <- require (unifyTyFlex tt [] (S.singleton aVar) S.empty emptySubst (TVar aVar) concrete)
  _ <- require (unifyTm tt [tmCtxSort] S.empty subst expectedSort bound0 bound0)
  pure ()

testMatchBoundSortUsesCurrentSubst :: Assertion
testMatchBoundSortUsesCurrentSubst = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let aVar = TyVar { tvName = "a", tvMode = modeM }
  let lenRef = TypeRef modeI (TypeName "Len")
  let fooRef = TypeRef modeM (TypeName "Foo")
  let concrete = TCon (TypeRef modeM (TypeName "AConcrete")) []
  let tmCtxSort = TCon lenRef [TAType (TVar aVar)]
  let expectedSort = TCon lenRef [TAType concrete]
  let tt =
        TypeTheory
          { ttModes = mkModes [modeM, modeI]
          , ttTypeParams =
              M.fromList
                [ (lenRef, [TPS_Ty modeM])
                , (fooRef, [TPS_Tm expectedSort])
                ]
          , ttTmFuns = M.empty
          , ttTmRules = M.empty
          , ttTmFuel = defaultTmFuel
          , ttTmPolicy = UseOnlyComputationalLR
          }
  bound0 <- require (termExprToDiagram tt [tmCtxSort] tmCtxSort (TMBound 0))

  let d0 = emptyDiagram modeM [tmCtxSort]
  let (p1, d1) = freshPort (TVar aVar) d0
  let (p2, d2) = freshPort (TCon fooRef [TATm bound0]) d1
  d3 <- require (addEdgePayload (PGen (GenName "g") M.empty []) [p1, p2] [] d2)
  let lhs = d3 { dIn = [p1, p2], dOut = [] }
  _ <- require (validateDiagram lhs)

  let h0 = emptyDiagram modeM [tmCtxSort]
  let (h1, h1d) = freshPort concrete h0
  let (h2, h2d) = freshPort (TCon fooRef [TATm bound0]) h1d
  h3 <- require (addEdgePayload (PGen (GenName "g") M.empty []) [h1, h2] [] h2d)
  let host = h3 { dIn = [h1, h2], dOut = [] }
  _ <- require (validateDiagram host)

  let cfg = MatchConfig tt (S.singleton aVar) S.empty S.empty
  matches <- require (findAllMatches cfg lhs host)
  assertBool "expected at least one match" (not (null matches))

testDependentCompDefEq :: Assertion
testDependentCompDefEq = do
  (tt0, natTy, modeM, _modeI) <- require mkNatTypeTheory
  let vecRef = TypeRef modeM (TypeName "Vec")
  let outRef = TypeRef modeM (TypeName "Out")
  let z = TMFun (TmFunName "Z") []
  let add x y = TMFun (TmFunName "add") [x, y]
  let vecTy tmArg = TCon vecRef [TATm tmArg]
  let outTy = TCon outRef []
  let tt =
        tt0
          { ttTypeParams =
              M.fromList
                [ (vecRef, [TPS_Tm natTy])
                , (outRef, [])
                ]
          }
  addzz <- require (termExprToDiagram tt [] natTy (add z z))
  zTm <- require (termExprToDiagram tt [] natTy z)
  f <- require (genDTm modeM [] [] [vecTy addzz] (GenName "f"))
  g <- require (genDTm modeM [] [vecTy zTm] [outTy] (GenName "g"))
  _ <- require (compD tt g f)
  pure ()

testMatchTmCtxCompatibility :: Assertion
testMatchTmCtxCompatibility = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let aTy = TCon (TypeRef modeM (TypeName "A")) []
  let natTy = TCon (TypeRef modeI (TypeName "Nat")) []
  let boolTy = TCon (TypeRef modeI (TypeName "Bool")) []
  let tt =
        TypeTheory
          { ttModes = mkModes [modeM, modeI]
          , ttTypeParams = M.empty
          , ttTmFuns = M.empty
          , ttTmRules = M.empty
          , ttTmFuel = defaultTmFuel
          , ttTmPolicy = UseOnlyComputationalLR
          }
  let lhs = (idD modeM [aTy]) { dTmCtx = [natTy] }
  let host = (idD modeM [aTy]) { dTmCtx = [boolTy] }
  _ <- require (validateDiagram lhs)
  _ <- require (validateDiagram host)
  let cfg = MatchConfig tt S.empty S.empty S.empty
  matches <- require (findAllMatches cfg lhs host)
  assertBool "expected no matches for incompatible term contexts" (null matches)

testIsoMatchDropsSubstFailure :: Assertion
testIsoMatchDropsSubstFailure = do
  let mode = ModeName "M"
  let goodTy = TCon (TypeRef mode (TypeName "A")) []
  let badSort = TCon (TypeRef mode (TypeName "BadSort")) [TAType goodTy]
  let tt = modeOnlyTypeTheory (mkModes [mode])
  let inner = emptyDiagram mode [badSort]
  _ <- require (validateDiagram inner)
  lhs <- require (mkWrapWithBinder mode goodTy inner)
  rhs <- require (mkWrapWithBinder mode goodTy inner)
  matches <- require (diagramIsoMatchWithVars tt S.empty S.empty S.empty lhs rhs)
  assertBool "expected no matches when binder substitution normalization fails" (null matches)

testBinderMetaSplice :: Assertion
testBinderMetaSplice = do
  let mode = ModeName "M"
  let aTy = TCon (TypeRef mode (TypeName "A")) []
  let meta = BinderMetaVar "Body"
  let body = idD mode [aTy]

  lhs <- require (mkBetaInput mode aTy (BAMeta meta))
  host <- require (mkBetaInput mode aTy (BAConcrete body))
  rhs <- require (mkSpliceRHS mode aTy meta)

  let rule = RewriteRule { rrName = "beta", rrLHS = lhs, rrRHS = rhs, rrTyVars = [], rrTmVars = [] }
  let tt = modeOnlyTypeTheory (mkModes [mode])
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
        , "  mode M;"
        , "  mode I;"
        , "  type Nat @I;"
        , "  gen Z : [] -> [Nat] @I;"
        , "  type Vec(n : Nat) @M;"
        , "  type Out @M;"
        , "  gen use(n : Nat) : [] -> [Vec(n)] @M;"
        , "  gen wrap : [binder { tm n : Nat } : [Vec(n)]] -> [Out] @M;"
        , "}"
        ]
  env <- require (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "ImplicitBinderIndex" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine ImplicitBinderIndex" >> fail "unreachable"
      Just d -> pure d
  raw <- require (parseDiagExpr "wrap[use{n}]")
  diag <- require (elabDiagExpr env doc (ModeName "M") [] raw)
  assertBool "expected no unresolved term variables" (S.null (freeTmVarsDiagram diag))

mkBetaInput :: ModeName -> TypeExpr -> BinderArg -> Either Text Diagram
mkBetaInput mode aTy lamArg = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let (lamOut, d1) = freshPort aTy d0
  let (y, d2) = freshPort aTy d1
  d3 <- addEdgePayload (PGen (GenName "lam") M.empty [lamArg]) [] [lamOut] d2
  d4 <- addEdgePayload (PGen (GenName "app") M.empty []) [lamOut, x] [y] d3
  let diag = d4 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure diag

mkSpliceRHS :: ModeName -> TypeExpr -> BinderMetaVar -> Either Text Diagram
mkSpliceRHS mode aTy meta = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let (y, d1) = freshPort aTy d0
  d2 <- addEdgePayload (PSplice meta) [x] [y] d1
  let diag = d2 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure diag

mkWrapWithBinder :: ModeName -> TypeExpr -> Diagram -> Either Text Diagram
mkWrapWithBinder mode outTy inner = do
  let (outPort, d0) = freshPort outTy (emptyDiagram mode [])
  d1 <- addEdgePayload (PGen (GenName "wrap") M.empty [BAConcrete inner]) [] [outPort] d0
  let diag = d1 { dOut = [outPort] }
  validateDiagram diag
  pure diag

mkNatTypeTheory :: Either Text (TypeTheory, TypeExpr, ModeName, ModeName)
mkNatTypeTheory = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  mt0 <- addMode modeM emptyModeTheory
  mt1 <- addMode modeI mt0
  let natTy = TCon (TypeRef modeI (TypeName "Nat")) []
  let z = TMFun (TmFunName "Z") []
  let s x = TMFun (TmFunName "S") [x]
  let add x y = TMFun (TmFunName "add") [x, y]
  let vM = TmVar { tmvName = "m", tmvSort = natTy, tmvScope = 0 }
  let vN = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0 }
  let funSigs =
        M.fromList
          [ (TmFunName "Z", TmFunSig [] natTy)
          , (TmFunName "S", TmFunSig [natTy] natTy)
          , (TmFunName "add", TmFunSig [natTy, natTy] natTy)
          ]
  let ttSig =
        TypeTheory
          { ttModes = mt1
          , ttTypeParams = M.empty
          , ttTmFuns = M.fromList [(modeI, funSigs)]
          , ttTmRules = M.empty
          , ttTmFuel = defaultTmFuel
          , ttTmPolicy = UseOnlyComputationalLR
          }
  r1L <- termExprToDiagram ttSig [] natTy (add z (TMVar vN))
  r1R <- termExprToDiagram ttSig [] natTy (TMVar vN)
  r2L <- termExprToDiagram ttSig [] natTy (add (s (TMVar vM)) (TMVar vN))
  r2R <- termExprToDiagram ttSig [] natTy (s (add (TMVar vM) (TMVar vN)))
  r3L <- termExprToDiagram ttSig [] natTy (add (TMVar vN) z)
  r3R <- termExprToDiagram ttSig [] natTy (TMVar vN)
  let rules =
        [ TmRule { trVars = [vN], trLHS = r1L, trRHS = r1R }
        , TmRule { trVars = [vM, vN], trLHS = r2L, trRHS = r2R }
        , TmRule { trVars = [vN], trLHS = r3L, trRHS = r3R }
        ]
  let tt = ttSig { ttTmRules = M.fromList [(modeI, rules)] }
  pure (tt, natTy, modeM, modeI)
