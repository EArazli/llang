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

import Strat.Poly.ModeTheory (ModeName(..), addMode, emptyModeTheory)
import Strat.Poly.TypeExpr
  ( TypeExpr(..)
  , TypeArg(..)
  , TypeName(..)
  , TypeRef(..)
  , IxFunName(..)
  , IxVar(..)
  , IxTerm(..)
  )
import Strat.Poly.IndexTheory (IxTheory(..), IxFunSig(..), IxRule(..), normalizeIx)
import Strat.Poly.TypeTheory (TypeTheory(..))
import Strat.Poly.UnifyTy (unifyIx, unifyTyFlex, emptySubst, sIx)
import Strat.Poly.Graph
  ( BinderMetaVar(..)
  , BinderArg(..)
  , EdgePayload(..)
  , dIn
  , dOut
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , validateDiagram
  , diagramIsoEq
  )
import Strat.Poly.Diagram (Diagram, idD)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Rewrite (RewriteRule(..), rewriteOnce)
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.Dependent"
    [ testCase "index normalization reduces add(S(Z),S(Z))" testNormalizeIx
    , testCase "scoped index unification rejects escapes" testScopedIxUnify
    , testCase "dependent unification normalizes index arguments" testDependentUnify
    , testCase "binder metas + splice rewrite" testBinderMetaSplice
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

testNormalizeIx :: Assertion
testNormalizeIx = do
  (tt, natTy, _modeM, _modeI) <- require mkNatTypeTheory
  let z = IXFun (IxFunName "Z") []
  let s x = IXFun (IxFunName "S") [x]
  let add x y = IXFun (IxFunName "add") [x, y]
  let tm = add (s z) (s z)
  norm <- require (normalizeIx tt natTy tm)
  norm @?= s (s z)

testScopedIxUnify :: Assertion
testScopedIxUnify = do
  (tt, natTy, _modeM, _modeI) <- require mkNatTypeTheory
  let i0 = IxVar { ixvName = "i", ixvSort = natTy, ixvScope = 0 }
  let j1 = IxVar { ixvName = "j", ixvSort = natTy, ixvScope = 1 }
  case unifyIx tt [natTy] (S.singleton i0) emptySubst natTy (IXVar i0) (IXBound 0) of
    Left err ->
      assertBool "expected escape error" ("escape" `T.isInfixOf` err || "scope-0" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected scope-0 metavar to reject bound index"
  sub <- require (unifyIx tt [natTy] (S.singleton j1) emptySubst natTy (IXVar j1) (IXBound 0))
  case M.lookup j1 (sIx sub) of
    Just (IXBound 0) -> pure ()
    _ -> assertFailure "expected j := ^0"

testDependentUnify :: Assertion
testDependentUnify = do
  (tt, natTy, modeM, _modeI) <- require mkNatTypeTheory
  let vecRef = TypeRef modeM (TypeName "Vec")
  let aTy = TCon (TypeRef modeM (TypeName "A")) []
  let n = IxVar { ixvName = "n", ixvSort = natTy, ixvScope = 0 }
  let z = IXFun (IxFunName "Z") []
  let add x y = IXFun (IxFunName "add") [x, y]
  let lhs = TCon vecRef [TAIndex (add (IXVar n) z), TAType aTy]
  let rhs = TCon vecRef [TAIndex (IXVar n), TAType aTy]
  _ <- require (unifyTyFlex tt [] S.empty (S.singleton n) emptySubst lhs rhs)
  pure ()

testBinderMetaSplice :: Assertion
testBinderMetaSplice = do
  let mode = ModeName "M"
  let aTy = TCon (TypeRef mode (TypeName "A")) []
  let meta = BinderMetaVar "Body"
  let body = idD mode [aTy]

  lhs <- require (mkBetaInput mode aTy (BAMeta meta))
  host <- require (mkBetaInput mode aTy (BAConcrete body))
  rhs <- require (mkSpliceRHS mode aTy meta)

  let rule = RewriteRule { rrName = "beta", rrLHS = lhs, rrRHS = rhs, rrTyVars = [], rrIxVars = [] }
  let tt = TypeTheory { ttModes = mkModes [mode], ttIndex = M.empty, ttTypeParams = M.empty, ttIxFuel = 200 }
  step <- require (rewriteOnce tt [rule] host)
  out <-
    case step of
      Nothing -> assertFailure "expected beta rewrite to fire" >> fail "unreachable"
      Just d -> pure d
  ok <- require (diagramIsoEq out (idD mode [aTy]))
  assertBool "expected splice rewrite to produce identity body" ok

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

mkNatTypeTheory :: Either Text (TypeTheory, TypeExpr, ModeName, ModeName)
mkNatTypeTheory = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  mt0 <- addMode modeM emptyModeTheory
  mt1 <- addMode modeI mt0
  let natTy = TCon (TypeRef modeI (TypeName "Nat")) []
  let z = IXFun (IxFunName "Z") []
  let s x = IXFun (IxFunName "S") [x]
  let add x y = IXFun (IxFunName "add") [x, y]
  let vM = IxVar { ixvName = "m", ixvSort = natTy, ixvScope = 0 }
  let vN = IxVar { ixvName = "n", ixvSort = natTy, ixvScope = 0 }
  let theory =
        IxTheory
          { itFuns =
              M.fromList
                [ (IxFunName "Z", IxFunSig [] natTy)
                , (IxFunName "S", IxFunSig [natTy] natTy)
                , (IxFunName "add", IxFunSig [natTy, natTy] natTy)
                ]
          , itRules =
              [ IxRule { irVars = [vN], irLHS = add z (IXVar vN), irRHS = IXVar vN }
              , IxRule { irVars = [vM, vN], irLHS = add (s (IXVar vM)) (IXVar vN), irRHS = s (add (IXVar vM) (IXVar vN)) }
              , IxRule { irVars = [vN], irLHS = add (IXVar vN) z, irRHS = IXVar vN }
              ]
          }
  let tt = TypeTheory { ttModes = mt1, ttIndex = M.fromList [(modeI, theory)], ttTypeParams = M.empty, ttIxFuel = 200 }
  pure (tt, natTy, modeM, modeI)
