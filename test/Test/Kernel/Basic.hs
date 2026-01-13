{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Basic
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.Signature
import Strat.Kernel.Subst
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Unify
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Test.Kernel.Fixtures

tests :: TestTree
tests =
  testGroup
    "Kernel.Basic"
    [ testCase "mkVar carries sort" testMkVar
    , testCase "mkSort unknown sort" testMkSortUnknown
    , testCase "mkSort arity mismatch" testMkSortArity
    , testCase "mkSort index sort mismatch" testMkSortIndexMismatch
    , testCase "mkOp unknown op" testMkOpUnknown
    , testCase "mkOp arity mismatch" testMkOpArity
    , testCase "mkOp arg sort mismatch" testMkOpArgSort
    , testCase "mkOp binder sort depends on earlier binder" testMkOpDependentBinder
    , testCase "positions preorder" testPositionsOrder
    , testCase "subtermAt/replaceAt" testSubtermReplace
    , testCase "renameScope touches only one scope" testRenameScope
    , testCase "applySubstTerm recursive" testApplySubstRecursive
    , testCase "applySubstTerm updates sort indices" testApplySubstSortIndices
    , testCase "unify sort mismatch fails" testUnifySortMismatch
    , testCase "match repeated variable" testMatchRepeatedVar
    , testCase "match respects op mismatch" testMatchOpMismatch
    , testCase "match respects sort indices" testMatchSortIndices
    ]

testMkVar :: Assertion
testMkVar = do
  let scope = ScopeId "t:mkvar"
  let v0 = Var scope 0
  let t = mkVar objSort v0
  termSort t @?= objSort

testMkSortUnknown :: Assertion
testMkSortUnknown =
  case mkSort sigBasic (SortName "Missing") [] of
    Left (UnknownSort _) -> pure ()
    other -> assertFailure ("expected UnknownSort, got " <> show other)

testMkSortArity :: Assertion
testMkSortArity =
  case mkSort sigBasic homName [] of
    Left (SortArityMismatch _ _ _) -> pure ()
    other -> assertFailure ("expected SortArityMismatch, got " <> show other)

testMkSortIndexMismatch :: Assertion
testMkSortIndexMismatch = do
  case mkOp sigBasic opA [] of
    Left err -> assertFailure (show err)
    Right a ->
      case mkOp sigBasic opId [a] of
        Left err -> assertFailure (show err)
        Right ida ->
          case mkSort sigBasic homName [a, ida] of
            Left (SortIndexSortMismatch _ _ _ _) -> pure ()
            other -> assertFailure ("expected SortIndexSortMismatch, got " <> show other)

testMkOpUnknown :: Assertion
testMkOpUnknown =
  case mkOp sigBasic (OpName "missing") [] of
    Left (UnknownOp _) -> pure ()
    other -> assertFailure ("expected UnknownOp, got " <> show other)

testMkOpArity :: Assertion
testMkOpArity =
  case mkOp sigBasic opF [] of
    Left (ArityMismatch _ _ _) -> pure ()
    other -> assertFailure ("expected ArityMismatch, got " <> show other)

testMkOpArgSort :: Assertion
testMkOpArgSort = do
  case mkOp sigBasic opA [] of
    Left err -> assertFailure (show err)
    Right a ->
      case mkOp sigBasic opId [a] of
        Left err -> assertFailure (show err)
        Right ida ->
          case mkOp sigBasic opF [ida] of
            Left (ArgSortMismatch _ _ _ _) -> pure ()
            other -> assertFailure ("expected ArgSortMismatch, got " <> show other)

testMkOpDependentBinder :: Assertion
testMkOpDependentBinder = do
  let opP = OpName "p"
  let vx = Var (ScopeId "op:p") 0
  let vh = Var (ScopeId "op:p") 1
  let x = mkVar objSort vx
  let decl = OpDecl opP [Binder vx objSort, Binder vh (homSort x x)] objSort
  let sig = sigBasic { sigOps = M.insert opP decl (sigOps sigBasic) }
  let a = mkTerm sig "a" []
  let b = mkTerm sig "b" []
  let ida = mkTerm sig "id" [a]
  let idb = mkTerm sig "id" [b]
  case mkOp sig opP [a, ida] of
    Left err -> assertFailure (show err)
    Right _ -> pure ()
  case mkOp sig opP [a, idb] of
    Left (ArgSortMismatch _ _ _ _) -> pure ()
    other -> assertFailure ("expected ArgSortMismatch, got " <> show other)

testPositionsOrder :: Assertion
testPositionsOrder = do
  let a = mkTerm sigBasic "a" []
  let fa = mkTerm sigBasic "f" [a]
  let term = mkTerm sigBasic "m" [fa, a]
  positions term @?= [[], [0], [0, 0], [1]]

testSubtermReplace :: Assertion
testSubtermReplace = do
  let a = mkTerm sigBasic "a" []
  let fa = mkTerm sigBasic "f" [a]
  let term = mkTerm sigBasic "m" [fa, a]
  subtermAt term [0] @?= Just fa
  case replaceAt term [0] a of
    Nothing -> assertFailure "expected replaceAt"
    Just term' -> do
      termNode term' @?= termNode (mkTerm sigBasic "m" [a, a])
      termSort term' @?= termSort term
  replaceAt term [2] a @?= Nothing

testRenameScope :: Assertion
testRenameScope = do
  let s1 = ScopeId "s1"
  let s2 = ScopeId "s2"
  let s3 = ScopeId "s3"
  let x = mkVar objSort (Var s1 0)
  let y = mkVar objSort (Var s2 0)
  let term = mkTerm sigBasic "m" [x, y]
  let term' = renameScope s1 s3 term
  let scopes = S.map vScope (varsTerm term')
  scopes @?= S.fromList [s2, s3]

testApplySubstRecursive :: Assertion
testApplySubstRecursive = do
  let x = Var (ScopeId "s") 0
  let y = Var (ScopeId "s") 1
  let a = mkTerm sigBasic "a" []
  let fy = mkTerm sigBasic "f" [mkVar objSort y]
  let subst = M.fromList [(x, fy), (y, a)]
  let term = mkVar objSort x
  let term' = applySubstTerm subst term
  termNode term' @?= termNode (mkTerm sigBasic "f" [a])

testApplySubstSortIndices :: Assertion
testApplySubstSortIndices = do
  let x = Var (ScopeId "s") 0
  let a = mkTerm sigBasic "a" []
  let vx = mkVar objSort x
  let ida = mkTerm sigBasic "id" [a]
  let term = mkTerm sigBasic "id" [vx]
  let subst = M.fromList [(x, a)]
  let term' = applySubstTerm subst term
  termSort term' @?= termSort ida

testUnifySortMismatch :: Assertion
testUnifySortMismatch = do
  let a = mkTerm sigBasic "a" []
  let ida = mkTerm sigBasic "id" [a]
  unify a ida @?= Nothing

testMatchRepeatedVar :: Assertion
testMatchRepeatedVar = do
  let scope = ScopeId "p"
  let vx = Var scope 0
  let x = mkVar objSort vx
  let a = mkTerm sigBasic "a" []
  let b = mkTerm sigBasic "b" []
  let pat = mkTerm sigBasic "m" [x, x]
  match pat (mkTerm sigBasic "m" [a, b]) @?= Nothing
  case match pat (mkTerm sigBasic "m" [a, a]) of
    Nothing -> assertFailure "expected repeated-var match"
    Just subst ->
      M.lookup vx subst @?= Just a

testMatchOpMismatch :: Assertion
testMatchOpMismatch = do
  let a = mkTerm sigBasic "a" []
  let fa = mkTerm sigBasic "f" [a]
  let ga = mkTerm sigBasic "g" [a]
  match fa ga @?= Nothing

testMatchSortIndices :: Assertion
testMatchSortIndices = do
  let scope = ScopeId "p"
  let vx = Var scope 0
  let x = mkVar objSort vx
  let a = mkTerm sigBasic "a" []
  let pat = mkTerm sigBasic "id" [x]
  case match pat (mkTerm sigBasic "id" [a]) of
    Nothing -> assertFailure "expected match"
    Just subst -> M.lookup vx subst @?= Just a
