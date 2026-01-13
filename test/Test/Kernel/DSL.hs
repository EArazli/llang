{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.DSL
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Elab
import Strat.Kernel.DoctrineExpr
import Strat.Kernel.Presentation
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Types
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Test.Kernel.Fixtures

tests :: TestTree
tests =
  testGroup
    "Kernel.DSL"
    [ testCase "load succeeds" testLoad
    , testCase "AB disjoint" testDisjoint
    , testCase "ABshared enables cross-apply" testShared
    , testCase "Base@C & Ext@C works" testExtendsLike
    , testCase "duplicate eq names fails" testDuplicateEq
    , testCase "rename ops works" testRenameOps
    , testCase "share unknown op fails" testShareUnknown
    , testCase "RL orientation parses" testRLOrientation
    , testCase "associativity preserves order" testAssocOrdering
    , testCase "share precedence" testSharePrecedence
    , testCase "share sorts merges" testShareSorts
    , testCase "parse error" testParseError
    , testCase "instantiation requires where-defined" testInstRequiresWhere
    , testCase "unknown doctrine reference" testUnknownDoctrine
    ]

kernelDslProgram :: T.Text
kernelDslProgram =
  T.unlines
    [ "doctrine A where {"
    , "  sort Obj;"
    , "  op z : Obj;"
    , "  op f : (x:Obj) -> Obj;"
    , "  op g : (x:Obj) -> Obj;"
    , "  computational r : (x:Obj) |- f(?x) -> g(?x);"
    , "}"
    , ""
    , "doctrine B where {"
    , "  sort Obj;"
    , "  op z : Obj;"
    , "  op f : (x:Obj) -> Obj;"
    , "  op h : (x:Obj) -> Obj;"
    , "  computational r : (x:Obj) |- f(?x) -> h(?x);"
    , "}"
    , ""
    , "doctrine AB = A & B;"
    , ""
    , "doctrine ABshared = share ops { A.f = B.f } in share sorts { A.Obj = B.Obj } in (A & B);"
    , ""
    , "doctrine Base where {"
    , "  sort Obj;"
    , "  op z : Obj;"
    , "  op f : (x:Obj) -> Obj;"
    , "  computational base : (x:Obj) |- f(?x) -> ?x;"
    , "}"
    , ""
    , "doctrine Ext where {"
    , "  sort Obj;"
    , "  op z : Obj;"
    , "  op f : (x:Obj) -> Obj;"
    , "  op k : (x:Obj) -> Obj;"
    , "  computational ext : (x:Obj) |- k(f(?x)) -> ?x;"
    , "}"
    , ""
    , "doctrine C = (Base@C) & (Ext@C);"
    , ""
    , "doctrine Cbad = (A@C) & (B@C);"
    , ""
    , "doctrine Aren = rename ops { A.g -> A.g2 } in A;"
    , ""
    , "doctrine BadShare = share ops { A.missing = B.f } in (A & B);"
    , ""
    , "doctrine RLTest where {"
    , "  sort Obj;"
    , "  op a : Obj;"
    , "  op b : Obj;"
    , "  computational rr : a <- b;"
    , "}"
    , ""
    , "doctrine AssocTest = A & B & Base;"
    , ""
    , "doctrine ABshared2 = share ops { A.f = B.f } in share sorts { A.Obj = B.Obj } in A & B;"
    , ""
    , "doctrine ABshareSort = share sorts { A.Obj = B.Obj } in (A & B);"
    ]

testLoad :: Assertion
testLoad =
  case loadDoctrines kernelDslProgram of
    Left err -> assertFailure (show err)
    Right env -> do
      let expected =
            [ "A", "B", "AB", "ABshared", "Base", "Ext", "C", "Cbad"
            , "Aren", "BadShare", "RLTest", "AssocTest", "ABshared2", "ABshareSort"
            ]
      assertBool "expected all keys" (all (`M.member` env) expected)

requireEnv :: IO (M.Map T.Text DocExpr)
requireEnv =
  case loadDoctrines kernelDslProgram of
    Left err -> assertFailure (show err) >> pure M.empty
    Right env -> pure env

requireExpr :: M.Map T.Text DocExpr -> T.Text -> IO DocExpr
requireExpr env name =
  case M.lookup name env of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> pure (Atom "Missing" (Presentation "Missing" (Signature M.empty M.empty) []))
    Just expr -> pure expr

testDisjoint :: Assertion
testDisjoint = do
  env <- requireEnv
  expr <- requireExpr env "AB"
  case (elabDocExpr expr, compileDocExpr UseOnlyComputationalLR expr) of
    (Right pres, Right rs) -> do
      let sig = presSig pres
      let t = mkTerm sig "A.f" [mkTerm sig "A.z" []]
      let reds = rewriteOnce rs t
      map (stepRule . redexStep) reds @?= [RuleId "A.r" DirLR]
    (Left err, _) -> assertFailure (T.unpack err)
    (_, Left err) -> assertFailure (T.unpack err)

testShared :: Assertion
testShared = do
  env <- requireEnv
  expr <- requireExpr env "ABshared"
  case (elabDocExpr expr, compileDocExpr UseOnlyComputationalLR expr) of
    (Right pres, Right rs) -> do
      let sig = presSig pres
      let t = mkTerm sig "A.f" [mkTerm sig "A.z" []]
      let reds = rewriteOnce rs t
      map (stepRule . redexStep) reds
        @?= [RuleId "A.r" DirLR, RuleId "B.r" DirLR]
    (Left err, _) -> assertFailure (T.unpack err)
    (_, Left err) -> assertFailure (T.unpack err)

testExtendsLike :: Assertion
testExtendsLike = do
  env <- requireEnv
  expr <- requireExpr env "C"
  case (elabDocExpr expr, compileDocExpr UseOnlyComputationalLR expr) of
    (Right pres, Right rs) -> do
      let sig = presSig pres
      let z = mkTerm sig "C.z" []
      let t = mkTerm sig "C.k" [mkTerm sig "C.f" [z]]
      normalize 1 rs t @?= z
    (Left err, _) -> assertFailure (T.unpack err)
    (_, Left err) -> assertFailure (T.unpack err)

testDuplicateEq :: Assertion
testDuplicateEq = do
  env <- requireEnv
  expr <- requireExpr env "Cbad"
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate eq name error"

testRenameOps :: Assertion
testRenameOps = do
  env <- requireEnv
  expr <- requireExpr env "Aren"
  case elabDocExpr expr of
    Left err -> assertFailure (T.unpack err)
    Right pres ->
      case presEqs pres of
        (e1 : _) ->
          case termNode (eqRHS e1) of
            TOp op _ -> op @?= OpName "A.g2"
            _ -> assertFailure "expected op"
        _ -> assertFailure "expected equation"

testShareUnknown :: Assertion
testShareUnknown = do
  env <- requireEnv
  expr <- requireExpr env "BadShare"
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected unknown op error"

testRLOrientation :: Assertion
testRLOrientation = do
  env <- requireEnv
  expr <- requireExpr env "RLTest"
  case compileDocExpr UseAllOriented expr of
    Left err -> assertFailure (T.unpack err)
    Right rs -> map ruleId (rsRules rs) @?= [RuleId "RLTest.rr" DirRL]

testAssocOrdering :: Assertion
testAssocOrdering = do
  env <- requireEnv
  expr <- requireExpr env "AssocTest"
  case elabDocExpr expr of
    Left err -> assertFailure (T.unpack err)
    Right pres -> map eqName (presEqs pres) @?= ["A.r", "B.r", "Base.base"]

testSharePrecedence :: Assertion
testSharePrecedence = do
  env <- requireEnv
  expr <- requireExpr env "ABshared2"
  case (elabDocExpr expr, compileDocExpr UseOnlyComputationalLR expr) of
    (Right pres, Right rs) -> do
      let sig = presSig pres
      let t = mkTerm sig "A.f" [mkTerm sig "A.z" []]
      map (stepRule . redexStep) (rewriteOnce rs t)
        @?= [RuleId "A.r" DirLR, RuleId "B.r" DirLR]
    (Left err, _) -> assertFailure (T.unpack err)
    (_, Left err) -> assertFailure (T.unpack err)

testShareSorts :: Assertion
testShareSorts = do
  env <- requireEnv
  expr <- requireExpr env "ABshareSort"
  case elabDocExpr expr of
    Left err -> assertFailure (T.unpack err)
    Right pres -> do
      let names = M.keys (sigSortCtors (presSig pres))
      names @?= [SortName "A.Obj"]

testParseError :: Assertion
testParseError = do
  let bad = "doctrine A where { op f : Obj }"
  case loadDoctrines bad of
    Left _ -> pure ()
    Right _ -> assertFailure "expected parse error"

testInstRequiresWhere :: Assertion
testInstRequiresWhere = do
  let prog =
        T.unlines
          [ "doctrine A where { sort Obj; op a : Obj; }"
          , "doctrine B = A;"
          , "doctrine C = B@C;"
          ]
  case loadDoctrines prog of
    Left _ -> pure ()
    Right _ -> assertFailure "expected instantiation error"

testUnknownDoctrine :: Assertion
testUnknownDoctrine = do
  let prog = "doctrine A = Missing;"
  case loadDoctrines prog of
    Left _ -> pure ()
    Right _ -> assertFailure "expected unknown doctrine error"
