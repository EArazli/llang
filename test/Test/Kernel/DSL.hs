{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.DSL
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile, parseRawExpr)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Kernel.DSL.AST
import Strat.Kernel.DoctrineExpr
import Strat.Kernel.Presentation
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Types
import Strat.Frontend.Env
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
    , testCase "syntax/model/run parsing" testSyntaxModelRunParse
    , testCase "parse morphism op mapping with params" testParseMorphismParams
    , testCase "parse morphism shorthand" testParseMorphismShorthand
    , testCase "parse run_spec and multiple runs" testParseRunSpecMultiple
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

loadEnv :: T.Text -> IO ModuleEnv
loadEnv src =
  case parseRawFile src of
    Left err -> assertFailure (show err) >> pure emptyEnv
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (show err) >> pure emptyEnv
        Right env -> pure env

requireExpr :: ModuleEnv -> T.Text -> IO DocExpr
requireExpr env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> pure (Atom "Missing" (Presentation "Missing" (Signature M.empty M.empty) []))
    Just expr -> pure expr


testLoad :: Assertion
testLoad = do
  env <- loadEnv kernelDslProgram
  let expected =
        [ "A", "B", "AB", "ABshared", "Base", "Ext", "C", "Cbad"
        , "Aren", "BadShare", "RLTest", "AssocTest", "ABshared2", "ABshareSort"
        ]
  assertBool "expected all keys" (all (`M.member` meDoctrines env) expected)


testDisjoint :: Assertion
testDisjoint = do
  env <- loadEnv kernelDslProgram
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
  env <- loadEnv kernelDslProgram
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
  env <- loadEnv kernelDslProgram
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
  env <- loadEnv kernelDslProgram
  expr <- requireExpr env "Cbad"
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate eq name error"


testRenameOps :: Assertion
testRenameOps = do
  env <- loadEnv kernelDslProgram
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
  env <- loadEnv kernelDslProgram
  expr <- requireExpr env "BadShare"
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected unknown op error"


testRLOrientation :: Assertion
testRLOrientation = do
  env <- loadEnv kernelDslProgram
  expr <- requireExpr env "RLTest"
  case compileDocExpr UseAllOriented expr of
    Left err -> assertFailure (T.unpack err)
    Right rs -> map ruleId (rsRules rs) @?= [RuleId "RLTest.rr" DirRL]


testAssocOrdering :: Assertion
testAssocOrdering = do
  env <- loadEnv kernelDslProgram
  expr <- requireExpr env "AssocTest"
  case elabDocExpr expr of
    Left err -> assertFailure (T.unpack err)
    Right pres -> map eqName (presEqs pres) @?= ["A.r", "B.r", "Base.base"]


testSharePrecedence :: Assertion
testSharePrecedence = do
  env <- loadEnv kernelDslProgram
  expr <- requireExpr env "ABshared2"
  case (elabDocExpr expr, compileDocExpr UseOnlyComputationalLR expr) of
    (Right pres, Right rs) -> do
      let sig = presSig pres
      let t = mkTerm sig "A.f" [mkTerm sig "A.z" []]
      let reds = rewriteOnce rs t
      map (stepRule . redexStep) reds
        @?= [RuleId "A.r" DirLR, RuleId "B.r" DirLR]
    (Left err, _) -> assertFailure (T.unpack err)
    (_, Left err) -> assertFailure (T.unpack err)


testShareSorts :: Assertion
testShareSorts = do
  env <- loadEnv kernelDslProgram
  expr <- requireExpr env "ABshareSort"
  case elabDocExpr expr of
    Left err -> assertFailure (T.unpack err)
    Right pres ->
      case sigSortCtors (presSig pres) of
        ctors -> assertBool "merged sort ctor" (M.member (SortName "A.Obj") ctors && not (M.member (SortName "B.Obj") ctors))


testParseError :: Assertion
testParseError =
  case parseRawExpr "A &" of
    Left _ -> pure ()
    Right _ -> assertFailure "expected parse error"


testInstRequiresWhere :: Assertion
testInstRequiresWhere = do
  let prog = T.unlines
        [ "doctrine A where {"
        , "  sort Obj;"
        , "  op f : Obj;"
        , "}"
        , "doctrine B = A;"
        , "doctrine C = (B@C);"
        ]
  case parseRawFile prog of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected instantiation error"


testUnknownDoctrine :: Assertion
testUnknownDoctrine = do
  let prog = T.unlines
        [ "doctrine A = Missing;"
        ]
  case parseRawFile prog of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected unknown doctrine error"


testSyntaxModelRunParse :: Assertion
testSyntaxModelRunParse = do
  let prog = T.unlines
        [ "syntax S for doctrine A where {"
        , "  print atom \"e\" = e;"
        , "  allow call;"
        , "  varprefix \"?\";"
        , "}"
        , "model M where {"
        , "  default = symbolic;"
        , "  op e() = \"\";"
        , "}"
        , "run_spec RS where {"
        , "  doctrine A;"
        , "  syntax S;"
        , "  model M;"
        , "  show normalized;"
        , "}"
        , "run main using RS where { }"
        , "---"
        , "e"
        ]
  case parseRawFile prog of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testParseMorphismParams :: Assertion
testParseMorphismParams = do
  let prog = T.unlines
        [ "doctrine A where { sort Obj; op f : (x:Obj)(y:Obj) -> Obj; }"
        , "doctrine B where { sort Obj; op g : (x:Obj)(y:Obj) -> Obj; }"
        , "morphism M : A -> B where { op f(x,y) = g(?y,?x); }"
        ]
  case parseRawFile prog of
    Left err -> assertFailure (T.unpack err)
    Right (RawFile decls) ->
      case [ item | DeclMorphismWhere item <- decls ] of
        [morph] ->
          case [ i | i@RMIOp{} <- rmdItems morph ] of
            [RMIOp src (Just params) rhs] -> do
              src @?= "f"
              params @?= ["x","y"]
              rhs @?= RApp "g" [RVar "y", RVar "x"]
            _ -> assertFailure "expected morphism op mapping with params"
        _ -> assertFailure "expected one morphism decl"

testParseMorphismShorthand :: Assertion
testParseMorphismShorthand = do
  let prog = T.unlines
        [ "doctrine A where { sort Obj; op f : (x:Obj) -> Obj; }"
        , "doctrine B where { sort Obj; op g : (x:Obj) -> Obj; }"
        , "morphism M : A -> B where { op f = g; }"
        ]
  case parseRawFile prog of
    Left err -> assertFailure (T.unpack err)
    Right (RawFile decls) ->
      case [ item | DeclMorphismWhere item <- decls ] of
        [morph] ->
          case [ i | i@RMIOp{} <- rmdItems morph ] of
            [RMIOp src Nothing rhs] -> do
              src @?= "f"
              rhs @?= RApp "g" []
            _ -> assertFailure "expected morphism shorthand op mapping"
        _ -> assertFailure "expected one morphism decl"

testParseRunSpecMultiple :: Assertion
testParseRunSpecMultiple = do
  let prog = T.unlines
        [ "run_spec S where { doctrine A; }"
        , "run main using S where { }"
        , "---"
        , "a"
        , "---"
        , "run other using S where { }"
        , "---"
        , "b"
        ]
  case parseRawFile prog of
    Left err -> assertFailure (T.unpack err)
    Right (RawFile decls) -> do
      let specCount = length [ () | DeclRunSpec _ _ <- decls ]
      let runNames = [ rnrName r | DeclRun r <- decls ]
      specCount @?= 1
      runNames @?= ["main","other"]
