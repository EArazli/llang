{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.DSL
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Kernel.DSL.AST
import Strat.Frontend.Env
import qualified Data.Map.Strict as M
import qualified Data.Text as T

tests :: TestTree
tests =
  testGroup
    "Kernel.DSL"
    [ testCase "load succeeds" testLoad
    , testCase "pushout decl generates morphisms" testPushoutDecl
    , testCase "duplicate eq names fails" testDuplicateEq
    , testCase "unknown doctrine reference" testUnknownDoctrine
    , testCase "syntax/model/run parsing" testSyntaxModelRunParse
    , testCase "parse morphism op mapping with params" testParseMorphismParams
    , testCase "parse morphism shorthand" testParseMorphismShorthand
    , testCase "parse run_spec and multiple runs" testParseRunSpecMultiple
    ]

kernelDslProgram :: T.Text
kernelDslProgram =
  T.unlines
    [ "doctrine Category where {"
    , "  sort Obj;"
    , "  op a : Obj;"
    , "  op f : (x:Obj) -> Obj;"
    , "}"
    , "doctrine BoolExt extends Category where {"
    , "  op g : (x:Obj) -> Obj;"
    , "  computational rB : (x:Obj) |- f(?x) -> g(?x);"
    , "}"
    , "doctrine NatExt extends Category where {"
    , "  op h : (x:Obj) -> Obj;"
    , "  computational rN : (x:Obj) |- f(?x) -> h(?x);"
    , "}"
    , "doctrine Both = pushout BoolExt.fromBase NatExt.fromBase;"
    ]

loadEnv :: T.Text -> IO ModuleEnv
loadEnv src =
  case parseRawFile src of
    Left err -> assertFailure (show err) >> pure emptyEnv
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (show err) >> pure emptyEnv
        Right env -> pure env

testLoad :: Assertion
testLoad = do
  env <- loadEnv kernelDslProgram
  let expected = ["Category", "BoolExt", "NatExt", "Both"]
  assertBool "expected all doctrines" (all (`M.member` meDoctrines env) expected)

testPushoutDecl :: Assertion
testPushoutDecl = do
  env <- loadEnv kernelDslProgram
  assertBool "Both doctrine present" (M.member "Both" (meDoctrines env))
  assertBool "Both.inl present" (M.member "Both.inl" (meMorphisms env))
  assertBool "Both.inr present" (M.member "Both.inr" (meMorphisms env))
  assertBool "Both.glue present" (M.member "Both.glue" (meMorphisms env))

testDuplicateEq :: Assertion
testDuplicateEq = do
  let prog = T.unlines
        [ "doctrine A where {"
        , "  sort Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational r : (x:Obj) |- f(?x) -> ?x;"
        , "  computational r : (x:Obj) |- f(?x) -> f(?x);"
        , "}"
        ]
  case parseRawFile prog of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected duplicate equation error"

testUnknownDoctrine :: Assertion
testUnknownDoctrine = do
  let prog = T.unlines
        [ "doctrine A extends Missing where {"
        , "  sort Obj;"
        , "}"
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
        [ "doctrine A where {"
        , "  sort Obj;"
        , "  op e : Obj;"
        , "}"
        , "syntax S where {"
        , "  print atom \"e\" = e;"
        , "  allow call;"
        , "  varprefix \"?\";"
        , "}"
        , "model M : A where {"
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
