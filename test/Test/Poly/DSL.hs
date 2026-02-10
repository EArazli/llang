{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.DSL
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (emptyEnv, meDoctrines, meModels, meMorphisms, meRuns)
import Strat.Model.Spec (MExpr(..), ModelBackend(..), ModelSpec(..), OpClause(..), FoldSpec(..))
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.ModeTheory (ModeName(..), mtModes)
import Strat.Poly.Doctrine
import Strat.Poly.Diagram (Diagram(..), diagramCod)
import Strat.Poly.Graph (Edge(..), EdgePayload(..), BinderArg(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeArg(..), IxTerm(..), TypeName(..), TypeRef(..))
import Strat.Poly.Rewrite (rulesFromDoctrine, rewriteOnce)
import Strat.Poly.Normalize (normalize, NormalizationStatus(..))
import Strat.Poly.Pretty (renderDiagram)
import Strat.Poly.Morphism (Morphism(..), checkMorphism)
import Strat.RunSpec (RunSpec(..))
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "Poly.DSL"
    [ testCase "parse/elab monoid doctrine and normalize" testPolyDSLNormalize
    , testCase "implicit index arg infers bound binder index" testImplicitBinderIndexInference
    , testCase "morphism declared in example file" testPolyMorphismDSL
    , testCase "doctrine extends produces fromBase morphism" testPolyFromBaseMorphism
    , testCase "pushout renames gen types" testPolyPushoutRenamesTypes
    , testCase "morphism type map binder arity mismatch fails" testTypeMapBinderMismatch
    , testCase "morphism type map unknown binder fails" testTypeMapUnknownVar
    , testCase "morphism type map target mode mismatch fails" testTypeMapTargetModeMismatch
    , testCase "morphism mode map parses and elaborates" testMorphismModeMap
    , testCase "run inherits expression from run_spec" testRunExprInheritedFromRunSpec
    , testCase "run_spec inheritance chains expression" testRunSpecInheritanceChain
    , testCase "run without inherited expression fails" testRunMissingExpressionFails
    , testCase "model fold block elaborates required hooks" testModelFoldBlockElab
    , testCase "model using merges fold and ops" testModelUsingMerges
    ]

testPolyDSLNormalize :: Assertion
testPolyDSLNormalize = do
  let src = T.unlines
        [ "doctrine Monoid where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen unit : [] -> [A] @M;"
        , "  gen mul : [A, A] -> [A] @M;"
        , "  rule computational assoc -> : [A, A, A] -> [A] @M ="
        , "    (mul * id[A]) ; mul == (id[A] * mul) ; mul"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  doc <- case M.lookup "Monoid" (meDoctrines env) of
    Nothing -> assertFailure "expected Monoid doctrine"
    Just d -> pure d
  mode <- case M.keys (mtModes (dModes doc)) of
    [m] -> pure m
    _ -> assertFailure "expected single mode"
  rawExpr <- case parseDiagExpr "(mul * id[A]) ; mul" of
    Left err -> assertFailure (T.unpack err)
    Right e -> pure e
  diag <- case elabDiagExpr emptyEnv doc mode [] rawExpr of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let rules = rulesFromDoctrine doc
  norm <- case normalize (doctrineTypeTheory doc) 10 rules diag of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case norm of
    Finished d -> do
      -- normalization should agree with a single rewrite step
      step <- case rewriteOnce (doctrineTypeTheory doc) rules diag of
        Left err -> assertFailure (T.unpack err)
        Right r -> pure r
      case step of
        Nothing -> assertFailure "expected a rewrite step"
        Just expected -> do
          got <- case renderDiagram d of
            Left err -> assertFailure (T.unpack err)
            Right txt -> pure txt
          want <- case renderDiagram expected of
            Left err -> assertFailure (T.unpack err)
            Right txt -> pure txt
          got @?= want
    OutOfFuel _ -> assertFailure "expected normalization to finish"

testImplicitBinderIndexInference :: Assertion
testImplicitBinderIndexInference = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  mode I;"
        , "  index_mode I;"
        , "  type Nat @I;"
        , "  index_fun Z : Nat @I;"
        , "  type Vec(n : Nat) @M;"
        , "  type Out @M;"
        , "  gen use(n : Nat) : [] -> [Vec(n)] @M;"
        , "  gen wrap : [binder { n : Nat } : [Vec(n)]] -> [Out] @M;"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  doc <- case M.lookup "D" (meDoctrines env) of
    Nothing -> assertFailure "expected doctrine D"
    Just d -> pure d
  expr <- case parseDiagExpr "wrap[use]" of
    Left err -> assertFailure (T.unpack err)
    Right e -> pure e
  diag <- case elabDiagExpr emptyEnv doc (ModeName "M") [] expr of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  case IM.elems (dEdges diag) of
    [Edge _ (PGen g _ [BAConcrete inner]) _ _] -> do
      g @?= GenName "wrap"
      cod <- case diagramCod inner of
        Left err -> assertFailure (T.unpack err)
        Right c -> pure c
      cod @?= [TCon (TypeRef (ModeName "M") (TypeName "Vec")) [TAIndex (IXBound 0)]]
    _ -> assertFailure "expected single wrap edge with one concrete binder argument"

testPolyMorphismDSL :: Assertion
testPolyMorphismDSL = do
  path <- getDataFileName "examples/lib/algebra/monoid_to_string.llang"
  src <- TIO.readFile path
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  case M.lookup "MonoidToString" (meMorphisms env) of
    Nothing -> assertFailure "expected morphism MonoidToString"
    Just _ -> pure ()

testPolyFromBaseMorphism :: Assertion
testPolyFromBaseMorphism = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen f : [A] -> [A] @M;"
        , "}"
        , "doctrine Ext extends Base where {"
        , "  gen g : [A] -> [A] @M;"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  mor <- case M.lookup "Ext.fromBase" (meMorphisms env) of
    Nothing -> assertFailure "expected morphism Ext.fromBase"
    Just m -> pure m
  case checkMorphism mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()

testPolyPushoutRenamesTypes :: Assertion
testPolyPushoutRenamesTypes = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode M;"
        , "}"
        , "doctrine Left extends Base where {"
        , "  type A @M;"
        , "  gen f : [A] -> [A] @M;"
        , "}"
        , "doctrine Right extends Base where {"
        , "  type B @M;"
        , "  gen g : [B] -> [B] @M;"
        , "}"
        , "doctrine Push = pushout Left.fromBase Right.fromBase;"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  doc <- case M.lookup "Push" (meDoctrines env) of
    Nothing -> assertFailure "expected Push doctrine"
    Just d -> pure d
  let mode = ModeName "M"
  types <- case M.lookup mode (dTypes doc) of
    Nothing -> assertFailure "expected type table for mode M"
    Just t -> pure t
  assertBool "expected Left_inl_A type" (M.member (TypeName "Left_inl_A") types)
  assertBool "expected Right_inr_B type" (M.member (TypeName "Right_inr_B") types)
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected generator table for mode M"
    Just g -> pure g
  genLeft <- case M.lookup (GenName "Left_inl_f") gens of
    Nothing -> assertFailure "expected Left_inl_f generator"
    Just g -> pure g
  let leftTy = TCon (TypeRef mode (TypeName "Left_inl_A")) []
  gdPlainDom genLeft @?= [leftTy]
  gdCod genLeft @?= [leftTy]

testTypeMapBinderMismatch :: Assertion
testTypeMapBinderMismatch = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  type T (a@M, b@M) @M;"
        , "}"
        , "morphism Bad : D -> D where {"
        , "  type T(a) @M -> T(a) @M;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected binder arity mismatch to fail"

testTypeMapUnknownVar :: Assertion
testTypeMapUnknownVar = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  type T (a@M) @M;"
        , "}"
        , "morphism Bad : D -> D where {"
        , "  type T(a) @M -> T(b) @M;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected unknown binder to fail"

testTypeMapTargetModeMismatch :: Assertion
testTypeMapTargetModeMismatch = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  mode C;"
        , "  type A @M;"
        , "  type B @C;"
        , "}"
        , "morphism Bad : D -> D where {"
        , "  type A @M -> C.B @M;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected target mode mismatch to fail"

testMorphismModeMap :: Assertion
testMorphismModeMap = do
  let src = T.unlines
        [ "doctrine Src where {"
        , "  mode C;"
        , "  type A @C;"
        , "  gen f : [A] -> [A] @C;"
        , "}"
        , "doctrine Tgt where {"
        , "  mode V;"
        , "  type B @V;"
        , "  gen g : [B] -> [B] @V;"
        , "}"
        , "morphism M : Src -> Tgt where {"
        , "  mode C -> V;"
        , "  type A @C -> B @V;"
        , "  gen f @C -> g"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  mor <- case M.lookup "M" (meMorphisms env) of
    Nothing -> assertFailure "expected morphism M"
    Just m -> pure m
  let modeC = ModeName "C"
  let modeV = ModeName "V"
  M.lookup modeC (morModeMap mor) @?= Just modeV

testRunExprInheritedFromRunSpec :: Assertion
testRunExprInheritedFromRunSpec = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen Lit : [] -> [A] @M;"
        , "}"
        , "run_spec Base where {"
        , "  doctrine D;"
        , "} "
        , "---"
        , "Lit"
        , "---"
        , "run main using Base;"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  runSpec <- case M.lookup "main" (meRuns env) of
    Nothing -> assertFailure "expected run main"
    Just rs -> pure rs
  prExprText runSpec @?= "Lit"

testRunSpecInheritanceChain :: Assertion
testRunSpecInheritanceChain = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen Lit : [] -> [A] @M;"
        , "}"
        , "run_spec Base where {"
        , "  doctrine D;"
        , "}"
        , "---"
        , "Lit"
        , "---"
        , "run_spec Derived using Base where {"
        , "}"
        , "run main using Derived;"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  runSpec <- case M.lookup "main" (meRuns env) of
    Nothing -> assertFailure "expected run main"
    Just rs -> pure rs
  prExprText runSpec @?= "Lit"

testModelFoldBlockElab :: Assertion
testModelFoldBlockElab = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen g : [A] -> [A] @M;"
        , "}"
        , "model F : D where {"
        , "  backend = fold;"
        , "  default = symbolic;"
        , "  fold {"
        , "    indent = \"  \";"
        , "    reserved = [\"if\", \"return\"];"
        , "    prologue_closed() = \"(() => {\";"
        , "    epilogue_closed() = \"})()\";"
        , "    prologue_open(params, paramDecls) = \"(x) => {\";"
        , "    epilogue_open() = \"}\";"
        , "    bind0(stmt) = stmt;"
        , "    bind1(out, ty, expr) = expr;"
        , "    bindN(outs, decls, expr) = expr;"
        , "    return0() = \"\";"
        , "    return1(out, ty) = out;"
        , "    returnN(outs, decls) = outs;"
        , "  }"
        , "  op g(x) = x;"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  (_, modelSpec) <- case M.lookup "F" (meModels env) of
    Nothing -> assertFailure "expected model F"
    Just m -> pure m
  msBackend modelSpec @?= BackendFold
  foldSpec <- case msFold modelSpec of
    Nothing -> assertFailure "expected fold spec in model F"
    Just fs -> pure fs
  let requiredHooks =
        [ "prologue_closed"
        , "epilogue_closed"
        , "prologue_open"
        , "epilogue_open"
        , "bind0"
        , "bind1"
        , "bindN"
        , "return0"
        , "return1"
        , "returnN"
        ]
  mapM_ (\name -> assertBool ("missing hook: " <> T.unpack name) (M.member name (fsHooks foldSpec))) requiredHooks

testModelUsingMerges :: Assertion
testModelUsingMerges = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen concat : [A, A] -> [A] @M;"
        , "  gen serve : [A] -> [] @M;"
        , "}"
        , "model Base : D where {"
        , "  backend = fold;"
        , "  default = symbolic;"
        , "  fold {"
        , "    prologue_closed() = \"(() => {\";"
        , "    epilogue_closed() = \"})()\";"
        , "    prologue_open(params, paramDecls) = \"(x) => {\";"
        , "    epilogue_open() = \"}\";"
        , "    bind0(stmt) = stmt;"
        , "    bind1(out, ty, expr) = expr;"
        , "    bindN(outs, decls, expr) = expr;"
        , "    return0() = \"\";"
        , "    return1(out, ty) = out;"
        , "    returnN(outs, decls) = outs;"
        , "  }"
        , "  op concat(a, b) = \"base_concat\";"
        , "  op serve(x) = \"base_serve\";"
        , "}"
        , "model Child : D using Base where {"
        , "  op serve(x) = \"child_serve\";"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  (_, baseModel) <- case M.lookup "Base" (meModels env) of
    Nothing -> assertFailure "expected model Base"
    Just m -> pure m
  (_, childModel) <- case M.lookup "Child" (meModels env) of
    Nothing -> assertFailure "expected model Child"
    Just m -> pure m
  msBackend childModel @?= BackendFold
  msFold childModel @?= msFold baseModel
  lookupOpExpr "concat" childModel @?= Just (MString "base_concat")
  lookupOpExpr "serve" childModel @?= Just (MString "child_serve")
  where
    lookupOpExpr name spec = ocExpr <$> findOp name (msOps spec)
    findOp _ [] = Nothing
    findOp name (clause:rest)
      | ocOp clause == name = Just clause
      | otherwise = findOp name rest

testRunMissingExpressionFails :: Assertion
testRunMissingExpressionFails = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  type A @M;"
        , "}"
        , "run main where {"
        , "  doctrine D;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertBool "expected missing expression error" ("run: missing expression" `T.isInfixOf` err)
        Right _ -> assertFailure "expected run elaboration failure"
