{-# LANGUAGE OverloadedStrings #-}
module Test.DSL.Functors
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile, elabRawFileWithEnv)
import Strat.Frontend.Env (ModuleEnv(..), DoctrineFunctorDef(..))
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , GenDecl(..)
  , deriveCtorTables
  , gdPlainDom
  , lookupCtorRefForOwnerInTables
  )
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj (Obj(..), ObjName(..), ObjRef(..), mkCon)
import qualified Strat.Poly.Morphism as PolyMorph


tests :: TestTree
tests =
  testGroup
    "DSL.Functors"
    [ testCase "apply preserves target names and maps body references via impl" testApplyPreservesTargetNames
    , testCase "apply collision renaming keeps target name and prefixes body collision" testApplyCollisionRename
    , testCase "multi-parameter apply requires exact mapping keys" testApplyMappingCoverage
    , testCase "apply fills implicit identity type maps from implementation morphisms" testApplyImplicitIdentityTypeMap
    , testCase "apply implicit identity type maps require matching arity" testApplyImplicitIdentityTypeMapArity
    , testCase "apply checks generator targets after mode mapping" testApplyGeneratorModeMapping
    , testCase "apply reports missing type mappings per parameter" testApplyMissingMappingDiagnostics
    , testCase "apply reports missing gen mappings per parameter" testApplyMissingGenMappingDiagnostics
    , testCase "zero-parameter functors are rejected" testZeroParameterFunctorRejected
    , testCase "functor body requires parameter namespaces" testNamespaceEnforcement
    , testCase "functor body may extend mode theory" testModeTheoryExtensionAllowed
    , testCase "morphism checking enforces mod_eq preservation" testModEqPreservation
    , testCase "functor body and iface get deterministic internal doctrine names" testFunctorInternalNames
    ]


testApplyPreservesTargetNames :: Assertion
testApplyPreservesTargetNames = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "doctrine L where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen Box : [] -> [M.U_M] @M;"
          , "}"
          , "morphism impl : S -> L where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  type X @M -> Box @M;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  gen flip : [L::M.L::X] -> [L::M.L::X] @L::M;"
          , "}"
          , "doctrine R = apply F to L using { L = impl; };"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "R"
  let mode = ModeName "M"
  ctorTables <- case deriveCtorTables doc of
    Left err -> assertFailure (T.unpack err)
    Right tables -> pure tables
  boxRef <- case lookupCtorRefForOwnerInTables doc ctorTables mode (ObjName "Box") of
    Nothing -> assertFailure "expected Box constructor in R"
    Just ref -> pure ref
  let xRef = lookupCtorRefForOwnerInTables doc ctorTables mode (ObjName "X")
  assertBool "R should not expose X constructor" (xRef == Nothing)
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected mode M generator table"
    Just table -> pure table
  flipGen <- case M.lookup (GenName "flip") gens of
    Nothing -> assertFailure "expected generator flip"
    Just g -> pure g
  let expectedTy = mkCon boxRef []
  gdPlainDom flipGen @?= [expectedTy]
  gdCod flipGen @?= [expectedTy]


testApplyCollisionRename :: Assertion
testApplyCollisionRename = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "doctrine L where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen Box : [] -> [M.U_M] @M;"
          , "  gen get : [] -> [Box] @M;"
          , "}"
          , "morphism impl : S -> L where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  type X @M -> Box @M;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  gen get : [L::M.L::X] -> [L::M.L::X] @L::M;"
          , "}"
          , "doctrine R = apply F to L using { L = impl; };"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "R"
  let mode = ModeName "M"
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected mode M generator table"
    Just table -> pure table
  assertBool "target get should be preserved" (M.member (GenName "get") gens)
  let renamed = [ g | GenName g <- M.keys gens, "F_get" `T.isPrefixOf` g ]
  assertBool "expected functor-collision rename F_get*" (not (null renamed))


testApplyMappingCoverage :: Assertion
testApplyMappingCoverage = do
  let srcMissing =
        T.unlines
          [ "doctrine SA where { mode M classifiedBy M via U_M; gen comp_ctx_ext(a@M) : [a] -> [a] @M; gen comp_var(a@M) : [a] -> [a] @M; gen comp_reindex(a@M) : [a] -> [a] @M; comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; }; gen U_M : [] -> [U_M] @M; gen A : [] -> [U_M] @M; }"
          , "doctrine SB where { mode M classifiedBy M via U_M; gen comp_ctx_ext(a@M) : [a] -> [a] @M; gen comp_var(a@M) : [a] -> [a] @M; gen comp_reindex(a@M) : [a] -> [a] @M; comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; }; gen U_M : [] -> [U_M] @M; gen B : [] -> [U_M] @M; }"
          , "doctrine T where { mode M classifiedBy M via U_M; gen comp_ctx_ext(a@M) : [a] -> [a] @M; gen comp_var(a@M) : [a] -> [a] @M; gen comp_reindex(a@M) : [a] -> [a] @M; comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; }; gen U_M : [] -> [U_M] @M; gen TA : [] -> [U_M] @M; gen TB : [] -> [U_M] @M; }"
          , "morphism implA : SA -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  type A @M -> TA @M;"
          , "}"
          , "morphism implB : SB -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  type B @M -> TB @M;"
          , "}"
          , "doctrine_functor F(A : SA, B : SB) where {"
          , "  gen a : [A::M.A::A] -> [A::M.A::A] @A::M;"
          , "  gen b : [B::M.B::B] -> [B::M.B::B] @B::M;"
          , "}"
          , "doctrine R = apply F to T using { A = implA; };"
          ]
  errMissing <- expectElabFailure srcMissing
  assertBool
    ("expected missing key B, got: " <> T.unpack errMissing)
    ("missing" `T.isInfixOf` errMissing && "B" `T.isInfixOf` errMissing)

  let srcExtra =
        T.unlines
          [ "doctrine SA where { mode M classifiedBy M via U_M; gen comp_ctx_ext(a@M) : [a] -> [a] @M; gen comp_var(a@M) : [a] -> [a] @M; gen comp_reindex(a@M) : [a] -> [a] @M; comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; }; gen U_M : [] -> [U_M] @M; gen A : [] -> [U_M] @M; }"
          , "doctrine SB where { mode M classifiedBy M via U_M; gen comp_ctx_ext(a@M) : [a] -> [a] @M; gen comp_var(a@M) : [a] -> [a] @M; gen comp_reindex(a@M) : [a] -> [a] @M; comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; }; gen U_M : [] -> [U_M] @M; gen B : [] -> [U_M] @M; }"
          , "doctrine T where { mode M classifiedBy M via U_M; gen comp_ctx_ext(a@M) : [a] -> [a] @M; gen comp_var(a@M) : [a] -> [a] @M; gen comp_reindex(a@M) : [a] -> [a] @M; comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; }; gen U_M : [] -> [U_M] @M; gen TA : [] -> [U_M] @M; gen TB : [] -> [U_M] @M; }"
          , "morphism implA : SA -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  type A @M -> TA @M;"
          , "}"
          , "morphism implB : SB -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  type B @M -> TB @M;"
          , "}"
          , "doctrine_functor F(A : SA, B : SB) where {"
          , "  gen a : [A::M.A::A] -> [A::M.A::A] @A::M;"
          , "  gen b : [B::M.B::B] -> [B::M.B::B] @B::M;"
          , "}"
          , "doctrine R = apply F to T using { A = implA; B = implB; C = implA; };"
          ]
  errExtra <- expectElabFailure srcExtra
  assertBool
    ("expected extra key C, got: " <> T.unpack errExtra)
    ("extra" `T.isInfixOf` errExtra && "C" `T.isInfixOf` errExtra)

testApplyImplicitIdentityTypeMap :: Assertion
testApplyImplicitIdentityTypeMap = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "}"
          , "doctrine_functor F(A : S) where {"
          , "  gen keep : [A::M.A::X] -> [A::M.A::X] @A::M;"
          , "}"
          , "doctrine App = apply F to T using { A = impl; };"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "App"
  let mode = ModeName "M"
  let ty = mkCon (ObjRef mode (ObjName "X")) []
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected mode M generator table"
    Just table -> pure table
  keepGen <- case M.lookup (GenName "keep") gens of
    Nothing -> assertFailure "expected keep generator"
    Just g -> pure g
  gdPlainDom keepGen @?= [ty]
  gdCod keepGen @?= [ty]

testApplyImplicitIdentityTypeMapArity :: Assertion
testApplyImplicitIdentityTypeMapArity = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X(a@M) : [] -> [M.U_M] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "}"
          , "doctrine_functor F(A : S) where {"
          , "}"
          , "doctrine App = apply F to T using { A = impl; };"
          ]
  err <- expectElabFailure src
  assertBool "expected apply coverage diagnostics" ("missing/incompatible required mappings" `T.isInfixOf` err)
  assertBool "expected arity-incompatible type to require explicit mapping" ("type=[M.X]" `T.isInfixOf` err)
  assertBool "expected explicit incompatible-type diagnostics" ("type_incompatible=[M.X]" `T.isInfixOf` err)

testApplyGeneratorModeMapping :: Assertion
testApplyGeneratorModeMapping = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "  gen f : [M.X] -> [M.X] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "  gen f : [M.X] -> [M.X] @M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  gen f @M -> f"
          , "}"
          , "doctrine_functor F(A : S) where {"
          , "}"
          , "doctrine App = apply F to T using { A = impl; };"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "App"
  let mode = ModeName "M"
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected mode M generator table"
    Just table -> pure table
  assertBool "expected target generator f to be preserved" (M.member (GenName "f") gens)

testApplyMissingMappingDiagnostics :: Assertion
testApplyMissingMappingDiagnostics = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen Str : [] -> [M.U_M] @M;"
          , "  literal Str @M = string;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "}"
          , "doctrine_functor F(A : S) where {"
          , "}"
          , "doctrine App = apply F to T using { A = impl; };"
          ]
  err <- expectElabFailure src
  assertBool "expected missing literal constructor in diagnostics" ("missing mapped constructor M.Str" `T.isInfixOf` err)
  assertBool "expected type-map guidance in diagnostics" ("Add a type_map entry" `T.isInfixOf` err)

testApplyMissingGenMappingDiagnostics :: Assertion
testApplyMissingGenMappingDiagnostics = do
  let setupSrc =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "  gen f : [M.X] -> [M.X] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "  gen f : [M.X] -> [M.X] @M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  gen f @M -> f"
          , "}"
          , "doctrine_functor F(A : S) where {"
          , "}"
          ]
  env <- expectElab setupSrc
  impl <- case M.lookup "impl" (meMorphisms env) of
    Nothing -> assertFailure "missing morphism impl" >> error "unreachable"
    Just m -> pure m
  let implBad =
        impl
          { PolyMorph.morName = "impl_bad"
          , PolyMorph.morGenMap = M.empty
          }
  let envBad =
        env
          { meMorphisms = M.insert "impl_bad" implBad (meMorphisms env)
          }
  let applySrc = "doctrine App = apply F to T using { A = impl_bad; };"
  err <- expectElabFailureWithEnv envBad applySrc
  assertBool "expected param name in diagnostics" ("parameter A" `T.isInfixOf` err)
  assertBool "expected missing gen in diagnostics" ("gen=[M.f]" `T.isInfixOf` err)

testZeroParameterFunctorRejected :: Assertion
testZeroParameterFunctorRejected = do
  let src =
        T.unlines
          [ "doctrine_functor F() where {"
          , "}"
          ]
  case parseRawFile src of
    Left _ -> pure ()
    Right _ -> assertFailure "expected parser to reject zero-parameter doctrine_functor"


testNamespaceEnforcement :: Assertion
testNamespaceEnforcement = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  gen bad : [L::M.X] -> [L::M.X] @L::M;"
          , "}"
          ]
  err <- expectElabFailure src
  assertBool "expected unknown type due missing namespace" ("unknown type" `T.isInfixOf` err)


testModeTheoryExtensionAllowed :: Assertion
testModeTheoryExtensionAllowed = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  modality mu : M -> M;"
          , "  mod_eq mu -> id@M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode N classifiedBy N via N.U_N;"
          , "  gen comp_ctx_ext(a@N) : [a] -> [a] @N;"
          , "  gen comp_var(a@N) : [a] -> [a] @N;"
          , "  gen comp_reindex(a@N) : [a] -> [a] @N;"
          , "  comprehension N where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_N : [] -> [N.U_N] @N;"
          , "  modality nu : N -> N;"
          , "  mod_eq nu -> id@N;"
          , "  gen Y : [] -> [N.U_N] @N;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> N;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  modality mu -> nu;"
          , "  type U_M @M -> U_N @N;"
          , "  type X @M -> Y @N;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  mode K classifiedBy K via up(L::M.L::U_M);"
          , "  gen comp_ctx_ext(a@K) : [a] -> [a] @K;"
          , "  gen comp_var(a@K) : [a] -> [a] @K;"
          , "  gen comp_reindex(a@K) : [a] -> [a] @K;"
          , "  comprehension K where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  modality up : L::M -> K;"
          , "  gen U_K : [] -> [up(L::M.L::U_M)] @K;"
          , "  gen Z : [] -> [up(L::M.L::U_M)] @K;"
          , "}"
          , "doctrine R = apply F to T using { L = impl; };"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "R"
  ctorTables <- case deriveCtorTables doc of
    Left err -> assertFailure (T.unpack err)
    Right tables -> pure tables
  let yRef = lookupCtorRefForOwnerInTables doc ctorTables (ModeName "N") (ObjName "Y")
  let zRef = lookupCtorRefForOwnerInTables doc ctorTables (ModeName "K") (ObjName "Z")
  assertBool "expected pushed mode N constructor Y" (yRef /= Nothing)
  assertBool "expected new body mode K constructor Z" (zRef /= Nothing)


testModEqPreservation :: Assertion
testModEqPreservation = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  modality mu : M -> M;"
          , "  lift_classifier mu = id@M;"
          , "  mod_eq mu . mu -> mu;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "  gen g : [M.X] -> [M.X] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  modality a : M -> M;"
          , "  modality b : M -> M;"
          , "  lift_classifier a = id@M;"
          , "  lift_classifier b = id@M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "  gen g : [M.X] -> [M.X] @M;"
          , "}"
          , "morphism bad : S -> T where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  modality mu -> a . b;"
          , "  type X @M -> X @M;"
          , "  gen g @M -> g"
          , "}"
          ]
  err <- expectElabFailure src
  assertBool "expected mod_eq preservation error" ("mod_eq" `T.isInfixOf` err)


testFunctorInternalNames :: Assertion
testFunctorInternalNames = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen X : [] -> [M.U_M] @M;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  gen flip : [L::M.L::X] -> [L::M.L::X] @L::M;"
          , "}"
          ]
  env <- expectElab src
  functorDef <- case M.lookup "F" (meFunctors env) of
    Nothing -> assertFailure "missing doctrine_functor F" >> error "unreachable"
    Just def -> pure def
  dName (dfBody functorDef) @?= "F.__body"
  dName (dfIface functorDef) @?= "F.__iface"


expectElab :: T.Text -> IO ModuleEnv
expectElab src =
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right raw ->
      case elabRawFile raw of
        Left err -> assertFailure (T.unpack err) >> error "unreachable"
        Right env -> pure env


expectDoctrine :: ModuleEnv -> T.Text -> IO Doctrine
expectDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> error "unreachable"
    Just doc -> pure doc


expectElabFailure :: T.Text -> IO T.Text
expectElabFailure src =
  case parseRawFile src of
    Left err -> pure err
    Right raw ->
      case elabRawFile raw of
        Left err -> pure err
        Right _ -> assertFailure "expected elaboration failure" >> error "unreachable"

expectElabFailureWithEnv :: ModuleEnv -> T.Text -> IO T.Text
expectElabFailureWithEnv env src =
  case parseRawFile src of
    Left err -> pure err
    Right raw ->
      case elabRawFileWithEnv env raw of
        Left err -> pure err
        Right _ -> assertFailure "expected elaboration failure" >> error "unreachable"
