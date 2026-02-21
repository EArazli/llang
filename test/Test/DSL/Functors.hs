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
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), gdPlainDom)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..))
import qualified Strat.Poly.Morphism as PolyMorph


tests :: TestTree
tests =
  testGroup
    "DSL.Functors"
    [ testCase "apply preserves target names and maps body references via impl" testApplyPreservesTargetNames
    , testCase "apply collision renaming keeps target name and prefixes body collision" testApplyCollisionRename
    , testCase "multi-parameter apply requires exact mapping keys" testApplyMappingCoverage
    , testCase "apply fills implicit identity type maps from implementation morphisms" testApplyImplicitIdentityTypeMap
    , testCase "apply checks generator targets after mode mapping" testApplyGeneratorModeMapping
    , testCase "apply reports missing type/attr mappings per parameter" testApplyMissingMappingDiagnostics
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
          , "  mode M;"
          , "  type X @M;"
          , "}"
          , "doctrine L where {"
          , "  mode M;"
          , "  type Box @M;"
          , "}"
          , "morphism impl : S -> L where {"
          , "  mode M -> M;"
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
  let types = M.findWithDefault M.empty mode (dTypes doc)
  assertBool "expected Box type in R" (M.member (TypeName "Box") types)
  assertBool "R should not expose X type" (not (M.member (TypeName "X") types))
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected mode M generator table"
    Just table -> pure table
  flipGen <- case M.lookup (GenName "flip") gens of
    Nothing -> assertFailure "expected generator flip"
    Just g -> pure g
  let expectedTy = TCon (TypeRef mode (TypeName "Box")) []
  gdPlainDom flipGen @?= [expectedTy]
  gdCod flipGen @?= [expectedTy]


testApplyCollisionRename :: Assertion
testApplyCollisionRename = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  type X @M;"
          , "}"
          , "doctrine L where {"
          , "  mode M;"
          , "  type Box @M;"
          , "  gen get : [] -> [Box] @M;"
          , "}"
          , "morphism impl : S -> L where {"
          , "  mode M -> M;"
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
          [ "doctrine SA where { mode M; type A @M; }"
          , "doctrine SB where { mode M; type B @M; }"
          , "doctrine T where { mode M; type TA @M; type TB @M; }"
          , "morphism implA : SA -> T where { mode M -> M; type A @M -> TA @M; }"
          , "morphism implB : SB -> T where { mode M -> M; type B @M -> TB @M; }"
          , "doctrine_functor F(A : SA, B : SB) where {"
          , "  gen a : [A::M.A::A] -> [A::M.A::A] @A::M;"
          , "  gen b : [B::M.B::B] -> [B::M.B::B] @B::M;"
          , "}"
          , "doctrine R = apply F to T using { A = implA; };"
          ]
  errMissing <- expectElabFailure srcMissing
  assertBool "expected missing key B" ("missing: B" `T.isInfixOf` errMissing)

  let srcExtra =
        T.unlines
          [ "doctrine SA where { mode M; type A @M; }"
          , "doctrine SB where { mode M; type B @M; }"
          , "doctrine T where { mode M; type TA @M; type TB @M; }"
          , "morphism implA : SA -> T where { mode M -> M; type A @M -> TA @M; }"
          , "morphism implB : SB -> T where { mode M -> M; type B @M -> TB @M; }"
          , "doctrine_functor F(A : SA, B : SB) where {"
          , "  gen a : [A::M.A::A] -> [A::M.A::A] @A::M;"
          , "  gen b : [B::M.B::B] -> [B::M.B::B] @B::M;"
          , "}"
          , "doctrine R = apply F to T using { A = implA; B = implB; C = implA; };"
          ]
  errExtra <- expectElabFailure srcExtra
  assertBool "expected extra key C" ("extra: C" `T.isInfixOf` errExtra)

testApplyImplicitIdentityTypeMap :: Assertion
testApplyImplicitIdentityTypeMap = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  type X @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M;"
          , "  type X @M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
          , "}"
          , "doctrine_functor F(A : S) where {"
          , "  gen keep : [A::M.A::X] -> [A::M.A::X] @A::M;"
          , "}"
          , "doctrine App = apply F to T using { A = impl; };"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "App"
  let mode = ModeName "M"
  let ty = TCon (TypeRef mode (TypeName "X")) []
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected mode M generator table"
    Just table -> pure table
  keepGen <- case M.lookup (GenName "keep") gens of
    Nothing -> assertFailure "expected keep generator"
    Just g -> pure g
  gdPlainDom keepGen @?= [ty]
  gdCod keepGen @?= [ty]

testApplyGeneratorModeMapping :: Assertion
testApplyGeneratorModeMapping = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  type X @M;"
          , "  gen f : [M.X] -> [M.X] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M;"
          , "  type X @M;"
          , "  gen f : [M.X] -> [M.X] @M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
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
          , "  mode M;"
          , "  attrsort Str = string;"
          , "  type X @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
          , "}"
          , "doctrine_functor F(A : S) where {"
          , "}"
          , "doctrine App = apply F to T using { A = impl; };"
          ]
  err <- expectElabFailure src
  assertBool "expected param name in diagnostics" ("parameter A" `T.isInfixOf` err)
  assertBool "expected missing type in diagnostics" ("type=[M.X]" `T.isInfixOf` err)
  assertBool "expected missing attr sort in diagnostics" ("attr_sort=[Str]" `T.isInfixOf` err)
  assertBool "expected gen category in diagnostics" ("gen=(none)" `T.isInfixOf` err)

testApplyMissingGenMappingDiagnostics :: Assertion
testApplyMissingGenMappingDiagnostics = do
  let setupSrc =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  type X @M;"
          , "  gen f : [M.X] -> [M.X] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M;"
          , "  type X @M;"
          , "  gen f : [M.X] -> [M.X] @M;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> M;"
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
          , "  mode M;"
          , "  type X @M;"
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
          , "  mode M;"
          , "  modality mu : M -> M;"
          , "  type X @M;"
          , "}"
          , "doctrine T where {"
          , "  mode N;"
          , "  modality nu : N -> N;"
          , "  type Y @N;"
          , "}"
          , "morphism impl : S -> T where {"
          , "  mode M -> N;"
          , "  modality mu -> nu;"
          , "  type X @M -> Y @N;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  mode K;"
          , "  modality up : L::M -> K;"
          , "  type Z @K;"
          , "}"
          , "doctrine R = apply F to T using { L = impl; };"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "R"
  assertBool "expected pushed mode N" (M.member (ModeName "N") (dTypes doc))
  assertBool "expected new body mode K" (M.member (ModeName "K") (dTypes doc))


testModEqPreservation :: Assertion
testModEqPreservation = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  modality mu : M -> M;"
          , "  mod_eq mu . mu -> mu;"
          , "  type X @M;"
          , "  gen g : [M.X] -> [M.X] @M;"
          , "}"
          , "doctrine T where {"
          , "  mode M;"
          , "  modality a : M -> M;"
          , "  modality b : M -> M;"
          , "  type X @M;"
          , "  gen g : [M.X] -> [M.X] @M;"
          , "}"
          , "morphism bad : S -> T where {"
          , "  mode M -> M;"
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
          , "  mode M;"
          , "  type X @M;"
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
