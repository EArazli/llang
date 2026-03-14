{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Builds
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab
  ( elabRawFileWithEnv
  )
import Strat.Frontend.Env (ModuleEnv, emptyEnv, meDoctrines, meModules)
import Strat.Frontend.Model
  ( mdProviders
  , mdExports
  , mdExportTypes
  , ModuleItemDef(..)
  , mpAdapters
  , mpDescriptor
  , mpInterface
  , prProvider
  , prValueName
  , mtdDoctrine
  , mddDoctrine
  , mddTypeDef
  , mddCtorDefs
  , mvdDoctrine
  , mvdDiagram
  )
import Strat.Poly.Doctrine (dName)
import Strat.Poly.Diagram (moduleValueRefsDiagram, providerRefsDiagram)
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Frontend.Build
  ( selectBuild
  , buildWithEnv
  , buildWithEnvAndBackendRegistry
  , BuildResult(..)
  , BuildProduct(..)
  , ModuleComponent(..)
  , ModuleArtifact(..)
  )
import Strat.Host.Backend (BackendPlugin(..), HostArtifact(..), buildBackendRegistry)
import Strat.Pipeline (BackendSpec(..))


tests :: TestTree
tests =
  testGroup
    "Frontend.Builds"
    [ testCase "module build emits exported doc directly via module emission" testModuleBuildDoc
    , testCase "module imports expose aliased interface-restricted values" testModuleImport
    , testCase "interface-exported type aliases flow through module imports" testInterfaceTypeImport
    , testCase "module imports can adapt exports across doctrines via morphisms" testModuleImportAdapter
    , testCase "foreign imports elaborate through typed provider descriptors" testForeignImport
    , testCase "foreign imports can adapt provider interfaces across doctrines via morphisms" testForeignImportAdapter
    , testCase "duplicate module_surface defaults and declaration uses are deduplicated" testDuplicateUsesDeduped
    , testCase "provider dependencies propagate onto compiled module values" testProviderDepsPropagate
    , testCase "renamed exports are visible to projection/builds" testExportRename
    , testCase "link and bundle compose module exports" testLinkAndBundle
    , testCase "module declarations only see earlier imports and aliases" testForwardImportRejected
    , testCase "module value signatures cannot use later type aliases" testForwardModuleTypeRejected
    , testCase "interface values cannot use later type aliases" testForwardInterfaceTypeRejected
    , testCase "export interface checking rejects mismatched values" testExportInterfaceMismatch
    , testCase "typed value declarations reject boundary mismatches" testTypedValueSignatureMismatch
    , testCase "module data packages elaborate to type and constructor bindings" testModuleDataPackage
    , testCase "module data exports import through opaque interfaces" testModuleDataImport
    , testCase "module data rejects missing doctrine constructors" testModuleDataMissingCtor
    , testCase "module data rejects constructor signature mismatches" testModuleDataSigMismatch
    , testCase "module data rejects unknown representations" testModuleDataUnknownRepr
    , testCase "module data syntax rejects unsupported parameters" testModuleDataParametricRejected
    , testCase "module data representations can be defined in source" testModuleDataSourceDefinedRepr
    , testCase "module surfaces can supply a default data representation" testModuleSurfaceDefaultDataRepr
    , testCase "module surfaces can reject unsupported declaration kinds" testModuleSurfaceRejectsForeignImport
    , testCase "module surfaces can expand custom declaration items through source-defined elaborators" testModuleSurfaceCustomDeclarations
    , testCase "opaque module data representations support abstract imports and exports" testOpaqueModuleDataPackage
    , testCase "module morphism application translates export types and data packages" testModuleApplyMorphTranslatesTypes
    , testCase "identity morphism application preserves valid export interfaces" testModuleApplyIdentityPreservesExportInterface
    , testCase "module morphism application preserves internal import edges without re-adapting them" testModuleApplyMorphPreservesInternalImports
    , testCase "quote on typed modules lowers to value-only module artifacts" testQuoteTypedModuleDropsTypeMetadata
    , testCase "quote on modules closes imports/providers and lowers abstract refs" testQuoteModuleClosesImportsAndProviders
    , testCase "quote on provider-backed exports reflects q_provider bindings" testQuoteProviderBackedModule
    , testCase "builds can emit through an injected backend registry" testBuildWithInjectedBackendRegistry
    , testCase "foreign imports can materialize opaque interface types" testForeignOpaqueTypeImport
    , testCase "link satisfies typed module imports and removes satisfied requirements" testLinkSatisfiesImports
    , testCase "link allows overlapping private local names across components" testLinkAllowsPrivateNameOverlap
    , testCase "link satisfies imports against previously linked components" testLinkSatisfiesTransitiveComponents
    ]


testModuleBuildDoc :: Assertion
testModuleBuildDoc = do
  env <- require (elabProgram moduleDocProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  brOutput result @?= "hello"


testModuleImport :: Assertion
testModuleImport = do
  env <- require (elabProgram moduleImportProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  brOutput result @?= "hello!"


testInterfaceTypeImport :: Assertion
testInterfaceTypeImport = do
  env <- require (elabProgram interfaceTypeImportProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  brOutput result @?= "hello"


testForeignImport :: Assertion
testForeignImport = do
  env <- require (elabProgram foreignImportProgram)
  let providers =
        case M.lookup "App" (meModules env) of
          Nothing -> []
          Just modDef -> mdProviders modDef
  length providers @?= 1
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  assertBool "expected projected provider-backed generator" ("ping" `T.isInfixOf` brOutput result)


testModuleImportAdapter :: Assertion
testModuleImportAdapter = do
  env <- require (elabProgram moduleImportAdapterProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  assertBool "expected adapted target generator" ("greet" `T.isInfixOf` brOutput result)


testForeignImportAdapter :: Assertion
testForeignImportAdapter = do
  env <- require (elabProgram foreignImportAdapterProgram)
  let adapterNames =
        case M.lookup "App" (meModules env) of
          Nothing -> []
          Just modDef -> map mpAdapters (mdProviders modDef)
  adapterNames @?= [["liftPing"]]
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  assertBool "expected provider payload in rendered output" ("provider(Remote::ping via provider:ping using liftPing)" `T.isInfixOf` brOutput result)


testDuplicateUsesDeduped :: Assertion
testDuplicateUsesDeduped = do
  src <- TIO.readFile "examples/run/surfaces/implements_uses.run.llang"
  let src' =
        T.replace
          "module_surface ImplementsUsesRunUnit where {\n  doctrine Target;\n}"
          "module_surface ImplementsUsesRunUnit where {\n  doctrine Target;\n  uses Iface;\n}"
          src
  env <- require (elabProgram src')
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  assertBool "expected deduplicated interface default morphism application" ("f [p0] -> [p1]" `T.isInfixOf` brOutput result)


testProviderDepsPropagate :: Assertion
testProviderDepsPropagate = do
  env <- require (elabProgram foreignImportAdapterProgram)
  modDef <-
    case M.lookup "App" (meModules env) of
      Nothing -> assertFailure "expected App module" >> fail "unreachable"
      Just md -> pure md
  mainValue <-
    case M.lookup "main" (mdExports modDef) of
      Nothing -> assertFailure "expected main export" >> fail "unreachable"
      Just mv -> pure mv
  let deps = S.toList (providerRefsDiagram (mvdDiagram mainValue))
  length deps @?= 1
  dep <-
    case deps of
      [one] -> pure one
      _ -> assertFailure "expected exactly one provider dependency" >> fail "unreachable"
  prValueName dep @?= "ping"
  mpDescriptor (prProvider dep) @?= "provider:ping"
  mpAdapters (prProvider dep) @?= ["liftPing"]


testExportRename :: Assertion
testExportRename = do
  env <- require (elabProgram exportRenameProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  brOutput result @?= "hello"


testLinkAndBundle :: Assertion
testLinkAndBundle = do
  env <- require (elabProgram linkAndBundleProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  let out = brOutput result
  assertBool "expected bundled alpha entry" ("alpha:\nhello" `T.isInfixOf` out)
  assertBool "expected bundled world entry" ("world:\nworld" `T.isInfixOf` out)


testForwardImportRejected :: Assertion
testForwardImportRejected = do
  err <- requireLeft (elabProgram forwardImportProgram)
  assertBool "expected forward import reference failure" ("Lib::hello" `T.isInfixOf` err)


testForwardModuleTypeRejected :: Assertion
testForwardModuleTypeRejected = do
  err <- requireLeft (elabProgram forwardModuleTypeProgram)
  assertBool "expected forward type reference failure" ("Greeting" `T.isInfixOf` err)


testForwardInterfaceTypeRejected :: Assertion
testForwardInterfaceTypeRejected = do
  err <- requireLeft (elabProgram forwardInterfaceTypeProgram)
  assertBool "expected forward interface type reference failure" ("Greeting" `T.isInfixOf` err)


testExportInterfaceMismatch :: Assertion
testExportInterfaceMismatch = do
  err <- requireLeft (elabProgram exportInterfaceMismatchProgram)
  assertBool "expected interface mismatch" ("domain mismatch" `T.isInfixOf` err)


testTypedValueSignatureMismatch :: Assertion
testTypedValueSignatureMismatch = do
  err <- requireLeft (elabProgram typedValueSignatureMismatchProgram)
  assertBool "expected declared-domain mismatch" ("declared domain" `T.isInfixOf` err)


testModuleDataPackage :: Assertion
testModuleDataPackage = do
  env <- require (elabProgram moduleDataProgram)
  buildDef <- require (selectBuild env (Just "pkg"))
  result <- require (buildWithEnv env buildDef)
  let out = brOutput result
  assertBool "expected Wrap constructor in projected diagram" ("Wrap" `T.isInfixOf` out)
  assertBool "expected Red constructor in projected diagram" ("Red" `T.isInfixOf` out)


testModuleDataImport :: Assertion
testModuleDataImport = do
  env <- require (elabProgram moduleDataProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  let out = brOutput result
  assertBool "expected imported Wrap constructor in projected diagram" ("Wrap" `T.isInfixOf` out)
  assertBool "expected imported Red constructor in projected diagram" ("Red" `T.isInfixOf` out)


testModuleDataMissingCtor :: Assertion
testModuleDataMissingCtor = do
  err <- requireLeft (elabProgram moduleDataMissingCtorProgram)
  assertBool "expected missing doctrine constructor failure" ("missing constructor Blue" `T.isInfixOf` err)


testModuleDataSigMismatch :: Assertion
testModuleDataSigMismatch = do
  err <- requireLeft (elabProgram moduleDataSigMismatchProgram)
  assertBool "expected constructor domain mismatch" ("constructor Wrap domain mismatch" `T.isInfixOf` err)


testModuleDataUnknownRepr :: Assertion
testModuleDataUnknownRepr = do
  err <- requireLeft (elabProgram moduleDataUnknownReprProgram)
  assertBool "expected unknown representation rejection" ("unknown representation not_a_repr" `T.isInfixOf` err)


testModuleDataParametricRejected :: Assertion
testModuleDataParametricRejected = do
  err <- requireLeft (elabProgram moduleDataParametricProgram)
  assertBool "expected module data syntax failure" (not (T.null err))


testModuleDataSourceDefinedRepr :: Assertion
testModuleDataSourceDefinedRepr = do
  env <-
    require
      ( elabProgram
          ( T.unlines
              [ "data_repr color_repr where {"
              , "  extends doctrine_data;"
              , "}"
              ]
              <> T.replace "using doctrine_data" "using color_repr" moduleDataProgram
          )
      )
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  let out = brOutput result
  assertBool "expected imported Wrap constructor with injected repr" ("Wrap" `T.isInfixOf` out)
  assertBool "expected imported Red constructor with injected repr" ("Red" `T.isInfixOf` out)


testModuleSurfaceDefaultDataRepr :: Assertion
testModuleSurfaceDefaultDataRepr = do
  env <- require (elabProgram (T.replace "using doctrine_data" "" moduleSurfaceDefaultDataReprProgram))
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  let out = brOutput result
  assertBool "expected default data repr to elaborate Wrap" ("Wrap" `T.isInfixOf` out)
  assertBool "expected default data repr to elaborate Red" ("Red" `T.isInfixOf` out)


testModuleSurfaceRejectsForeignImport :: Assertion
testModuleSurfaceRejectsForeignImport = do
  err <- requireLeft (elabProgram moduleSurfaceRejectsForeignImportProgram)
  assertBool "expected module surface rejection" ("does not allow foreign imports" `T.isInfixOf` err)


testModuleSurfaceCustomDeclarations :: Assertion
testModuleSurfaceCustomDeclarations = do
  env <- require (elabProgram moduleSurfaceCustomProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  brOutput result @?= "hello"


testOpaqueModuleDataPackage :: Assertion
testOpaqueModuleDataPackage = do
  env <- require (elabProgram opaqueModuleDataProgram)
  colors <-
    case M.lookup "Colors" (meModules env) of
      Nothing -> assertFailure "expected Colors module" >> fail "unreachable"
      Just modDef -> pure modDef
  redCtor <-
    case M.lookup "Red" (mdExports colors) of
      Nothing -> assertFailure "expected opaque Red export" >> fail "unreachable"
      Just mv -> pure mv
  providerRef <-
    case S.toList (providerRefsDiagram (mvdDiagram redCtor)) of
      [ref] -> pure ref
      _ -> assertFailure "expected one opaque provider ref" >> fail "unreachable"
  mpInterface (prProvider providerRef) @?= "ColorProviderSig"
  mpDescriptor (prProvider providerRef) @?= "remote-color:Color"
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  let out = brOutput result
  assertBool "expected opaque constructor provider payload" ("provider(Color::Red via remote-color:Color)" `T.isInfixOf` out)


testModuleApplyMorphTranslatesTypes :: Assertion
testModuleApplyMorphTranslatesTypes = do
  env <- require (elabProgram moduleApplyMorphProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  modArt <-
    case brArtifact result of
      BPModule art -> pure art
      _ -> assertFailure "expected module artifact after morphism application" >> fail "unreachable"
  dName (maDoctrine modArt) @?= "TgtDoc"
  maExportInterfaces modArt @?= []
  exportTy <-
    case M.lookup "Color" (maExportTypes modArt) of
      Nothing -> assertFailure "expected translated exported type" >> fail "unreachable"
      Just ty -> pure ty
  mtdDoctrine exportTy @?= "TgtDoc"
  pkg <-
    case M.lookup "Color" (maDataPackages modArt) of
      Nothing -> assertFailure "expected translated data package" >> fail "unreachable"
      Just dataPkg -> pure dataPkg
  mddDoctrine pkg @?= "TgtDoc"
  mtdDoctrine (mddTypeDef pkg) @?= "TgtDoc"
  ctorWrap <-
    case M.lookup "Wrap" (mddCtorDefs pkg) of
      Nothing -> assertFailure "expected translated constructor binding" >> fail "unreachable"
      Just mv -> pure mv
  mvdDoctrine ctorWrap @?= "TgtDoc"


testModuleApplyIdentityPreservesExportInterface :: Assertion
testModuleApplyIdentityPreservesExportInterface = do
  env <- require (elabProgram applyIdentityPreservesInterfaceProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  modArt <-
    case brArtifact result of
      BPModule art -> pure art
      _ -> assertFailure "expected module artifact after identity morphism application" >> fail "unreachable"
  maExportInterfaces modArt @?= ["Sig"]
  assertBool "expected export interface item to survive identity morphism" (MIDExportInterface "Sig" `elem` maItems modArt)


testModuleApplyMorphPreservesInternalImports :: Assertion
testModuleApplyMorphPreservesInternalImports = do
  env <- require (elabProgram applyMorphInternalImportProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  assertBool "expected translated target generator after morphing imported module graph" ("greet" `T.isInfixOf` brOutput result)


testQuoteTypedModuleDropsTypeMetadata :: Assertion
testQuoteTypedModuleDropsTypeMetadata = do
  env <- require (elabProgram quoteTypedModuleProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  modArt <-
    case brArtifact result of
      BPModule art -> pure art
      _ -> assertFailure "expected quoted module artifact" >> fail "unreachable"
  dName (maDoctrine modArt) @?= "D_Q"
  assertBool "expected quoted module values" (M.member "main" (maExports modArt))
  maTypes modArt @?= M.empty
  maExportTypes modArt @?= M.empty
  maDataPackages modArt @?= M.empty
  maImports modArt @?= []
  maProviders modArt @?= []
  maExportInterfaces modArt @?= []


testQuoteModuleClosesImportsAndProviders :: Assertion
testQuoteModuleClosesImportsAndProviders = do
  env <- require (elabProgram quoteModuleClosureProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  modArt <-
    case brArtifact result of
      BPModule art -> pure art
      _ -> assertFailure "expected quoted module artifact" >> fail "unreachable"
  maImports modArt @?= []
  maProviders modArt @?= []
  mainComp <-
    case filter (\comp -> mcName comp == "Main") (maComponents modArt) of
      [comp] -> pure comp
      _ -> assertFailure "expected Main component" >> fail "unreachable"
  mcImports mainComp @?= []
  mcProviders mainComp @?= []
  let quotedValues = M.elems (maExports modArt) <> M.elems (maValues modArt)
  assertBool
    "expected quoted module artifact to eliminate abstract module refs"
    (all (S.null . moduleValueRefsDiagram . mvdDiagram) quotedValues)
  assertBool
    "expected quoted module artifact to eliminate provider refs"
    (all (S.null . providerRefsDiagram . mvdDiagram) quotedValues)


testQuoteProviderBackedModule :: Assertion
testQuoteProviderBackedModule = do
  env <- require (elabProgram quoteProviderProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  assertBool "expected reflected provider binding" ("q_provider" `T.isInfixOf` brOutput result)
  assertBool "expected reflected provider descriptor" ("provider:ping" `T.isInfixOf` brOutput result)


testBuildWithInjectedBackendRegistry :: Assertion
testBuildWithInjectedBackendRegistry = do
  env <- require (elabProgram injectedBackendProgram)
  buildDef <- require (selectBuild env (Just "main"))
  registry <- require (buildBackendRegistry [traceBackend "Trace" ["trace_alias"]])
  result <- require (buildWithEnvAndBackendRegistry registry env buildDef)
  brOutput result @?= "diagram:TrAcE_AlIaS"


testForeignOpaqueTypeImport :: Assertion
testForeignOpaqueTypeImport = do
  env <- require (elabProgram foreignOpaqueTypeProgram)
  modDef <-
    case M.lookup "App" (meModules env) of
      Nothing -> assertFailure "expected App module" >> fail "unreachable"
      Just md -> pure md
  assertBool "expected exported opaque foreign type" (M.member "Token" (mdExportTypes modDef))


testLinkSatisfiesImports :: Assertion
testLinkSatisfiesImports = do
  env <- require (elabProgram linkSatisfiesImportsProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  modArt <-
    case brArtifact result of
      BPModule art -> pure art
      _ -> assertFailure "expected linked module artifact" >> fail "unreachable"
  length (maComponents modArt) @?= 2
  assertBool "expected linked module to preserve abstract import structure" (not (null (maImports modArt)))
  assertBool "expected linked module to retain import items until closure" (any isImportItem (maItems modArt))
  where
    isImportItem item =
      case item of
        MIDImport _ -> True
        _ -> False


testLinkAllowsPrivateNameOverlap :: Assertion
testLinkAllowsPrivateNameOverlap = do
  env <- require (elabProgram linkPrivateOverlapProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  modArt <-
    case brArtifact result of
      BPModule art -> pure art
      _ -> assertFailure "expected linked module artifact" >> fail "unreachable"
  assertBool "expected first export to survive private overlap" (M.member "a" (maExports modArt))
  assertBool "expected second export to survive private overlap" (M.member "b" (maExports modArt))
  assertBool "expected component-scoped local map entries after link" (M.member "A::helper" (maValues modArt))
  assertBool "expected component-scoped local map entries after link" (M.member "B::helper" (maValues modArt))


testLinkSatisfiesTransitiveComponents :: Assertion
testLinkSatisfiesTransitiveComponents = do
  env <- require (elabProgram linkTransitiveSatisfactionProgram)
  buildDef <- require (selectBuild env (Just "main"))
  result <- require (buildWithEnv env buildDef)
  modArt <-
    case brArtifact result of
      BPModule art -> pure art
      _ -> assertFailure "expected linked module artifact" >> fail "unreachable"
  assertBool "expected linked artifact to preserve transitive import edges" (not (null (maImports modArt)))
  assertBool "expected linked artifact to contain all three components" (length (maComponents modArt) == 3)
  assertBool "expected transitive component order to place A before D" (map mcName (maComponents modArt) == ["C", "A", "D"] || map mcName (maComponents modArt) == ["A", "C", "D"])


moduleDocProgram :: Text
moduleDocProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello };"
    , "}"
    , "pipeline p where {"
    , "  emit via Doc { stdout = true; };"
    , "}"
    , "build main from Greeting using p;"
    ]


moduleImportProgram :: Text
moduleImportProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "interface GreetingSig in DocLang where {"
    , "  val hello : [] -> [Doc] @Doc;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  let secret"
    , "  ---"
    , "  text(\"secret\")"
    , "  ---"
    , "  export { hello, secret };"
    , "  export interface GreetingSig;"
    , "}"
    , "module App in DocLang where {"
    , "  import Greeting as Lib : GreetingSig;"
    , "  let main"
    , "  ---"
    , "  (Lib::hello * text(\"!\")); cat"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  emit via Doc { stdout = true; };"
    , "}"
    , "build main from App using p;"
    ]


interfaceTypeImportProgram :: Text
interfaceTypeImportProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "interface GreetingSig in DocLang where {"
    , "  opaque type Greeting @Doc;"
    , "  val hello : [] -> [Greeting] @Doc;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  type Greeting @Doc = Doc;"
    , "  let hello : [] -> [Greeting] @Doc"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export type { Greeting };"
    , "  export { hello };"
    , "  export interface GreetingSig;"
    , "}"
    , "module App in DocLang where {"
    , "  import Greeting as Lib : GreetingSig;"
    , "  let main : [] -> [Lib::Greeting] @Doc"
    , "  ---"
    , "  Lib::hello"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  emit via Doc { stdout = true; };"
    , "}"
    , "build main from App using p;"
    ]


moduleImportAdapterProgram :: Text
moduleImportAdapterProgram =
  T.unlines
    [ "doctrine SrcDoc where {"
    , "  mode S classifiedBy S via S.U_S;"
    , "  gen comp_ctx_ext(a@S) : [a] -> [a] @S;"
    , "  gen comp_var(a@S) : [a] -> [a] @S;"
    , "  gen comp_reindex(a@S) : [a] -> [a] @S;"
    , "  comprehension S where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_S : [] -> [S.U_S] @S;"
    , "  gen Token : [] -> [U_S] @S;"
    , "  gen hello : [] -> [Token] @S;"
    , "}"
    , "doctrine TgtDoc where {"
    , "  mode T classifiedBy T via T.U_T;"
    , "  gen comp_ctx_ext(a@T) : [a] -> [a] @T;"
    , "  gen comp_var(a@T) : [a] -> [a] @T;"
    , "  gen comp_reindex(a@T) : [a] -> [a] @T;"
    , "  comprehension T where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_T : [] -> [T.U_T] @T;"
    , "  gen Token : [] -> [U_T] @T;"
    , "  gen greet : [] -> [Token] @T;"
    , "}"
    , "morphism liftGreeting : SrcDoc -> TgtDoc where {"
    , "  mode S -> T;"
    , "  gen comp_ctx_ext @S -> comp_ctx_ext(a)"
    , "  gen comp_var @S -> comp_var(a)"
    , "  gen comp_reindex @S -> comp_reindex(a)"
    , "  type Token @S -> Token @T;"
    , "  gen hello @S -> greet"
    , "}"
    , "module_surface SrcUnit where {"
    , "  doctrine SrcDoc;"
    , "  mode S;"
    , "}"
    , "language SrcLang where {"
    , "  doctrine SrcDoc;"
    , "  module_surface SrcUnit;"
    , "}"
    , "module_surface TgtUnit where {"
    , "  doctrine TgtDoc;"
    , "  mode T;"
    , "}"
    , "language TgtLang where {"
    , "  doctrine TgtDoc;"
    , "  module_surface TgtUnit;"
    , "}"
    , "interface GreetingSig in SrcLang where {"
    , "  val hello : [] -> [Token] @S;"
    , "}"
    , "module Greeting in SrcLang where {"
    , "  let hello : [] -> [Token] @S"
    , "  ---"
    , "  hello"
    , "  ---"
    , "  export { hello };"
    , "  export interface GreetingSig;"
    , "}"
    , "module App in TgtLang where {"
    , "  import Greeting as Lib : GreetingSig using liftGreeting;"
    , "  let main : [] -> [Token] @T"
    , "  ---"
    , "  Lib::hello"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "}"
    , "build main from App using p;"
    ]


foreignImportProgram :: Text
foreignImportProgram =
  T.unlines
    [ "doctrine PingDoc where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [U_M] @M;"
    , "  gen Doc : [] -> [U_M] @M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  gen ping : [] -> [Doc] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    , "module_surface PingUnit where {"
    , "  doctrine PingDoc;"
    , "  mode M;"
    , "}"
    , "language PingLang where {"
    , "  doctrine PingDoc;"
    , "  module_surface PingUnit;"
    , "}"
    , "interface PingSig in PingLang where {"
    , "  val ping : [] -> [Doc] @M;"
    , "}"
    , "module App in PingLang where {"
    , "  import foreign Remote : PingSig via \"provider:ping\";"
    , "  let main : [] -> [Doc] @M"
    , "  ---"
    , "  Remote::ping"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "}"
    , "build main from App using p;"
    ]


foreignImportAdapterProgram :: Text
foreignImportAdapterProgram =
  T.unlines
    [ "doctrine PingSrc where {"
    , "  mode S classifiedBy S via S.U_S;"
    , "  gen comp_ctx_ext(a@S) : [a] -> [a] @S;"
    , "  gen comp_var(a@S) : [a] -> [a] @S;"
    , "  gen comp_reindex(a@S) : [a] -> [a] @S;"
    , "  comprehension S where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_S : [] -> [S.U_S] @S;"
    , "  gen Token : [] -> [U_S] @S;"
    , "  gen ping : [] -> [Token] @S;"
    , "}"
    , "doctrine PingTgt where {"
    , "  mode T classifiedBy T via T.U_T;"
    , "  gen comp_ctx_ext(a@T) : [a] -> [a] @T;"
    , "  gen comp_var(a@T) : [a] -> [a] @T;"
    , "  gen comp_reindex(a@T) : [a] -> [a] @T;"
    , "  comprehension T where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_T : [] -> [T.U_T] @T;"
    , "  gen Token : [] -> [U_T] @T;"
    , "  gen greet : [] -> [Token] @T;"
    , "}"
    , "morphism liftPing : PingSrc -> PingTgt where {"
    , "  mode S -> T;"
    , "  gen comp_ctx_ext @S -> comp_ctx_ext(a)"
    , "  gen comp_var @S -> comp_var(a)"
    , "  gen comp_reindex @S -> comp_reindex(a)"
    , "  type Token @S -> Token @T;"
    , "  gen ping @S -> greet"
    , "}"
    , "module_surface SrcUnit where {"
    , "  doctrine PingSrc;"
    , "  mode S;"
    , "}"
    , "language SrcLang where {"
    , "  doctrine PingSrc;"
    , "  module_surface SrcUnit;"
    , "}"
    , "module_surface TgtUnit where {"
    , "  doctrine PingTgt;"
    , "  mode T;"
    , "}"
    , "language TgtLang where {"
    , "  doctrine PingTgt;"
    , "  module_surface TgtUnit;"
    , "}"
    , "interface PingSig in SrcLang where {"
    , "  val ping : [] -> [Token] @S;"
    , "}"
    , "module App in TgtLang where {"
    , "  import foreign Remote : PingSig via \"provider:ping\" using liftPing;"
    , "  let main : [] -> [Token] @T"
    , "  ---"
    , "  Remote::ping"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "}"
    , "build main from App using p;"
    ]


exportRenameProgram :: Text
exportRenameProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello as main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "  emit via Doc { stdout = true; };"
    , "}"
    , "build main from Greeting using p;"
    ]


linkAndBundleProgram :: Text
linkAndBundleProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "module A in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello };"
    , "}"
    , "module B in DocLang where {"
    , "  let world"
    , "  ---"
    , "  text(\"world\")"
    , "  ---"
    , "  export { world };"
    , "}"
    , "pipeline p where {"
    , "  link B;"
    , "  bundle { hello as alpha, world };"
    , "  emit via Doc { stdout = true; };"
    , "}"
    , "build main from A using p;"
    ]


forwardImportProgram :: Text
forwardImportProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "interface GreetingSig in DocLang where {"
    , "  val hello : [] -> [Doc] @Doc;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello };"
    , "  export interface GreetingSig;"
    , "}"
    , "module App in DocLang where {"
    , "  let main"
    , "  ---"
    , "  Lib::hello"
    , "  ---"
    , "  import Greeting as Lib : GreetingSig;"
    , "  export { main };"
    , "}"
    ]


forwardModuleTypeProgram :: Text
forwardModuleTypeProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello : [] -> [Greeting] @Doc"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  type Greeting @Doc = Doc;"
    , "  export { hello };"
    , "}"
    ]


forwardInterfaceTypeProgram :: Text
forwardInterfaceTypeProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "interface GreetingSig in DocLang where {"
    , "  val hello : [] -> [Greeting] @Doc;"
    , "  type Greeting @Doc = Doc;"
    , "}"
    ]


exportInterfaceMismatchProgram :: Text
exportInterfaceMismatchProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "interface BadSig in DocLang where {"
    , "  val hello : [Doc] -> [Doc] @Doc;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello };"
    , "  export interface BadSig;"
    , "}"
    ]


typedValueSignatureMismatchProgram :: Text
typedValueSignatureMismatchProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello : [Doc] -> [Doc] @Doc"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello };"
    , "}"
    ]


moduleDataProgram :: Text
moduleDataProgram =
  T.unlines
    [ "doctrine ColorDoc where {"
    , "  mode C classifiedBy C via C.U_C;"
    , "  gen comp_ctx_ext(a@C) : [a] -> [a] @C;"
    , "  gen comp_var(a@C) : [a] -> [a] @C;"
    , "  gen comp_reindex(a@C) : [a] -> [a] @C;"
    , "  comprehension C where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_C : [] -> [U_C] @C;"
    , "  data Color @C where {"
    , "    Red : [];"
    , "    Blue : [];"
    , "    Wrap : [Color];"
    , "  }"
    , "}"
    , "module_surface ColorUnit where {"
    , "  doctrine ColorDoc;"
    , "  mode C;"
    , "}"
    , "language ColorLang where {"
    , "  doctrine ColorDoc;"
    , "  module_surface ColorUnit;"
    , "}"
    , "interface ColorSig in ColorLang where {"
    , "  opaque type Color @C;"
    , "  val Red : [] -> [Color] @C;"
    , "  val Wrap : [Color] -> [Color] @C;"
    , "}"
    , "module Palette in ColorLang where {"
    , "  data Color @C using doctrine_data where {"
    , "    ctor Red : [] -> [Color] @C;"
    , "    ctor Blue : [] -> [Color] @C;"
    , "    ctor Wrap : [Color] -> [Color] @C;"
    , "  }"
    , "  let main : [] -> [Color] @C"
    , "  ---"
    , "  Red ; Wrap"
    , "  ---"
    , "  export type { Color };"
    , "  export { Red, Wrap, main };"
    , "  export interface ColorSig;"
    , "}"
    , "module App in ColorLang where {"
    , "  import Palette as P : ColorSig;"
    , "  let main : [] -> [P::Color] @C"
    , "  ---"
    , "  P::Red ; P::Wrap"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "}"
    , "build pkg from Palette using p;"
    , "build main from App using p;"
    ]


moduleSurfaceDefaultDataReprProgram :: Text
moduleSurfaceDefaultDataReprProgram =
  T.unlines
    [ "doctrine ColorDoc where {"
    , "  mode C classifiedBy C via C.U_C;"
    , "  gen comp_ctx_ext(a@C) : [a] -> [a] @C;"
    , "  gen comp_var(a@C) : [a] -> [a] @C;"
    , "  gen comp_reindex(a@C) : [a] -> [a] @C;"
    , "  comprehension C where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_C : [] -> [U_C] @C;"
    , "  data Color @C where {"
    , "    Red : [];"
    , "    Blue : [];"
    , "    Wrap : [Color];"
    , "  }"
    , "}"
    , "data_repr color_repr where {"
    , "  extends doctrine_data;"
    , "}"
    , "module_surface ColorUnit where {"
    , "  doctrine ColorDoc;"
    , "  mode C;"
    , "  allow data;"
    , "  allow value;"
    , "  allow export_type;"
    , "  allow export;"
    , "  data_repr color_repr;"
    , "}"
    , "language ColorLang where {"
    , "  doctrine ColorDoc;"
    , "  module_surface ColorUnit;"
    , "}"
    , "module Palette in ColorLang where {"
    , "  data Color @C where {"
    , "    ctor Red : [] -> [Color] @C;"
    , "    ctor Blue : [] -> [Color] @C;"
    , "    ctor Wrap : [Color] -> [Color] @C;"
    , "  }"
    , "  let main : [] -> [Color] @C"
    , "  ---"
    , "  Red ; Wrap"
    , "  ---"
    , "  export type { Color };"
    , "  export { Red, Wrap, main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "}"
    , "build main from Palette using p;"
    ]


moduleSurfaceRejectsForeignImportProgram :: Text
moduleSurfaceRejectsForeignImportProgram =
  T.unlines
    [ "doctrine TokenDoc where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [U_M] @M;"
    , "}"
    , "module_surface TokenUnit where {"
    , "  doctrine TokenDoc;"
    , "  mode M;"
    , "  allow export_type;"
    , "}"
    , "language TokenLang where {"
    , "  doctrine TokenDoc;"
    , "  module_surface TokenUnit;"
    , "}"
    , "interface TokenSig in TokenLang where {"
    , "  opaque type Token @M;"
    , "}"
    , "module App in TokenLang where {"
    , "  import foreign Remote : TokenSig via \"provider:token\";"
    , "  export type { Remote::Token as Token };"
    , "}"
    ]


moduleSurfaceCustomProgram :: Text
moduleSurfaceCustomProgram =
  T.unlines
    [ "module_elaborator macro where {"
    , "  extends standard;"
    , "  interface custom doc_sig as items;"
    , "  module custom doc_export as items;"
    , "}"
    , "module_surface CustomUnit where {"
    , "  doctrine Doc;"
    , "  elaborator macro;"
    , "  allow value;"
    , "  allow export;"
    , "  allow export_interface;"
    , "  allow custom;"
    , "}"
    , "language CustomLang where {"
    , "  doctrine Doc;"
    , "  module_surface CustomUnit;"
    , "}"
    , "interface GreetingSig in CustomLang where {"
    , "  custom doc_sig"
    , "  ---"
    , "  val hello : [] -> [Doc] @Doc;"
    , "  ---"
    , "}"
    , "module Greeting in CustomLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  custom doc_export"
    , "  ---"
    , "  export { hello };"
    , "  ---"
    , "  export interface GreetingSig;"
    , "}"
    , "pipeline p where {"
    , "  project export hello;"
    , "  emit via Doc { stdout = true; };"
    , "}"
    , "build main from Greeting using p;"
    ]


opaqueModuleDataProgram :: Text
opaqueModuleDataProgram =
  T.unlines
    [ "doctrine D where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen Doc : [] -> [M.U_M] @M;"
    , "}"
    , "module_surface Unit where {"
    , "  doctrine D;"
    , "  mode M;"
    , "}"
    , "language Lang where {"
    , "  doctrine D;"
    , "  module_surface Unit;"
    , "}"
    , "interface ColorProviderSig in Lang where {"
    , "  opaque type Color @M;"
    , "  val Red : [] -> [Color] @M;"
    , "}"
    , "data_repr remote_color where {"
    , "  extends opaque_data;"
    , "  provider_interface ColorProviderSig;"
    , "  descriptor_prefix \"remote-color\";"
    , "}"
    , "module Colors in Lang where {"
    , "  data Color @M using remote_color where {"
    , "    ctor Red : [] -> [Color] @M;"
    , "  }"
    , "  export type { Color };"
    , "  export { Red };"
    , "  export interface ColorProviderSig;"
    , "}"
    , "module App in Lang where {"
    , "  import Colors as C : ColorProviderSig;"
    , "  let main : [] -> [C::Color] @M"
    , "  ---"
    , "  C::Red"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "}"
    , "build main from App using p;"
    ]


moduleDataMissingCtorProgram :: Text
moduleDataMissingCtorProgram =
  T.unlines
    [ "doctrine ColorDoc where {"
    , "  mode C classifiedBy C via C.U_C;"
    , "  gen comp_ctx_ext(a@C) : [a] -> [a] @C;"
    , "  gen comp_var(a@C) : [a] -> [a] @C;"
    , "  gen comp_reindex(a@C) : [a] -> [a] @C;"
    , "  comprehension C where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_C : [] -> [U_C] @C;"
    , "  data Color @C where {"
    , "    Red : [];"
    , "  }"
    , "}"
    , "module_surface ColorUnit where {"
    , "  doctrine ColorDoc;"
    , "  mode C;"
    , "}"
    , "language ColorLang where {"
    , "  doctrine ColorDoc;"
    , "  module_surface ColorUnit;"
    , "}"
    , "module Palette in ColorLang where {"
    , "  data Color @C where {"
    , "    ctor Red : [] -> [Color] @C;"
    , "    ctor Blue : [] -> [Color] @C;"
    , "  }"
    , "  export type { Color };"
    , "}"
    ]


moduleDataSigMismatchProgram :: Text
moduleDataSigMismatchProgram =
  T.unlines
    [ "doctrine ColorDoc where {"
    , "  mode C classifiedBy C via C.U_C;"
    , "  gen comp_ctx_ext(a@C) : [a] -> [a] @C;"
    , "  gen comp_var(a@C) : [a] -> [a] @C;"
    , "  gen comp_reindex(a@C) : [a] -> [a] @C;"
    , "  comprehension C where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_C : [] -> [U_C] @C;"
    , "  data Color @C where {"
    , "    Red : [];"
    , "    Wrap : [Color];"
    , "  }"
    , "}"
    , "module_surface ColorUnit where {"
    , "  doctrine ColorDoc;"
    , "  mode C;"
    , "}"
    , "language ColorLang where {"
    , "  doctrine ColorDoc;"
    , "  module_surface ColorUnit;"
    , "}"
    , "module Palette in ColorLang where {"
    , "  data Color @C where {"
    , "    ctor Red : [] -> [Color] @C;"
    , "    ctor Wrap : [] -> [Color] @C;"
    , "  }"
    , "  export type { Color };"
    , "}"
    ]


moduleDataParametricProgram :: Text
moduleDataParametricProgram =
  T.unlines
    [ "doctrine OptionDoc where {"
    , "  mode C classifiedBy C via C.U_C;"
    , "  gen comp_ctx_ext(a@C) : [a] -> [a] @C;"
    , "  gen comp_var(a@C) : [a] -> [a] @C;"
    , "  gen comp_reindex(a@C) : [a] -> [a] @C;"
    , "  comprehension C where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_C : [] -> [U_C] @C;"
    , "  data Option(a@C) @C where {"
    , "    None : [];"
    , "    Some : [a];"
    , "  }"
    , "}"
    , "module_surface OptionUnit where {"
    , "  doctrine OptionDoc;"
    , "  mode C;"
    , "}"
    , "language OptionLang where {"
    , "  doctrine OptionDoc;"
    , "  module_surface OptionUnit;"
    , "}"
    , "module Opt in OptionLang where {"
    , "  data Option(a@C) @C where {"
    , "    ctor None : [] -> [Option(a)] @C;"
    , "    ctor Some : [a] -> [Option(a)] @C;"
    , "  }"
    , "  export type { Option };"
    , "}"
    ]


moduleDataUnknownReprProgram :: Text
moduleDataUnknownReprProgram =
  T.unlines
    [ "doctrine ColorDoc where {"
    , "  mode C classifiedBy C via C.U_C;"
    , "  gen comp_ctx_ext(a@C) : [a] -> [a] @C;"
    , "  gen comp_var(a@C) : [a] -> [a] @C;"
    , "  gen comp_reindex(a@C) : [a] -> [a] @C;"
    , "  comprehension C where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_C : [] -> [U_C] @C;"
    , "  data Color @C where {"
    , "    Red : [];"
    , "  }"
    , "}"
    , "module_surface ColorUnit where {"
    , "  doctrine ColorDoc;"
    , "  mode C;"
    , "}"
    , "language ColorLang where {"
    , "  doctrine ColorDoc;"
    , "  module_surface ColorUnit;"
    , "}"
    , "module Palette in ColorLang where {"
    , "  data Color @C using not_a_repr where {"
    , "    ctor Red : [] -> [Color] @C;"
    , "  }"
    , "  export type { Color };"
    , "}"
    ]


moduleApplyMorphProgram :: Text
moduleApplyMorphProgram =
  T.unlines
    [ "doctrine SrcDoc where {"
    , "  mode S classifiedBy S via S.U_S;"
    , "  gen comp_ctx_ext(a@S) : [a] -> [a] @S;"
    , "  gen comp_var(a@S) : [a] -> [a] @S;"
    , "  gen comp_reindex(a@S) : [a] -> [a] @S;"
    , "  comprehension S where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_S : [] -> [U_S] @S;"
    , "  data Color @S where {"
    , "    Red : [];"
    , "    Wrap : [Color];"
    , "  }"
    , "}"
    , "doctrine TgtDoc where {"
    , "  mode T classifiedBy T via T.U_T;"
    , "  gen comp_ctx_ext(a@T) : [a] -> [a] @T;"
    , "  gen comp_var(a@T) : [a] -> [a] @T;"
    , "  gen comp_reindex(a@T) : [a] -> [a] @T;"
    , "  comprehension T where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_T : [] -> [U_T] @T;"
    , "  data Color @T where {"
    , "    Red : [];"
    , "    Wrap : [Color];"
    , "  }"
    , "}"
    , "morphism liftColor : SrcDoc -> TgtDoc where {"
    , "  check none;"
    , "  mode S -> T;"
    , "  gen comp_ctx_ext @S -> comp_ctx_ext(a)"
    , "  gen comp_var @S -> comp_var(a)"
    , "  gen comp_reindex @S -> comp_reindex(a)"
    , "  type Color @S -> Color @T;"
    , "  gen fold_Color @S -> fold_Color(r_Color)[?b0, ?b1]"
    , "  gen Red @S -> Red"
    , "  gen Wrap @S -> Wrap"
    , "}"
    , "module_surface SrcUnit where {"
    , "  doctrine SrcDoc;"
    , "  mode S;"
    , "}"
    , "language SrcLang where {"
    , "  doctrine SrcDoc;"
    , "  module_surface SrcUnit;"
    , "}"
    , "module Palette in SrcLang where {"
    , "  data Color @S using doctrine_data where {"
    , "    ctor Red : [] -> [Color] @S;"
    , "    ctor Wrap : [Color] -> [Color] @S;"
    , "  }"
    , "  let main : [] -> [Color] @S"
    , "  ---"
    , "  Red ; Wrap"
    , "  ---"
    , "  export type { Color };"
    , "  export { Red, Wrap, main };"
    , "}"
    , "pipeline p where {"
    , "  apply liftColor;"
    , "}"
    , "build main from Palette using p;"
    ]


applyIdentityPreservesInterfaceProgram :: Text
applyIdentityPreservesInterfaceProgram =
  T.unlines
    [ "doctrine D where {"
    , "  mode M;"
    , "  gen a : [] -> [] @M;"
    , "}"
    , "morphism idD : D -> D where {"
    , "  check none;"
    , "  gen a @M -> a"
    , "}"
    , "module_surface Unit where {"
    , "  doctrine D;"
    , "  mode M;"
    , "}"
    , "language Lang where {"
    , "  doctrine D;"
    , "  module_surface Unit;"
    , "}"
    , "interface Sig in Lang where {"
    , "  val main : [] -> [] @M;"
    , "}"
    , "module Main in Lang where {"
    , "  let main : [] -> [] @M"
    , "  ---"
    , "  a"
    , "  ---"
    , "  export { main };"
    , "  export interface Sig;"
    , "}"
    , "pipeline p where {"
    , "  apply idD;"
    , "}"
    , "build main from Main using p;"
    ]


applyMorphInternalImportProgram :: Text
applyMorphInternalImportProgram =
  T.replace
    "pipeline p where {\n  project export main;\n}"
    "pipeline p where {\n  apply liftGreeting;\n  project export main;\n}"
    ( T.replace
        "  import Greeting as Lib : GreetingSig using liftGreeting;\n  let main : [] -> [Token] @T"
        "  import Greeting as Lib : GreetingSig;\n  let main : [] -> [Token] @S"
        (T.replace "module App in TgtLang where {" "module App in SrcLang where {" moduleImportAdapterProgram)
    )


quoteTypedModuleProgram :: Text
quoteTypedModuleProgram =
  T.unlines
    [ "doctrine D where {"
    , "  mode M acyclic classifiedBy M via U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [U_M] @M;"
    , "  gen T : [] -> [U_M] @M;"
    , "  gen a : [] -> [T] @M;"
    , "}"
    , "module_surface Unit where {"
    , "  doctrine D;"
    , "  mode M;"
    , "}"
    , "language Lang where {"
    , "  doctrine D;"
    , "  module_surface Unit;"
    , "}"
    , "fragment Share in D mode M where {"
    , "  include gen a;"
    , "}"
    , "derived doctrine D_Q = reflect quotation of D mode M;"
    , "module Main in Lang where {"
    , "  type Alias @M = T;"
    , "  let main : [] -> [Alias] @M"
    , "  ---"
    , "  a"
    , "  ---"
    , "  export type { Alias };"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  quote using Share into D_Q;"
    , "}"
    , "build main from Main using p;"
    ]


quoteProviderProgram :: Text
quoteProviderProgram =
  T.unlines
    [ "doctrine D where {"
    , "  mode M acyclic classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen Str : [] -> [M.U_M] @M;"
    , "  literal Str @M = string;"
    , "  gen Doc : [] -> [M.U_M] @M;"
    , "  gen ping : [] -> [Doc] @M;"
    , "}"
    , "module_surface Unit where {"
    , "  doctrine D;"
    , "  mode M;"
    , "}"
    , "language Lang where {"
    , "  doctrine D;"
    , "  module_surface Unit;"
    , "}"
    , "interface PingSig in Lang where {"
    , "  val ping : [] -> [Doc] @M;"
    , "}"
    , "fragment Share in D mode M where {"
    , "}"
    , "derived doctrine D_Q = reflect quotation of D mode M;"
    , "module Main in Lang where {"
    , "  import foreign Remote : PingSig via \"provider:ping\";"
    , "  let main : [] -> [Doc] @M"
    , "  ---"
    , "  Remote::ping"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "  quote using Share into D_Q;"
    , "}"
    , "build main from Main using p;"
    ]


quoteModuleClosureProgram :: Text
quoteModuleClosureProgram =
  T.unlines
    [ "doctrine D where {"
    , "  mode M acyclic classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen Str : [] -> [M.U_M] @M;"
    , "  literal Str @M = string;"
    , "  gen Doc : [] -> [M.U_M] @M;"
    , "  gen ping : [] -> [Doc] @M;"
    , "  gen helper : [] -> [Doc] @M;"
    , "}"
    , "module_surface Unit where {"
    , "  doctrine D;"
    , "  mode M;"
    , "}"
    , "language Lang where {"
    , "  doctrine D;"
    , "  module_surface Unit;"
    , "}"
    , "interface PingSig in Lang where {"
    , "  val ping : [] -> [Doc] @M;"
    , "}"
    , "module Lib in Lang where {"
    , "  let helper : [] -> [Doc] @M"
    , "  ---"
    , "  helper"
    , "  ---"
    , "  export { helper };"
    , "}"
    , "fragment Share in D mode M where {"
    , "}"
    , "derived doctrine D_Q = reflect quotation of D mode M;"
    , "module Main in Lang where {"
    , "  import Lib as Lib;"
    , "  import foreign Remote : PingSig via \"provider:ping\";"
    , "  let fromLib : [] -> [Doc] @M"
    , "  ---"
    , "  Lib::helper"
    , "  ---"
    , "  let main : [] -> [Doc] @M"
    , "  ---"
    , "  Remote::ping"
    , "  ---"
    , "  export { fromLib, main };"
    , "}"
    , "pipeline p where {"
    , "  quote using Share into D_Q;"
    , "}"
    , "build main from Main using p;"
    ]


injectedBackendProgram :: Text
injectedBackendProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let main"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "  emit via TrAcE_AlIaS { stdout = true; };"
    , "}"
    , "build main from Greeting using p;"
    ]


foreignOpaqueTypeProgram :: Text
foreignOpaqueTypeProgram =
  T.unlines
    [ "doctrine TokenDoc where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [U_M] @M;"
    , "}"
    , "module_surface TokenUnit where {"
    , "  doctrine TokenDoc;"
    , "  mode M;"
    , "}"
    , "language TokenLang where {"
    , "  doctrine TokenDoc;"
    , "  module_surface TokenUnit;"
    , "}"
    , "interface TokenSig in TokenLang where {"
    , "  opaque type Token @M;"
    , "}"
    , "module App in TokenLang where {"
    , "  import foreign Remote : TokenSig via \"provider:token\";"
    , "  export type { Remote::Token as Token };"
    , "}"
    ]


linkSatisfiesImportsProgram :: Text
linkSatisfiesImportsProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "interface GreetingSig in DocLang where {"
    , "  val hello : [] -> [Doc] @Doc;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello };"
    , "  export interface GreetingSig;"
    , "}"
    , "module App in DocLang where {"
    , "  import Greeting as Lib : GreetingSig;"
    , "  let main"
    , "  ---"
    , "  Lib::hello"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  link Greeting;"
    , "}"
    , "build main from App using p;"
    ]


linkPrivateOverlapProgram :: Text
linkPrivateOverlapProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "module A in DocLang where {"
    , "  let helper"
    , "  ---"
    , "  text(\"a\")"
    , "  ---"
    , "  export { helper as a };"
    , "}"
    , "module B in DocLang where {"
    , "  let helper"
    , "  ---"
    , "  text(\"b\")"
    , "  ---"
    , "  export { helper as b };"
    , "}"
    , "pipeline p where {"
    , "  link B;"
    , "}"
    , "build main from A using p;"
    ]


linkTransitiveSatisfactionProgram :: Text
linkTransitiveSatisfactionProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "interface GreetingSig in DocLang where {"
    , "  val hello : [] -> [Doc] @Doc;"
    , "}"
    , "module A in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello };"
    , "  export interface GreetingSig;"
    , "}"
    , "module C in DocLang where {"
    , "  let c"
    , "  ---"
    , "  text(\"c\")"
    , "  ---"
    , "  export { c };"
    , "}"
    , "module D in DocLang where {"
    , "  import A as A : GreetingSig;"
    , "  let main"
    , "  ---"
    , "  A::hello"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  link A;"
    , "  link D;"
    , "}"
    , "build main from C using p;"
    ]


elabProgram :: Text -> Either Text ModuleEnv
elabProgram src = do
  raw <- parseRawFile src
  elabRawFileWithEnv env0 raw
  where
    env0 = emptyEnv { meDoctrines = preludeDoctrines }


require :: Either Text a -> IO a
require res =
  case res of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right x -> pure x


requireLeft :: Either Text a -> IO Text
requireLeft res =
  case res of
    Left err -> pure err
    Right _ -> assertFailure "expected failure" >> fail "unreachable"


traceBackend :: T.Text -> [T.Text] -> BackendPlugin
traceBackend name aliases =
  BackendPlugin
    { bpName = name
    , bpAliases = aliases
    , bpEmitDiagram = \spec _doc _diag ->
        Right HostArtifact { haStdout = "diagram:" <> bsName spec, haFiles = M.empty }
    , bpEmitBundle = \_spec entries ->
        Right
          HostArtifact
            { haStdout = "bundle:" <> T.intercalate "," (map (\(entryName, _, _) -> entryName) entries)
            , haFiles = M.empty
            }
    }
