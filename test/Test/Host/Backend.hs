{-# LANGUAGE OverloadedStrings #-}
module Test.Host.Backend
  ( tests
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Host.Backend
  ( BackendPlugin(..)
  , HostArtifact(..)
  , buildBackendRegistry
  , emitBundleViaBackendWithRegistry
  , emitViaBackendWithRegistry
  )
import Strat.Pipeline (BackendSpec(..))
import Strat.Poly.Doctrine (Doctrine)
import Strat.Poly.Syntax (Diagram)
import Strat.Poly.Graph (emptyDiagram)
import Strat.Poly.ModeTheory (ModeName(..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit


tests :: TestTree
tests =
  testGroup
    "Host.Backend"
    [ testCase "backend registry rejects duplicate aliases case-insensitively" testDuplicateAliasRejected
    , testCase "custom backend registry resolves aliases case-insensitively for diagram emission" testEmitViaInjectedRegistry
    , testCase "custom backend registry supports bundle emission" testEmitBundleViaInjectedRegistry
    ]


testDuplicateAliasRejected :: Assertion
testDuplicateAliasRejected =
  case buildBackendRegistry [customBackend "One" ["alias"], customBackend "Two" ["ALIAS"]] of
    Left err ->
      assertBool "expected duplicate alias rejection" ("duplicate alias alias" `T.isInfixOf` T.toLower err)
    Right _ ->
      assertFailure "expected duplicate alias rejection"


testEmitViaInjectedRegistry :: Assertion
testEmitViaInjectedRegistry = do
  registry <- require (buildBackendRegistry [customBackend "Trace" ["trace_alias"]])
  doc <- requireDocDoctrine
  let spec =
        BackendSpec
          { bsName = "TrAcE_AlIaS"
          , bsStdout = Just True
          , bsRoot = Nothing
          }
  art <- require (emitViaBackendWithRegistry registry spec doc dummyDiagram)
  haStdout art @?= "diagram:TrAcE_AlIaS"


testEmitBundleViaInjectedRegistry :: Assertion
testEmitBundleViaInjectedRegistry = do
  registry <- require (buildBackendRegistry [customBackend "Trace" ["trace_alias"]])
  doc <- requireDocDoctrine
  let spec =
        BackendSpec
          { bsName = "TRACE"
          , bsStdout = Just True
          , bsRoot = Nothing
          }
      entries =
        [ ("alpha", doc, dummyDiagram)
        , ("beta", doc, dummyDiagram)
        ]
  art <- require (emitBundleViaBackendWithRegistry registry spec entries)
  haStdout art @?= "bundle:alpha,beta"


customBackend :: T.Text -> [T.Text] -> BackendPlugin
customBackend name aliases =
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


requireDocDoctrine :: IO Doctrine
requireDocDoctrine =
  case M.lookup "Doc" preludeDoctrines of
    Nothing -> assertFailure "expected Doc doctrine in prelude" >> fail "unreachable"
    Just doc -> pure doc


dummyDiagram :: Diagram
dummyDiagram = emptyDiagram (ModeName "Doc") []


require :: Either T.Text a -> IO a
require res =
  case res of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right x -> pure x
