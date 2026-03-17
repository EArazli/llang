{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.CanonicalCoverage
  ( tests
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Strat.Frontend.Build (buildWithEnv, selectBuild)
import Strat.Frontend.Env (ModuleEnv, meDoctrines)
import Strat.Frontend.Loader (loadModule)
import System.Directory (doesFileExist)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)

data BuildArtifact = BuildArtifact
  { baLabel :: String
  , baPath :: FilePath
  , baBuildName :: Maybe T.Text
  }

data LoadArtifact = LoadArtifact
  { laLabel :: String
  , laPath :: FilePath
  , laExpectedDoctrines :: [T.Text]
  }

tests :: TestTree
tests =
  testGroup
    "Frontend.CanonicalCoverage"
    [ testGroup "explicit executable canonical artifacts" (map mkBuildCase canonicalBuilds)
    , testGroup "explicit elaboration-only canonical artifacts" (map mkLoadCase canonicalLoads)
    ]

canonicalBuilds :: [BuildArtifact]
canonicalBuilds =
  [ BuildArtifact
      { baLabel = "hello doc module target"
      , baPath = "examples/build/hello_doc.llang"
      , baBuildName = Just "main"
      }
  , BuildArtifact
      { baLabel = "bundle doc target"
      , baPath = "examples/build/bundle_docs.llang"
      , baBuildName = Just "main"
      }
  , BuildArtifact
      { baLabel = "type alias import target"
      , baPath = "examples/build/type_alias_import.llang"
      , baBuildName = Just "main"
      }
  , BuildArtifact
      { baLabel = "foreign provider target"
      , baPath = "examples/build/foreign_ping.llang"
      , baBuildName = Just "main"
      }
  , BuildArtifact
      { baLabel = "module data package target"
      , baPath = "examples/build/doctrine_data_package.llang"
      , baBuildName = Just "main"
      }
  , BuildArtifact
      { baLabel = "logic codegen target"
      , baPath = "examples/build/logic_full_adder_codegen.llang"
      , baBuildName = Just "main"
      }
  , BuildArtifact
      { baLabel = "sharing quotation target"
      , baPath = "examples/build/explicit_sharing_js_codegen.llang"
      , baBuildName = Just "main"
      }
  , BuildArtifact
      { baLabel = "pair autodiff share target"
      , baPath = "examples/build/autodiff_times_sin_pair_core.llang"
      , baBuildName = Just "share"
      }
  ]

canonicalLoads :: [LoadArtifact]
canonicalLoads =
  [ LoadArtifact
      { laLabel = "schema adjunction target"
      , laPath = "stdlib/schema.adjunction.llang"
      , laExpectedDoctrines = ["SchemaAdjunction"]
      }
  , LoadArtifact
      { laLabel = "schema monad target"
      , laPath = "stdlib/schema.monad.llang"
      , laExpectedDoctrines = ["SchemaMonad"]
      }
  ]

mkBuildCase :: BuildArtifact -> TestTree
mkBuildCase art =
  testCase ("canonical artifact executes: " <> baLabel art) $ do
    assertFileExists (baPath art)
    env <- requireIO =<< loadModule (baPath art)
    buildDef <- requireIO (selectBuild env (baBuildName art))
    _ <- requireIO (buildWithEnv env buildDef)
    pure ()

mkLoadCase :: LoadArtifact -> TestTree
mkLoadCase art =
  testCase ("canonical artifact elaborates: " <> laLabel art) $ do
    assertFileExists (laPath art)
    env <- requireIO =<< loadModule (laPath art)
    mapM_ (assertDoctrine env) (laExpectedDoctrines art)

assertFileExists :: FilePath -> IO ()
assertFileExists path = do
  exists <- doesFileExist path
  assertBool ("expected artifact file to exist: " <> path) exists

assertDoctrine :: ModuleEnv -> T.Text -> IO ()
assertDoctrine env doctrineName =
  let doctrines = meDoctrines env
   in assertBool
        ( "expected doctrine `"
            <> T.unpack doctrineName
            <> "` from canonical artifact"
        )
        (M.member doctrineName doctrines)

requireIO :: Either T.Text a -> IO a
requireIO (Left err) = assertFailure (T.unpack err) >> fail "unreachable"
requireIO (Right a) = pure a
