{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.CanonicalCoverage
  ( tests
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Strat.Frontend.Env (ModuleEnv, meDoctrines)
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Run (selectRun, runWithEnv)
import System.Directory (doesFileExist)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)

data RunArtifact = RunArtifact
  { raLabel :: String
  , raPath :: FilePath
  , raRunName :: Maybe T.Text
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
    [ testGroup "explicit runnable canonical artifacts" (map mkRunCase canonicalRuns)
    , testGroup "explicit elaboration-only canonical artifacts" (map mkLoadCase canonicalLoads)
    ]

canonicalRuns :: [RunArtifact]
canonicalRuns =
  [ RunArtifact
      { raLabel = "two-layer classification target"
      , raPath = "examples/run/classification_resolution.ok.run.llang"
      , raRunName = Just "main"
      }
  , RunArtifact
      { raLabel = "three-layer classification target"
      , raPath = "examples/run/classification_layered_3level.ok.run.llang"
      , raRunName = Just "main"
      }
  , RunArtifact
      { raLabel = "dependent doctrine target"
      , raPath = "examples/run/dependent/vec.run.llang"
      , raRunName = Just "main"
      }
  , RunArtifact
      { raLabel = "pushout doctrine target"
      , raPath = "examples/run/pushout/nat_bool_plus.run.llang"
      , raRunName = Just "main"
      }
  , RunArtifact
      { raLabel = "classified modality target"
      , raPath = "examples/run/modes/adjunction_real.run.llang"
      , raRunName = Just "triangle_left"
      }
  , RunArtifact
      { raLabel = "effects composition target"
      , raPath = "examples/run/effects/combined_with_handler.run.llang"
      , raRunName = Just "main"
      }
  , RunArtifact
      { raLabel = "foliation+forget target"
      , raPath = "examples/run/foliation/basic_foliate.run.llang"
      , raRunName = Just "main"
      }
  , RunArtifact
      { raLabel = "codegen target"
      , raPath = "examples/run/codegen/simple_codegen.run.llang"
      , raRunName = Just "main"
      }
  , RunArtifact
      { raLabel = "data macro target"
      , raPath = "examples/run/data/list.run.llang"
      , raRunName = Just "main"
      }
  , RunArtifact
      { raLabel = "data fold target"
      , raPath = "examples/run/data/list_fold_length.run.llang"
      , raRunName = Just "main"
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

mkRunCase :: RunArtifact -> TestTree
mkRunCase art =
  testCase ("canonical artifact executes: " <> raLabel art) $ do
    assertFileExists (raPath art)
    env <- requireIO =<< loadModule (raPath art)
    runDef <- requireIO (selectRun env (raRunName art))
    _ <- requireIO (runWithEnv env runDef)
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
