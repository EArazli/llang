{-# LANGUAGE OverloadedStrings #-}
module Strat.CLI
  ( CLIOptions(..)
  , parseArgs
  , runCLI
  ) where

import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Run (runWithEnv, selectRun, RunResult(..), Artifact(..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as M
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeDirectory)


data CLIOptions = CLIOptions
  { optFile :: FilePath
  , optRun  :: Maybe Text
  }
  deriving (Eq, Show)

parseArgs :: [String] -> Either Text CLIOptions
parseArgs args =
  case args of
    [file] -> Right (CLIOptions file Nothing)
    [file, "--run", name] -> Right (CLIOptions file (Just (T.pack name)))
    _ -> Left usage

runCLI :: CLIOptions -> IO (Either Text Text)
runCLI opts = do
  envResult <- loadModule (optFile opts)
  case envResult of
    Left err -> pure (Left err)
    Right env ->
      case selectRun env (optRun opts) of
        Left err -> pure (Left err)
        Right spec ->
          case runWithEnv env spec of
            Left err -> pure (Left err)
            Right res -> do
              writeExtractedFiles (prArtifact res)
              pure (Right (prOutput res))

writeExtractedFiles :: Artifact -> IO ()
writeExtractedFiles art =
  case art of
    ArtExtracted _ files ->
      mapM_ writeOne (M.toList files)
    _ -> pure ()
  where
    writeOne (path, body) = do
      createDirectoryIfMissing True (takeDirectory path)
      TIO.writeFile path body

usage :: Text
usage =
  T.unlines
    [ "Usage: llang-exe FILE [--run NAME]"
    , "Run a named run in FILE (default: main or the only run)."
    ]
