{-# LANGUAGE OverloadedStrings #-}
module Strat.CLI
  ( CLIOptions(..)
  , parseArgs
  , runCLI
  ) where

import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Run (runWithEnv, selectRun, RunResult(..))
import Data.Text (Text)
import qualified Data.Text as T


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
            Right res -> pure (Right (prOutput res))

usage :: Text
usage =
  T.unlines
    [ "Usage: llang-exe FILE [--run NAME]"
    , "Run a named run in FILE (default: main or the only run)."
    ]
