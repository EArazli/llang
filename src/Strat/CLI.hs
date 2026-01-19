{-# LANGUAGE OverloadedStrings #-}
module Strat.CLI
  ( CLIOptions(..)
  , parseArgs
  , runCLI
  ) where

import Strat.Frontend.Run (runFile, RunResult(..))
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
  result <- runFile (optFile opts) (optRun opts)
  pure (fmap rrOutput result)

usage :: Text
usage =
  T.unlines
    [ "Usage: llang-exe FILE [--run NAME]"
    , "Run a named run in FILE (default: main or the only run)."
    ]
