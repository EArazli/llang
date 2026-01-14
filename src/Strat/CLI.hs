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
  }
  deriving (Eq, Show)

parseArgs :: [String] -> Either Text CLIOptions
parseArgs args =
  case args of
    [file] -> Right (CLIOptions file)
    _ -> Left usage

runCLI :: CLIOptions -> IO (Either Text Text)
runCLI opts = do
  result <- runFile (optFile opts)
  pure (fmap rrOutput result)

usage :: Text
usage =
  T.unlines
    [ "Usage: llang-exe FILE"
    , "Run the program defined by FILE (must contain a run block)."
    ]
