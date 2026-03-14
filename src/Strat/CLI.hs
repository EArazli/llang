{-# LANGUAGE OverloadedStrings #-}
module Strat.CLI
  ( CLIOptions(..)
  , parseArgs
  , runCLI
  ) where

import Strat.Frontend.Loader (loadModuleWithBudget)
import Strat.Frontend.Env (ModuleEnv(..), ProofStats(..), proofStatsTotal)
import Strat.Frontend.Build (buildWithEnv, selectBuild, BuildResult(..), BuildProduct(..))
import Strat.Host.Backend (HostArtifact(..))
import Strat.Poly.Proof (SearchBudget(..), defaultSearchBudget)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as M
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeDirectory)
import System.IO (stderr)


data CLIOptions = CLIOptions
  { optFile :: FilePath
  , optBuild  :: Maybe Text
  , optOutput :: Bool
  , optSearchBudget :: SearchBudget
  }
  deriving (Eq, Show)

parseArgs :: [String] -> Either Text CLIOptions
parseArgs args =
  case args of
    (file:rest) -> parseRest (CLIOptions file Nothing False defaultSearchBudget) rest
    _ -> Left usage
  where
    parseRest opts rest =
      case rest of
        [] -> Right opts
        "--build" : name : xs ->
          case optBuild opts of
            Just _ -> Left "duplicate --build flag"
            Nothing -> parseRest opts { optBuild = Just (T.pack name) } xs
        "--output" : xs ->
          if optOutput opts
            then Left "duplicate --output flag"
            else parseRest opts { optOutput = True } xs
        "--max-depth" : nTxt : xs -> do
          n <- parseInt "--max-depth" nTxt
          if n < 0
            then Left "--max-depth must be >= 0"
            else parseRest opts { optSearchBudget = (optSearchBudget opts) { sbMaxDepth = n } } xs
        "--max-states" : nTxt : xs -> do
          n <- parseInt "--max-states" nTxt
          if n <= 0
            then Left "--max-states must be > 0"
            else parseRest opts { optSearchBudget = (optSearchBudget opts) { sbMaxStates = n } } xs
        "--timeout-ms" : nTxt : xs -> do
          n <- parseInt "--timeout-ms" nTxt
          if n < 0
            then Left "--timeout-ms must be >= 0"
            else parseRest opts { optSearchBudget = (optSearchBudget opts) { sbTimeoutMs = n } } xs
        _ -> Left usage

    parseInt flag raw =
      case reads raw of
        [(n, "")] -> Right n
        _ -> Left (T.pack flag <> ": expected integer, got `" <> T.pack raw <> "`")

runCLI :: CLIOptions -> IO (Either Text Text)
runCLI opts = do
  envResult <- loadModuleWithBudget (optSearchBudget opts) (optFile opts)
  case envResult of
    Left err -> pure (Left err)
    Right env ->
      case selectBuild env (optBuild opts) of
        Left err ->
          pure (Left err)
        Right spec ->
          case buildWithEnv env spec of
            Left err -> pure (Left err)
            Right res -> do
              TIO.hPutStrLn stderr (renderProofSummary (meProofStats env))
              if optOutput opts
                then writeExtractedFiles (brArtifact res)
                else pure ()
              pure (Right (brOutput res))

writeExtractedFiles :: BuildProduct -> IO ()
writeExtractedFiles art =
  case art of
    BPHost host ->
      mapM_ writeOne (M.toList (haFiles host))
    _ -> pure ()
  where
    writeOne (path, body) = do
      createDirectoryIfMissing True (takeDirectory path)
      TIO.writeFile path body

usage :: Text
usage =
  T.unlines
    [ "Usage: llang-exe FILE [--build NAME] [--output] [--max-depth N] [--max-states N] [--timeout-ms N]"
    , "Run a named build in FILE (default: main or the only build)."
    , "--output enables writing emitted file artifacts to disk."
    , "Search-budget flags tune auto-proof search during module elaboration/checking."
    ]

renderProofSummary :: ProofStats -> Text
renderProofSummary stats =
  "proof-summary: total="
    <> tshow (proofStatsTotal stats)
    <> " (morphism="
    <> tshow (psMorphismProofs stats)
    <> ", action="
    <> tshow (psActionProofs stats)
    <> ", implements="
    <> tshow (psImplementsProofs stats)
    <> ")"

tshow :: Show a => a -> Text
tshow = T.pack . show
