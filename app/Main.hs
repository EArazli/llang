module Main (main) where

import Strat.CLI
import qualified Data.Text.IO as TIO
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (stderr)

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Left msg -> do
      TIO.hPutStrLn stderr msg
      exitFailure
    Right opts -> do
      result <- runCLI opts
      case result of
        Left err -> do
          TIO.hPutStrLn stderr err
          exitFailure
        Right out -> TIO.putStrLn (renderResult out)
