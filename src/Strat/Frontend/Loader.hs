{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Loader
  ( loadModule
  ) where

import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.AST (RawFile(..), RawDecl(..))
import Strat.Kernel.DSL.Elab (elabRawFileWithEnv)
import Strat.Frontend.Env
import Data.Text (Text)
import qualified Data.Text.IO as TIO
import qualified Data.Set as S
import System.FilePath (takeDirectory, (</>))
import System.Directory (canonicalizePath)

loadModule :: FilePath -> IO (Either Text ModuleEnv)
loadModule path = do
  absPath <- canonicalizePath path
  loadWith S.empty absPath True

loadWith :: S.Set FilePath -> FilePath -> Bool -> IO (Either Text ModuleEnv)
loadWith seen path isMain = do
  absPath <- canonicalizePath path
  if absPath `S.member` seen
    then pure (Left "Import cycle detected")
    else do
      content <- TIO.readFile absPath
      case parseRawFile content of
        Left err -> pure (Left err)
        Right raw@(RawFile decls) -> do
          let imports = [p | DeclImport p <- decls]
          envImports <- loadImports (S.insert absPath seen) (takeDirectory absPath) imports
          case envImports of
            Left err -> pure (Left err)
            Right envBase -> do
              case elabRawFileWithEnv envBase raw of
                Left err -> pure (Left err)
                Right env ->
                  if not isMain && meRun env /= Nothing
                    then pure (Left "run block is only allowed in the main file")
                    else pure (Right env)

loadImports :: S.Set FilePath -> FilePath -> [FilePath] -> IO (Either Text ModuleEnv)
loadImports _ _ [] = pure (Right emptyEnv)
loadImports seen base (p:ps) = do
  let nextPath = base </> p
  loaded <- loadWith seen nextPath False
  case loaded of
    Left err -> pure (Left err)
    Right env1 -> do
      rest <- loadImports seen base ps
      case rest of
        Left err -> pure (Left err)
        Right env2 -> pure (mergeEnv env1 env2)
