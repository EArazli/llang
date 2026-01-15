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
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import System.FilePath (takeDirectory, (</>))
import System.Directory (canonicalizePath)
import Data.List (sort)
import Control.Monad (foldM)


data LoadedModule = LoadedModule
  { lmLocal   :: ModuleEnv
  , lmClosure :: S.Set FilePath
  }

data LoadState = LoadState
  { lsLoading :: S.Set FilePath
  , lsLoaded  :: M.Map FilePath LoadedModule
  }

emptyState :: LoadState
emptyState = LoadState S.empty M.empty

loadModule :: FilePath -> IO (Either Text ModuleEnv)
loadModule path = do
  absPath <- canonicalizePath path
  result <- loadModuleWith emptyState absPath True
  pure ((\(_, _, env) -> env) <$> result)

loadModuleWith :: LoadState -> FilePath -> Bool -> IO (Either Text (LoadState, S.Set FilePath, ModuleEnv))
loadModuleWith st path isMain = do
  absPath <- canonicalizePath path
  case M.lookup absPath (lsLoaded st) of
    Just loaded -> do
      case envForPaths st (lmClosure loaded) of
        Left err -> pure (Left err)
        Right env -> pure (Right (st, lmClosure loaded, env))
    Nothing ->
      if absPath `S.member` lsLoading st
        then pure (Left "Import cycle detected")
        else do
          content <- TIO.readFile absPath
          case parseRawFile content of
            Left err -> pure (Left err)
            Right raw@(RawFile decls) -> do
              let imports = [p | DeclImport p <- decls]
              let stLoading = st { lsLoading = S.insert absPath (lsLoading st) }
              resImports <- loadImports stLoading (takeDirectory absPath) imports
              case resImports of
                Left err -> pure (Left err)
                Right (stAfter, closureImports) ->
                  case envForPaths stAfter closureImports of
                    Left err -> pure (Left err)
                    Right envBase ->
                      case elabRawFileWithEnv envBase raw of
                        Left err -> pure (Left err)
                        Right envFull ->
                          let envLocal = diffEnv envFull envBase
                          in if not isMain && meRun envLocal /= Nothing
                            then pure (Left "run block is only allowed in the main file")
                            else do
                              let closure = S.insert absPath closureImports
                              let envAgg =
                                    case mergeEnv envBase envLocal of
                                      Left err -> Left err
                                      Right merged -> Right merged
                              let stFinal = stAfter
                                    { lsLoading = S.delete absPath (lsLoading stAfter)
                                    , lsLoaded = M.insert absPath (LoadedModule envLocal closure) (lsLoaded stAfter)
                                    }
                              case envAgg of
                                Left err -> pure (Left err)
                                Right merged -> pure (Right (stFinal, closure, merged))

loadImports :: LoadState -> FilePath -> [FilePath] -> IO (Either Text (LoadState, S.Set FilePath))
loadImports st _ [] = pure (Right (st, S.empty))
loadImports st base (p:ps) = do
  let nextPath = base </> p
  loaded <- loadModuleWith st nextPath False
  case loaded of
    Left err -> pure (Left err)
    Right (st1, closure1, _) -> do
      rest <- loadImports st1 base ps
      case rest of
        Left err -> pure (Left err)
        Right (st2, closureRest) ->
          pure (Right (st2, S.union closure1 closureRest))

envForPaths :: LoadState -> S.Set FilePath -> Either Text ModuleEnv
envForPaths st paths =
  foldM step emptyEnv (sort (S.toList paths))
  where
    step acc path =
      case M.lookup path (lsLoaded st) of
        Nothing -> Left ("Missing loaded module: " <> T.pack path)
        Just loaded -> mergeEnv acc (lmLocal loaded)

diffEnv :: ModuleEnv -> ModuleEnv -> ModuleEnv
diffEnv full base = ModuleEnv
  { meDoctrines = M.difference (meDoctrines full) (meDoctrines base)
  , mePresentations = M.difference (mePresentations full) (mePresentations base)
  , meSyntaxes = M.difference (meSyntaxes full) (meSyntaxes base)
  , meModels = M.difference (meModels full) (meModels base)
  , meRun = meRun full
  }
