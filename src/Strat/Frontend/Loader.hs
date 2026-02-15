{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Loader
  ( loadModule
  , loadModuleWithBudget
  ) where

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.AST (RawFile(..), RawDecl(..))
import Strat.DSL.Elab (elabRawFileWithEnvAndBudget)
import Strat.Frontend.Env
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Poly.Proof (SearchBudget, defaultSearchBudget)
import Data.Text (Text)
import qualified Data.Text.IO as TIO
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Monad (foldM)
import System.FilePath (takeDirectory, (</>))
import System.Directory (canonicalizePath)


data LoadedModule = LoadedModule
  { lmLocal :: ModuleEnv
  , lmDeps  :: S.Set FilePath
  }

data LoadState = LoadState
  { lsLoading :: S.Set FilePath
  , lsLoaded  :: M.Map FilePath LoadedModule
  }

emptyState :: LoadState
emptyState = LoadState S.empty M.empty

loadModule :: FilePath -> IO (Either Text ModuleEnv)
loadModule = loadModuleWithBudget defaultSearchBudget

loadModuleWithBudget :: SearchBudget -> FilePath -> IO (Either Text ModuleEnv)
loadModuleWithBudget budget path = do
  absPath <- canonicalizePath path
  result <- loadModuleWith budget emptyState absPath True
  case result of
    Left err -> pure (Left err)
    Right (st, modMain) -> pure (envFromDeps st (lmDeps modMain))

loadModuleWith :: SearchBudget -> LoadState -> FilePath -> Bool -> IO (Either Text (LoadState, LoadedModule))
loadModuleWith budget st path isMain = do
  absPath <- canonicalizePath path
  case M.lookup absPath (lsLoaded st) of
    Just mod -> pure (Right (st, mod))
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
              resImports <- loadImports budget stLoading (takeDirectory absPath) imports
              case resImports of
                Left err -> pure (Left err)
                Right (stAfter, importMods) ->
                  case depsFromMods importMods of
                    Left err -> pure (Left err)
                    Right importDeps ->
                      case envFromDeps stAfter importDeps of
                        Left err -> pure (Left err)
                        Right envBase ->
                          case elabRawFileWithEnvAndBudget budget envBase raw of
                            Left err -> pure (Left err)
                            Right envFull ->
                              let envLocal = diffEnv envFull envBase
                              in if not isMain && not (M.null (meRuns envLocal))
                                then pure (Left "runs are only allowed in the main file")
                                else do
                                  let deps = S.insert absPath importDeps
                                  let modLocal = LoadedModule envLocal deps
                                  let stFinal = stAfter
                                        { lsLoading = S.delete absPath (lsLoading stAfter)
                                        , lsLoaded = M.insert absPath modLocal (lsLoaded stAfter)
                                        }
                                  pure (Right (stFinal, modLocal))

loadImports :: SearchBudget -> LoadState -> FilePath -> [FilePath] -> IO (Either Text (LoadState, [LoadedModule]))
loadImports _ st _ [] = pure (Right (st, []))
loadImports budget st base (p:ps) = do
  let nextPath = base </> p
  loaded <- loadModuleWith budget st nextPath False
  case loaded of
    Left err -> pure (Left err)
    Right (st1, mod1) -> do
      rest <- loadImports budget st1 base ps
      case rest of
        Left err -> pure (Left err)
        Right (st2, mods) -> pure (Right (st2, mod1 : mods))

depsFromMods :: [LoadedModule] -> Either Text (S.Set FilePath)
depsFromMods mods = Right (S.unions (map lmDeps mods))

envFromDeps :: LoadState -> S.Set FilePath -> Either Text ModuleEnv
envFromDeps st deps =
  foldM step preludeEnv (S.toList deps)
  where
    preludeEnv = emptyEnv { meDoctrines = preludeDoctrines }
    step acc path =
      case M.lookup path (lsLoaded st) of
        Nothing -> Left "internal error: missing loaded module"
        Just modLocal -> mergeEnv acc (lmLocal modLocal)

diffEnv :: ModuleEnv -> ModuleEnv -> ModuleEnv
diffEnv full base = ModuleEnv
  { meDoctrines = M.difference (meDoctrines full) (meDoctrines base)
  , meMorphisms = M.difference (meMorphisms full) (meMorphisms base)
  , meSurfaces = M.difference (meSurfaces full) (meSurfaces base)
  , mePipelines = M.difference (mePipelines full) (mePipelines base)
  , meDerivedDoctrines = M.difference (meDerivedDoctrines full) (meDerivedDoctrines base)
  , meImplDefaults = diffImplDefaults (meImplDefaults full) (meImplDefaults base)
  , meRuns = M.difference (meRuns full) (meRuns base)
  , meTerms = M.difference (meTerms full) (meTerms base)
  , meTemplates = M.difference (meTemplates full) (meTemplates base)
  }

diffImplDefaults :: M.Map (Text, Text) [Text] -> M.Map (Text, Text) [Text] -> M.Map (Text, Text) [Text]
diffImplDefaults full base =
  M.mapMaybeWithKey dropBase full
  where
    dropBase key names =
      case M.lookup key base of
        Nothing -> Just names
        Just baseNames ->
          let baseSet = S.fromList baseNames
              remaining = filter (`S.notMember` baseSet) names
          in if null remaining then Nothing else Just remaining
