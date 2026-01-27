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
loadModule path = do
  absPath <- canonicalizePath path
  result <- loadModuleWith emptyState absPath True
  case result of
    Left err -> pure (Left err)
    Right (st, modMain) -> pure (envFromDeps st (lmDeps modMain))

loadModuleWith :: LoadState -> FilePath -> Bool -> IO (Either Text (LoadState, LoadedModule))
loadModuleWith st path isMain = do
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
              resImports <- loadImports stLoading (takeDirectory absPath) imports
              case resImports of
                Left err -> pure (Left err)
                Right (stAfter, importMods) ->
                  case depsFromMods importMods of
                    Left err -> pure (Left err)
                    Right importDeps ->
                      case envFromDeps stAfter importDeps of
                        Left err -> pure (Left err)
                        Right envBase ->
                          case elabRawFileWithEnv envBase raw of
                            Left err -> pure (Left err)
                            Right envFull ->
                              let envLocal = diffEnv envFull envBase
                              in if not isMain && (not (M.null (meRuns envLocal)) || not (M.null (mePolyRuns envLocal)))
                                then pure (Left "runs are only allowed in the main file")
                                else do
                                  let deps = S.insert absPath importDeps
                                  let modLocal = LoadedModule envLocal deps
                                  let stFinal = stAfter
                                        { lsLoading = S.delete absPath (lsLoading stAfter)
                                        , lsLoaded = M.insert absPath modLocal (lsLoaded stAfter)
                                        }
                                  pure (Right (stFinal, modLocal))

loadImports :: LoadState -> FilePath -> [FilePath] -> IO (Either Text (LoadState, [LoadedModule]))
loadImports st _ [] = pure (Right (st, []))
loadImports st base (p:ps) = do
  let nextPath = base </> p
  loaded <- loadModuleWith st nextPath False
  case loaded of
    Left err -> pure (Left err)
    Right (st1, mod1) -> do
      rest <- loadImports st1 base ps
      case rest of
        Left err -> pure (Left err)
        Right (st2, mods) -> pure (Right (st2, mod1 : mods))

depsFromMods :: [LoadedModule] -> Either Text (S.Set FilePath)
depsFromMods mods = Right (S.unions (map lmDeps mods))

envFromDeps :: LoadState -> S.Set FilePath -> Either Text ModuleEnv
envFromDeps st deps =
  foldM step emptyEnv (S.toList deps)
  where
    step acc path =
      case M.lookup path (lsLoaded st) of
        Nothing -> Left "internal error: missing loaded module"
        Just modLocal -> mergeEnv acc (lmLocal modLocal)

diffEnv :: ModuleEnv -> ModuleEnv -> ModuleEnv
diffEnv full base = ModuleEnv
  { meDoctrines = M.difference (meDoctrines full) (meDoctrines base)
  , meRawDoctrines = M.difference (meRawDoctrines full) (meRawDoctrines base)
  , mePolyDoctrines = M.difference (mePolyDoctrines full) (mePolyDoctrines base)
  , mePolyMorphisms = M.difference (mePolyMorphisms full) (mePolyMorphisms base)
  , mePolySurfaces = M.difference (mePolySurfaces full) (mePolySurfaces base)
  , mePolyModels = M.difference (mePolyModels full) (mePolyModels base)
  , meSyntaxes = M.difference (meSyntaxes full) (meSyntaxes base)
  , meSurfaces = M.difference (meSurfaces full) (meSurfaces base)
  , meMorphisms = M.difference (meMorphisms full) (meMorphisms base)
  , meModels = M.difference (meModels full) (meModels base)
  , meImplDefaults = diffImplDefaults (meImplDefaults full) (meImplDefaults base)
  , mePolyImplDefaults = diffImplDefaults (mePolyImplDefaults full) (mePolyImplDefaults base)
  , meRunSpecs = M.difference (meRunSpecs full) (meRunSpecs base)
  , mePolyRunSpecs = M.difference (mePolyRunSpecs full) (mePolyRunSpecs base)
  , meRuns = meRuns full
  , mePolyRuns = mePolyRuns full
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
