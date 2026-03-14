{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Loader
  ( CacheStatus(..)
  , CompilationDecl(..)
  , CompilationDeclGroup(..)
  , CompilationUnitArtifacts(..)
  , CompilationUnit(..)
  , LoadedProject(..)
  , loadProject
  , loadProjectWithBudget
  , loadModule
  , loadModuleWithBudget
  ) where

import Control.Exception (IOException, catch)
import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Strat.DSL.AST (RawDecl(..), RawFile(..))
import Strat.DSL.Elab (elabRawFileWithEnvAndBudget)
import Strat.DSL.Parse (parseRawFile)
import Strat.Frontend.CompilerFingerprint (compilerFingerprint)
import Strat.Frontend.Env
import Strat.Frontend.Model
  ( LanguageDef
  , ModuleElaboratorDef
  , ModuleDataReprDef
  , ModuleSurfaceDef
  , InterfaceDef
  , ModuleDef
  , BuildDef
  )
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Pipeline (Pipeline, DerivedDoctrine, FragmentDecl)
import Strat.Poly.Kernel (Doctrine)
import Strat.Poly.Morphism (Morphism)
import Strat.Poly.Proof (SearchBudget, defaultSearchBudget)
import Strat.Poly.Surface (PolySurfaceDef)
import Strat.Util.Fingerprint (fingerprintText)
import System.Directory
  ( canonicalizePath
  , createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , listDirectory
  , removeFile
  , renameFile
  )
import System.FilePath ((</>), takeDirectory)
import System.IO (hClose, openTempFile)
import Text.Read (readMaybe)


data CacheStatus
  = CacheHit
  | CacheMiss
  deriving (Eq, Read, Show)


data CompilationUnit = CompilationUnit
  { cuPath :: FilePath
  , cuImports :: [FilePath]
  , cuCacheKey :: Text
  , cuCacheStatus :: CacheStatus
  , cuArtifacts :: CompilationUnitArtifacts
  }
  deriving (Eq, Read, Show)


data LoadedProject = LoadedProject
  { lpEntryPath :: FilePath
  , lpUnits :: M.Map FilePath CompilationUnit
  , lpEnv :: ModuleEnv
  }
  deriving (Eq, Show)


data LoadState = LoadState
  { lsCacheRoot :: FilePath
  , lsLoading :: S.Set FilePath
  , lsLoaded :: M.Map FilePath CompilationUnit
  }


data CompilationDecl
  = CDeclDoctrine Text Doctrine
  | CDeclMorphism Text Morphism
  | CDeclSurface Text PolySurfaceDef
  | CDeclModuleElaborator Text ModuleElaboratorDef
  | CDeclModuleDataRepr Text ModuleDataReprDef
  | CDeclModuleSurface Text ModuleSurfaceDef
  | CDeclPipeline Text Pipeline
  | CDeclLanguage Text LanguageDef
  | CDeclInterface Text InterfaceDef
  | CDeclModule Text ModuleDef
  | CDeclBuild Text BuildDef
  | CDeclFragment Text FragmentDecl
  | CDeclDerivedDoctrine Text DerivedDoctrine
  | CDeclImplements Text Text Text
  | CDeclFunctor Text DoctrineFunctorDef
  deriving (Eq, Read, Show)


data CompilationDeclGroup = CompilationDeclGroup
  { cdgDecls :: [CompilationDecl]
  , cdgProofStats :: ProofStats
  }
  deriving (Eq, Read, Show)


data CompilationUnitArtifacts = CompilationUnitArtifacts
  { cuaDeclGroups :: [CompilationDeclGroup]
  , cuaDecls :: [CompilationDecl]
  , cuaDoctrines :: M.Map Text Doctrine
  , cuaMorphisms :: M.Map Text Morphism
  , cuaSurfaces :: M.Map Text PolySurfaceDef
  , cuaModuleElaborators :: M.Map Text ModuleElaboratorDef
  , cuaModuleDataReprs :: M.Map Text ModuleDataReprDef
  , cuaModuleSurfaces :: M.Map Text ModuleSurfaceDef
  , cuaPipelines :: M.Map Text Pipeline
  , cuaLanguages :: M.Map Text LanguageDef
  , cuaInterfaces :: M.Map Text InterfaceDef
  , cuaModules :: M.Map Text ModuleDef
  , cuaBuilds :: M.Map Text BuildDef
  , cuaFragments :: M.Map Text FragmentDecl
  , cuaDerivedDoctrines :: M.Map Text DerivedDoctrine
  , cuaImplDefaults :: M.Map (Text, Text) [Text]
  , cuaFunctors :: M.Map Text DoctrineFunctorDef
  }
  deriving (Eq, Read, Show)


data CachedUnit = CachedUnit
  { ccuVersion :: Int
  , ccuCompilerFingerprint :: Text
  , ccuPath :: FilePath
  , ccuSourceHash :: Text
  , ccuBudget :: SearchBudget
  , ccuImports :: [FilePath]
  , ccuImportKeys :: M.Map FilePath Text
  , ccuUnitKey :: Text
  , ccuArtifacts :: CompilationUnitArtifacts
  }
  deriving (Eq, Read, Show)


cacheFormatVersion :: Int
cacheFormatVersion = 5


loadProject :: FilePath -> IO (Either Text LoadedProject)
loadProject = loadProjectWithBudget defaultSearchBudget


loadModule :: FilePath -> IO (Either Text ModuleEnv)
loadModule path = fmap (fmap lpEnv) (loadProject path)


loadModuleWithBudget :: SearchBudget -> FilePath -> IO (Either Text ModuleEnv)
loadModuleWithBudget budget path = fmap (fmap lpEnv) (loadProjectWithBudget budget path)


loadProjectWithBudget :: SearchBudget -> FilePath -> IO (Either Text LoadedProject)
loadProjectWithBudget budget path = do
  absPathResult <- canonicalizePathEither "loadProject" path
  case absPathResult of
    Left err -> pure (Left err)
    Right absPath -> do
      cacheRoot <- discoverCacheRoot absPath
      cacheInit <-
        catch
          (createDirectoryIfMissing True cacheRoot >> pure (Right ()))
          (\err -> pure (Left ("cache: failed to initialize cache root " <> T.pack cacheRoot <> ": " <> T.pack (show (err :: IOException)))))
      case cacheInit of
        Left err -> pure (Left err)
        Right () -> do
          let st0 =
                LoadState
                  { lsCacheRoot = cacheRoot
                  , lsLoading = S.empty
                  , lsLoaded = M.empty
                  }
          result <- loadUnit budget st0 absPath
          case result of
            Left err -> pure (Left err)
            Right st ->
              pure (assembleProject st absPath)


loadUnit :: SearchBudget -> LoadState -> FilePath -> IO (Either Text LoadState)
loadUnit budget st path = do
  absPathResult <- canonicalizePathEither "loadUnit" path
  case absPathResult of
    Left err -> pure (Left err)
    Right absPath ->
      case M.lookup absPath (lsLoaded st) of
        Just _ -> pure (Right st)
        Nothing ->
          if absPath `S.member` lsLoading st
            then pure (Left "Import cycle detected")
            else do
              contentResult <- readTextFileEither "loadUnit" absPath
              case contentResult of
                Left err -> pure (Left err)
                Right content -> do
                  let sourceHash = fingerprintText content
                  let stLoading = st { lsLoading = S.insert absPath (lsLoading st) }
                  cachedResult <- readCachedUnit st absPath
                  case cachedResult of
                    Left err -> pure (Left err)
                    Right cached ->
                      case cached of
                        Just entry
                          | cacheMatches budget absPath sourceHash entry ->
                              loadCachedUnit budget stLoading absPath entry
                        _ ->
                          compileUnit budget stLoading absPath content sourceHash


loadCachedUnit :: SearchBudget -> LoadState -> FilePath -> CachedUnit -> IO (Either Text LoadState)
loadCachedUnit budget st absPath cached = do
  depsResult <- loadAbsoluteImports budget st (ccuImports cached)
  case depsResult of
    Left err -> pure (Left err)
    Right stAfter ->
      case buildImportKeyMap stAfter (ccuImports cached) of
        Left err -> pure (Left err)
        Right importKeys ->
          if importKeys == ccuImportKeys cached
            then
              let unit =
                    CompilationUnit
                      { cuPath = absPath
                      , cuImports = ccuImports cached
                      , cuCacheKey = ccuUnitKey cached
                      , cuCacheStatus = CacheHit
                      , cuArtifacts = ccuArtifacts cached
                      }
               in pure
                    ( Right
                        stAfter
                          { lsLoading = S.delete absPath (lsLoading stAfter)
                          , lsLoaded = M.insert absPath unit (lsLoaded stAfter)
                          }
                    )
            else do
              contentResult <- readTextFileEither "loadCachedUnit" absPath
              case contentResult of
                Left err -> pure (Left err)
                Right content -> do
                  let sourceHash = fingerprintText content
                  compileUnit budget stAfter absPath content sourceHash


compileUnit :: SearchBudget -> LoadState -> FilePath -> Text -> Text -> IO (Either Text LoadState)
compileUnit budget st absPath content sourceHash =
  case parseRawFile content of
    Left err -> pure (Left err)
    Right (RawFile decls) -> do
      let relImports = [p | DeclImport p <- decls]
      depsResult <- loadImports budget st (takeDirectory absPath) relImports
      case depsResult of
        Left err -> pure (Left err)
        Right (stAfter, importPaths) ->
          case assembleEnv stAfter importPaths of
            Left err -> pure (Left err)
            Right envBase ->
              case compileUnitArtifacts budget envBase decls of
                Left err -> pure (Left err)
                Right artifacts ->
                  case buildImportKeyMap stAfter importPaths of
                    Left err -> pure (Left err)
                    Right importKeys -> do
                      let unitKey = computeUnitKey absPath sourceHash budget importKeys
                          unit =
                            CompilationUnit
                              { cuPath = absPath
                              , cuImports = importPaths
                              , cuCacheKey = unitKey
                              , cuCacheStatus = CacheMiss
                              , cuArtifacts = artifacts
                              }
                      cacheWrite <-
                        writeCachedUnit stAfter absPath
                          CachedUnit
                            { ccuVersion = cacheFormatVersion
                            , ccuCompilerFingerprint = compilerFingerprint
                            , ccuPath = absPath
                            , ccuSourceHash = sourceHash
                            , ccuBudget = budget
                            , ccuImports = importPaths
                            , ccuImportKeys = importKeys
                            , ccuUnitKey = unitKey
                            , ccuArtifacts = artifacts
                            }
                      case cacheWrite of
                        Left err -> pure (Left err)
                        Right () ->
                          pure
                            ( Right
                                stAfter
                                  { lsLoading = S.delete absPath (lsLoading stAfter)
                                  , lsLoaded = M.insert absPath unit (lsLoaded stAfter)
                                  }
                            )


loadImports :: SearchBudget -> LoadState -> FilePath -> [FilePath] -> IO (Either Text (LoadState, [FilePath]))
loadImports _ st _ [] = pure (Right (st, []))
loadImports budget st base (path:rest) = do
  absPathResult <- canonicalizePathEither "loadImports" (base </> path)
  case absPathResult of
    Left err -> pure (Left err)
    Right absPath -> do
      loaded <- loadUnit budget st absPath
      case loaded of
        Left err -> pure (Left err)
        Right st1 -> do
          tailResult <- loadImports budget st1 base rest
          case tailResult of
            Left err -> pure (Left err)
            Right (st2, restPaths) -> pure (Right (st2, absPath : restPaths))


loadAbsoluteImports :: SearchBudget -> LoadState -> [FilePath] -> IO (Either Text LoadState)
loadAbsoluteImports _ st [] = pure (Right st)
loadAbsoluteImports budget st (path:rest) = do
  loaded <- loadUnit budget st path
  case loaded of
    Left err -> pure (Left err)
    Right st1 -> loadAbsoluteImports budget st1 rest


assembleProject :: LoadState -> FilePath -> Either Text LoadedProject
assembleProject st entryPath = do
  order <- orderedClosure st [entryPath]
  env <- assembleEnvInOrder st order
  let units = M.restrictKeys (lsLoaded st) (S.fromList order)
  pure
    LoadedProject
      { lpEntryPath = entryPath
      , lpUnits = units
      , lpEnv = env
      }


assembleEnv :: LoadState -> [FilePath] -> Either Text ModuleEnv
assembleEnv st roots = do
  order <- orderedClosure st roots
  assembleEnvInOrder st order


assembleEnvInOrder :: LoadState -> [FilePath] -> Either Text ModuleEnv
assembleEnvInOrder st order =
  foldM step preludeEnv order
  where
    preludeEnv = emptyEnv { meDoctrines = preludeDoctrines }
    step acc path =
      case M.lookup path (lsLoaded st) of
        Nothing -> Left "internal error: missing compilation unit"
        Just unit -> appendCompilationUnitArtifacts acc (cuArtifacts unit)


orderedClosure :: LoadState -> [FilePath] -> Either Text [FilePath]
orderedClosure st roots =
  snd <$> foldM visitOne (S.empty, []) roots
  where
    visitOne (seen, acc) path
      | path `S.member` seen = Right (seen, acc)
      | otherwise =
          case M.lookup path (lsLoaded st) of
            Nothing -> Left "internal error: missing compilation unit in dependency closure"
            Just unit -> do
              (seen', acc') <- foldM visitOne (S.insert path seen, acc) (cuImports unit)
              Right (seen', path : acc')


readCachedUnit :: LoadState -> FilePath -> IO (Either Text (Maybe CachedUnit))
readCachedUnit st absPath = do
  let cachePath = cacheFilePath st absPath
  exists <- doesFileExist cachePath
  if not exists
    then pure (Right Nothing)
    else do
      txtResult <- readTextFileEither "readCachedUnit" cachePath
      pure
        ( fmap
            ( \txt ->
                case readMaybe (T.unpack txt) of
                  Just entry -> Just entry
                  Nothing -> Nothing
            )
            txtResult
        )


writeCachedUnit :: LoadState -> FilePath -> CachedUnit -> IO (Either Text ())
writeCachedUnit st absPath cached = do
  let cachePath = cacheFilePath st absPath
      cacheDir = takeDirectory cachePath
      payload = T.pack (show cached)
  catch
    (do
        createDirectoryIfMissing True cacheDir
        (tmpPath, handle) <- openTempFile cacheDir "unit.cache.tmp"
        let cleanupTmp = do
              hClose handle `catch` ignoreIOException
              removeFile tmpPath `catch` ignoreIOException
        catch
          (do
              TIO.hPutStr handle payload
              hClose handle
              renameFile tmpPath cachePath
              pure (Right ())
          )
          (\err -> do
              cleanupTmp
              cleanupTempFiles cacheDir
              pure (Left ("cache: failed to write unit " <> T.pack absPath <> ": " <> T.pack (show (err :: IOException)))))
    )
    (\err -> do
        cleanupTempFiles cacheDir
        pure (Left ("cache: failed to initialize unit cache " <> T.pack absPath <> ": " <> T.pack (show (err :: IOException)))))


cleanupTempFiles :: FilePath -> IO ()
cleanupTempFiles cacheDir = do
  let tempPrefix = "unit.cache.tmp"
  entries <- listDirectorySafe cacheDir
  mapM_ (removeIfTemp cacheDir tempPrefix) entries


removeIfTemp :: FilePath -> String -> FilePath -> IO ()
removeIfTemp cacheDir tempPrefix name
  | T.pack tempPrefix `T.isPrefixOf` T.pack name =
      removeFile (cacheDir </> name) `catch` ignoreIOException
  | otherwise = pure ()


listDirectorySafe :: FilePath -> IO [FilePath]
listDirectorySafe path =
  catch
    (listDirectory path)
    (\err -> let _ = err :: IOException in pure [])


ignoreIOException :: IOException -> IO ()
ignoreIOException _ = pure ()


cacheMatches :: SearchBudget -> FilePath -> Text -> CachedUnit -> Bool
cacheMatches budget absPath sourceHash cached =
  ccuVersion cached == cacheFormatVersion
    && ccuCompilerFingerprint cached == compilerFingerprint
    && ccuPath cached == absPath
    && ccuSourceHash cached == sourceHash
    && ccuBudget cached == budget


buildImportKeyMap :: LoadState -> [FilePath] -> Either Text (M.Map FilePath Text)
buildImportKeyMap st =
  foldM step M.empty
  where
    step acc path =
      case M.lookup path (lsLoaded st) of
        Nothing -> Left "internal error: missing imported compilation unit"
        Just unit -> Right (M.insert path (cuCacheKey unit) acc)


computeUnitKey :: FilePath -> Text -> SearchBudget -> M.Map FilePath Text -> Text
computeUnitKey absPath sourceHash budget importKeys =
  fingerprintText
    ( T.intercalate
        "\n"
        [ "compiler:" <> compilerFingerprint
        , "path:" <> T.pack absPath
        , "source:" <> sourceHash
        , "budget:" <> T.pack (show budget)
        , "deps:" <> T.pack (show (M.toAscList importKeys))
        ]
    )


cacheFilePath :: LoadState -> FilePath -> FilePath
cacheFilePath st absPath =
  lsCacheRoot st </> T.unpack (fingerprintText (T.pack absPath)) <> ".cache"


canonicalizePathEither :: Text -> FilePath -> IO (Either Text FilePath)
canonicalizePathEither context path =
  catch
    (Right <$> canonicalizePath path)
    (\err -> pure (Left (context <> ": failed to resolve path " <> T.pack path <> ": " <> T.pack (show (err :: IOException)))))


readTextFileEither :: Text -> FilePath -> IO (Either Text Text)
readTextFileEither context path =
  catch
    (Right <$> TIO.readFile path)
    (\err -> pure (Left (context <> ": failed to read " <> T.pack path <> ": " <> T.pack (show (err :: IOException)))))


discoverCacheRoot :: FilePath -> IO FilePath
discoverCacheRoot absEntry = do
  let entryDir = takeDirectory absEntry
  root <- findRootMarker entryDir (ancestorDirs entryDir)
  pure (root </> ".llang-cache" </> T.unpack compilerFingerprint </> "units")


findRootMarker :: FilePath -> [FilePath] -> IO FilePath
findRootMarker fallback [] = pure fallback
findRootMarker fallback (dir:rest) = do
  hasGit <- doesDirectoryExist (dir </> ".git")
  hasPackageYaml <- doesFileExist (dir </> "package.yaml")
  hasCabal <- doesFileExist (dir </> "llang.cabal")
  if hasGit || hasPackageYaml || hasCabal
    then pure dir
    else
      findRootMarker fallback rest


ancestorDirs :: FilePath -> [FilePath]
ancestorDirs dir =
  dir : if parent == dir then [] else ancestorDirs parent
  where
    parent = takeDirectory dir


compileUnitArtifacts :: SearchBudget -> ModuleEnv -> [RawDecl] -> Either Text CompilationUnitArtifacts
compileUnitArtifacts budget base decls = do
  (_, compiledGroupsRev) <- foldM step (base, []) decls
  pure (mkCompilationUnitArtifacts (reverse compiledGroupsRev))
  where
    step (env, acc) decl = do
      env' <- elabRawFileWithEnvAndBudget budget env (RawFile [decl])
      let decls' = diffCompilationDecls env env'
          proofs' = subProofStats (meProofStats env') (meProofStats env)
      if null decls' && proofs' == emptyProofStats
        then pure (env', acc)
        else
          pure
            ( env'
            , CompilationDeclGroup
                { cdgDecls = decls'
                , cdgProofStats = proofs'
                }
                : acc
            )


diffCompilationDecls :: ModuleEnv -> ModuleEnv -> [CompilationDecl]
diffCompilationDecls before after =
  concat
    [ [CDeclDoctrine name doc | (name, doc) <- M.toAscList (M.difference (meDoctrines after) (meDoctrines before))]
    , [CDeclMorphism name morph | (name, morph) <- M.toAscList (M.difference (meMorphisms after) (meMorphisms before))]
    , [CDeclSurface name surface | (name, surface) <- M.toAscList (M.difference (meSurfaces after) (meSurfaces before))]
    , [CDeclModuleElaborator name elaborator | (name, elaborator) <- M.toAscList (M.difference (meModuleElaborators after) (meModuleElaborators before))]
    , [CDeclModuleDataRepr name reprDef | (name, reprDef) <- M.toAscList (M.difference (meModuleDataReprs after) (meModuleDataReprs before))]
    , [CDeclModuleSurface name surface | (name, surface) <- M.toAscList (M.difference (meModuleSurfaces after) (meModuleSurfaces before))]
    , [CDeclPipeline name pipeline | (name, pipeline) <- M.toAscList (M.difference (mePipelines after) (mePipelines before))]
    , [CDeclLanguage name lang | (name, lang) <- M.toAscList (M.difference (meLanguages after) (meLanguages before))]
    , [CDeclInterface name iface | (name, iface) <- M.toAscList (M.difference (meInterfaces after) (meInterfaces before))]
    , [CDeclModule name modDef | (name, modDef) <- M.toAscList (M.difference (meModules after) (meModules before))]
    , [CDeclBuild name buildDef | (name, buildDef) <- M.toAscList (M.difference (meBuilds after) (meBuilds before))]
    , [CDeclFragment name fragment | (name, fragment) <- M.toAscList (M.difference (meFragments after) (meFragments before))]
    , [CDeclDerivedDoctrine name derived | (name, derived) <- M.toAscList (M.difference (meDerivedDoctrines after) (meDerivedDoctrines before))]
    ,
      [ CDeclImplements iface tgt morphName
      | ((iface, tgt), morphNames) <- M.toAscList (diffImplDefaults (meImplDefaults after) (meImplDefaults before))
      , morphName <- morphNames
      ]
    , [CDeclFunctor name functorDef | (name, functorDef) <- M.toAscList (M.difference (meFunctors after) (meFunctors before))]
    ]


mkCompilationUnitArtifacts :: [CompilationDeclGroup] -> CompilationUnitArtifacts
mkCompilationUnitArtifacts groups =
  foldl' indexDecl emptyArtifacts decls
  where
    decls = concatMap cdgDecls groups
    emptyArtifacts =
      CompilationUnitArtifacts
        { cuaDeclGroups = groups
        , cuaDecls = decls
        , cuaDoctrines = M.empty
        , cuaMorphisms = M.empty
        , cuaSurfaces = M.empty
        , cuaModuleElaborators = M.empty
        , cuaModuleDataReprs = M.empty
        , cuaModuleSurfaces = M.empty
        , cuaPipelines = M.empty
        , cuaLanguages = M.empty
        , cuaInterfaces = M.empty
        , cuaModules = M.empty
        , cuaBuilds = M.empty
        , cuaFragments = M.empty
        , cuaDerivedDoctrines = M.empty
        , cuaImplDefaults = M.empty
        , cuaFunctors = M.empty
        }

    indexDecl acc decl =
      case decl of
        CDeclDoctrine name doc -> acc { cuaDoctrines = M.insert name doc (cuaDoctrines acc) }
        CDeclMorphism name morph -> acc { cuaMorphisms = M.insert name morph (cuaMorphisms acc) }
        CDeclSurface name surface -> acc { cuaSurfaces = M.insert name surface (cuaSurfaces acc) }
        CDeclModuleElaborator name elaborator -> acc { cuaModuleElaborators = M.insert name elaborator (cuaModuleElaborators acc) }
        CDeclModuleDataRepr name reprDef -> acc { cuaModuleDataReprs = M.insert name reprDef (cuaModuleDataReprs acc) }
        CDeclModuleSurface name surface -> acc { cuaModuleSurfaces = M.insert name surface (cuaModuleSurfaces acc) }
        CDeclPipeline name pipeline -> acc { cuaPipelines = M.insert name pipeline (cuaPipelines acc) }
        CDeclLanguage name lang -> acc { cuaLanguages = M.insert name lang (cuaLanguages acc) }
        CDeclInterface name iface -> acc { cuaInterfaces = M.insert name iface (cuaInterfaces acc) }
        CDeclModule name modDef -> acc { cuaModules = M.insert name modDef (cuaModules acc) }
        CDeclBuild name buildDef -> acc { cuaBuilds = M.insert name buildDef (cuaBuilds acc) }
        CDeclFragment name fragment -> acc { cuaFragments = M.insert name fragment (cuaFragments acc) }
        CDeclDerivedDoctrine name derived -> acc { cuaDerivedDoctrines = M.insert name derived (cuaDerivedDoctrines acc) }
        CDeclImplements iface tgt morphName ->
          acc
            { cuaImplDefaults =
                M.insertWith
                  (\new old -> old <> filter (`notElem` old) new)
                  (iface, tgt)
                  [morphName]
                  (cuaImplDefaults acc)
            }
        CDeclFunctor name functorDef -> acc { cuaFunctors = M.insert name functorDef (cuaFunctors acc) }


appendCompilationUnitArtifacts :: ModuleEnv -> CompilationUnitArtifacts -> Either Text ModuleEnv
appendCompilationUnitArtifacts env artifacts = do
  env' <- foldM appendGroup env (cuaDeclGroups artifacts)
  pure env'
  where
    appendGroup acc group = do
      let deltaEnv = envForDeclGroup group
      merged <- mergeEnv acc deltaEnv
      if merged == acc
        then Right acc
        else Right merged { meProofStats = addProofStats (meProofStats merged) (cdgProofStats group) }


envForDeclGroup :: CompilationDeclGroup -> ModuleEnv
envForDeclGroup group =
  unitArtifactsEnv (mkCompilationUnitArtifacts [group])


unitArtifactsEnv :: CompilationUnitArtifacts -> ModuleEnv
unitArtifactsEnv artifacts =
  emptyEnv
    { meDoctrines = cuaDoctrines artifacts
    , meMorphisms = cuaMorphisms artifacts
    , meSurfaces = cuaSurfaces artifacts
    , meModuleElaborators = cuaModuleElaborators artifacts
    , meModuleDataReprs = cuaModuleDataReprs artifacts
    , meModuleSurfaces = cuaModuleSurfaces artifacts
    , mePipelines = cuaPipelines artifacts
    , meLanguages = cuaLanguages artifacts
    , meInterfaces = cuaInterfaces artifacts
    , meModules = cuaModules artifacts
    , meBuilds = cuaBuilds artifacts
    , meFragments = cuaFragments artifacts
    , meDerivedDoctrines = cuaDerivedDoctrines artifacts
    , meImplDefaults = cuaImplDefaults artifacts
    , meFunctors = cuaFunctors artifacts
    , meProofStats = emptyProofStats
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
