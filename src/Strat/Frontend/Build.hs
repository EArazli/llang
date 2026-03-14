{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Frontend.Build
  ( BuildProduct(..)
  , ModuleComponent(..)
  , ModuleArtifact(..)
  , BundleArtifact(..)
  , BundleEntry(..)
  , BuildResult(..)
  , buildFile
  , buildFileWithBackendRegistry
  , buildWithEnv
  , buildWithEnvAndBackendRegistry
  , selectBuild
  , renderBuildResult
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Common.ModuleRef
  ( ModuleValueRef(..)
  , appendModuleValueRefAdapter
  )
import Strat.Common.Provider (appendProviderAdapter)
import Strat.DSL.Elab (ensureModuleMatchesInterface)
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Frontend.Model
import Strat.Pipeline
import Strat.Host.Backend
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph
import Strat.Poly.DiagramInterpretation (spliceEdge)
import Strat.Poly.Obj (objOwnerMode)
import Strat.Poly.DSL.Elab.Diag (renderModeName, topologicalEdges)
import qualified Strat.Poly.Morphism as Morph
import Strat.Poly.Pretty (renderDiagram)
import Strat.Poly.Quote (quoteDiagram)
import Strat.Poly.ModAction (applyModExpr)
import Strat.Poly.Normalize (NormalizationStatus(..), normalizeWithMapper)
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Common.Rules (RewritePolicy)
import Strat.Util.List (dedupe)


data ModuleComponent = ModuleComponent
  { mcName :: Text
  , mcImports :: [ModuleImport]
  , mcItems :: [ModuleItemDef]
  , mcProviders :: [ModuleProvider]
  , mcDataPackages :: M.Map Text ModuleDataDef
  , mcTypes :: M.Map Text ModuleTypeDef
  , mcValues :: M.Map Text ModuleValueDef
  , mcExportTypes :: M.Map Text ModuleTypeDef
  , mcExports :: M.Map Text ModuleValueDef
  , mcExportInterfaces :: [Text]
  }
  deriving (Eq, Show)


data ModuleArtifact = ModuleArtifact
  { maName :: Text
  , maLanguage :: Text
  , maDoctrine :: Doctrine
  , maPublicComponents :: [Text]
  , maComponents :: [ModuleComponent]
  , maImports :: [ModuleImport]
  , maItems :: [ModuleItemDef]
  , maProviders :: [ModuleProvider]
  , maDataPackages :: M.Map Text ModuleDataDef
  , maTypes :: M.Map Text ModuleTypeDef
  , maValues :: M.Map Text ModuleValueDef
  , maExportTypes :: M.Map Text ModuleTypeDef
  , maExports :: M.Map Text ModuleValueDef
  , maExportInterfaces :: [Text]
  }
  deriving (Eq, Show)


data BundleEntry = BundleEntry
  { beName :: Text
  , beDoctrine :: Doctrine
  , beDiagram :: Diagram
  }
  deriving (Eq, Show)


newtype BundleArtifact = BundleArtifact
  { baEntries :: M.Map Text BundleEntry
  }
  deriving (Eq, Show)


data BuildProduct
  = BPModule ModuleArtifact
  | BPBundle BundleArtifact
  | BPDiagram Doctrine Diagram
  | BPHost HostArtifact
  deriving (Eq, Show)


data BuildResult = BuildResult
  { brArtifact :: BuildProduct
  , brOutput :: Text
  }
  deriving (Eq, Show)


buildFile :: FilePath -> Maybe Text -> IO (Either Text BuildResult)
buildFile path mBuildName =
  case standardBackendRegistry of
    Left err -> pure (Left err)
    Right backendRegistry -> buildFileWithBackendRegistry backendRegistry path mBuildName


buildFileWithBackendRegistry :: BackendRegistry -> FilePath -> Maybe Text -> IO (Either Text BuildResult)
buildFileWithBackendRegistry backendRegistry path mBuildName = do
  envResult <- loadModule path
  case envResult of
    Left err -> pure (Left err)
    Right env ->
      case selectBuild env mBuildName of
        Left err -> pure (Left err)
        Right spec -> pure (buildWithEnvAndBackendRegistry backendRegistry env spec)


selectBuild :: ModuleEnv -> Maybe Text -> Either Text BuildDef
selectBuild env mName =
  case mName of
    Just name ->
      case M.lookup name (meBuilds env) of
        Nothing -> Left ("Unknown build: " <> name <> available)
        Just spec -> Right spec
    Nothing ->
      case M.lookup "main" (meBuilds env) of
        Just spec -> Right spec
        Nothing ->
          case M.toList (meBuilds env) of
            [] -> Left "No builds found"
            [(_, spec)] -> Right spec
            _ -> Left ("Multiple builds found; specify --build. Available: " <> T.intercalate ", " (M.keys (meBuilds env)))
  where
    available =
      if M.null (meBuilds env)
        then ""
        else " (available: " <> T.intercalate ", " (M.keys (meBuilds env)) <> ")"


buildWithEnv :: ModuleEnv -> BuildDef -> Either Text BuildResult
buildWithEnv env buildDef = do
  backendRegistry <- standardBackendRegistry
  buildWithEnvAndBackendRegistry backendRegistry env buildDef


buildWithEnvAndBackendRegistry :: BackendRegistry -> ModuleEnv -> BuildDef -> Either Text BuildResult
buildWithEnvAndBackendRegistry backendRegistry env buildDef = do
  pipeline <- lookupPipeline env (bdPipeline buildDef)
  artifact0 <- buildModuleArtifact env (bdModule buildDef)
  final <- foldM (runPhase backendRegistry env) (BPModule artifact0) (plPhases pipeline)
  out <- renderBuildResult final
  pure BuildResult { brArtifact = final, brOutput = out }


renderBuildResult :: BuildProduct -> Either Text Text
renderBuildResult art =
  case art of
    BPDiagram _ diag -> renderDiagram diag
    BPBundle bundle ->
      let names = M.keys (baEntries bundle)
       in Right ("bundle exports: " <> T.intercalate ", " names)
    BPHost host -> Right (renderHostArtifact host)
    BPModule modArt ->
      let valueNames = M.keys (maExports modArt)
          typeNames = M.keys (maExportTypes modArt)
          rendered =
            filter (not . T.null)
              [ if null valueNames then "" else "values: " <> T.intercalate ", " valueNames
              , if null typeNames then "" else "types: " <> T.intercalate ", " typeNames
              ]
       in Right ("module " <> maName modArt <> " exports: " <> T.intercalate "; " rendered)


buildModuleArtifact :: ModuleEnv -> Text -> Either Text ModuleArtifact
buildModuleArtifact env name =
  case M.lookup name (meModules env) of
    Nothing -> Left ("Unknown module: " <> name)
    Just modDef -> do
      doc <- lookupDoctrine env (mdDoctrine modDef)
      components0 <- collectArtifactComponents env S.empty name
      assembleModuleArtifact env (mdName modDef) (mdLanguage modDef) doc [name] components0


buildLinkedModuleArtifact :: ModuleEnv -> Text -> Either Text ModuleArtifact
buildLinkedModuleArtifact env name =
  case M.lookup name (meModules env) of
    Nothing -> Left ("Unknown module: " <> name)
    Just modDef -> do
      doc <- lookupDoctrine env (mdDoctrine modDef)
      assembleModuleArtifact env (mdName modDef) (mdLanguage modDef) doc [name] [moduleComponentFromDef modDef]


runPhase :: BackendRegistry -> ModuleEnv -> BuildProduct -> Phase -> Either Text BuildProduct
runPhase backendRegistry env art phase =
  case phase of
    ApplyMorph name ->
      case art of
        BPDiagram doc diag -> do
          mor <- lookupMorphism env name
          if dName (Morph.morSrc mor) /= dName doc
            then Left ("pipeline: morphism source mismatch for " <> name)
            else do
              diag' <- Morph.applyMorphismDiagram mor diag
              let doc' = Morph.morTgt mor
              ensureAcyclicIfRequired doc' diag'
              pure (BPDiagram doc' diag')
        BPModule modArt -> do
          mor <- lookupMorphism env name
          if dName (Morph.morSrc mor) /= dName (maDoctrine modArt)
            then Left ("pipeline: morphism source mismatch for " <> name)
            else do
              modArt' <- translateModuleArtifact env mor modArt
              pure (BPModule modArt')
        BPBundle bundle -> do
          bundle' <- mapBundleEntries bundle applyOne
          pure (BPBundle bundle')
          where
            applyOne entry = do
              mor <- lookupMorphism env name
              if dName (Morph.morSrc mor) /= dName (beDoctrine entry)
                then Left ("pipeline: morphism source mismatch for " <> name)
                else do
                  diag' <- Morph.applyMorphismDiagram mor (beDiagram entry)
                  let doc' = Morph.morTgt mor
                  ensureAcyclicIfRequired doc' diag'
                  pure entry { beDoctrine = doc', beDiagram = diag' }
        BPHost{} ->
          Left "pipeline: cannot apply morphism after host emission"
    Normalize policy fuel ->
      case art of
        BPDiagram doc diag -> do
          diag' <- normalizeDiagram doc policy fuel diag
          ensureAcyclicIfRequired doc diag'
          pure (BPDiagram doc diag')
        BPModule modArt -> BPModule <$> mapModuleValues modArt normalizeOne
          where
            normalizeOne mv = do
              doc <- lookupDoctrine env (mvdDoctrine mv)
              diag' <- normalizeDiagram doc policy fuel (mvdDiagram mv)
              ensureAcyclicIfRequired doc diag'
              pure mv { mvdMode = dMode diag', mvdDiagram = diag' }
        BPBundle bundle -> BPBundle <$> mapBundleEntries bundle normalizeOne
          where
            normalizeOne entry = do
              diag' <- normalizeDiagram (beDoctrine entry) policy fuel (beDiagram entry)
              ensureAcyclicIfRequired (beDoctrine entry) diag'
              pure entry { beDiagram = diag' }
        BPHost{} -> Left "pipeline: cannot normalize emitted host artifact"
    QuoteInto fragmentName targetName ->
      case art of
        BPDiagram doc diag -> do
          quoted <- quoteOne env doc diag fragmentName targetName
          derivedDoc <- lookupDoctrine env targetName
          pure (BPDiagram derivedDoc quoted)
        BPModule modArt -> do
          derivedDoc <- lookupDoctrine env targetName
          closed <- closeModuleArtifact env modArt
          quoted <- quoteClosedModuleArtifact env closed fragmentName targetName derivedDoc
          pure (BPModule quoted)
        BPBundle bundle -> do
          quoted <- mapBundleEntries bundle quoteEntry
          pure (BPBundle quoted)
          where
            quoteEntry entry = do
              diag' <- quoteOne env (beDoctrine entry) (beDiagram entry) fragmentName targetName
              derivedDoc <- lookupDoctrine env targetName
              pure entry { beDoctrine = derivedDoc, beDiagram = diag' }
        BPHost{} -> Left "pipeline: cannot quote emitted host artifact"
    LinkModule name ->
      case art of
        BPModule modArt -> do
          other <- buildLinkedModuleArtifact env name
          linked <- linkModuleArtifacts env modArt other
          pure (BPModule linked)
        BPDiagram{} -> Left "pipeline: link expects a module"
        BPBundle{} -> Left "pipeline: link expects a module"
        BPHost{} -> Left "pipeline: link expects a module"
    BundleAll ->
      case art of
        BPModule modArt -> do
          closed <- closeModuleArtifact env modArt
          BPBundle <$> bundleAllExports env closed
        BPDiagram{} -> Left "pipeline: bundle expects a module"
        BPBundle{} -> Left "pipeline: value already bundled"
        BPHost{} -> Left "pipeline: cannot bundle emitted host artifact"
    BundleExports items ->
      case art of
        BPModule modArt -> do
          closed <- closeModuleArtifact env modArt
          BPBundle <$> bundleSelectedExports env closed items
        BPDiagram{} -> Left "pipeline: bundle expects a module"
        BPBundle{} -> Left "pipeline: value already bundled"
        BPHost{} -> Left "pipeline: cannot bundle emitted host artifact"
    ProjectExport name ->
      case art of
        BPModule modArt -> do
          closed <- closeModuleArtifact env modArt
          case M.lookup name (maExports closed) of
            Nothing -> Left ("pipeline: unknown module export " <> name)
            Just mv -> do
              doc <- lookupDoctrine env (mvdDoctrine mv)
              pure (BPDiagram doc (mvdDiagram mv))
        BPBundle bundle ->
          case M.lookup name (baEntries bundle) of
            Nothing -> Left ("pipeline: unknown bundle export " <> name)
            Just entry -> pure (BPDiagram (beDoctrine entry) (beDiagram entry))
        BPDiagram{} -> Left "pipeline: project export expects a module or bundle"
        BPHost{} -> Left "pipeline: project export expects a module"
    EmitVia backend ->
      case art of
        BPDiagram doc diag -> BPHost <$> emitViaBackendWithRegistry backendRegistry backend doc diag
        BPBundle bundle ->
          BPHost <$> emitBundleViaBackendWithRegistry backendRegistry backend (bundleEntries bundle)
        BPModule modArt -> do
          closed <- closeModuleArtifact env modArt
          bundle <- bundleAllExports env closed
          BPHost <$> emitBundleViaBackendWithRegistry backendRegistry backend (bundleEntries bundle)
        BPHost{} -> Left "pipeline: value already emitted"


mapModuleValues :: ModuleArtifact -> (ModuleValueDef -> Either Text ModuleValueDef) -> Either Text ModuleArtifact
mapModuleValues modArt f = do
  components' <- traverse (`mapModuleComponentValues` f) (maComponents modArt)
  pure (moduleArtifactFromComponents (maName modArt) (maLanguage modArt) (maDoctrine modArt) (maPublicComponents modArt) components')


translateModuleArtifact :: ModuleEnv -> Morph.Morphism -> ModuleArtifact -> Either Text ModuleArtifact
translateModuleArtifact env mor modArt = do
  let internalComponents = S.fromList (map mcName (maComponents modArt))
  components' <- traverse (translateModuleComponent env internalComponents mor) (maComponents modArt)
  pure (moduleArtifactFromComponents (maName modArt) (maLanguage modArt) (Morph.morTgt mor) (maPublicComponents modArt) components')


translateModuleTypeDef :: Morph.Morphism -> ModuleTypeDef -> Either Text ModuleTypeDef
translateModuleTypeDef mor mtd = do
  body' <- Morph.applyMorphismTy mor (mtdBody mtd)
  pure
    mtd
      { mtdDoctrine = dName (Morph.morTgt mor)
      , mtdMode = objOwnerMode body'
      , mtdBody = body'
      }


translateModuleDataDef :: S.Set Text -> Morph.Morphism -> ModuleDataDef -> Either Text ModuleDataDef
translateModuleDataDef internalComponents mor mdd = do
  typeDef' <- translateModuleTypeDef mor (mddTypeDef mdd)
  ctorDefs' <- traverse translateCtor (mddCtorDefs mdd)
  pure
    mdd
      { mddDoctrine = dName (Morph.morTgt mor)
      , mddMode = mtdMode typeDef'
      , mddTypeDef = typeDef'
      , mddCtorDefs = ctorDefs'
      }
  where
    translateCtor mv = do
      diag' <- Morph.applyMorphismDiagram mor (mvdDiagram mv)
      let diag'' = retargetTranslatedDiagram internalComponents (morNameText mor) diag'
      pure
        mv
          { mvdDoctrine = dName (Morph.morTgt mor)
          , mvdMode = dMode diag''
          , mvdDiagram = diag''
          }

adaptProviderRef :: Text -> ProviderRef -> ProviderRef
adaptProviderRef morphName ref =
  ref { prProvider = appendProviderAdapter (Just morphName) (prProvider ref) }


adaptModuleValueRef :: Text -> ModuleValueRef -> ModuleValueRef
adaptModuleValueRef morphName =
  appendModuleValueRefAdapter (Just morphName)


morNameText :: Morph.Morphism -> Text
morNameText = Morph.morName


moduleComponentFromDef :: ModuleDef -> ModuleComponent
moduleComponentFromDef modDef =
  ModuleComponent
    { mcName = mdName modDef
    , mcImports = mdImports modDef
    , mcItems = mdItems modDef
    , mcProviders = mdProviders modDef
    , mcDataPackages = mdDataPackages modDef
    , mcTypes = mdTypes modDef
    , mcValues = mdValues modDef
    , mcExportTypes = mdExportTypes modDef
    , mcExports = mdExports modDef
    , mcExportInterfaces = mdExportInterfaces modDef
    }


moduleArtifactFromComponents :: Text -> Text -> Doctrine -> [Text] -> [ModuleComponent] -> ModuleArtifact
moduleArtifactFromComponents name lang doctrine publicComponents components =
  let multiComponent = length components > 1
      publicNames = S.fromList publicComponents
      publicOnly = filter (\comp -> mcName comp `S.member` publicNames) components
   in ModuleArtifact
        { maName = name
        , maLanguage = lang
        , maDoctrine = doctrine
        , maPublicComponents = publicComponents
        , maComponents = components
        , maImports = dedupe (concatMap mcImports components)
        , maItems = concatMap mcItems components
        , maProviders = dedupe (concatMap mcProviders components)
        , maDataPackages = flattenComponentDataPackages multiComponent components
        , maTypes = flattenComponentTypes multiComponent components
        , maValues = flattenComponentValues multiComponent components
        , maExportTypes = M.unions (map mcExportTypes publicOnly)
        , maExports = M.unions (map mcExports publicOnly)
        , maExportInterfaces = dedupe (concatMap mcExportInterfaces publicOnly)
        }


flattenComponentTypes :: Bool -> [ModuleComponent] -> M.Map Text ModuleTypeDef
flattenComponentTypes multiComponent =
  flattenComponentMap multiComponent mcName mcTypes renameType
  where
    renameType flatName mtd = mtd { mtdName = flatName }


flattenComponentValues :: Bool -> [ModuleComponent] -> M.Map Text ModuleValueDef
flattenComponentValues multiComponent =
  flattenComponentMap multiComponent mcName mcValues renameValue
  where
    renameValue flatName mvd = mvd { mvdName = flatName }


flattenComponentDataPackages :: Bool -> [ModuleComponent] -> M.Map Text ModuleDataDef
flattenComponentDataPackages multiComponent comps =
  M.unions (map flattenOne comps)
  where
    flattenOne comp =
      M.fromList
        [ let qualify itemName =
                if multiComponent
                  then qualifyComponentName (mcName comp) itemName
                  else itemName
              flatName = qualify localName
              ctorNames' = map qualify (mddCtorNames pkg)
              ctorDefs' =
                M.fromList
                  [ (qualify ctorName, mvd { mvdName = qualify ctorName })
                  | (ctorName, mvd) <- M.toList (mddCtorDefs pkg)
                  ]
              pkg' =
                pkg
                  { mddName = flatName
                  , mddTypeDef = (mddTypeDef pkg) { mtdName = flatName }
                  , mddCtorNames = ctorNames'
                  , mddCtorDefs = ctorDefs'
                  }
           in (flatName, pkg')
        | (localName, pkg) <- M.toList (mcDataPackages comp)
        ]


flattenComponentMap
  :: Bool
  -> (comp -> Text)
  -> (comp -> M.Map Text a)
  -> (Text -> a -> a)
  -> [comp]
  -> M.Map Text a
flattenComponentMap multiComponent getCompName getMap renameOne comps =
  M.unions (map flattenOne comps)
  where
    flattenOne comp =
      M.fromList
        [ let flatName =
                if multiComponent
                  then qualifyComponentName (getCompName comp) localName
                  else localName
           in (flatName, renameOne flatName val)
        | (localName, val) <- M.toList (getMap comp)
        ]


qualifyComponentName :: Text -> Text -> Text
qualifyComponentName compName localName =
  compName <> "::" <> localName


mapModuleComponentValues :: ModuleComponent -> (ModuleValueDef -> Either Text ModuleValueDef) -> Either Text ModuleComponent
mapModuleComponentValues comp f = do
  values' <- traverse f (mcValues comp)
  exports' <-
    traverse
      (\old ->
        case M.lookup (mvdName old) values' of
          Just new -> Right new
          Nothing -> f old
      )
      (mcExports comp)
  pure
    comp
      { mcDataPackages = rebuildComponentDataPackages (mcDataPackages comp) values'
      , mcValues = values'
      , mcExports = exports'
      }


rebuildComponentDataPackages :: M.Map Text ModuleDataDef -> M.Map Text ModuleValueDef -> M.Map Text ModuleDataDef
rebuildComponentDataPackages dataPkgs values =
  M.map rebuildOne dataPkgs
  where
    rebuildOne pkg =
      pkg
        { mddCtorDefs =
            M.fromList
              [ (ctorName, quoted)
              | ctorName <- mddCtorNames pkg
              , Just quoted <- [M.lookup ctorName values]
              ]
        }


translateModuleComponent :: ModuleEnv -> S.Set Text -> Morph.Morphism -> ModuleComponent -> Either Text ModuleComponent
translateModuleComponent env internalComponents mor comp = do
  types' <- traverse (translateModuleTypeDef mor) (mcTypes comp)
  exportTypes' <- traverse (translateModuleTypeDef mor) (mcExportTypes comp)
  values' <- traverse translateValue (mcValues comp)
  exports' <- traverse translateValue (mcExports comp)
  let imports' = map (translateModuleImport internalComponents (morNameText mor)) (mcImports comp)
  let providers' = map (appendProviderAdapter (Just (morNameText mor))) (mcProviders comp)
  dataPackages' <- traverse (translateModuleDataDef internalComponents mor) (mcDataPackages comp)
  let exportInterfaces' =
        retainExportInterfaces
          env
          (dName (Morph.morTgt mor))
          exportTypes'
          exports'
          (mcExportInterfaces comp)
  pure
    comp
      { mcImports = imports'
      , mcItems = translatedModuleItems imports' exportInterfaces' (mcItems comp)
      , mcProviders = providers'
      , mcDataPackages = dataPackages'
      , mcTypes = types'
      , mcValues = values'
      , mcExportTypes = exportTypes'
      , mcExports = exports'
      , mcExportInterfaces = exportInterfaces'
      }
  where
    translateValue mv = do
      diag' <- Morph.applyMorphismDiagram mor (mvdDiagram mv)
      let diag'' = retargetTranslatedDiagram internalComponents (morNameText mor) diag'
      let doc' = Morph.morTgt mor
      ensureAcyclicIfRequired doc' diag''
      pure
        mv
          { mvdDoctrine = dName doc'
          , mvdMode = dMode diag''
          , mvdDiagram = diag''
          }

translateModuleImport :: S.Set Text -> Text -> ModuleImport -> ModuleImport
translateModuleImport internalComponents morphName modImport =
  case modImport of
    ModuleImport {} ->
      if miModule modImport `S.member` internalComponents
        then modImport
        else modImport { miAdapters = miAdapters modImport <> [morphName] }
    ModuleForeignImport {} ->
      modImport { miForeignAdapters = miForeignAdapters modImport <> [morphName] }


retargetTranslatedDiagram :: S.Set Text -> Text -> Diagram -> Diagram
retargetTranslatedDiagram internalComponents morphName =
  mapModuleValueRefsDiagram adaptModuleRef
    . mapProviderRefsDiagram (adaptProviderRef morphName)
  where
    adaptModuleRef ref
      | mvrModule ref `S.member` internalComponents = ref
      | otherwise = adaptModuleValueRef morphName ref


translatedModuleItems :: [ModuleImport] -> [Text] -> [ModuleItemDef] -> [ModuleItemDef]
translatedModuleItems imports exportInterfaces =
  filter keep
  where
    importSet = S.fromList imports
    exportInterfaceSet = S.fromList exportInterfaces
    keep item =
      case item of
        MIDImport modImport -> modImport `S.member` importSet
        MIDExportInterface ifaceName -> ifaceName `S.member` exportInterfaceSet
        _ -> True


quotedModuleItems
  :: [ModuleItemDef]
  -> M.Map Text ModuleValueDef
  -> M.Map Text ModuleValueDef
  -> [ModuleItemDef]
quotedModuleItems items values exports =
  concatMap keepItem items
  where
    keepItem item =
      case item of
        MIDImport _ -> []
        MIDData _ _ -> []
        MIDType _ -> []
        MIDValue name
          | M.member name values -> [MIDValue name]
          | otherwise -> []
        MIDExportType _ _ -> []
        MIDExport local public
          | M.member public exports -> [MIDExport local public]
          | otherwise -> []
        MIDExportInterface _ -> []

quoteClosedModuleArtifact
  :: ModuleEnv
  -> ModuleArtifact
  -> Text
  -> Text
  -> Doctrine
  -> Either Text ModuleArtifact
quoteClosedModuleArtifact env modArt fragmentName targetName derivedDoc = do
  components' <- traverse quoteComponent (maComponents modArt)
  pure
    (moduleArtifactFromComponents (maName modArt) (maLanguage modArt) derivedDoc (maPublicComponents modArt) components')
  where
    quoteValue mv = do
      doc <- lookupDoctrine env (mvdDoctrine mv)
      diag' <- quoteOne env doc (mvdDiagram mv) fragmentName targetName
      pure mv { mvdDoctrine = targetName, mvdMode = dMode diag', mvdDiagram = diag' }

    quoteComponent comp = do
      quotedComp <- mapModuleComponentValues comp quoteValue
      pure
        quotedComp
          { mcItems = quotedModuleItems (mcItems comp) (mcValues quotedComp) (mcExports quotedComp)
          , mcImports = []
          , mcProviders = []
          , mcDataPackages = M.empty
          , mcTypes = M.empty
          , mcExportTypes = M.empty
          , mcExportInterfaces = []
          }


retainExportInterfaces
  :: ModuleEnv
  -> Text
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> [Text]
  -> [Text]
retainExportInterfaces env doctrineName exportTypes exports =
  dedupe . foldr keep []
  where
    keep ifaceName acc =
      case M.lookup ifaceName (meInterfaces env) of
        Just iface
          | idefDoctrine iface == doctrineName ->
              case ensureModuleMatchesInterface env doctrineName exportTypes exports ifaceName of
                Right () -> ifaceName : acc
                Left _ -> acc
        _ -> acc


mapBundleEntries :: BundleArtifact -> (BundleEntry -> Either Text BundleEntry) -> Either Text BundleArtifact
mapBundleEntries bundle f =
  BundleArtifact <$> traverse f (baEntries bundle)


bundleEntries :: BundleArtifact -> [(Text, Doctrine, Diagram)]
bundleEntries bundle =
  [ (name, beDoctrine entry, beDiagram entry)
  | (name, entry) <- M.toList (baEntries bundle)
  ]


bundleAllExports :: ModuleEnv -> ModuleArtifact -> Either Text BundleArtifact
bundleAllExports env modArt =
  BundleArtifact <$> traverse (mkBundleEntry env) (maExports modArt)


bundleSelectedExports :: ModuleEnv -> ModuleArtifact -> [BundleItem] -> Either Text BundleArtifact
bundleSelectedExports env modArt =
  foldM step (BundleArtifact M.empty)
  where
    step bundle item =
      case M.lookup (biSource item) (maExports modArt) of
        Nothing -> Left ("pipeline: unknown module export " <> biSource item)
        Just mv ->
          if M.member (biTarget item) (baEntries bundle)
            then Left ("pipeline: duplicate bundle name " <> biTarget item)
            else do
              entry <- mkBundleEntry env mv
              let named = entry { beName = biTarget item }
              pure bundle { baEntries = M.insert (biTarget item) named (baEntries bundle) }


mkBundleEntry :: ModuleEnv -> ModuleValueDef -> Either Text BundleEntry
mkBundleEntry env mv = do
  doc <- lookupDoctrine env (mvdDoctrine mv)
  pure
    BundleEntry
      { beName = mvdName mv
      , beDoctrine = doc
      , beDiagram = mvdDiagram mv
      }


linkModuleArtifacts :: ModuleEnv -> ModuleArtifact -> ModuleArtifact -> Either Text ModuleArtifact
linkModuleArtifacts env left right = do
  if maLanguage left /= maLanguage right
    then Left "pipeline: linked modules must share a language"
    else Right ()
  if dName (maDoctrine left) /= dName (maDoctrine right)
    then Left "pipeline: linked modules must share a doctrine"
    else Right ()
  components0 <- mergeEqualComponents (maComponents left) (maComponents right)
  assembleModuleArtifact
    env
    (maName left <> "+" <> maName right)
    (maLanguage left)
    (maDoctrine left)
    (dedupe (maPublicComponents left <> maPublicComponents right))
    components0


collectArtifactComponents :: ModuleEnv -> S.Set Text -> Text -> Either Text [ModuleComponent]
collectArtifactComponents env visiting rootName = do
  compMap <- collectComponentMap env visiting rootName
  pure (M.elems compMap)


collectComponentMap :: ModuleEnv -> S.Set Text -> Text -> Either Text (M.Map Text ModuleComponent)
collectComponentMap env visiting name
  | name `S.member` visiting =
      Left ("module: import cycle detected involving " <> name)
  | otherwise =
      case M.lookup name (meModules env) of
        Nothing -> Left ("Unknown module import: " <> name)
        Just modDef -> do
          deps <- foldM step M.empty (mdImports modDef)
          pure (M.insert name (moduleComponentFromDef modDef) deps)
  where
    step acc modImport =
      case modImport of
        ModuleImport { miModule = depName } ->
          case M.lookup depName acc of
            Just _ -> Right acc
            Nothing -> do
              depMap <- collectComponentMap env (S.insert name visiting) depName
              pure (M.union depMap acc)
        ModuleForeignImport {} ->
          Right acc


assembleModuleArtifact
  :: ModuleEnv
  -> Text
  -> Text
  -> Doctrine
  -> [Text]
  -> [ModuleComponent]
  -> Either Text ModuleArtifact
assembleModuleArtifact env artName lang doctrine publicComponents components0 = do
  depGraph <- componentDependencyGraph env (dName doctrine) components0
  orderedNames <- topologicalComponentOrder depGraph (map mcName components0)
  let compMap = M.fromList [(mcName comp, comp) | comp <- components0]
  components' <-
    traverse
      (\compName ->
        case M.lookup compName compMap of
          Nothing -> Left ("pipeline: internal link error; missing component " <> compName)
          Just comp -> Right comp)
      orderedNames
  _ <- collectPublicTypeExports publicComponents components'
  _ <- collectPublicValueExports publicComponents components'
  pure (moduleArtifactFromComponents artName lang doctrine publicComponents components')


componentDependencyGraph
  :: ModuleEnv
  -> Text
  -> [ModuleComponent]
  -> Either Text (M.Map Text [Text])
componentDependencyGraph env doctrineName components = do
  providerMap <- componentProviderMap components
  M.fromList <$> traverse (componentDeps providerMap) components
  where
    componentDeps providerMap comp = do
      deps <- foldM (step providerMap comp) [] (mcImports comp)
      pure (mcName comp, reverse deps)

    step providerMap _comp deps modImport =
      case modImport of
        ModuleImport {} ->
          case M.lookup (miModule modImport) providerMap of
            Nothing ->
              pure deps
            Just provider -> do
              validateInternalImport provider modImport
              pure (miModule modImport : deps)
        ModuleForeignImport {} ->
          pure deps

    validateInternalImport provider modImport =
      case miInterface modImport of
        Nothing -> Right ()
        Just ifaceName ->
          case M.lookup ifaceName (meInterfaces env) of
            Just iface
              | idefDoctrine iface == doctrineName ->
                  ensureModuleMatchesInterface
                    env
                    doctrineName
                    (mcExportTypes provider)
                    (mcExports provider)
                    ifaceName
            _ -> Right ()


collectPublicTypeExports :: [Text] -> [ModuleComponent] -> Either Text (M.Map Text ModuleTypeDef)
collectPublicTypeExports publicComponents components = do
  publicOnly <- resolvePublicComponents publicComponents components
  foldM step M.empty publicOnly
  where
    step acc comp =
      mergeEqualMap
        "pipeline: duplicate public type export "
        acc
        (mcExportTypes comp)


collectPublicValueExports :: [Text] -> [ModuleComponent] -> Either Text (M.Map Text ModuleValueDef)
collectPublicValueExports publicComponents components = do
  publicOnly <- resolvePublicComponents publicComponents components
  foldM step M.empty publicOnly
  where
    step acc comp =
      mergeEqualMap
        "pipeline: duplicate public export "
        acc
        (mcExports comp)


resolvePublicComponents :: [Text] -> [ModuleComponent] -> Either Text [ModuleComponent]
resolvePublicComponents publicComponents components =
  traverse resolveOne publicComponents
  where
    compMap = M.fromList [(mcName comp, comp) | comp <- components]
    resolveOne compName =
      case M.lookup compName compMap of
        Nothing -> Left ("pipeline: missing public component " <> compName)
        Just comp -> Right comp


closeModuleArtifact :: ModuleEnv -> ModuleArtifact -> Either Text ModuleArtifact
closeModuleArtifact env modArt = do
  providerMap <- componentProviderMap (maComponents modArt)
  components' <- traverse (resolveClosedComponent env providerMap) (maComponents modArt)
  assembleModuleArtifact
    env
    (maName modArt)
    (maLanguage modArt)
    (maDoctrine modArt)
    (maPublicComponents modArt)
    components'


resolveClosedComponent :: ModuleEnv -> M.Map Text ModuleComponent -> ModuleComponent -> Either Text ModuleComponent
resolveClosedComponent env providers comp = do
  internalImports <- internalLocalImports providers comp
  values' <- traverse (closeModuleValueDef env providers) (mcValues comp)
  exports' <- traverse (closeModuleValueDef env providers) (mcExports comp)
  let dataPackages' = rebuildComponentDataPackages (mcDataPackages comp) values'
      comp1 =
        clearSatisfiedComponentImports internalImports
          comp
            { mcDataPackages = dataPackages'
            , mcValues = values'
            , mcExports = exports'
            }
      providers' = collectComponentProviders values' exports'
      exportInterfaces' =
        retainExportInterfaces
          env
          (mvdDoctrineOfComponent values' exports' comp1)
          (mcExportTypes comp1)
          exports'
          (mcExportInterfaces comp1)
  pure
    comp1
      { mcProviders = dedupe (mcProviders comp1 <> providers')
      , mcExportInterfaces = exportInterfaces'
      , mcItems = filterClosedComponentItems exportInterfaces' (mcItems comp1)
      }


internalLocalImports :: M.Map Text ModuleComponent -> ModuleComponent -> Either Text [ModuleImport]
internalLocalImports providers comp =
  traverse requireProvider locals
  where
    locals = filter isLocalImport (mcImports comp)
    requireProvider modImport =
      case M.lookup (miModule modImport) providers of
        Nothing ->
          Left ("module: unresolved local import " <> miModule modImport <> " in component " <> mcName comp)
        Just _ -> Right modImport


closeModuleValueDef :: ModuleEnv -> M.Map Text ModuleComponent -> ModuleValueDef -> Either Text ModuleValueDef
closeModuleValueDef env providers mv = do
  diag' <- resolveModuleRefsInDiagram env providers (mvdDoctrine mv) (mvdDiagram mv)
  doc <- lookupDoctrine env (mvdDoctrine mv)
  diag'' <- normalizeDiagram doc (mvdPolicy mv) (mvdFuel mv) diag'
  ensureAcyclicIfRequired doc diag''
  pure mv { mvdMode = dMode diag'', mvdDiagram = diag'' }


resolveModuleRefsInDiagram :: ModuleEnv -> M.Map Text ModuleComponent -> Text -> Diagram -> Either Text Diagram
resolveModuleRefsInDiagram env providers targetDoctrine diag0 = do
  diag1 <- recurseDiagram diag0
  expandRefsLoop diag1
  where
    recurseDiagram diag = do
      edges' <- traverse recurseEdge (dEdges diag)
      pure diag { dEdges = edges' }

    recurseEdge edge =
      case ePayload edge of
        PBox name inner -> do
          inner' <- resolveModuleRefsInDiagram env providers targetDoctrine inner
          pure edge { ePayload = PBox name inner' }
        PFeedback inner -> do
          inner' <- resolveModuleRefsInDiagram env providers targetDoctrine inner
          pure edge { ePayload = PFeedback inner' }
        _ ->
          pure edge

    expandRefsLoop diag =
      case firstModuleRefEdge diag of
        Nothing -> Right diag
        Just (edgeKey, ref) -> do
          image <- resolveModuleValueRef env providers targetDoctrine ref
          diag' <- spliceEdge diag edgeKey image
          expandRefsLoop diag'


firstModuleRefEdge :: Diagram -> Maybe (Int, ModuleValueRef)
firstModuleRefEdge diag =
  firstMatch (IM.toAscList (dEdges diag))
  where
    firstMatch [] = Nothing
    firstMatch ((edgeKey, edge):rest) =
      case ePayload edge of
        PModuleRef ref -> Just (edgeKey, ref)
        _ -> firstMatch rest


resolveModuleValueRef :: ModuleEnv -> M.Map Text ModuleComponent -> Text -> ModuleValueRef -> Either Text Diagram
resolveModuleValueRef env providers targetDoctrine ref = do
  provider <-
    case M.lookup (mvrModule ref) providers of
      Nothing -> Left ("module: unresolved import " <> mvrModule ref <> "::" <> mvrValueName ref)
      Just comp -> Right comp
  exportValue <-
    case M.lookup (mvrValueName ref) (mcExports provider) of
      Nothing -> Left ("module: imported module " <> mvrModule ref <> " does not export " <> mvrValueName ref)
      Just mv -> Right mv
  doc0 <- lookupDoctrine env (mvdDoctrine exportValue)
  (docFinal, diagFinal) <- applyMorphismNames env doc0 (mvdDiagram exportValue) (mvrAdapters ref)
  if dName docFinal == targetDoctrine
    then Right diagFinal
    else Left ("module: import " <> mvrModule ref <> "::" <> mvrValueName ref <> " resolved to doctrine " <> dName docFinal <> ", expected " <> targetDoctrine)


applyMorphismNames :: ModuleEnv -> Doctrine -> Diagram -> [Text] -> Either Text (Doctrine, Diagram)
applyMorphismNames env doc0 diag0 =
  foldM step (doc0, diag0)
  where
    step (doc, diag) morphName = do
      mor <- lookupMorphism env morphName
      if dName (Morph.morSrc mor) /= dName doc
        then Left ("module: morphism source mismatch for " <> morphName)
        else do
          diag' <- Morph.applyMorphismDiagram mor diag
          let diag'' =
                mapModuleValueRefsDiagram (adaptModuleValueRef (morNameText mor))
                  (mapProviderRefsDiagram (adaptProviderRef (morNameText mor)) diag')
          pure (Morph.morTgt mor, diag'')


collectComponentProviders :: M.Map Text ModuleValueDef -> M.Map Text ModuleValueDef -> [ModuleProvider]
collectComponentProviders values exports =
  S.toList . S.fromList $
    [ prProvider ref
    | mv <- M.elems (M.union exports values)
    , ref <- S.toList (providerRefsDiagram (mvdDiagram mv))
    ]


mvdDoctrineOfComponent :: M.Map Text ModuleValueDef -> M.Map Text ModuleValueDef -> ModuleComponent -> Text
mvdDoctrineOfComponent values exports comp =
  case M.elems (M.union exports values) of
    (mv:_) -> mvdDoctrine mv
    [] ->
      case M.elems (mcExportTypes comp) of
        (mt:_) -> mtdDoctrine mt
        [] ->
          case M.elems (mcTypes comp) of
            (mt:_) -> mtdDoctrine mt
            [] -> ""


filterClosedComponentItems :: [Text] -> [ModuleItemDef] -> [ModuleItemDef]
filterClosedComponentItems exportInterfaces =
  filter keep
  where
    exportInterfaceSet = S.fromList exportInterfaces
    keep item =
      case item of
        MIDImport ModuleImport {} -> False
        MIDExportInterface ifaceName -> ifaceName `S.member` exportInterfaceSet
        _ -> True


isLocalImport :: ModuleImport -> Bool
isLocalImport ModuleImport {} = True
isLocalImport ModuleForeignImport {} = False


mergeEqualMap :: (Ord k, Show k, Eq v) => Text -> M.Map k v -> M.Map k v -> Either Text (M.Map k v)
mergeEqualMap label left right =
  case conflicts of
    [] -> Right (M.union left right)
    bad:_ -> Left (label <> T.pack (show bad))
  where
    conflicts =
      [ key
      | key <- M.keys (M.intersection left right)
      , M.lookup key left /= M.lookup key right
      ]


mergeEqualComponents :: [ModuleComponent] -> [ModuleComponent] -> Either Text [ModuleComponent]
mergeEqualComponents left right =
  fmap reverse (foldM step left right)
  where
    step acc comp =
      case filter (\existing -> mcName existing == mcName comp) acc of
        [] -> Right (comp : acc)
        [existing]
          | existing == comp -> Right acc
          | otherwise -> Left ("pipeline: linked modules collide on component " <> mcName comp)
        _ -> Left ("pipeline: internal link error; duplicate component " <> mcName comp)


componentProviderMap :: [ModuleComponent] -> Either Text (M.Map Text ModuleComponent)
componentProviderMap =
  foldM step M.empty
  where
    step acc comp =
      if M.member (mcName comp) acc
        then Left ("pipeline: linked modules collide on component " <> mcName comp)
        else Right (M.insert (mcName comp) comp acc)

topologicalComponentOrder :: M.Map Text [Text] -> [Text] -> Either Text [Text]
topologicalComponentOrder deps startOrder =
  reverse . tsOrder <$> foldM visit emptyState startOrder
  where
    emptyState =
      TopoState
        { tsTemp = S.empty
        , tsDone = S.empty
        , tsOrder = []
        }

    visit st name
      | name `S.member` tsDone st = Right st
      | name `S.member` tsTemp st = Left "pipeline: link would create a circular module dependency"
      | otherwise = do
          depNames <-
            case M.lookup name deps of
              Nothing -> Left ("pipeline: internal link error; missing dependency node " <> name)
              Just ds -> Right ds
          st' <- foldM visit (st { tsTemp = S.insert name (tsTemp st) }) depNames
          Right
            st'
              { tsTemp = S.delete name (tsTemp st')
              , tsDone = S.insert name (tsDone st')
              , tsOrder = name : tsOrder st'
              }


data TopoState = TopoState
  { tsTemp :: S.Set Text
  , tsDone :: S.Set Text
  , tsOrder :: [Text]
  }


filterModuleImportItems :: S.Set ModuleImport -> [ModuleItemDef] -> [ModuleItemDef]
filterModuleImportItems satisfied =
  filter keepItem
  where
    keepItem item =
      case item of
        MIDImport modImport -> modImport `S.notMember` satisfied
        _ -> True


clearSatisfiedComponentImports :: [ModuleImport] -> ModuleComponent -> ModuleComponent
clearSatisfiedComponentImports satisfied comp =
  let satisfiedSet = S.fromList satisfied
   in comp
        { mcImports = filter (`notElem` satisfied) (mcImports comp)
        , mcItems = filterModuleImportItems satisfiedSet (mcItems comp)
        }


normalizeDiagram :: Doctrine -> RewritePolicy -> Int -> Diagram -> Either Text Diagram
normalizeDiagram doc policy fuel diag = do
  let rules = rulesFromPolicy policy (dCells2 doc)
  tt <- doctrineTypeTheory doc
  status <- normalizeWithMapper (applyModExpr doc) tt fuel rules diag
  pure
    (case status of
       Finished d -> d
       OutOfFuel d -> d)


quoteOne :: ModuleEnv -> Doctrine -> Diagram -> Text -> Text -> Either Text Diagram
quoteOne env doc diag fragmentName targetName = do
  derived <- lookupDerivedDoctrine env targetName
  if ddBase derived /= dName doc
    then Left "pipeline: quote target base doctrine mismatch"
    else do
      let expectedMode = ddMode derived
      if expectedMode /= renderModeName (dMode diag)
        then Left "pipeline: quote target mode mismatch"
        else do
          frag <- lookupFragment env fragmentName
          if frBase frag /= dName doc
            then Left "pipeline: quote fragment base doctrine mismatch"
            else
              if frMode frag /= renderModeName (dMode diag)
                then Left "pipeline: quote fragment mode mismatch"
                else Right ()
          derivedDoc <- lookupDoctrine env targetName
          quoteDiagram doc derivedDoc (dMode diag) frag diag


lookupPipeline :: ModuleEnv -> Text -> Either Text Pipeline
lookupPipeline env name =
  case M.lookup name (mePipelines env) of
    Nothing -> Left ("Unknown pipeline: " <> name)
    Just p -> Right p


lookupMorphism :: ModuleEnv -> Text -> Either Text Morph.Morphism
lookupMorphism env name =
  case M.lookup name (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> name)
    Just m -> Right m


lookupDerivedDoctrine :: ModuleEnv -> Text -> Either Text DerivedDoctrine
lookupDerivedDoctrine env name =
  case M.lookup name (meDerivedDoctrines env) of
    Nothing -> Left ("Unknown derived doctrine: " <> name)
    Just dd -> Right dd


lookupFragment :: ModuleEnv -> Text -> Either Text FragmentDecl
lookupFragment env name =
  case M.lookup name (meFragments env) of
    Nothing -> Left ("Unknown fragment: " <> name)
    Just frag -> Right frag


lookupDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just doc -> Right doc


ensureAcyclicIfRequired :: Doctrine -> Diagram -> Either Text ()
ensureAcyclicIfRequired doc diag =
  if modeIsAcyclic doc (dMode diag)
    then do
      _ <- topologicalEdges diag
      mapM_ checkInner (IM.elems (dEdges diag))
    else Right ()
  where
    checkInner edge =
      case ePayload edge of
        PBox _ inner -> ensureAcyclicIfRequired doc inner
        PFeedback body -> ensureAcyclicIfRequired doc body
        _ -> Right ()
