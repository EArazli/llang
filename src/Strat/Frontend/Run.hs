{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Run
  ( Artifact(..)
  , RunResult(..)
  , runFile
  , runWithEnv
  , selectRun
  , renderRunResult
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Frontend.Compile (compileSourceDiagram)
import Strat.Pipeline
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.ModeTheory (ModeName(..))
import qualified Strat.Poly.Morphism as Morph
import Strat.Poly.Pretty (renderDiagram)
import Strat.Poly.Foliation (SSA(..), SSAStep(..), foliate, forgetSSA)
import Strat.Poly.Normalize (NormalizationStatus(..), normalize)
import Strat.Poly.Rewrite (rulesFromPolicy)


data Artifact
  = ArtDiagram
      { artDoctrine :: Doctrine
      , artDiagram :: Diagram
      }
  | ArtSSA
      { artBaseDoctrine :: Doctrine
      , artFoliatedName :: Text
      , artSSA :: SSA
      }
  | ArtExtracted
      { artStdout :: Text
      , artFiles :: M.Map FilePath Text
      }
  deriving (Eq, Show)


data RunResult = RunResult
  { prArtifact :: Artifact
  , prOutput :: Text
  }
  deriving (Eq, Show)


runFile :: FilePath -> Maybe Text -> IO (Either Text RunResult)
runFile path mRunName = do
  envResult <- loadModule path
  case envResult of
    Left err -> pure (Left err)
    Right env ->
      case selectRun env mRunName of
        Left err -> pure (Left err)
        Right spec -> pure (runWithEnv env spec)


selectRun :: ModuleEnv -> Maybe Text -> Either Text Run
selectRun env mName =
  case mName of
    Just name ->
      case M.lookup name (meRuns env) of
        Nothing -> Left ("Unknown run: " <> name <> available)
        Just spec -> Right spec
    Nothing ->
      case M.lookup "main" (meRuns env) of
        Just spec -> Right spec
        Nothing ->
          case M.toList (meRuns env) of
            [] -> Left "No runs found"
            [(_, spec)] -> Right spec
            _ -> Left ("Multiple runs found; specify --run. Available: " <> T.intercalate ", " (M.keys (meRuns env)))
  where
    available =
      if M.null (meRuns env)
        then ""
        else " (available: " <> T.intercalate ", " (M.keys (meRuns env)) <> ")"


runWithEnv :: ModuleEnv -> Run -> Either Text RunResult
runWithEnv env runDef = do
  pipeline <- lookupPipeline env (runPipeline runDef)
  (doc0, diag0) <-
    compileSourceDiagram
      env
      (runDoctrine runDef)
      (runMode runDef)
      (runSurface runDef)
      (runUses runDef)
      (runExprText runDef)
  ensureAcyclicIfRequired doc0 diag0
  final <- foldM (runPhase env) (ArtDiagram doc0 diag0) (plPhases pipeline)
  out <- renderRunResult final
  pure
    RunResult
      { prArtifact = final
      , prOutput = out
      }


runPhase :: ModuleEnv -> Artifact -> Phase -> Either Text Artifact
runPhase env art phase =
  case phase of
    ApplyMorph name ->
      case art of
        ArtDiagram doc diag -> do
          mor <- lookupMorphism env name
          if dName (Morph.morSrc mor) /= dName doc
            then Left ("pipeline: morphism source mismatch for " <> name)
            else do
              diag' <- Morph.applyMorphismDiagram mor diag
              let doc' = Morph.morTgt mor
              ensureAcyclicIfRequired doc' diag'
              pure (ArtDiagram doc' diag')
        ArtSSA baseDoc derivedName ssa ->
          if name == derivedName <> ".forget"
            then do
              let diag = forgetSSA ssa
              ensureAcyclicIfRequired baseDoc diag
              pure (ArtDiagram baseDoc diag)
            else do
              mor <- lookupMorphism env name
              if dName (Morph.morSrc mor) /= dName baseDoc
                then Left ("pipeline: morphism source mismatch for " <> name)
                else do
                  let diagBase = forgetSSA ssa
                  diag' <- Morph.applyMorphismDiagram mor diagBase
                  let doc' = Morph.morTgt mor
                  ensureAcyclicIfRequired doc' diag'
                  pure (ArtDiagram doc' diag')
        ArtExtracted{} ->
          Left "pipeline: cannot apply morphism after extraction"
    Normalize policy fuel ->
      case art of
        ArtDiagram doc diag -> do
          let rules = rulesFromPolicy policy (dCells2 doc)
          status <- normalize (doctrineTypeTheory doc) fuel rules diag
          let diag' =
                case status of
                  Finished d -> d
                  OutOfFuel d -> d
          ensureAcyclicIfRequired doc diag'
          pure (ArtDiagram doc diag')
        ArtSSA{} -> Left "pipeline: normalize expects a diagram artifact"
        ArtExtracted{} -> Left "pipeline: cannot normalize extracted host value"
    ExtractFoliation targetName folPolicy ->
      case art of
        ArtDiagram doc diag -> do
          derived <- lookupDerivedDoctrine env targetName
          if ddBase derived /= dName doc
            then Left "pipeline: foliation target base doctrine mismatch"
            else do
              let expectedMode = ddMode derived
              if expectedMode /= renderModeName (dMode diag)
                then Left "pipeline: foliation target mode mismatch"
                else do
                  ssa <- foliate folPolicy doc (dMode diag) diag
                  pure (ArtSSA doc targetName ssa)
        ArtSSA{} -> Left "pipeline: foliate expects a diagram artifact"
        ArtExtracted{} -> Left "pipeline: cannot foliate extracted host value"
    ExtractValue doctrineName extractorSpec ->
      case art of
        ArtDiagram doc diag -> do
          if dName doc /= doctrineName
            then Left ("pipeline: extractor doctrine mismatch, expected " <> doctrineName)
            else extractValue extractorSpec doc diag
        ArtSSA{} -> Left "pipeline: extract value expects a diagram artifact"
        ArtExtracted{} -> Left "pipeline: value already extracted"
    ExtractDiagramPretty ->
      case art of
        ArtDiagram _ diag -> do
          txt <- renderDiagram diag
          pure (ArtExtracted txt M.empty)
        ArtSSA _ _ ssa ->
          pure (ArtExtracted (renderSSA ssa) M.empty)
        ArtExtracted{} -> Right art


renderRunResult :: Artifact -> Either Text Text
renderRunResult art =
  case art of
    ArtDiagram _ diag -> renderDiagram diag
    ArtSSA _ _ ssa -> Right (renderSSA ssa)
    ArtExtracted out files ->
      if M.null files
        then Right out
        else
          let fileLines =
                [ T.pack path <> ":\n" <> body
                | (path, body) <- M.toList files
                ]
           in Right (T.intercalate "\n\n" (filter (not . T.null) (out : fileLines)))


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
        PFeedback _ body -> ensureAcyclicIfRequired doc body
        _ -> Right ()


topologicalEdges :: Diagram -> Either Text [Edge]
topologicalEdges diag =
  if IM.null edgeTable
    then Right []
    else if length orderedIds == IM.size edgeTable
      then mapM lookupEdge orderedIds
      else Left "acyclic mode violation: diagram contains a cycle"
  where
    edgeTable = dEdges diag
    edges = IM.elems edgeTable
    edgeIds = map eId edges

    deps0 = M.fromList [(eid, depsFor eid) | eid <- edgeIds]
    dependents = foldl insertDeps M.empty (M.toList deps0)

    insertDeps acc (eid, deps) =
      S.foldl' (\m dep -> M.insertWith S.union dep (S.singleton eid) m) acc deps

    depsFor eid =
      case findEdge eid of
        Nothing -> S.empty
        Just edge ->
          S.fromList
            [ prod
            | p <- eIns edge
            , Just (Just prod) <- [IM.lookup (portInt p) (dProd diag)]
            ]

    ready0 =
      S.fromList
        [ eid
        | (eid, deps) <- M.toList deps0
        , S.null deps
        ]

    orderedIds = go ready0 deps0 []

    go ready deps acc =
      case S.lookupMin ready of
        Nothing -> reverse acc
        Just eid ->
          let readyRest = S.deleteMin ready
              out = M.findWithDefault S.empty eid dependents
              (deps', ready') = S.foldl' (dropDep eid) (deps, readyRest) out
           in go ready' deps' (eid : acc)

    dropDep done (deps, ready) target =
      let old = M.findWithDefault S.empty target deps
          new = S.delete done old
          deps' = M.insert target new deps
          ready' = if S.null new then S.insert target ready else ready
       in (deps', ready')

    findEdge eid =
      let EdgeId k = eid
       in IM.lookup k edgeTable

    lookupEdge eid =
      case findEdge eid of
        Nothing -> Left "internal error: missing edge"
        Just edge -> Right edge

    portInt (PortId i) = i


extractValue :: ValueExtractorSpec -> Doctrine -> Diagram -> Either Text Artifact
extractValue extractorSpec _doc diag =
  case extractorSpec of
    ExtractDoc _stdout -> do
      txt <- extractDoc diag
      pure (ArtExtracted txt M.empty)
    ExtractFileTree root -> do
      files <- extractFileTree diag
      let files' = M.mapKeys (\path -> root <> "/" <> path) files
      pure (ArtExtracted "" files')


extractDoc :: Diagram -> Either Text Text
extractDoc diag = do
  ordered <- topologicalEdges diag
  env <- foldM step M.empty ordered
  vals <- mapM (lookupPort env) (dOut diag)
  pure (T.concat (map renderDoc vals))
  where
    step env edge = do
      ins <- mapM (lookupPort env) (eIns edge)
      outs <- evalEdge edge ins
      if length outs /= length (eOuts edge)
        then Left "extract Doc: arity mismatch"
        else Right (insertMany env (zip (eOuts edge) outs))

    lookupPort env p =
      case M.lookup p env of
        Nothing -> Left "extract Doc: open input port"
        Just v -> Right v

    insertMany env pairs = foldl (\m (k, v) -> M.insert k v m) env pairs

    evalEdge edge ins =
      case ePayload edge of
        PGen (GenName "empty") _ _ -> Right [DEmpty]
        PGen (GenName "text") attrs _ -> do
          s <- attrString "s" attrs
          Right [DText s]
        PGen (GenName "line") _ _ -> Right [DLine]
        PGen (GenName "cat") _ _ ->
          case ins of
            [a, b] -> Right [DCat a b]
            _ -> Left "extract Doc: cat expects 2 inputs"
        PGen (GenName "indent") attrs _ ->
          case ins of
            [d] -> do
              n <- attrInt "n" attrs
              Right [DIndent n d]
            _ -> Left "extract Doc: indent expects 1 input"
        PGen _ _ _ -> Left "extract Doc: unsupported generator"
        PBox _ _ -> Left "extract Doc: boxes are not supported"
        PFeedback _ _ -> Left "extract Doc: feedback is not supported"
        PSplice _ -> Left "extract Doc: splice is not supported"


extractFileTree :: Diagram -> Either Text (M.Map FilePath Text)
extractFileTree diag = do
  ordered <- topologicalEdges diag
  env <- foldM step M.empty ordered
  vals <- mapM (lookupPort env) (dOut diag)
  foldM mergeOne M.empty vals
  where
    step env edge = do
      ins <- mapM (lookupPort env) (eIns edge)
      outs <- evalEdge edge ins
      if length outs /= length (eOuts edge)
        then Left "extract FileTree: arity mismatch"
        else Right (insertMany env (zip (eOuts edge) outs))

    lookupPort env p =
      case M.lookup p env of
        Nothing -> Left "extract FileTree: open input port"
        Just v -> Right v

    insertMany env pairs = foldl (\m (k, v) -> M.insert k v m) env pairs

    evalEdge edge ins =
      case ePayload edge of
        PGen (GenName "singleFile") attrs _ -> do
          path <- T.unpack <$> attrString "path" attrs
          content <- attrString "content" attrs
          Right [FTFile path content]
        PGen (GenName "concatTree") _ _ ->
          case ins of
            [a, b] -> Right [FTConcat [a, b]]
            _ -> Left "extract FileTree: concatTree expects 2 inputs"
        PGen _ _ _ -> Left "extract FileTree: unsupported generator"
        PBox _ _ -> Left "extract FileTree: boxes are not supported"
        PFeedback _ _ -> Left "extract FileTree: feedback is not supported"
        PSplice _ -> Left "extract FileTree: splice is not supported"

    mergeOne acc v =
      case v of
        FTFile path body ->
          if M.member path acc
            then Left "extract FileTree: duplicate file path"
            else Right (M.insert path body acc)
        FTConcat xs -> foldM mergeOne acc xs


data DocValue
  = DEmpty
  | DText Text
  | DLine
  | DCat DocValue DocValue
  | DIndent Int DocValue


renderDoc :: DocValue -> Text
renderDoc doc =
  case doc of
    DEmpty -> ""
    DText s -> s
    DLine -> "\n"
    DCat a b -> renderDoc a <> renderDoc b
    DIndent n d -> indentAfterNewline n (renderDoc d)


indentAfterNewline :: Int -> Text -> Text
indentAfterNewline n txt =
  case T.splitOn "\n" txt of
    [] -> ""
    x : xs -> T.intercalate "\n" (x : map (prefix n) xs)
  where
    prefix k seg = T.replicate k " " <> seg


data FileTreeValue
  = FTFile FilePath Text
  | FTConcat [FileTreeValue]


attrString :: Text -> AttrMap -> Either Text Text
attrString key attrs =
  case M.lookup key attrs of
    Just (ATLit (ALString s)) -> Right s
    _ -> Left ("missing or non-string attribute: " <> key)


attrInt :: Text -> AttrMap -> Either Text Int
attrInt key attrs =
  case M.lookup key attrs of
    Just (ATLit (ALInt n)) -> Right n
    _ -> Left ("missing or non-int attribute: " <> key)


renderSSA :: SSA -> Text
renderSSA ssa =
  T.unlines
    (["SSA " <> ssaBaseDoctrine ssa <> " {", "  steps = " <> T.pack (show (length (ssaSteps ssa)))]
      <> map renderStep (ssaSteps ssa)
      <> ["}"])
  where
    renderStep st =
      case st of
        StepGen eid gen _attrs _ins _outs _ ->
          "  gen " <> T.pack (show eid) <> " " <> T.pack (show gen)
        StepBox eid _ _ _ _ ->
          "  box " <> T.pack (show eid)
        StepFeedback eid _ _ _ _ ->
          "  feedback " <> T.pack (show eid)


renderModeName :: ModeName -> Text
renderModeName (ModeName name) = name
