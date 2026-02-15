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
import Data.List (findIndex)
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Frontend.Compile (compileSourceDiagram)
import Strat.Pipeline
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.Attr
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeRef(..), TypeName(..))
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
        ArtDiagram doc diag ->
          if ".forget" `T.isSuffixOf` name
            then
              Left
                ( "cannot apply `"
                    <> name
                    <> "` to a diagram; `.forget` is only defined on SSA artifacts produced by `extract foliate`."
                )
            else do
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
              let srcName = dName (Morph.morSrc mor)
              if srcName == derivedName
                then do
                  derivedDoc <- lookupDoctrine env derivedName
                  ssaDiag <- encodeSSAArtifact derivedDoc ssa
                  diag' <- Morph.applyMorphismDiagram mor ssaDiag
                  let doc' = Morph.morTgt mor
                  ensureAcyclicIfRequired doc' diag'
                  pure (ArtDiagram doc' diag')
                else
                  if srcName == dName baseDoc
                    then do
                      let diagBase = forgetSSA ssa
                      diag' <- Morph.applyMorphismDiagram mor diagBase
                      let doc' = Morph.morTgt mor
                      ensureAcyclicIfRequired doc' diag'
                      pure (ArtDiagram doc' diag')
                    else Left ("pipeline: morphism source mismatch for " <> name)
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
    ExtractFoliation targetName mFolPolicy ->
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
                  let folPolicy = maybe (ddDefaultPolicy derived) id mFolPolicy
                  ssa <- foliate folPolicy doc (dMode diag) diag
                  pure (ArtSSA doc targetName ssa)
        ArtSSA{} -> Left "pipeline: foliate expects a diagram artifact"
        ArtExtracted{} -> Left "pipeline: cannot foliate extracted host value"
    ExtractValue doctrineName extractorSpec ->
      case art of
        ArtDiagram doc diag -> do
          if not (extractorDoctrineMatches doctrineName doc)
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


lookupDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just doc -> Right doc


extractorDoctrineMatches :: Text -> Doctrine -> Bool
extractorDoctrineMatches doctrineName doc =
  dName doc == doctrineName
    || (dName doc == "Artifact" && (doctrineName == "Doc" || doctrineName == "FileTree"))


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


encodeSSAArtifact :: Doctrine -> SSA -> Either Text Diagram
encodeSSAArtifact doc ssa = do
  let mode = ssaMode ssa
      tt = doctrineTypeTheory doc
      requireType0 tName = do
        _ <- lookupTypeSig doc (TypeRef mode (TypeName tName))
        pure (TCon (TypeRef mode (TypeName tName)) [])
      requireGen gName =
        case M.lookup mode (dGens doc) >>= M.lookup (GenName gName) of
          Nothing -> Left ("pipeline: derived doctrine missing SSA generator " <> gName)
          Just _ -> Right ()
      portName pid =
        case M.lookup pid (ssaPortNames ssa) of
          Just name -> name
          Nothing ->
            case pid of
              PortId i -> "p" <> T.pack (show i)
  portTy <- requireType0 "PortRef"
  portsTy <- requireType0 "PortList"
  stepTy <- requireType0 "Step"
  stepsTy <- requireType0 "StepList"
  ssaTy <- requireType0 "SSA"
  mapM_ requireGen
    [ "portRef"
    , "portsNil"
    , "portsCons"
    , "stepGen"
    , "stepBox"
    , "stepFeedback"
    , "stepsNil"
    , "stepsCons"
    , "ssaProgram"
    ]
  let mkPortList names =
        case names of
          [] -> genD mode [] [portsTy] (GenName "portsNil")
          n:rest -> do
            headPort <- genDWithAttrs mode [] [portTy] (GenName "portRef") (M.singleton "name" (ATLit (ALString n)))
            tailPorts <- mkPortList rest
            pair <- tensorD headPort tailPorts
            cons <- genD mode [portTy, portsTy] [portsTy] (GenName "portsCons")
            compD tt cons pair
      mkStepEdge st =
        case st of
          StepGen _ gen _ _ _ _ ->
            genDWithAttrs
              mode
              [portsTy, portsTy]
              [stepTy]
              (GenName "stepGen")
              (M.singleton "name" (ATLit (ALString (renderGenName gen))))
          StepBox _ box _ _ _ ->
            genDWithAttrs
              mode
              [portsTy, portsTy]
              [stepTy]
              (GenName "stepBox")
              (M.singleton "name" (ATLit (ALString (renderBoxName box))))
          StepFeedback{} ->
            genD mode [portsTy, portsTy] [stepTy] (GenName "stepFeedback")
      mkStep st = do
        ins <- mkPortList (map portName (stepIns st))
        outs <- mkPortList (map portName (stepOuts st))
        pair <- tensorD ins outs
        mk <- mkStepEdge st
        compD tt mk pair
      mkStepList steps =
        case steps of
          [] -> genD mode [] [stepsTy] (GenName "stepsNil")
          st:rest -> do
            headStep <- mkStep st
            tailSteps <- mkStepList rest
            pair <- tensorD headStep tailSteps
            cons <- genD mode [stepTy, stepsTy] [stepsTy] (GenName "stepsCons")
            compD tt cons pair
      renderGenName (GenName name) = name
      renderBoxName (BoxName name) = name
  inPorts <- mkPortList (map portName (ssaInputs ssa))
  outPorts <- mkPortList (map portName (ssaOutputs ssa))
  steps <- mkStepList (ssaSteps ssa)
  tuple2 <- tensorD inPorts outPorts
  tuple3 <- tensorD tuple2 steps
  build <- genD mode [portsTy, portsTy, stepsTy] [ssaTy] (GenName "ssaProgram")
  compD tt build tuple3


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
  env <- evalArtifactDiagram diag
  vals <- mapM (lookupOut env "extract Doc") (dOut diag)
  docs <- mapM expectDoc vals
  pure (T.concat (map renderDoc docs))
  where
    lookupOut env label p =
      case M.lookup p env of
        Nothing -> Left (label <> ": open output port")
        Just v -> Right v

extractFileTree :: Diagram -> Either Text (M.Map FilePath Text)
extractFileTree diag = do
  env <- evalArtifactDiagram diag
  vals <- mapM (lookupOut env "extract FileTree") (dOut diag)
  trees <- mapM expectFileTree vals
  foldM mergeOne M.empty trees
  where
    lookupOut env label p =
      case M.lookup p env of
        Nothing -> Left (label <> ": open output port")
        Just v -> Right v

    mergeOne acc v =
      case v of
        FTFile path bodyDoc ->
          if M.member path acc
            then Left "extract FileTree: duplicate file path"
            else Right (M.insert path (renderDoc bodyDoc) acc)
        FTConcat xs -> foldM mergeOne acc xs


evalArtifactDiagram :: Diagram -> Either Text (M.Map PortId RuntimeValue)
evalArtifactDiagram diag = do
  ordered <- topologicalEdges diag
  foldM step M.empty ordered
  where
    step env edge = do
      ins <- mapM (lookupPort env) (eIns edge)
      outs <- evalEdge edge ins
      if length outs /= length (eOuts edge)
        then Left "extract value: arity mismatch"
        else Right (insertMany env (zip (eOuts edge) outs))

    lookupPort env p =
      case M.lookup p env of
        Nothing -> Left "extract value: open input port"
        Just v -> Right v

    insertMany env pairs = foldl (\m (k, v) -> M.insert k v m) env pairs

    evalEdge edge ins =
      case ePayload edge of
        PGen (GenName "empty") _ _ -> Right [RVDoc DEmpty]
        PGen (GenName "text") attrs _ -> do
          s <- attrString "s" attrs
          Right [RVDoc (DText s)]
        PGen (GenName "line") _ _ -> Right [RVDoc DLine]
        PGen (GenName "cat") _ _ ->
          case ins of
            [a, b] -> do
              da <- expectDoc a
              db <- expectDoc b
              Right [RVDoc (DCat da db)]
            _ -> Left "extract Doc: cat expects 2 inputs"
        PGen (GenName "indent") attrs _ ->
          case ins of
            [d] -> do
              n <- attrInt "n" attrs
              dd <- expectDoc d
              Right [RVDoc (DIndent n dd)]
            _ -> Left "extract Doc: indent expects 1 input"
        PGen (GenName "singleFile") attrs _ -> do
          path <- T.unpack <$> attrString "path" attrs
          body <-
            case ins of
              [v] -> expectDoc v
              [] -> DText <$> attrString "content" attrs
              _ -> Left "extract FileTree: singleFile expects 1 Doc input"
          Right [RVFileTree (FTFile path body)]
        PGen (GenName "concatTree") _ _ ->
          case ins of
            [a, b] -> do
              ta <- expectFileTree a
              tb <- expectFileTree b
              Right [RVFileTree (FTConcat [ta, tb])]
            _ -> Left "extract FileTree: concatTree expects 2 inputs"
        PGen _ _ _ -> Left "extract value: unsupported generator"
        PBox _ _ -> Left "extract value: boxes are not supported"
        PFeedback _ -> Left "extract value: feedback is not supported"
        PSplice _ -> Left "extract value: splice is not supported"
        PTmMeta _ -> Left "extract value: term-meta nodes are not supported"
        PInternalDrop -> Left "extract value: internal drop nodes are not supported"


data RuntimeValue
  = RVDoc DocValue
  | RVFileTree FileTreeValue


expectDoc :: RuntimeValue -> Either Text DocValue
expectDoc val =
  case val of
    RVDoc doc -> Right doc
    RVFileTree _ -> Left "extract Doc: expected Doc output"


expectFileTree :: RuntimeValue -> Either Text FileTreeValue
expectFileTree val =
  case val of
    RVDoc _ -> Left "extract FileTree: expected FileTree output"
    RVFileTree tree -> Right tree


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
  = FTFile FilePath DocValue
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
    ( [ "SSA " <> ssaBaseDoctrine ssa <> " {"
      , "  steps = " <> T.pack (show (length (ssaSteps ssa)))
      , "  inputs = " <> renderPorts (ssaInputs ssa)
      , "  outputs = " <> renderPorts (ssaOutputs ssa)
      ]
        <> map renderStep (ssaSteps ssa)
        <> ["}"]
    )
  where
    diag = ssaOriginal ssa
    inIndex = M.fromList (zip (ssaInputs ssa) [0 :: Int ..])

    renderStep st =
      case st of
        StepGen eid gen attrs ins outs binders ->
          "  gen "
            <> renderEdgeId eid
            <> " "
            <> renderGenName gen
            <> renderAttrs attrs
            <> " in="
            <> renderInputs ins
            <> " out="
            <> renderPorts outs
            <> renderBinderCount binders
        StepBox eid box inner ins outs ->
          "  box "
            <> renderEdgeId eid
            <> " "
            <> renderBoxName box
            <> " in="
            <> renderInputs ins
            <> " out="
            <> renderPorts outs
            <> " innerSteps="
            <> T.pack (show (length (ssaSteps inner)))
        StepFeedback eid body ins outs ->
          "  feedback "
            <> renderEdgeId eid
            <> " in="
            <> renderInputs ins
            <> " out="
            <> renderPorts outs
            <> " bodySteps="
            <> T.pack (show (length (ssaSteps body)))

    renderGenName (GenName n) = n
    renderBoxName (BoxName n) = n
    renderEdgeId (EdgeId i) = "e" <> T.pack (show i)
    renderPortId (PortId i) = "p" <> T.pack (show i)

    renderPort pid =
      let pidTxt = renderPortId pid
          nm = M.findWithDefault pidTxt pid (ssaPortNames ssa)
       in if nm == pidTxt then pidTxt else pidTxt <> ":" <> nm

    renderPorts ps = "[" <> T.intercalate ", " (map renderPort ps) <> "]"

    renderInputs ps = "[" <> T.intercalate ", " (map renderInput ps) <> "]"

    renderInput pid = renderPort pid <> " <- " <> renderProducer pid

    renderProducer pid =
      case IM.lookup (portInt pid) (dProd diag) of
        Just (Just eid) ->
          case IM.lookup (edgeInt eid) (dEdges diag) of
            Just edge ->
              case findIndex (== pid) (eOuts edge) of
                Just outPos -> renderEdgeId eid <> "#" <> T.pack (show outPos)
                Nothing -> renderEdgeId eid
            Nothing -> "<missing-edge>"
        _ ->
          case M.lookup pid inIndex of
            Just ix -> "input#" <> T.pack (show ix)
            Nothing -> "<open>"

    renderAttrs attrs
      | M.null attrs = " attrs={}"
      | otherwise =
          " attrs={"
            <> T.intercalate ", " (map renderOne (M.toList attrs))
            <> "}"
      where
        renderOne (k, v) = k <> "=" <> renderAttrTerm v

    renderAttrTerm term =
      case term of
        ATVar v -> "$" <> avName v
        ATLit lit ->
          case lit of
            ALInt n -> T.pack (show n)
            ALString s -> T.pack (show s)
            ALBool b -> if b then "true" else "false"

    renderBinderCount binders =
      if null binders
        then ""
        else " binders=" <> T.pack (show (length binders))

    portInt (PortId i) = i
    edgeInt (EdgeId i) = i


renderModeName :: ModeName -> Text
renderModeName (ModeName name) = name
