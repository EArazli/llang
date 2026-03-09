{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
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
import Strat.Poly.Kernel (Obj(..), pattern OCon, ObjRef(..), ObjName(..))
import Strat.Poly.Obj (mkCon)
import Strat.Poly.Diagram
import Strat.Poly.Graph
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.ModeTheory (ModeName(..))
import qualified Strat.Poly.Morphism as Morph
import Strat.Poly.Pretty (renderDiagram)
import Strat.Poly.Quote (quoteDiagram)
import Strat.Poly.ModAction (applyModExpr)
import Strat.Poly.Normalize (NormalizationStatus(..), normalizeWithMapper)
import Strat.Poly.Rewrite (rulesFromPolicy)


data Artifact
  = ArtDiagram
      { artDoctrine :: Doctrine
      , artDiagram :: Diagram
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
        ArtExtracted{} ->
          Left "pipeline: cannot apply morphism after extraction"
    Normalize policy fuel ->
      case art of
        ArtDiagram doc diag -> do
          let rules = rulesFromPolicy policy (dCells2 doc)
          tt <- doctrineTypeTheory doc
          status <- normalizeWithMapper (applyModExpr doc) tt fuel rules diag
          let diag' =
                case status of
                  Finished d -> d
                  OutOfFuel d -> d
          ensureAcyclicIfRequired doc diag'
          pure (ArtDiagram doc diag')
        ArtExtracted{} -> Left "pipeline: cannot normalize extracted host value"
    QuoteInto targetName ->
      case art of
        ArtDiagram doc diag -> do
          derived <- lookupDerivedDoctrine env targetName
          if ddBase derived /= dName doc
            then Left "pipeline: quote target base doctrine mismatch"
            else do
              let expectedMode = ddMode derived
              if expectedMode /= renderModeName (dMode diag)
                then Left "pipeline: quote target mode mismatch"
                else do
                  fragment <- lookupFragment env (ddFragment derived)
                  derivedDoc <- lookupDoctrine env targetName
                  layout <-
                    case ddQuoteLayout derived of
                      Nothing -> Left "pipeline: quote target does not define a quote-compatible layout"
                      Just qtl -> Right qtl
                  quoted <- quoteDiagram layout doc derivedDoc (dMode diag) fragment diag
                  pure (ArtDiagram derivedDoc quoted)
        ArtExtracted{} -> Left "pipeline: cannot quote extracted host value"
    ExtractValue doctrineName extractorSpec ->
      case art of
        ArtDiagram doc diag -> do
          case ensureExtractorSupported doctrineName doc (dMode diag) of
            Left err -> Left ("pipeline: " <> err)
            Right () -> extractValue extractorSpec doc diag
        ArtExtracted{} -> Left "pipeline: value already extracted"
    ExtractDiagramPretty ->
      case art of
        ArtDiagram _ diag -> do
          txt <- renderDiagram diag
          pure (ArtExtracted txt M.empty)
        ArtExtracted{} -> Right art


renderRunResult :: Artifact -> Either Text Text
renderRunResult art =
  case art of
    ArtDiagram _ diag -> renderDiagram diag
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


lookupFragment :: ModuleEnv -> Text -> Either Text FragmentDecl
lookupFragment env name =
  case M.lookup name (meFragments env) of
    Nothing -> Left ("Unknown fragment: " <> name)
    Just fragment -> Right fragment


lookupDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just doc -> Right doc


ensureExtractorSupported :: Text -> Doctrine -> ModeName -> Either Text ()
ensureExtractorSupported extractorName doc mode =
  case extractorName of
    "Doc" -> ensureDocFragment doc mode
    "FileTree" -> ensureFileTreeFragment doc mode
    other -> Left ("extract: unknown extractor " <> other)


ensureDocFragment :: Doctrine -> ModeName -> Either Text ()
ensureDocFragment = ensureDocFragmentWithLabel "extract Doc"


ensureDocFragmentWithLabel :: Text -> Doctrine -> ModeName -> Either Text ()
ensureDocFragmentWithLabel label doc mode = do
  let docTy = mkCon (ObjRef mode (ObjName "Doc")) []
  _ <- requireFragmentGen label doc mode (GenName "empty") [] [docTy]
  textDecl <- requireFragmentGen label doc mode (GenName "text") [] [docTy]
  _ <- requireFragmentGen label doc mode (GenName "line") [] [docTy]
  _ <- requireFragmentGen label doc mode (GenName "cat") [docTy, docTy] [docTy]
  indentDecl <- requireFragmentGen label doc mode (GenName "indent") [docTy] [docTy]
  requireAttrLitKind label doc "s" LKString textDecl
  requireAttrLitKind label doc "n" LKInt indentDecl


ensureFileTreeFragment :: Doctrine -> ModeName -> Either Text ()
ensureFileTreeFragment doc mode = do
  ensureDocFragmentWithLabel "extract FileTree" doc mode
  let label = "extract FileTree"
      docTy = mkCon (ObjRef mode (ObjName "Doc")) []
      ftTy = mkCon (ObjRef mode (ObjName "FileTree")) []
  singleFileDecl <- requireFragmentGen label doc mode (GenName "singleFile") [docTy] [ftTy]
  _ <- requireFragmentGen label doc mode (GenName "concatTree") [ftTy, ftTy] [ftTy]
  requireAttrLitKind label doc "path" LKString singleFileDecl


requireFragmentGen :: Text -> Doctrine -> ModeName -> GenName -> [Obj] -> [Obj] -> Either Text GenDecl
requireFragmentGen label doc mode name expectedDom expectedCod = do
  gd <- lookupGenInMode doc mode name
    `prefixErr` (label <> ": ")
  requireGenSig label mode name expectedDom expectedCod gd
  pure gd


lookupGenInMode :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGenInMode doc mode genName =
  case M.lookup mode (dGens doc) >>= M.lookup genName of
    Nothing ->
      Left
        ( "missing generator '"
            <> renderGenNameText genName
            <> "' in mode "
            <> renderModeName mode
        )
    Just gd -> Right gd


requireNoParamsNoBinders :: Text -> GenDecl -> Either Text ()
requireNoParamsNoBinders label gd =
  if null (gdParams gd) && all isPort (gdDom gd)
    then Right ()
    else
      Left
        ( label
            <> ": generator '"
            <> renderGenNameText (gdName gd)
            <> "' must have no parameters and no binder inputs"
        )
  where
    isPort sh =
      case sh of
        InPort _ -> True
        InBinder _ -> False


requireGenSig
  :: Text
  -> ModeName
  -> GenName
  -> [Obj]
  -> [Obj]
  -> GenDecl
  -> Either Text ()
requireGenSig label mode genName expectedDom expectedCod gd = do
  if gdMode gd /= mode
    then
      Left
        ( label
            <> ": generator '"
            <> renderGenNameText genName
            <> "' is in mode "
            <> renderModeName (gdMode gd)
            <> ", expected mode "
            <> renderModeName mode
        )
    else Right ()
  requireNoParamsNoBinders label gd
  let expectedDomShape = map InPort expectedDom
  if gdDom gd == expectedDomShape && gdCod gd == expectedCod
    then Right ()
    else
      Left
        ( label
            <> ": generator '"
            <> renderGenNameText genName
            <> "' has wrong signature; expected "
            <> renderSig expectedDom expectedCod
            <> " in mode "
            <> renderModeName mode
        )
  where
    renderSig dom cod = "[" <> renderObjList dom <> "]->[" <> renderObjList cod <> "]"
    renderObjList xs = T.intercalate "," (map renderObj xs)
    renderObj ty =
      case ty of
        OCon (ObjRef _ (ObjName n)) [] -> n
        _ -> "<obj>"


requireAttrLitKind
  :: Text
  -> Doctrine
  -> AttrName
  -> AttrLitKind
  -> GenDecl
  -> Either Text ()
requireAttrLitKind label doc key expectedKind gd = do
  attrSort <-
    case lookup key (gdAttrs gd) of
      Nothing ->
        Left
          ( label
              <> ": generator '"
              <> renderGenNameText (gdName gd)
              <> "' missing attribute '"
              <> key
              <> "'"
          )
      Just sortName -> Right sortName
  decl <-
    case M.lookup attrSort (dAttrSorts doc) of
      Nothing ->
        Left
          ( label
              <> ": generator '"
              <> renderGenNameText (gdName gd)
              <> "' attribute '"
              <> key
              <> "' refers to unknown sort "
              <> renderAttrSort attrSort
          )
      Just d -> Right d
  if asLitKind decl == Just expectedKind
    then Right ()
    else
      Left
        ( label
            <> ": generator '"
            <> renderGenNameText (gdName gd)
            <> "' attribute '"
            <> key
            <> "' must have "
            <> litKindLabel expectedKind
            <> " literal kind"
        )
  where
    litKindLabel lk =
      case lk of
        LKString -> "string"
        LKInt -> "int"
        LKBool -> "bool"


prefixErr :: Either Text a -> Text -> Either Text a
prefixErr res prefix =
  case res of
    Left err -> Left (prefix <> err)
    Right x -> Right x


renderGenNameText :: GenName -> Text
renderGenNameText (GenName name) = name


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
        PSplice _ _ -> Left "extract value: splice is not supported"
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


renderModeName :: ModeName -> Text
renderModeName (ModeName name) = name
