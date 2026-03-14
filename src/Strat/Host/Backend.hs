{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Host.Backend
  ( BackendRegistry
  , BackendPlugin(..)
  , HostArtifact(..)
  , standardBackends
  , standardBackendRegistry
  , buildBackendRegistry
  , resolveBackendPlugin
  , resolveBackendPluginFromRegistry
  , emitViaBackend
  , emitViaBackendWithRegistry
  , emitBundleViaBackend
  , emitBundleViaBackendWithRegistry
  , renderHostArtifact
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import Strat.Pipeline (BackendSpec(..))
import Strat.Poly.Doctrine
import Strat.Poly.Kernel (Obj(..), pattern OCon, ObjRef(..), ObjName(..))
import Strat.Poly.Obj (CodeArg(..), TermDiagram(..), TmVar, mkCon, tmvSort)
import Strat.Poly.Diagram
import Strat.Poly.Graph
import Strat.Poly.Literal (Literal(..), LiteralKind(..), literalKind)
import Strat.Poly.DSL.Elab.Diag (renderModeName, topologicalEdges)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.DefEq (diagramToTermExprChecked, normalizeTermDiagram)
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeTheory (TypeTheory, literalKindForObj)


data HostArtifact = HostArtifact
  { haStdout :: Text
  , haFiles :: M.Map FilePath Text
  }
  deriving (Eq, Show)

data BackendPlugin = BackendPlugin
  { bpName :: Text
  , bpAliases :: [Text]
  , bpEmitDiagram :: BackendSpec -> Doctrine -> Diagram -> Either Text HostArtifact
  , bpEmitBundle :: BackendSpec -> [(Text, Doctrine, Diagram)] -> Either Text HostArtifact
  }

type BackendRegistry = M.Map Text BackendPlugin


emitViaBackend :: BackendSpec -> Doctrine -> Diagram -> Either Text HostArtifact
emitViaBackend spec doc diag = do
  plugin <- resolveBackendPlugin (bsName spec)
  bpEmitDiagram plugin spec doc diag


emitViaBackendWithRegistry :: BackendRegistry -> BackendSpec -> Doctrine -> Diagram -> Either Text HostArtifact
emitViaBackendWithRegistry registry spec doc diag = do
  plugin <- resolveBackendPluginFromRegistry registry (bsName spec)
  bpEmitDiagram plugin spec doc diag


emitBundleViaBackend :: BackendSpec -> [(Text, Doctrine, Diagram)] -> Either Text HostArtifact
emitBundleViaBackend spec entries =
  case entries of
    [] -> Left "emit via: empty bundle"
    _ -> do
      plugin <- resolveBackendPlugin (bsName spec)
      bpEmitBundle plugin spec entries


emitBundleViaBackendWithRegistry :: BackendRegistry -> BackendSpec -> [(Text, Doctrine, Diagram)] -> Either Text HostArtifact
emitBundleViaBackendWithRegistry registry spec entries =
  case entries of
    [] -> Left "emit via: empty bundle"
    _ -> do
      plugin <- resolveBackendPluginFromRegistry registry (bsName spec)
      bpEmitBundle plugin spec entries


renderHostArtifact :: HostArtifact -> Text
renderHostArtifact art =
  if M.null (haFiles art)
    then haStdout art
    else
      let fileLines =
            [ T.pack path <> ":\n" <> body
            | (path, body) <- M.toList (haFiles art)
            ]
       in T.intercalate "\n\n" (filter (not . T.null) (haStdout art : fileLines))


backendLabel :: Text -> Text
backendLabel name = "emit via " <> name


backendStdout :: BackendSpec -> Bool
backendStdout spec = maybe True id (bsStdout spec)


resolveBackendPlugin :: Text -> Either Text BackendPlugin
resolveBackendPlugin name = do
  registry <- standardBackendRegistry
  resolveBackendPluginFromRegistry registry name


resolveBackendPluginFromRegistry :: BackendRegistry -> Text -> Either Text BackendPlugin
resolveBackendPluginFromRegistry registry name =
  case M.lookup (normalizeBackendName name) registry of
    Nothing -> Left ("emit via: unknown backend " <> name)
    Just plugin -> Right plugin


standardBackends :: [BackendPlugin]
standardBackends =
  [ docBackend
  , fileTreeBackend
  ]


standardBackendRegistry :: Either Text BackendRegistry
standardBackendRegistry =
  buildBackendRegistry standardBackends


buildBackendRegistry :: [BackendPlugin] -> Either Text BackendRegistry
buildBackendRegistry =
  foldM insertPlugin M.empty
  where
    insertPlugin acc plugin =
      foldM (insertAlias plugin) acc (backendPluginNames plugin)

    insertAlias plugin acc alias =
      case M.lookup alias acc of
        Nothing -> Right (M.insert alias plugin acc)
        Just other ->
          Left
            ( "backend registry: duplicate alias "
                <> alias
                <> " for "
                <> bpName other
                <> " and "
                <> bpName plugin
            )


backendPluginNames :: BackendPlugin -> [Text]
backendPluginNames plugin =
  L.nub (map normalizeBackendName (bpName plugin : bpAliases plugin))


normalizeBackendName :: Text -> Text
normalizeBackendName =
  T.toLower


docBackend :: BackendPlugin
docBackend =
  BackendPlugin
    { bpName = "Doc"
    , bpAliases = ["doc"]
    , bpEmitDiagram = \spec doc diag -> do
        let label = backendLabel "Doc"
        ensureDocFragmentWithLabel label doc (dMode diag)
        txt <- extractDoc doc diag
        pure HostArtifact { haStdout = if backendStdout spec then txt else "", haFiles = M.empty }
    , bpEmitBundle = \spec entries -> do
        rendered <- mapM renderDocEntry entries
        let stdoutText =
              if backendStdout spec
                then renderDocBundle rendered
                else ""
        pure HostArtifact { haStdout = stdoutText, haFiles = M.empty }
    }
  where
    renderDocEntry (name, doc, diag) = do
      ensureDocFragmentWithLabel "emit via Doc" doc (dMode diag)
      txt <- extractDoc doc diag
      pure (name, txt)

    renderDocBundle [(name, txt)] =
      if T.null name then txt else txt
    renderDocBundle xs =
      T.intercalate
        "\n\n"
        [ name <> ":\n" <> txt
        | (name, txt) <- xs
        ]


fileTreeBackend :: BackendPlugin
fileTreeBackend =
  BackendPlugin
    { bpName = "FileTree"
    , bpAliases = ["filetree", "file_tree"]
    , bpEmitDiagram = \spec doc diag -> do
        ensureFileTreeFragment doc (dMode diag)
        files <- extractFileTree doc diag
        let root = maybe "./out" id (bsRoot spec)
        pure HostArtifact { haStdout = "", haFiles = M.mapKeys (\path -> root <> "/" <> path) files }
    , bpEmitBundle = \spec entries -> do
        merged <- foldM mergeFileTreeEntry M.empty entries
        let root = maybe "./out" id (bsRoot spec)
        pure HostArtifact { haStdout = "", haFiles = M.mapKeys (\path -> root <> "/" <> path) merged }
    }
  where
    mergeFileTreeEntry acc (_, doc, diag) = do
      ensureFileTreeFragment doc (dMode diag)
      files <- extractFileTree doc diag
      foldM mergeOne acc (M.toList files)

    mergeOne acc (path, body) =
      if M.member path acc
        then Left ("emit via FileTree: duplicate file path " <> T.pack path)
        else Right (M.insert path body acc)


ensureDocFragmentWithLabel :: Text -> Doctrine -> ModeName -> Either Text ()
ensureDocFragmentWithLabel label doc mode = do
  let docTy = mkCon (ObjRef mode (ObjName "Doc")) []
  emptyDecl <- requireFragmentGen label doc mode (GenName "empty") [] [docTy]
  textDecl <- requireFragmentGen label doc mode (GenName "text") [] [docTy]
  lineDecl <- requireFragmentGen label doc mode (GenName "line") [] [docTy]
  catDecl <- requireFragmentGen label doc mode (GenName "cat") [docTy, docTy] [docTy]
  indentDecl <- requireFragmentGen label doc mode (GenName "indent") [docTy] [docTy]
  requireNoParams label emptyDecl
  requireNoParams label lineDecl
  requireNoParams label catDecl
  _ <- requireExactlyOneLiteralTmParam label doc LKString textDecl
  _ <- requireExactlyOneLiteralTmParam label doc LKInt indentDecl
  pure ()


ensureFileTreeFragment :: Doctrine -> ModeName -> Either Text ()
ensureFileTreeFragment doc mode = do
  ensureDocFragmentWithLabel "emit via FileTree" doc mode
  let label = "emit via FileTree"
      docTy = mkCon (ObjRef mode (ObjName "Doc")) []
      ftTy = mkCon (ObjRef mode (ObjName "FileTree")) []
  singleFileDecl <- requireFragmentGen label doc mode (GenName "singleFile") [docTy] [ftTy]
  concatDecl <- requireFragmentGen label doc mode (GenName "concatTree") [ftTy, ftTy] [ftTy]
  requireNoParams label concatDecl
  _ <- requireExactlyOneLiteralTmParam label doc LKString singleFileDecl
  pure ()


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


requireNoParams :: Text -> GenDecl -> Either Text ()
requireNoParams label gd =
  if null (gdParams gd)
    then Right ()
    else
      Left
        ( label
            <> ": generator '"
            <> renderGenNameText (gdName gd)
            <> "' must have no parameters"
        )


requireNoBinders :: Text -> GenDecl -> Either Text ()
requireNoBinders label gd =
  if all isPort (gdDom gd)
    then Right ()
    else
      Left
        ( label
            <> ": generator '"
            <> renderGenNameText (gdName gd)
            <> "' must have no binder inputs"
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
  requireNoBinders label gd
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


requireExactlyOneLiteralTmParam
  :: Text
  -> Doctrine
  -> LiteralKind
  -> GenDecl
  -> Either Text TmVar
requireExactlyOneLiteralTmParam label doc expectedKind gd = do
  tt <- doctrineTypeTheory doc
  tmv <-
    case gdParams gd of
      [GP_Tm v] -> Right v
      [] ->
        Left
          ( label
              <> ": generator '"
              <> renderGenNameText (gdName gd)
              <> "' must have exactly one sole term parameter"
          )
      [_] ->
        Left
          ( label
              <> ": generator '"
              <> renderGenNameText (gdName gd)
              <> "' sole parameter must be a term parameter"
          )
      _ ->
        Left
          ( label
              <> ": generator '"
              <> renderGenNameText (gdName gd)
              <> "' must have exactly one sole term parameter"
          )
  if literalKindForObj tt (tmvSort tmv) == Just expectedKind
    then Right tmv
    else
      Left
        ( label
            <> ": generator '"
            <> renderGenNameText (gdName gd)
            <> "' sole term parameter must admit "
            <> litKindLabel expectedKind
            <> " literals"
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


extractDoc :: Doctrine -> Diagram -> Either Text Text
extractDoc doc diag = do
  env <- evalArtifactDiagram doc diag
  vals <- mapM (lookupOut env "emit via Doc") (dOut diag)
  docs <- mapM expectDoc vals
  pure (T.concat (map renderDoc docs))
  where
    lookupOut env label p =
      case M.lookup p env of
        Nothing -> Left (label <> ": open output port")
        Just v -> Right v


extractFileTree :: Doctrine -> Diagram -> Either Text (M.Map FilePath Text)
extractFileTree doc diag = do
  env <- evalArtifactDiagram doc diag
  vals <- mapM (lookupOut env "emit via FileTree") (dOut diag)
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
            then Left "emit via FileTree: duplicate file path"
            else Right (M.insert path (renderDoc bodyDoc) acc)
        FTConcat xs -> foldM mergeOne acc xs


evalArtifactDiagram :: Doctrine -> Diagram -> Either Text (M.Map PortId RuntimeValue)
evalArtifactDiagram doc diag = do
  ordered <- topologicalEdges diag
  foldM step M.empty ordered
  where
    step env edge = do
      ins <- mapM (lookupPort env) (eIns edge)
      outs <- evalEdge edge ins
      if length outs /= length (eOuts edge)
        then Left "emit via: arity mismatch"
        else Right (insertMany env (zip (eOuts edge) outs))

    lookupPort env p =
      case M.lookup p env of
        Nothing -> Left "emit via: open input port"
        Just v -> Right v

    insertMany env pairs = foldl (\m (k, v) -> M.insert k v m) env pairs

    evalEdge edge ins =
      case ePayload edge of
        PGen (GenName "empty") _ _ -> Right [RVDoc DEmpty]
        PGen (GenName "text") args _ -> do
          s <- literalStringArg args
          Right [RVDoc (DText s)]
        PGen (GenName "line") _ _ -> Right [RVDoc DLine]
        PGen (GenName "cat") _ _ ->
          case ins of
            [a, b] -> do
              da <- expectDoc a
              db <- expectDoc b
              Right [RVDoc (DCat da db)]
            _ -> Left "emit via Doc: cat expects 2 inputs"
        PGen (GenName "indent") args _ ->
          case ins of
            [d] -> do
              n <- literalIntArg args
              dd <- expectDoc d
              Right [RVDoc (DIndent n dd)]
            _ -> Left "emit via Doc: indent expects 1 input"
        PGen (GenName "singleFile") args _ -> do
          path <- T.unpack <$> literalStringArg args
          body <-
            case ins of
              [v] -> expectDoc v
              _ -> Left "emit via FileTree: singleFile expects 1 Doc input"
          Right [RVFileTree (FTFile path body)]
        PGen (GenName "concatTree") _ _ ->
          case ins of
            [a, b] -> do
              ta <- expectFileTree a
              tb <- expectFileTree b
              Right [RVFileTree (FTConcat [ta, tb])]
            _ -> Left "emit via FileTree: concatTree expects 2 inputs"
        PGen _ _ _ -> Left "emit via: unsupported generator"
        PProvider _ -> Left "emit via: provider nodes are not supported"
        PModuleRef _ -> Left "emit via: module-reference nodes are not supported"
        PBox _ _ -> Left "emit via: boxes are not supported"
        PFeedback _ -> Left "emit via: feedback is not supported"
        PSplice _ _ -> Left "emit via: splice is not supported"
        PTmMeta _ -> Left "emit via: term-meta nodes are not supported"
        PTmLit _ -> Left "emit via: literal term nodes are not supported at top level"
        PInternalDrop -> Left "emit via: internal drop nodes are not supported"

    literalStringArg args = do
      tt <- doctrineTypeTheory doc
      arg <- requireSoleStoredArg args
      lit <- extractClosedLiteralArg tt LKString arg
      case lit of
        LString s -> Right s
        _ -> Left "emit via: sole term parameter is not a string literal"

    literalIntArg args = do
      tt <- doctrineTypeTheory doc
      arg <- requireSoleStoredArg args
      lit <- extractClosedLiteralArg tt LKInt arg
      case lit of
        LInt n -> Right n
        _ -> Left "emit via: sole term parameter is not an int literal"

    requireSoleStoredArg args =
      case args of
        [arg] -> Right arg
        _ -> Left "emit via: expected exactly one sole term parameter"


data RuntimeValue
  = RVDoc DocValue
  | RVFileTree FileTreeValue


expectDoc :: RuntimeValue -> Either Text DocValue
expectDoc val =
  case val of
    RVDoc doc -> Right doc
    RVFileTree _ -> Left "emit via Doc: expected Doc output"


expectFileTree :: RuntimeValue -> Either Text FileTreeValue
expectFileTree val =
  case val of
    RVDoc _ -> Left "emit via FileTree: expected FileTree output"
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


extractClosedLiteralArg
  :: TypeTheory
  -> LiteralKind
  -> CodeArg
  -> Either Text Literal
extractClosedLiteralArg tt expectedKind arg = do
  tm <-
    case arg of
      CATm term -> Right term
      CAObj _ -> Left "emit via: sole term parameter must be term-valued"
  let tmDiag = unTerm tm
  if null (dIn tmDiag)
    then Right ()
    else Left "emit via: sole term parameter must be closed"
  sortTy <-
    case dOut tmDiag of
      [outPid] ->
        case diagramPortObj tmDiag outPid of
          Just ty -> Right ty
          Nothing -> Left "emit via: sole term parameter is missing an output sort"
      _ -> Left "emit via: sole term parameter must have exactly one output"
  tmNorm <- normalizeTermDiagram tt (dTmCtx tmDiag) sortTy tm
  lit <-
    case normalizedLiteral tmNorm of
      Just lit -> Right lit
      Nothing -> do
        expr <- diagramToTermExprChecked tt (dTmCtx tmDiag) sortTy tmNorm
        case expr of
          TMLit lit -> Right lit
          _ -> Left "emit via: sole term parameter must normalize to a literal"
  if literalKind lit == expectedKind
    then Right lit
    else Left "emit via: sole term parameter has the wrong literal kind"
  where
    normalizedLiteral (TermDiagram diag) =
      case (dIn diag, dOut diag, IM.elems (dEdges diag)) of
        ([], [outPid], [edge])
          | null (eIns edge)
          , eOuts edge == [outPid] ->
              case ePayload edge of
                PTmLit lit -> Just lit
                _ -> Nothing
        _ -> Nothing
