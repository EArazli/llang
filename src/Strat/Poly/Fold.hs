{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Fold
  ( renderFold
  ) where

import Control.Monad (foldM)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import qualified Data.Graph as G
import qualified Data.IntMap.Strict as IM
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Backend (RuntimeError(..), Value(..))
import Strat.Model.Spec (DefaultBehavior(..), FoldSpec(..), MExpr(..), ModelBackend(..), ModelSpec(..), OpClause(..))
import Strat.Poly.Attr (AttrMap, AttrLit(..), AttrTerm(..), renderAttrVar)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..))
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , PortId(..)
  , getPortLabel
  , renumberDiagram
  )
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr)
import Strat.Poly.TypePretty (renderType)


data FoldCtx = FoldCtx
  { fcDoctrine :: Doctrine
  , fcSpec :: ModelSpec
  , fcFoldSpec :: FoldSpec
  , fcClauses :: M.Map Text OpClause
  }

data RenderBlock = RenderBlock
  { rbInputs :: [Text]
  , rbOutputs :: [Text]
  , rbLines :: [Text]
  , rbPortNames :: M.Map PortId Text
  , rbDiagram :: Diagram
  }

data OpResult
  = OpStmt Text
  | OpExpr Text

renderFold :: Doctrine -> ModelSpec -> Diagram -> Either Text [Value]
renderFold doc spec diag = do
  foldSpec <- case (msBackend spec, msFold spec) of
    (BackendFold, Just fs) -> Right fs
    (BackendFold, Nothing) -> Left "fold: backend fold requires fold block"
    _ -> Left "fold: backend is not fold"
  let ctx =
        FoldCtx
          { fcDoctrine = doc
          , fcSpec = spec
          , fcFoldSpec = foldSpec
          , fcClauses = M.fromList [ (ocOp clause, clause) | clause <- msOps spec ]
          }
  block <- renderBlock ctx "" Nothing Nothing diag
  returnLines <- renderReturn ctx block
  (openLine, closeLine) <-
    if null (rbInputs block)
      then do
        open <- evalHook foldSpec "prologue_closed" []
        close <- evalHook foldSpec "epilogue_closed" []
        pure (open, close)
      else do
        paramDecls <- renderDeclList (rbDiagram block) (rbPortNames block) (dIn (rbDiagram block))
        let params = T.intercalate ", " (rbInputs block)
        open <- evalHook foldSpec "prologue_open" [VString params, VString paramDecls]
        close <- evalHook foldSpec "epilogue_open" []
        pure (open, close)
  let output =
        wrapBlock
          (fsIndent foldSpec)
          openLine
          closeLine
          (rbLines block <> returnLines)
  pure [VString output]

renderBlock :: FoldCtx -> Text -> Maybe [Text] -> Maybe [Text] -> Diagram -> Either Text RenderBlock
renderBlock ctx namePrefix mBoundaryInputs mBoundaryOutputs diag0 = do
  diag <- renumberDiagram diag0
  fixedInputNames <- case mBoundaryInputs of
    Nothing -> Right M.empty
    Just inputNames ->
      if length inputNames == length (dIn diag)
        then Right (M.fromList (zip (dIn diag) inputNames))
        else Left "fold_ssa: box boundary mismatch"
  fixedOutputNames <- case mBoundaryOutputs of
    Nothing -> Right M.empty
    Just outputNames ->
      if length outputNames == length (dOut diag)
        then Right (M.fromList (zip (dOut diag) outputNames))
        else Left "fold_ssa: box boundary mismatch"
  fixedNames <- mergeFixedNames fixedInputNames fixedOutputNames
  portNames <- assignPortNames namePrefix (fsReserved (fcFoldSpec ctx)) diag fixedNames
  edges <- edgeOrder diag
  linesOut <- fmap concat (mapM (renderEdge ctx namePrefix diag (dMode diag) portNames) edges)
  inNames <- mapM (lookupPortName portNames) (dIn diag)
  outNames <- mapM (lookupPortName portNames) (dOut diag)
  pure
    RenderBlock
      { rbInputs = inNames
      , rbOutputs = outNames
      , rbLines = linesOut
      , rbPortNames = portNames
      , rbDiagram = diag
      }

mergeFixedNames :: M.Map PortId Text -> M.Map PortId Text -> Either Text (M.Map PortId Text)
mergeFixedNames left right = foldM step left (M.toList right)
  where
    step acc (pid, name) =
      case M.lookup pid acc of
        Nothing -> Right (M.insert pid name acc)
        Just oldName ->
          if oldName == name
            then Right acc
            else Left "fold_ssa: box boundary mismatch"

renderReturn :: FoldCtx -> RenderBlock -> Either Text [Text]
renderReturn ctx block = do
  let foldSpec = fcFoldSpec ctx
  let diag = rbDiagram block
  case dOut diag of
    [] -> do
      ret <- evalHook foldSpec "return0" []
      pure (if T.null ret then [] else splitLines ret)
    [pid] -> do
      out <- lookupPortName (rbPortNames block) pid
      ty <- lookupPortTypeText diag pid
      ret <- evalHook foldSpec "return1" [VString out, VString ty]
      pure (if T.null ret then [] else splitLines ret)
    pids -> do
      outs <- mapM (lookupPortName (rbPortNames block)) pids
      decls <- renderDeclList diag (rbPortNames block) pids
      let outsCsv = T.intercalate ", " outs
      ret <- evalHook foldSpec "returnN" [VString outsCsv, VString decls]
      pure (if T.null ret then [] else splitLines ret)

renderEdge :: FoldCtx -> Text -> Diagram -> ModeName -> M.Map PortId Text -> Edge -> Either Text [Text]
renderEdge ctx namePrefix diag mode portNames edge =
  case ePayload edge of
    PGen gen attrs -> renderGenEdge ctx diag mode portNames gen attrs (eIns edge) (eOuts edge)
    PBox _ inner -> do
      innerInputs <- mapM (lookupPortName portNames) (eIns edge)
      innerOutputs <- mapM (lookupPortName portNames) (eOuts edge)
      innerBlock <- renderBlock ctx (namePrefix <> "__b" <> renderEdgeId (eId edge) <> "_") (Just innerInputs) (Just innerOutputs) inner
      pure (rbLines innerBlock)

renderGenEdge
  :: FoldCtx
  -> Diagram
  -> ModeName
  -> M.Map PortId Text
  -> GenName
  -> AttrMap
  -> [PortId]
  -> [PortId]
  -> Either Text [Text]
renderGenEdge ctx diag mode portNames gen attrs ins outs = do
  inputNames <- mapM (lookupPortName portNames) ins
  outputNames <- mapM (lookupPortName portNames) outs
  genDecl <- lookupGenDecl (fcDoctrine ctx) mode gen
  attrVals <- evalAttrValues genDecl attrs
  let args = attrVals <> map VString inputNames
  opResult <- renderOpResult ctx gen args (length outputNames)
  let foldSpec = fcFoldSpec ctx
  case (opResult, outs) of
    (OpStmt stmt, []) -> do
      bound <- evalHook foldSpec "bind0" [VString stmt]
      pure (concatMap splitLines [bound])
    (OpExpr expr, [pid]) -> do
      out <- lookupPortName portNames pid
      ty <- lookupPortTypeText diag pid
      bound <- evalHook foldSpec "bind1" [VString out, VString ty, VString expr]
      pure (concatMap splitLines [bound])
    (OpExpr expr, pids) -> do
      decls <- renderDeclList diag portNames pids
      let outsCsv = T.intercalate ", " outputNames
      bound <- evalHook foldSpec "bindN" [VString outsCsv, VString decls, VString expr]
      pure (concatMap splitLines [bound])
    (OpStmt _, _) ->
      Left ("fold: op " <> renderGen gen <> " must return a string expression")

renderOpResult :: FoldCtx -> GenName -> [Value] -> Int -> Either Text OpResult
renderOpResult ctx gen args codArity =
  case M.lookup (renderGen gen) (fcClauses ctx) of
    Just clause -> do
      val <- evalClause clause args
      case (codArity, val) of
        (0, VString stmt) -> Right (OpStmt stmt)
        (0, _) -> Left ("fold: op " <> renderGen gen <> " must return a string statement")
        (_, VString expr) ->
          if T.any (== '\n') expr
            then Left "fold_ssa: expression contains newline"
            else Right (OpExpr expr)
        (_, _) -> Left ("fold: op " <> renderGen gen <> " must return a string expression")
    Nothing ->
      case msDefault (fcSpec ctx) of
        DefaultError msg -> Left msg
        DefaultSymbolic -> do
          call <- renderSymbolicCall gen args
          if codArity == 0
            then Right (OpStmt (call <> ";"))
            else Right (OpExpr call)

renderSymbolicCall :: GenName -> [Value] -> Either Text Text
renderSymbolicCall gen args = do
  renderedArgs <- mapM (renderSymbolicArg gen) args
  pure (renderGen gen <> "(" <> T.intercalate ", " renderedArgs <> ")")

renderSymbolicArg :: GenName -> Value -> Either Text Text
renderSymbolicArg gen value =
  case value of
    VString s -> Right s
    VInt n -> Right (T.pack (show n))
    VBool True -> Right "true"
    VBool False -> Right "false"
    VAtom atom -> Right atom
    VList _ ->
      Left ("fold_ssa: symbolic default cannot render list-valued argument for " <> renderGen gen)

edgeOrder :: Diagram -> Either Text [Edge]
edgeOrder diag =
  let comps =
        G.stronglyConnComp
          [ (edge, eId edge, deps edge)
          | edge <- IM.elems (dEdges diag)
          ]
  in if any isCycle comps
      then Left "fold_ssa: cyclic diagrams are not supported"
      else Right [ edge | G.AcyclicSCC edge <- comps ]
  where
    deps edge =
      [ eid
      | port <- eIns edge
      , Just (Just eid) <- [IM.lookup (portKey port) (dProd diag)]
      ]
    isCycle comp =
      case comp of
        G.CyclicSCC _ -> True
        G.AcyclicSCC _ -> False

assignPortNames :: Text -> S.Set Text -> Diagram -> M.Map PortId Text -> Either Text (M.Map PortId Text)
assignPortNames namePrefix reserved diag fixedNames = do
  let portIds = [ PortId k | k <- IM.keys (dPortTy diag) ]
  let baseName pid@(PortId n) =
        case getPortLabel diag pid of
          Just lbl -> sanitizeIdent reserved lbl n
          Nothing -> "p" <> T.pack (show n)
  let candidates =
        [ (pid, namePrefix <> baseName pid)
        | pid <- portIds
        , M.notMember pid fixedNames
        ]
  allocateNames namePrefix fixedNames candidates

allocateNames
  :: Text
  -> M.Map PortId Text
  -> [(PortId, Text)]
  -> Either Text (M.Map PortId Text)
allocateNames _ fixedNames candidates = do
  let fixedVals = M.elems fixedNames
  if length fixedVals /= S.size (S.fromList fixedVals)
    then Left "fold_ssa: fixed boundary names are not unique"
    else pure ()
  let sorted = sortOn (portKey . fst) candidates
  (_, names) <- foldM assignOne (S.fromList fixedVals, fixedNames) sorted
  pure names
  where
    assignOne (used, names) (pid, cand) = do
      chosen <- chooseUnique used pid cand
      let used' = S.insert chosen used
      let names' = M.insert pid chosen names
      pure (used', names')
    chooseUnique used pid cand
      | cand `S.notMember` used = Right cand
      | otherwise =
          let seed = cand <> "_" <> T.pack (show (portKey pid))
          in if seed `S.notMember` used
              then Right seed
              else trySuffix seed 0
      where
        trySuffix base k =
          let candidate = base <> "_" <> T.pack (show k)
          in if candidate `S.notMember` used
              then Right candidate
              else trySuffix base (k + 1)

sanitizeIdent :: S.Set Text -> Text -> Int -> Text
sanitizeIdent reserved name fallbackN =
  let replaced = T.map sanitizeChar name
      nonEmpty =
        if T.null replaced
          then fallbackName fallbackN
          else replaced
      noLeadingDigit =
        case T.uncons nonEmpty of
          Just (c, _) | isDigit c -> "_" <> nonEmpty
          _ -> nonEmpty
  in if noLeadingDigit `S.member` reserved then "_" <> noLeadingDigit else noLeadingDigit
  where
    sanitizeChar c =
      if isAsciiLower c || isAsciiUpper c || isDigit c || c == '_'
        then c
        else '_'
    fallbackName n = "p" <> T.pack (show n)

portKey :: PortId -> Int
portKey (PortId k) = k

splitLines :: Text -> [Text]
splitLines t =
  case T.splitOn "\n" t of
    [] -> []
    xs -> xs

lookupPortName :: M.Map PortId Text -> PortId -> Either Text Text
lookupPortName names pid =
  case M.lookup pid names of
    Nothing -> Left "fold: missing port name"
    Just name -> Right name

lookupPortTypeText :: Diagram -> PortId -> Either Text Text
lookupPortTypeText diag pid = renderType <$> lookupPortType diag pid

lookupPortType :: Diagram -> PortId -> Either Text TypeExpr
lookupPortType diag (PortId k) =
  case IM.lookup k (dPortTy diag) of
    Nothing -> Left "fold: missing port type"
    Just ty -> Right ty

renderDeclList :: Diagram -> M.Map PortId Text -> [PortId] -> Either Text Text
renderDeclList diag names pids = do
  decls <- mapM (renderDecl diag names) pids
  pure (T.intercalate ", " decls)

renderDecl :: Diagram -> M.Map PortId Text -> PortId -> Either Text Text
renderDecl diag names pid = do
  ty <- lookupPortTypeText diag pid
  nm <- lookupPortName names pid
  pure (ty <> " " <> nm)

lookupGenDecl :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGenDecl doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "fold: unknown generator"
    Just gd -> Right gd

renderGen :: GenName -> Text
renderGen (GenName t) = t

renderEdgeId :: EdgeId -> Text
renderEdgeId (EdgeId n) = T.pack (show n)

evalAttrValues :: GenDecl -> AttrMap -> Either Text [Value]
evalAttrValues gen attrs = mapM fieldValue (gdAttrs gen)
  where
    fieldValue (field, _) =
      case M.lookup field attrs of
        Nothing -> Left "poly eval: missing attribute value"
        Just term -> attrTermToValue term

attrTermToValue :: AttrTerm -> Either Text Value
attrTermToValue term =
  case term of
    ATLit lit ->
      case lit of
        ALInt n -> Right (VInt n)
        ALString s -> Right (VString s)
        ALBool b -> Right (VBool b)
    ATVar v ->
      Right (VAtom (renderAttrVar v))

evalHook :: FoldSpec -> Text -> [Value] -> Either Text Text
evalHook foldSpec name args =
  case M.lookup name (fsHooks foldSpec) of
    Nothing -> Left ("fold: missing hook " <> name)
    Just clause ->
      if length (ocArgs clause) /= length args
        then Left ("fold: hook " <> name <> " arity mismatch")
        else do
          value <- evalClause clause args
          case value of
            VString s -> Right s
            _ -> Left ("fold: hook " <> name <> " did not return string")

evalClause :: OpClause -> [Value] -> Either Text Value
evalClause clause args =
  let env = M.fromList (zip (ocArgs clause) args)
  in case evalExpr env (ocExpr clause) of
      Left (RuntimeError msg) -> Left msg
      Right v -> Right v

evalExpr :: M.Map Text Value -> MExpr -> Either RuntimeError Value
evalExpr env expr =
  case expr of
    MVar name ->
      case M.lookup name env of
        Just v -> Right v
        Nothing -> Left (RuntimeError ("unknown variable: " <> name))
    MInt n -> Right (VInt n)
    MString s -> Right (VString s)
    MBool b -> Right (VBool b)
    MList xs -> VList <$> mapM (evalExpr env) xs
    MIf c t e -> do
      cv <- evalExpr env c
      case cv of
        VBool True -> evalExpr env t
        VBool False -> evalExpr env e
        _ -> Left (RuntimeError "if condition must be bool")
    MBinOp op a b -> do
      av <- evalExpr env a
      bv <- evalExpr env b
      evalBinOp op av bv

evalBinOp :: Text -> Value -> Value -> Either RuntimeError Value
evalBinOp op a b =
  case op of
    "+" -> binInt (+)
    "*" -> binInt (*)
    "++" -> binConcat
    "==" -> Right (VBool (a == b))
    _ -> Left (RuntimeError ("unknown operator: " <> op))
  where
    binInt f =
      case (a, b) of
        (VInt x, VInt y) -> Right (VInt (f x y))
        _ -> Left (RuntimeError "expected int operands")
    binConcat =
      case (a, b) of
        (VString x, VString y) -> Right (VString (x <> y))
        (VList xs, VList ys) -> Right (VList (xs <> ys))
        _ -> Left (RuntimeError "expected string or list operands")

wrapBlock :: Text -> Text -> Text -> [Text] -> Text
wrapBlock indent openLine closeLine bodyLines =
  let openLines = splitLines openLine
      closeLines = splitLines closeLine
      physicalBody = concatMap splitLines bodyLines
      indentedBody = map (indent <>) physicalBody
      full =
        if null physicalBody
          then openLines <> closeLines
          else openLines <> indentedBody <> closeLines
  in T.intercalate "\n" full
