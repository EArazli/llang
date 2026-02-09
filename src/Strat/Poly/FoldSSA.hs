{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.FoldSSA
  ( renderFoldSSA
  ) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Graph as G
import Strat.Backend (RuntimeError(..), Value(..))
import Strat.Model.Spec (DefaultBehavior(..), MExpr(..), ModelSpec(..), OpClause(..))
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
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))


data FoldCtx = FoldCtx
  { fcDoctrine :: Doctrine
  , fcSpec :: ModelSpec
  , fcClauses :: M.Map Text OpClause
  }

data RenderBlock = RenderBlock
  { rbInputs :: [Text]
  , rbOutputs :: [Text]
  , rbLines :: [Text]
  , rbPortNames :: M.Map PortId Text
  }

data OpResult
  = OpStmt Text
  | OpExpr Text

renderFoldSSA :: Doctrine -> ModelSpec -> Diagram -> Either Text [Value]
renderFoldSSA doc spec diag = do
  let ctx =
        FoldCtx
          { fcDoctrine = doc
          , fcSpec = spec
          , fcClauses = M.fromList [ (ocOp clause, clause) | clause <- msClauses spec ]
          }
  block <- renderBlock ctx "" Nothing diag
  let bodyLines = rbLines block <> renderReturn (rbOutputs block)
  let output =
        if null (rbInputs block)
          then wrapBlock "(() => {" "})()" bodyLines
          else
            wrapBlock
              ("(" <> T.intercalate ", " (rbInputs block) <> ") => {")
              "}"
              bodyLines
  pure [VString output]

renderBlock :: FoldCtx -> Text -> Maybe [Text] -> Diagram -> Either Text RenderBlock
renderBlock ctx namePrefix mBoundaryInputs diag0 = do
  diag <- renumberDiagram diag0
  fixedNames <- case mBoundaryInputs of
    Nothing -> Right M.empty
    Just inputNames ->
      if length inputNames == length (dIn diag)
        then Right (M.fromList (zip (dIn diag) inputNames))
        else Left "fold_ssa: box boundary mismatch"
  portNames <- assignPortNames namePrefix diag fixedNames
  edges <- edgeOrder diag
  linesOut <- fmap concat (mapM (renderEdge ctx namePrefix (dMode diag) portNames) edges)
  inNames <- mapM (lookupPortName portNames) (dIn diag)
  outNames <- mapM (lookupPortName portNames) (dOut diag)
  pure
    RenderBlock
      { rbInputs = inNames
      , rbOutputs = outNames
      , rbLines = linesOut
      , rbPortNames = portNames
      }

renderReturn :: [Text] -> [Text]
renderReturn outs =
  case outs of
    [] -> []
    [out] -> ["return " <> out <> ";"]
    _ -> ["return [" <> T.intercalate ", " outs <> "];"]

renderEdge :: FoldCtx -> Text -> ModeName -> M.Map PortId Text -> Edge -> Either Text [Text]
renderEdge ctx namePrefix mode portNames edge =
  case ePayload edge of
    PGen gen attrs -> renderGenEdge ctx mode portNames gen attrs (eIns edge) (eOuts edge)
    PBox _ inner -> do
      innerInputs <- mapM (lookupPortName portNames) (eIns edge)
      innerBlock <- renderBlock ctx (namePrefix <> "__b" <> renderEdgeId (eId edge) <> "_") (Just innerInputs) inner
      outerOuts <- mapM (lookupPortName portNames) (eOuts edge)
      if length outerOuts /= length (rbOutputs innerBlock)
        then Left "fold_ssa: box boundary mismatch"
        else do
          let aliases =
                zipWith
                  (\outerOut innerOut -> "const " <> outerOut <> " = " <> innerOut <> ";")
                  outerOuts
                  (rbOutputs innerBlock)
          pure (rbLines innerBlock <> aliases)

renderGenEdge
  :: FoldCtx
  -> ModeName
  -> M.Map PortId Text
  -> GenName
  -> AttrMap
  -> [PortId]
  -> [PortId]
  -> Either Text [Text]
renderGenEdge ctx mode portNames gen attrs ins outs = do
  inputNames <- mapM (lookupPortName portNames) ins
  outputNames <- mapM (lookupPortName portNames) outs
  genDecl <- lookupGenDecl (fcDoctrine ctx) mode gen
  attrVals <- evalAttrValues genDecl attrs
  let args = attrVals <> map VString inputNames
  opResult <- renderOpResult ctx gen args (length outputNames)
  case (opResult, outputNames) of
    (OpStmt stmt, []) -> Right [stmt]
    (OpExpr expr, [out]) -> Right ["const " <> out <> " = " <> expr <> ";"]
    (OpExpr expr, _) ->
      Right ["const [" <> T.intercalate ", " outputNames <> "] = " <> expr <> ";"]
    (OpStmt _, _) ->
      Left ("fold_ssa: op " <> renderGen gen <> " must return a string expression")

renderOpResult :: FoldCtx -> GenName -> [Value] -> Int -> Either Text OpResult
renderOpResult ctx gen args codArity =
  case M.lookup (renderGen gen) (fcClauses ctx) of
    Just clause -> do
      val <- evalClause clause args
      case (codArity, val) of
        (0, VString stmt) -> Right (OpStmt stmt)
        (0, _) -> Left ("fold_ssa: op " <> renderGen gen <> " must return a string statement")
        (_, VString expr) -> Right (OpExpr expr)
        (_, _) -> Left ("fold_ssa: op " <> renderGen gen <> " must return a string expression")
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
    portKey (PortId k) = k
    isCycle comp =
      case comp of
        G.CyclicSCC _ -> True
        G.AcyclicSCC _ -> False

assignPortNames :: Text -> Diagram -> M.Map PortId Text -> Either Text (M.Map PortId Text)
assignPortNames namePrefix diag fixedNames = do
  let portIds = [ PortId k | k <- IM.keys (dPortTy diag) ]
  let baseName pid@(PortId n) =
        case getPortLabel diag pid of
          Just lbl -> sanitizeIdent lbl n
          Nothing -> "p" <> T.pack (show n)
  let namedPorts = [ (pid, baseName pid) | pid <- portIds, M.notMember pid fixedNames ]
  let counts = M.fromListWith (+) [ (base, 1 :: Int) | (_, base) <- namedPorts ]
  let chooseName (pid@(PortId n), base) =
        let nameNoPrefix =
              if M.findWithDefault 0 base counts > 1
                then base <> "_" <> T.pack (show n)
                else base
        in (pid, namePrefix <> nameNoPrefix)
  pure (M.union fixedNames (M.fromList (map chooseName namedPorts)))

sanitizeIdent :: Text -> Int -> Text
sanitizeIdent name fallbackN =
  let replaced = T.map sanitizeChar name
      nonEmpty =
        if T.null replaced
          then fallbackName fallbackN
          else replaced
      noLeadingDigit =
        case T.uncons nonEmpty of
          Just (c, _) | isDigit c -> "_" <> nonEmpty
          _ -> nonEmpty
      reserved = if noLeadingDigit `S.member` jsReservedWords then "_" <> noLeadingDigit else noLeadingDigit
  in reserved
  where
    sanitizeChar c =
      if isAsciiLower c || isAsciiUpper c || isDigit c || c == '_'
        then c
        else '_'
    fallbackName n = "p" <> T.pack (show n)

jsReservedWords :: S.Set Text
jsReservedWords =
  S.fromList
    [ "await"
    , "break"
    , "case"
    , "catch"
    , "class"
    , "const"
    , "continue"
    , "debugger"
    , "default"
    , "delete"
    , "do"
    , "else"
    , "enum"
    , "export"
    , "extends"
    , "false"
    , "finally"
    , "for"
    , "function"
    , "if"
    , "implements"
    , "import"
    , "in"
    , "instanceof"
    , "interface"
    , "let"
    , "new"
    , "null"
    , "package"
    , "private"
    , "protected"
    , "public"
    , "return"
    , "super"
    , "switch"
    , "static"
    , "this"
    , "throw"
    , "try"
    , "true"
    , "typeof"
    , "var"
    , "void"
    , "while"
    , "with"
    , "yield"
    ]

lookupPortName :: M.Map PortId Text -> PortId -> Either Text Text
lookupPortName names pid =
  case M.lookup pid names of
    Nothing -> Left "fold_ssa: missing port name"
    Just name -> Right name

lookupGenDecl :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGenDecl doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "fold_ssa: unknown generator"
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

wrapBlock :: Text -> Text -> [Text] -> Text
wrapBlock openLine closeLine bodyLines =
  case bodyLines of
    [] -> openLine <> "\n" <> closeLine
    _ ->
      openLine
        <> "\n"
        <> T.intercalate "\n" (map ("  " <>) bodyLines)
        <> "\n"
        <> closeLine
