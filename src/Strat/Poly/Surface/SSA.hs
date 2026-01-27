{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.SSA
  ( elabSSA
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Void (Void)
import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Char (isLower, isAlphaNum)

import Strat.Poly.Doctrine
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr
import Strat.Poly.DSL.AST (RawPolyTypeExpr(..))
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.Diagram
import Strat.Poly.Graph (PortId, addEdgePayload, EdgePayload(..), validateDiagram, emptyDiagram, freshPort, diagramPortType)
import Strat.Poly.UnifyTy


data SSAStmt
  = SSAIn [(Text, RawPolyTypeExpr)]
  | SSAOut [Text]
  | SSAAssign [Text] GenCall
  | SSABox [Text] Text [Text] [SSAStmt]
  deriving (Eq, Show)


data GenCall = GenCall
  { gcName :: Text
  , gcTyArgs :: [RawPolyTypeExpr]
  , gcArgs :: [Text]
  } deriving (Eq, Show)

-- Parser

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

identRaw :: Parser Text
identRaw = lexeme $ do
  c <- letterChar <|> char '_'
  rest <- many (satisfy (\x -> isAlphaNum x || x == '_' ))
  pure (T.pack (c:rest))

ident :: Parser Text
ident = identRaw

commaSep :: Parser a -> Parser [a]
commaSep p = p `sepBy` symbol ","

polyTypeExpr :: Parser RawPolyTypeExpr
polyTypeExpr = lexeme $ do
  name <- identRaw
  case T.uncons name of
    Nothing -> fail "empty type"
    Just (c, _) ->
      if isLower c
        then pure (RPTVar name)
        else do
          mArgs <- optional (symbol "(" *> polyTypeExpr `sepBy` symbol "," <* symbol ")")
          pure (RPTCon name (maybe [] id mArgs))

ssaProgram :: Parser [SSAStmt]
ssaProgram = do
  _ <- symbol "diag"
  ssaBlock

ssaBlock :: Parser [SSAStmt]
ssaBlock = do
  _ <- symbol "{"
  stmts <- many (ssaStmt <* optionalSemi)
  _ <- symbol "}"
  pure stmts

optionalSemi :: Parser ()
optionalSemi = void (optional (symbol ";"))

ssaStmt :: Parser SSAStmt
ssaStmt =
  ssaIn <|> ssaOut <|> try ssaBox <|> ssaAssign

ssaIn :: Parser SSAStmt
ssaIn = do
  _ <- symbol "in"
  items <- commaSep wireDecl
  pure (SSAIn items)
  where
    wireDecl = do
      name <- ident
      _ <- symbol ":"
      ty <- polyTypeExpr
      pure (name, ty)

ssaOut :: Parser SSAStmt
ssaOut = do
  _ <- symbol "out"
  names <- commaSep ident
  pure (SSAOut names)

ssaAssign :: Parser SSAStmt
ssaAssign = do
  outs <- commaSep ident
  _ <- symbol "<-"
  call <- genCall
  pure (SSAAssign outs call)

ssaBox :: Parser SSAStmt
ssaBox = do
  outs <- commaSep ident
  _ <- symbol "<-"
  _ <- symbol "box"
  name <- ident
  _ <- symbol "("
  ins <- commaSep ident
  _ <- symbol ")"
  inner <- ssaBlock
  pure (SSABox outs name ins inner)


genCall :: Parser GenCall
genCall = do
  name <- ident
  tyArgs <- option [] (symbol "{" *> polyTypeExpr `sepBy` symbol "," <* symbol "}")
  _ <- symbol "("
  args <- commaSep ident
  _ <- symbol ")"
  pure GenCall { gcName = name, gcTyArgs = tyArgs, gcArgs = args }

parseSSA :: Text -> Either Text [SSAStmt]
parseSSA input =
  case runParser (sc *> ssaProgram <* eof) "<ssa>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right stmts -> Right stmts

-- Elaboration

elabSSA :: Doctrine -> ModeName -> Text -> Either Text Diagram
elabSSA doc mode src = do
  stmts <- parseSSA src
  diag <- elabSSAStmts doc mode stmts
  validateDiagram diag
  pure diag

elabSSAStmts :: Doctrine -> ModeName -> [SSAStmt] -> Either Text Diagram
elabSSAStmts doc mode stmts = do
  (env, diag, seenIn, seenOut) <- foldl step (Right (M.empty, emptyDiagram mode, False, False)) stmts
  if not seenIn
    then Left "ssa: missing in declaration"
    else if not seenOut
      then Left "ssa: missing out declaration"
      else Right diag
  where
    step acc stmt = do
      (env, diag, seenIn, seenOut) <- acc
      case stmt of
        SSAIn items ->
          if seenIn || not (M.null env)
            then Left "ssa: duplicate in declaration"
            else do
              (ports, diag') <- allocInputs doc mode items diag
              let env' = M.fromList ports
              let diag'' = diag' { dIn = map snd ports }
              pure (env', diag'', True, seenOut)
        SSAAssign outs call -> do
          if seenOut
            then Left "ssa: assignments after out"
            else do
              (diag', env') <- applyCall doc mode env diag outs call
              pure (env', diag', seenIn, seenOut)
        SSABox outs name ins inner -> do
          if seenOut
            then Left "ssa: assignments after out"
            else do
              (diag', env') <- applyBox doc mode env diag outs name ins inner
              pure (env', diag', seenIn, seenOut)
        SSAOut names ->
          if seenOut
            then Left "ssa: duplicate out declaration"
            else do
              ports <- mapM (lookupWire env) names
              let diag' = diag { dOut = ports }
              pure (env, diag', seenIn, True)

allocInputs :: Doctrine -> ModeName -> [(Text, RawPolyTypeExpr)] -> Diagram -> Either Text ([(Text, PortId)], Diagram)
allocInputs doc mode items diag =
  foldl step (Right ([], diag)) items
  where
    step acc (name, rawTy) = do
      (ports, d) <- acc
      ty <- elabType doc mode rawTy
      let (pid, d') = freshPort ty d
      pure (ports <> [(name, pid)], d')

applyCall :: Doctrine -> ModeName -> M.Map Text PortId -> Diagram -> [Text] -> GenCall -> Either Text (Diagram, M.Map Text PortId)
applyCall doc mode env diag outs call = do
  let genName = GenName (gcName call)
  gen <- lookupGen doc mode genName
  let args = gcArgs call
  ins <- mapM (lookupWire env) args
  insTy <- mapM (requirePortType diag) ins
  subst <-
    if null (gcTyArgs call)
      then unifyCtx (gdDom gen) insTy
      else do
        argsTy <- mapM (elabType doc mode) (gcTyArgs call)
        if length argsTy /= length (gdTyVars gen)
          then Left "ssa: generator type argument mismatch"
          else Right (M.fromList (zip (gdTyVars gen) argsTy))
  let dom = applySubstCtx subst (gdDom gen)
  _ <- unifyCtx dom insTy
  let cod = applySubstCtx subst (gdCod gen)
  if length outs /= length cod
    then Left "ssa: output arity mismatch"
    else do
      (outPorts, diag') <- allocPortsLocal cod diag
      diag'' <- addEdgePayload (PGen genName) ins outPorts diag'
      let env' = foldl (\m (n,p) -> M.insert n p m) env (zip outs outPorts)
      pure (diag'', env')

applyBox :: Doctrine -> ModeName -> M.Map Text PortId -> Diagram -> [Text] -> Text -> [Text] -> [SSAStmt] -> Either Text (Diagram, M.Map Text PortId)
applyBox doc mode env diag outs name ins inner = do
  insPorts <- mapM (lookupWire env) ins
  insTy <- mapM (requirePortType diag) insPorts
  innerDiag <- elabSSAStmts doc mode inner
  domInner <- diagramDom innerDiag
  codInner <- diagramCod innerDiag
  _ <- unifyCtx domInner insTy
  if length outs /= length codInner
    then Left "ssa: box output arity mismatch"
    else do
      (outPorts, diag') <- allocPortsLocal codInner diag
      diag'' <- addEdgePayload (PBox (BoxName name) innerDiag) insPorts outPorts diag'
      let env' = foldl (\m (n,p) -> M.insert n p m) env (zip outs outPorts)
      pure (diag'', env')

lookupWire :: M.Map Text PortId -> Text -> Either Text PortId
lookupWire env name =
  case M.lookup name env of
    Nothing -> Left "ssa: unknown wire"
    Just p -> Right p

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "ssa: missing port type"
    Just ty -> Right ty

elabType :: Doctrine -> ModeName -> RawPolyTypeExpr -> Either Text TypeExpr
elabType doc mode expr =
  case expr of
    RPTVar name -> Right (TVar (TyVar name))
    RPTCon name args -> do
      let tname = TypeName name
      arity <- case M.lookup mode (dTypes doc) >>= M.lookup tname of
        Nothing -> Left "ssa: unknown type constructor"
        Just a -> Right a
      if arity /= length args
        then Left "ssa: type constructor arity mismatch"
        else do
          args' <- mapM (elabType doc mode) args
          pure (TCon tname args')

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "ssa: unknown generator"
    Just gd -> Right gd

allocPortsLocal :: Context -> Diagram -> Either Text ([PortId], Diagram)
allocPortsLocal [] diag = Right ([], diag)
allocPortsLocal (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
  in do
    (pids, diag2) <- allocPortsLocal rest diag1
    pure (pid : pids, diag2)
