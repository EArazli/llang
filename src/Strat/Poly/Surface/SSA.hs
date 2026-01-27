{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.SSA
  ( elabSSA
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
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
import Strat.Poly.Graph (PortId, addEdgePayload, EdgePayload(..), validateDiagram, emptyDiagram, freshPort)
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

data Wire = Wire
  { wName :: Text
  , wPort :: PortId
  , wType :: TypeExpr
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
  mArgs <- optional (symbol "(" *> polyTypeExpr `sepBy` symbol "," <* symbol ")")
  case T.uncons name of
    Nothing -> fail "empty type"
    Just (c, _) ->
      case mArgs of
        Just args -> pure (RPTCon name args)
        Nothing ->
          if isLower c
            then pure (RPTVar name)
            else pure (RPTCon name [])

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
  (ctx, diag, seenIn, seenOut) <- foldl step (Right ([], emptyDiagram mode, False, False)) stmts
  if not seenIn
    then Left "ssa: missing in declaration"
    else if not seenOut
      then Left "ssa: missing out declaration"
      else Right diag
  where
    step acc stmt = do
      (ctx, diag, seenIn, seenOut) <- acc
      case stmt of
        SSAIn items ->
          if seenIn || not (null ctx)
            then Left "ssa: duplicate in declaration"
            else do
              ensureUnique "ssa: duplicate input declaration" (map fst items)
              (wires, diag') <- allocInputs doc mode items diag
              let diag'' = diag' { dIn = map wPort wires }
              pure (wires, diag'', True, seenOut)
        SSAAssign outs call ->
          if seenOut
            then Left "ssa: assignments after out"
            else do
              (diag', ctx') <- applyCall doc mode ctx diag outs call
              pure (ctx', diag', seenIn, seenOut)
        SSABox outs name ins inner -> do
          if seenOut
            then Left "ssa: assignments after out"
            else do
              (diag', ctx') <- applyBox doc mode ctx diag outs name ins inner
              pure (ctx', diag', seenIn, seenOut)
        SSAOut names ->
          if seenOut
            then Left "ssa: duplicate out declaration"
            else do
              ensureOutOrder ctx names
              let diag' = diag { dOut = map wPort ctx }
              pure (ctx, diag', seenIn, True)

allocInputs :: Doctrine -> ModeName -> [(Text, RawPolyTypeExpr)] -> Diagram -> Either Text ([Wire], Diagram)
allocInputs doc mode items diag =
  foldl step (Right ([], diag)) items
  where
    step acc (name, rawTy) = do
      (wires, d) <- acc
      ty <- elabType doc mode rawTy
      let (pid, d') = freshPort ty d
      pure (wires <> [Wire name pid ty], d')

applyCall :: Doctrine -> ModeName -> [Wire] -> Diagram -> [Text] -> GenCall -> Either Text (Diagram, [Wire])
applyCall doc mode ctx diag outs call = do
  ensureUnique "ssa: duplicate output name" outs
  let genName = GenName (gcName call)
  gen <- lookupGen doc mode genName
  let args = gcArgs call
  ensureUnique "ssa: duplicate input name" args
  (idx, slice) <- findSlice ctx args
  let ins = map wPort slice
  let insTy = map wType slice
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
      let outWires = zipWith3 Wire outs outPorts cod
      let (before, rest) = splitAt idx ctx
      let after = drop (length args) rest
      ensureFreshOutputs outs before after
      let ctx' = before <> outWires <> after
      pure (diag'', ctx')

applyBox :: Doctrine -> ModeName -> [Wire] -> Diagram -> [Text] -> Text -> [Text] -> [SSAStmt] -> Either Text (Diagram, [Wire])
applyBox doc mode ctx diag outs name ins inner = do
  ensureUnique "ssa: duplicate output name" outs
  ensureUnique "ssa: duplicate input name" ins
  (idx, slice) <- findSlice ctx ins
  let insPorts = map wPort slice
  let insTy = map wType slice
  innerDiag <- elabSSAStmts doc mode inner
  domInner <- diagramDom innerDiag
  codInner <- diagramCod innerDiag
  _ <- unifyCtx domInner insTy
  if length outs /= length codInner
    then Left "ssa: box output arity mismatch"
    else do
      (outPorts, diag') <- allocPortsLocal codInner diag
      diag'' <- addEdgePayload (PBox (BoxName name) innerDiag) insPorts outPorts diag'
      let outWires = zipWith3 Wire outs outPorts codInner
      let (before, rest) = splitAt idx ctx
      let after = drop (length ins) rest
      ensureFreshOutputs outs before after
      let ctx' = before <> outWires <> after
      pure (diag'', ctx')

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

ensureUnique :: Text -> [Text] -> Either Text ()
ensureUnique msg names =
  let dup = findDup names
  in case dup of
    Nothing -> Right ()
    Just _ -> Left msg
  where
    findDup xs = go S.empty xs
    go _ [] = Nothing
    go seen (x:rest)
      | x `S.member` seen = Just x
      | otherwise = go (S.insert x seen) rest

ensureFreshOutputs :: [Text] -> [Wire] -> [Wire] -> Either Text ()
ensureFreshOutputs outs before after =
  let existing = S.fromList (map wName (before <> after))
  in if any (`S.member` existing) outs
    then Left "ssa: output name already in use"
    else Right ()

ensureOutOrder :: [Wire] -> [Text] -> Either Text ()
ensureOutOrder ctx names =
  let ctxNames = map wName ctx
      ctxSet = S.fromList ctxNames
      nameSet = S.fromList names
  in if any (`S.notMember` ctxSet) names
    then Left "ssa: unknown wire in out"
    else if length names /= length ctxNames
      then Left "ssa: out must list all remaining wires"
      else if names /= ctxNames
        then Left "ssa: out must preserve order (use swap)"
        else Right ()

findSlice :: [Wire] -> [Text] -> Either Text (Int, [Wire])
findSlice ctx names
  | null names = Right (length ctx, [])
  | otherwise = do
      idxs <- mapM (indexOf ctx) names
      let start = head idxs
      let expected = [start .. start + length names - 1]
      if idxs == expected
        then Right (start, take (length names) (drop start ctx))
        else Left "ssa: inputs must be contiguous and ordered"
  where
    indexOf ctx' name =
      case findIndex ((== name) . wName) ctx' of
        Nothing -> Left "ssa: unknown wire"
        Just i -> Right i

findIndex :: (a -> Bool) -> [a] -> Maybe Int
findIndex p = go 0
  where
    go _ [] = Nothing
    go i (x:xs)
      | p x = Just i
      | otherwise = go (i + 1) xs
