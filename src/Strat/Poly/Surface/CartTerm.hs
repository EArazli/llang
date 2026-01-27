{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.CartTerm
  ( builtinSurface
  , elabCartTerm
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
import Control.Monad.Combinators.Expr (makeExprParser)

import Strat.Poly.Surface (PolySurfaceDef(..), PolySurfaceKind(..))
import Strat.Poly.Doctrine
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr
import Strat.Poly.DSL.AST (RawPolyTypeExpr(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram
import Strat.Poly.Graph (PortId, addEdgePayload, EdgePayload(..), emptyDiagram, freshPort, diagramPortType, validateDiagram)
import Strat.Poly.UnifyTy


data Term = Term Text [Term] deriving (Eq, Show)

data Program = Program
  { progInputs :: [(Text, RawPolyTypeExpr)]
  , progTerm :: Term
  } deriving (Eq, Show)

-- built-in surface marker

builtinSurface :: PolySurfaceDef
builtinSurface = PolySurfaceDef
  { psName = "CartTermSurface"
  , psDoctrine = ""
  , psMode = ModeName ""
  , psKind = SurfaceCartTerm
  }

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

programParser :: Parser Program
programParser = do
  _ <- symbol "term"
  _ <- symbol "{"
  inputs <- termIn
  _ <- optionalSemi
  term <- termOut
  _ <- optionalSemi
  _ <- symbol "}"
  pure Program { progInputs = inputs, progTerm = term }

optionalSemi :: Parser ()
optionalSemi = void (optional (symbol ";"))

termIn :: Parser [(Text, RawPolyTypeExpr)]
termIn = do
  _ <- symbol "in"
  commaSep wireDecl
  where
    wireDecl = do
      name <- ident
      _ <- symbol ":"
      ty <- polyTypeExpr
      pure (name, ty)

termOut :: Parser Term
termOut = do
  _ <- symbol "out"
  termExpr

termExpr :: Parser Term
termExpr = makeExprParser termAtom []

termAtom :: Parser Term
termAtom =
  parens termExpr <|> termApp

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

termApp :: Parser Term
termApp = do
  name <- ident
  mArgs <- optional (symbol "(" *> termExpr `sepBy` symbol "," <* symbol ")")
  pure (Term name (maybe [] id mArgs))

parseProgram :: Text -> Either Text Program
parseProgram input =
  case runParser (sc *> programParser <* eof) "<term>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right prog -> Right prog

-- Elaboration

elabCartTerm :: Doctrine -> ModeName -> Text -> Either Text Diagram
elabCartTerm doc mode src = do
  prog <- parseProgram src
  let ctxNames = map fst (progInputs prog)
  let counts = countVars (S.fromList ctxNames) (progTerm prog)
  let unknown = S.difference (S.fromList (M.keys counts)) (S.fromList ctxNames)
  if S.null unknown then Right () else Left "cart: unknown variable"
  inputs <- mapM (elabInput doc mode) (progInputs prog)
  let (ports, diag0) = allocPortsFrom inputs (emptyDiagram mode)
  let env0 = M.fromList [ (name, VarState pid ty (M.findWithDefault 0 name counts)) | (name, ty, pid) <- zip3 (map fst inputs) (map snd inputs) ports ]
  (diag1, env1, outPort) <- compileTerm doc mode env0 diag0 (progTerm prog)
  diag2 <- dropUnused doc mode env1 diag1
  let diag3 = diag2 { dIn = ports, dOut = [outPort] }
  validateDiagram diag3
  pure diag3

elabInput :: Doctrine -> ModeName -> (Text, RawPolyTypeExpr) -> Either Text (Text, TypeExpr)
elabInput doc mode (name, rawTy) = do
  ty <- elabType doc mode rawTy
  pure (name, ty)

elabType :: Doctrine -> ModeName -> RawPolyTypeExpr -> Either Text TypeExpr
elabType doc mode expr =
  case expr of
    RPTVar name -> Right (TVar (TyVar name))
    RPTCon name args -> do
      let tname = TypeName name
      arity <- case M.lookup mode (dTypes doc) >>= M.lookup tname of
        Nothing -> Left "cart: unknown type constructor"
        Just a -> Right a
      if arity /= length args
        then Left "cart: type constructor arity mismatch"
        else do
          args' <- mapM (elabType doc mode) args
          pure (TCon tname args')

allocPortsFrom :: [(Text, TypeExpr)] -> Diagram -> ([PortId], Diagram)
allocPortsFrom items diag =
  foldl step ([], diag) items
  where
    step (ports, d) (_, ty) =
      let (pid, d') = freshPort ty d
      in (ports <> [pid], d')

-- Term compilation

data VarState = VarState
  { vsPort :: PortId
  , vsType :: TypeExpr
  , vsRemaining :: Int
  } deriving (Eq, Show)

compileTerm :: Doctrine -> ModeName -> M.Map Text VarState -> Diagram -> Term -> Either Text (Diagram, M.Map Text VarState, PortId)
compileTerm doc mode env diag term =
  case term of
    Term name args
      | null args && M.member name env -> useVar doc mode env diag name
      | otherwise -> do
          gen <- lookupGen doc mode (GenName name)
          (diag', env', argPorts) <- compileArgs doc mode env diag args
          argTypes <- mapM (requirePortType diag') argPorts
          subst <- unifyCtx (gdDom gen) argTypes
          let cod = applySubstCtx subst (gdCod gen)
          if length cod /= 1
            then Left "cart: generator must have single output"
            else do
              let (outPort, diag'') = freshPort (head cod) diag'
              diag''' <- addEdgePayload (PGen (GenName name)) argPorts [outPort] diag''
              pure (diag''', env', outPort)

compileArgs :: Doctrine -> ModeName -> M.Map Text VarState -> Diagram -> [Term] -> Either Text (Diagram, M.Map Text VarState, [PortId])
compileArgs _ _ env diag [] = Right (diag, env, [])
compileArgs doc mode env diag (t:ts) = do
  (diag', env', p) <- compileTerm doc mode env diag t
  (diag'', env'', ps) <- compileArgs doc mode env' diag' ts
  pure (diag'', env'', p:ps)

useVar :: Doctrine -> ModeName -> M.Map Text VarState -> Diagram -> Text -> Either Text (Diagram, M.Map Text VarState, PortId)
useVar doc mode env diag name =
  case M.lookup name env of
    Nothing -> Left "cart: unknown variable"
    Just st ->
      case vsRemaining st of
        0 -> Left "cart: variable not in scope"
        1 -> Right (diag, M.delete name env, vsPort st)
        n -> do
          dup <- lookupGen doc mode (GenName "dup")
          (p1, p2, diag') <- dupPort diag dup (vsPort st) (vsType st)
          let env' = M.insert name st { vsPort = p2, vsRemaining = n - 1 } env
          pure (diag', env', p1)

-- create a dup edge that splits a port

dupPort :: Diagram -> GenDecl -> PortId -> TypeExpr -> Either Text (PortId, PortId, Diagram)
dupPort diag dupGen inPort ty = do
  ensureDupShape dupGen
  let (p1, diag1) = freshPort ty diag
  let (p2, diag2) = freshPort ty diag1
  diag3 <- addEdgePayload (PGen (gdName dupGen)) [inPort] [p1, p2] diag2
  pure (p1, p2, diag3)

ensureDupShape :: GenDecl -> Either Text ()
ensureDupShape gen =
  case (gdDom gen, gdCod gen) of
    ([TVar v1], [TVar v2, TVar v3])
      | v1 == v2 && v1 == v3 -> Right ()
    _ -> Left "cart: dup has wrong type"

ensureDropShape :: GenDecl -> Either Text ()
ensureDropShape gen =
  case (gdDom gen, gdCod gen) of
    ([TVar v1], []) -> Right ()
    _ -> Left "cart: drop has wrong type"

-- drop any unused variable ports

dropUnused :: Doctrine -> ModeName -> M.Map Text VarState -> Diagram -> Either Text Diagram
dropUnused doc mode env diag = do
  dropGen <- lookupGen doc mode (GenName "drop")
  ensureDropShape dropGen
  foldl dropOne (Right diag) (M.elems env)
  where
    dropOne acc st = do
      d <- acc
      if vsRemaining st == 0
        then addEdgePayload (PGen (GenName "drop")) [vsPort st] [] d
        else Right d

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "cart: missing port type"
    Just ty -> Right ty

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "cart: unknown generator"
    Just gd -> Right gd

countVars :: S.Set Text -> Term -> M.Map Text Int
countVars ctx term =
  case term of
    Term name args
      | null args && name `S.member` ctx -> M.singleton name 1
      | otherwise -> foldl (M.unionWith (+)) M.empty (map (countVars ctx) args)
