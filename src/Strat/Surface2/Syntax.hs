{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.Syntax
  ( SurfaceSyntaxInstance(..)
  , instantiateSurfaceSyntax
  ) where

import Strat.Surface2.Def
import Strat.Surface2.Term
import Strat.Surface2.SyntaxSpec
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.List (sortOn, elemIndex)
import Data.Void (Void)
import Control.Monad.State.Strict
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)

data SurfaceSyntaxInstance = SurfaceSyntaxInstance
  { ssiParseTm :: Text -> Either Text STerm
  , ssiPrintTm :: STerm -> Text
  , ssiParseTy :: Text -> Either Text STerm
  , ssiPrintTy :: STerm -> Text
  }

data Table = Table
  { tAtoms :: [(Text, Con2Name)]
  , tPrefixes :: [(Text, Con2Name)]
  , tInfixes :: [(SurfaceAssoc, Int, Text, Con2Name)]
  , tBinder :: Maybe BinderSpec
  , tApp :: Maybe Con2Name
  , tTuple :: Maybe (Text, Con2Name)
  }

data BinderSpec = BinderSpec
  { bTok :: Text
  , bTySep :: Text
  , bBodySep :: Text
  , bCon :: Con2Name
  }

data PrintForm
  = PFAtom Text
  | PFPrefix Text
  | PFInfix SurfaceAssoc Int Text
  | PFBinder BinderSpec
  | PFApp
  | PFTuple Text

instantiateSurfaceSyntax :: SurfaceDef -> SurfaceSyntaxSpec -> Either Text SurfaceSyntaxInstance
instantiateSurfaceSyntax surf spec = do
  if sssSurface spec /= sdName surf
    then Left "surface_syntax references unknown surface"
    else Right ()
  tyTable <- buildTable surf (sssTyNotations spec)
  tmTable <- buildTable surf (sssTmNotations spec)
  let tyPrinter = buildPrinter tyTable tyPrinter
  let tmPrinter = buildPrinter tmTable tyPrinter
  let tyParser = buildParser surf tyTable Nothing parseIdent
  let tmParser = buildParser surf tmTable (Just tyParser) parseIdent
  pure SurfaceSyntaxInstance
    { ssiParseTm = \input -> runWithParser tmParser input
    , ssiPrintTm = tmPrinter
    , ssiParseTy = \input -> runWithParser tyParser input
    , ssiPrintTy = tyPrinter
    }

buildTable :: SurfaceDef -> [SurfaceNotation] -> Either Text Table
buildTable surf notes = do
  let conMap = sdCons surf
  atoms <- mapM (resolveAtom conMap) [ n | n@(SAtom _ _) <- notes ]
  prefixes <- mapM (resolvePrefix conMap) [ n | n@(SPrefix _ _) <- notes ]
  infixes <- mapM (resolveInfix conMap) [ n | n@(SInfix _ _ _ _) <- notes ]
  binder <- resolveBinder conMap [ n | n@(SBinder _ _ _ _) <- notes ]
  appCon <- resolveApp conMap [ n | n@(SApp _) <- notes ]
  tupleCon <- resolveTuple conMap [ n | n@(STuple _ _) <- notes ]
  pure Table
    { tAtoms = atoms
    , tPrefixes = prefixes
    , tInfixes = infixes
    , tBinder = binder
    , tApp = appCon
    , tTuple = tupleCon
    }

resolveAtom :: M.Map Con2Name ConDecl -> SurfaceNotation -> Either Text (Text, Con2Name)
resolveAtom conMap (SAtom tok con) = do
  decl <- lookupCon conMap con
  if null (conArgs decl) then Right (tok, conName decl) else Left ("Atom expects nullary constructor: " <> con)
resolveAtom _ _ = Left "invalid atom notation"

resolvePrefix :: M.Map Con2Name ConDecl -> SurfaceNotation -> Either Text (Text, Con2Name)
resolvePrefix conMap (SPrefix tok con) = do
  decl <- lookupCon conMap con
  if length (conArgs decl) == 1 then Right (tok, conName decl) else Left ("Prefix expects unary constructor: " <> con)
resolvePrefix _ _ = Left "invalid prefix notation"

resolveInfix :: M.Map Con2Name ConDecl -> SurfaceNotation -> Either Text (SurfaceAssoc, Int, Text, Con2Name)
resolveInfix conMap (SInfix assoc prec tok con) = do
  decl <- lookupCon conMap con
  if length (conArgs decl) == 2 then Right (assoc, prec, tok, conName decl) else Left ("Infix expects binary constructor: " <> con)
resolveInfix _ _ = Left "invalid infix notation"

resolveBinder :: M.Map Con2Name ConDecl -> [SurfaceNotation] -> Either Text (Maybe BinderSpec)
resolveBinder _ [] = Right Nothing
resolveBinder conMap [SBinder tok tySep bodySep con] = do
  decl <- lookupCon conMap con
  case conArgs decl of
    [_, argBody] ->
      if length (caBinders argBody) == 1
        then Right (Just (BinderSpec tok tySep bodySep (conName decl)))
        else Left ("Binder constructor must bind one variable: " <> con)
    _ -> Left ("Binder constructor must have two arguments: " <> con)
resolveBinder _ _ = Left "Multiple binder notations"

resolveApp :: M.Map Con2Name ConDecl -> [SurfaceNotation] -> Either Text (Maybe Con2Name)
resolveApp _ [] = Right Nothing
resolveApp conMap [SApp con] = do
  decl <- lookupCon conMap con
  if length (conArgs decl) == 2 then Right (Just (conName decl)) else Left ("app expects binary constructor: " <> con)
resolveApp _ _ = Left "Multiple app notations"

resolveTuple :: M.Map Con2Name ConDecl -> [SurfaceNotation] -> Either Text (Maybe (Text, Con2Name))
resolveTuple _ [] = Right Nothing
resolveTuple conMap [STuple tok con] = do
  decl <- lookupCon conMap con
  if length (conArgs decl) == 2 then Right (Just (tok, conName decl)) else Left ("tuple expects binary constructor: " <> con)
resolveTuple _ _ = Left "Multiple tuple notations"

lookupCon :: M.Map Con2Name ConDecl -> Text -> Either Text ConDecl
lookupCon conMap name =
  case M.lookup (Con2Name name) conMap of
    Nothing -> Left ("Unknown constructor: " <> name)
    Just d -> Right d

type Parser = ParsecT Void Text (State [Text])

runWithParser :: Parser STerm -> Text -> Either Text STerm
runWithParser p input =
  case evalState (runParserT (sc *> p <* eof) "<surface>" input) [] of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right tm -> Right tm

buildParser :: SurfaceDef -> Table -> Maybe (Parser STerm) -> Parser Text -> Parser STerm
buildParser surf table mTyParser pIdent =
  makeExprParser term (opTable table)
  where
    term = do
      atoms <- some termAtom
      case tApp table of
        Nothing -> case atoms of
          [t] -> pure t
          _ -> fail "application syntax not enabled"
        Just con -> pure (foldl1 (mkApp con) atoms)

    termAtom =
      choice
        [ binderTerm
        , tupleTerm
        , atomTerm
        , parens (buildParser surf table mTyParser pIdent)
        , callTerm
        , varTerm
        ]

    binderTerm =
      case (tBinder table, mTyParser) of
        (Just spec, Just tyParser) -> do
          _ <- symbol (bTok spec)
          v <- pIdent
          _ <- symbol (bTySep spec)
          ty <- tyParser
          _ <- symbol (bBodySep spec)
          body <- withBinder v (buildParser surf table mTyParser pIdent)
          pure (SCon (bCon spec) [SArg [] ty, SArg [ty] body])
        _ -> empty

    tupleTerm =
      case tTuple table of
        Nothing -> fail "no tuple"
        Just (tok, con) -> try $ do
          _ <- symbol "("
          xs <- buildParser surf table mTyParser pIdent `sepBy1` symbol tok
          _ <- symbol ")"
          case xs of
            [x] -> pure x
            _ -> pure (foldl1 (mkApp con) xs)

    atomTerm =
      choice [ atomParser tok con | (tok, con) <- tAtoms table ]

    atomParser tok con = do
      _ <- symbol tok
      pure (SCon con [])

    callTerm = try $ do
      name <- pIdent
      _ <- symbol "("
      args <- buildParser surf table mTyParser pIdent `sepBy` symbol ","
      _ <- symbol ")"
      case M.lookup (Con2Name name) (sdCons surf) of
        Nothing -> fail ("unknown constructor: " <> T.unpack name)
        Just _ -> pure (SCon (Con2Name name) (map (SArg []) args))

    varTerm = do
      name <- pIdent
      env <- get
      case elemIndex name env of
        Nothing -> pure (SFree name)
        Just ix -> pure (SBound (Ix ix))

mkApp :: Con2Name -> STerm -> STerm -> STerm
mkApp con a b = SCon con [SArg [] a, SArg [] b]

opTable :: Table -> [[Operator Parser STerm]]
opTable table =
  [map prefixOp (tPrefixes table)] <> infixLevels
  where
    prefixOp (tok, con) = Prefix (mkPrefix con <$ symbol tok)
    infixOp (assoc, _prec, tok, con) =
      case assoc of
        SLeft -> InfixL (mkInfix con <$ symbol tok)
        SRight -> InfixR (mkInfix con <$ symbol tok)
        SNon -> InfixN (mkInfix con <$ symbol tok)

    mkPrefix con x = SCon con [SArg [] x]
    mkInfix con x y = SCon con [SArg [] x, SArg [] y]

    infixLevels =
      let grouped = groupByPrec (tInfixes table)
      in map (map infixOp) grouped

groupByPrec :: [(SurfaceAssoc, Int, Text, Con2Name)] -> [[(SurfaceAssoc, Int, Text, Con2Name)]]
groupByPrec ops =
  let sorted = sortOn (\(_, prec, _, _) -> negate prec) ops
  in foldr add [] sorted
  where
    add op [] = [[op]]
    add op@(_, prec, _, _) (g:gs) =
      let (_, prec', _, _) = head g
      in if prec == prec'
          then (op:g):gs
          else [op] : g : gs

buildPrinter :: Table -> (STerm -> Text) -> STerm -> Text
buildPrinter table printTy tm = go [] 0 tm
  where
    printForm = buildPrintForms table

    go env prec term =
      case term of
        SBound (Ix ix) ->
          case envName env ix of
            Just n -> n
            Nothing -> "x" <> T.pack (show ix)
        SFree name -> name
        SCon con args ->
          case M.lookup con printForm of
            Just (PFAtom tok) -> tok
            Just (PFPrefix tok) ->
              let inner = go env 10 (argBody args 0)
                  rendered = tok <> "(" <> inner <> ")"
              in parenIf (prec > 9) rendered
            Just (PFInfix assoc p tok) ->
              let a = go env (p + 1) (argBody args 0)
                  b = go env (p + 1) (argBody args 1)
                  rendered = a <> " " <> tok <> " " <> b
              in parenIf (prec > p) rendered
            Just (PFTuple tok) ->
              let a = go env 0 (argBody args 0)
                  b = go env 0 (argBody args 1)
              in "(" <> a <> tok <> " " <> b <> ")"
            Just PFApp ->
              let a = go env 10 (argBody args 0)
                  b = go env 10 (argBody args 1)
              in a <> " " <> b
            Just (PFBinder spec) ->
              case args of
                [SArg [] ty, SArg [bty] body] ->
                  let vname = freshName (length env)
                      env' = vname : env
                      tyTxt = printTy ty
                      bodyTxt = go env' 0 body
                      rendered = bTok spec <> vname <> bTySep spec <> tyTxt <> bBodySep spec <> bodyTxt
                  in parenIf (prec > 0) rendered
                _ -> fallback env con args
            Nothing -> fallback env con args

    fallback env con args =
      let argTxt = map (\a -> go env 0 (saBody a)) args
      in renderCon con <> "(" <> T.intercalate "," argTxt <> ")"

    argBody xs i =
      case drop i xs of
        (SArg _ b:_) -> b
        _ -> SFree "_"

    parenIf True t = "(" <> t <> ")"
    parenIf False t = t

    envName env ix =
      if ix < length env then Just (env !! ix) else Nothing

    freshName n = "x" <> T.pack (show n)

buildPrintForms :: Table -> M.Map Con2Name PrintForm
buildPrintForms table =
  M.fromList (atoms <> prefixes <> infixes <> binders <> apps <> tuples)
  where
    atoms = [ (con, PFAtom tok) | (tok, con) <- tAtoms table ]
    prefixes = [ (con, PFPrefix tok) | (tok, con) <- tPrefixes table ]
    infixes = [ (con, PFInfix assoc prec tok) | (assoc, prec, tok, con) <- tInfixes table ]
    binders = case tBinder table of
      Nothing -> []
      Just spec -> [(bCon spec, PFBinder spec)]
    apps = maybe [] (\con -> [(con, PFApp)]) (tApp table)
    tuples = maybe [] (\(tok, con) -> [(con, PFTuple tok)]) (tTuple table)

renderCon :: Con2Name -> Text
renderCon (Con2Name t) = t

withBinder :: Text -> Parser a -> Parser a
withBinder name action = do
  env <- get
  put (name:env)
  result <- action
  put env
  pure result

parseIdent :: Parser Text
parseIdent = lexeme identRaw

identRaw :: Parser Text
identRaw = T.pack <$> ((:) <$> letterChar <*> many (alphaNumChar <|> char '_' <|> char '-'))

sc :: Parser ()
sc = L.space space1 lineCmnt empty
  where
    lineCmnt = L.skipLineComment "--" <|> L.skipLineComment "#"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
