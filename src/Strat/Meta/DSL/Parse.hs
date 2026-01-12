{-# LANGUAGE OverloadedStrings #-}
module Strat.Meta.DSL.Parse where

import Strat.Meta.DSL.AST
import Strat.Meta.Types
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Functor (($>))
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text

parseRawFile :: Text -> Either Text RawFile
parseRawFile input =
  case runParser (sc *> rawFile <* eof) "<dsl>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right rf -> Right rf

parseRawExpr :: Text -> Either Text RawExpr
parseRawExpr input =
  case runParser (sc *> expr <* eof) "<expr>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right e -> Right e

rawFile :: Parser RawFile
rawFile = RawFile <$> many decl

decl :: Parser RawDecl
decl = do
  _ <- symbol "doctrine"
  name <- ident
  (do
      _ <- symbol "where"
      rules <- ruleBlock
      optionalSemi
      pure (DeclWhere name rules)
    )
    <|> (do
      _ <- symbol "="
      e <- expr
      optionalSemi
      pure (DeclExpr name e)
    )

ruleBlock :: Parser [RawRule]
ruleBlock = do
  _ <- symbol "{"
  rules <- many ruleDecl
  _ <- symbol "}"
  pure rules

ruleDecl :: Parser RawRule
ruleDecl = do
  cls <- (symbol "computational" $> Computational) <|> (symbol "structural" $> Structural)
  name <- ident
  _ <- symbol ":"
  lhs <- term
  orient <- orientation
  rhs <- term
  optionalSemi
  pure RawRule
    { rrClass = cls
    , rrName = name
    , rrOrient = orient
    , rrLHS = lhs
    , rrRHS = rhs
    }

orientation :: Parser Orientation
orientation =
  (symbol "<->" $> Bidirectional)
    <|> (symbol "->" $> LR)
    <|> (symbol "<-" $> RL)
    <|> (symbol "=" $> Unoriented)

expr :: Parser RawExpr
expr = shareExpr <|> renameExpr <|> andExpr

shareExpr :: Parser RawExpr
shareExpr = do
  _ <- symbol "share"
  _ <- symbol "syms"
  pairs <- mapEqPairs
  _ <- symbol "in"
  e <- expr
  pure (EShareSyms pairs e)

renameExpr :: Parser RawExpr
renameExpr = do
  _ <- symbol "rename"
  kind <- (symbol "syms" $> True) <|> (symbol "eqs" $> False)
  pairs <- mapArrowPairs
  _ <- symbol "in"
  e <- expr
  pure (if kind then ERenameSyms (M.fromList pairs) e else ERenameEqs (M.fromList pairs) e)

andExpr :: Parser RawExpr
andExpr = chainl1 postExpr (symbol "&" $> EAnd)

postExpr :: Parser RawExpr
postExpr = do
  prim <- primary
  mns <- optional (symbol "@" *> ident)
  case mns of
    Nothing -> pure prim
    Just ns ->
      case prim of
        ERef name -> pure (EInst name ns)
        _ -> fail "@ requires a doctrine name"

primary :: Parser RawExpr
primary =
  (ERef <$> ident)
    <|> (symbol "(" *> expr <* symbol ")")

term :: Parser RawTerm
term = lexeme (varTerm <|> appTerm)

varTerm :: Parser RawTerm
varTerm = do
  _ <- char '?'
  name <- identRaw
  pure (RVar name)

appTerm :: Parser RawTerm
appTerm = do
  name <- identRaw
  mArgs <- optional (symbol "(" *> term `sepBy` symbol "," <* symbol ")")
  case mArgs of
    Nothing -> pure (RApp name [])
    Just args -> pure (RApp name args)

mapEqPairs :: Parser [(Text, Text)]
mapEqPairs = braces (pair `sepBy` symbol ",")
  where
    pair = do
      a <- qualifiedIdent
      _ <- symbol "="
      b <- qualifiedIdent
      pure (a, b)

mapArrowPairs :: Parser [(Text, Text)]
mapArrowPairs = braces (pair `sepBy` symbol ",")
  where
    pair = do
      a <- qualifiedIdent
      _ <- symbol "->"
      b <- qualifiedIdent
      pure (a, b)

qualifiedIdent :: Parser Text
qualifiedIdent = lexeme $ do
  first <- identRaw
  rest <- many (char '.' *> identRaw)
  pure (T.intercalate "." (first : rest))

ident :: Parser Text
ident = lexeme identRaw

identRaw :: Parser Text
identRaw = T.pack <$> ((:) <$> letterChar <*> many identChar)

identChar :: Parser Char
identChar = alphaNumChar <|> char '_' <|> char '-'

braces :: Parser a -> Parser a
braces p = symbol "{" *> p <* symbol "}"

optionalSemi :: Parser ()
optionalSemi = do
  _ <- optional (symbol ";")
  pure ()

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

sc :: Parser ()
sc =
  L.space
    space1
    (L.skipLineComment "--" <|> L.skipLineComment "#")
    empty

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = do
  x <- p
  rest x
  where
    rest x =
      (do
          f <- op
          y <- p
          rest (f x y)
      )
      <|> pure x
