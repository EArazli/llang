{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface.Lambda.Parse
  ( parseLamTerm
  ) where

import Strat.Surface.Lambda
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


type Parser = Parsec Void Text

parseLamTerm :: Text -> Either Text LamTerm
parseLamTerm input =
  case runParser (sc *> expr <* eof) "<lambda>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right tm -> Right tm

expr :: Parser LamTerm
expr = try lambdaExpr <|> appExpr

lambdaExpr :: Parser LamTerm
lambdaExpr = do
  _ <- char '\\'
  sc
  name <- ident
  _ <- char '.'
  sc
  body <- expr
  pure (LLam name body)

appExpr :: Parser LamTerm
appExpr = do
  atoms <- some atom
  pure (foldl1 LApp atoms)

atom :: Parser LamTerm
atom =
  (LVar <$> ident)
    <|> (symbol "(" *> expr <* symbol ")")

ident :: Parser Text
ident = lexeme qualifiedIdent

qualifiedIdent :: Parser Text
qualifiedIdent = do
  first <- identRaw
  rest <- many (try (char '.' *> identRaw))
  pure (T.intercalate "." (first : rest))

identRaw :: Parser Text
identRaw = T.pack <$> ((:) <$> letterChar <*> many identChar)

identChar :: Parser Char
identChar = alphaNumChar <|> char '_' <|> char '-'

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
