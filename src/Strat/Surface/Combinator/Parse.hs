{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface.Combinator.Parse
  ( parseCombTerm
  ) where

import Strat.Surface.Combinator
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


type Parser = Parsec Void Text

parseCombTerm :: Text -> Either Text CombTerm
parseCombTerm input =
  case runParser (sc *> term <* eof) "<term>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right tm -> Right tm

term :: Parser CombTerm
term = lexeme (varTerm <|> appTerm)

varTerm :: Parser CombTerm
varTerm = do
  _ <- char '?'
  name <- identRaw
  pure (CVar name)

appTerm :: Parser CombTerm
appTerm = do
  name <- qualifiedIdent
  mArgs <- optional (symbol "(" *> term `sepBy` symbol "," <* symbol ")")
  pure (COp name (maybe [] id mArgs))

qualifiedIdent :: Parser Text
qualifiedIdent = lexeme $ do
  first <- identRaw
  rest <- many (char '.' *> identRaw)
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
