{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Parse
  ( parseDiagExpr
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Data.Char (isLower)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)
import Data.Functor (($>))
import Strat.Poly.DSL.AST


type Parser = Parsec Void Text

parseDiagExpr :: Text -> Either Text RawDiagExpr
parseDiagExpr input =
  case runParser (sc *> polyDiagExpr <* eof) "<poly>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right expr -> Right expr

polyDiagExpr :: Parser RawDiagExpr
polyDiagExpr = makeExprParser polyDiagTerm operators
  where
    operators =
      [ [ InfixL (symbol "*" $> RDTensor) ]
      , [ InfixL (symbol ";" $> RDComp) ]
      ]

polyDiagTerm :: Parser RawDiagExpr
polyDiagTerm =
  try polyIdTerm <|> polyLoopTerm <|> polyBoxTerm <|> polyGenTerm <|> parens polyDiagExpr

polyIdTerm :: Parser RawDiagExpr
polyIdTerm = do
  _ <- symbol "id"
  ctx <- polyContext
  pure (RDId ctx)

polyGenTerm :: Parser RawDiagExpr
polyGenTerm = do
  name <- ident
  mArgs <- optional (symbol "{" *> polyTypeExpr `sepBy` symbol "," <* symbol "}")
  pure (RDGen name mArgs)

polyBoxTerm :: Parser RawDiagExpr
polyBoxTerm = do
  _ <- symbol "box"
  name <- ident
  _ <- symbol "{"
  inner <- polyDiagExpr
  _ <- symbol "}"
  pure (RDBox name inner)

polyLoopTerm :: Parser RawDiagExpr
polyLoopTerm = do
  _ <- symbol "loop"
  _ <- symbol "{"
  inner <- polyDiagExpr
  _ <- symbol "}"
  pure (RDLoop inner)

polyContext :: Parser RawPolyContext
polyContext = do
  _ <- symbol "["
  tys <- polyTypeExpr `sepBy` symbol ","
  _ <- symbol "]"
  pure tys

polyTypeExpr :: Parser RawPolyTypeExpr
polyTypeExpr = lexeme $ do
  name <- identRaw
  mQual <- optional (try (char '.' *> identRaw))
  mArgs <- optional (symbol "(" *> polyTypeExpr `sepBy` symbol "," <* symbol ")")
  case mQual of
    Just qualName ->
      let ref = RawTypeRef { rtrMode = Just name, rtrName = qualName }
      in pure (RPTCon ref (maybe [] id mArgs))
    Nothing ->
      case T.uncons name of
        Nothing -> fail "empty type name"
        Just (c, _) ->
          case mArgs of
            Just args ->
              let ref = RawTypeRef { rtrMode = Nothing, rtrName = name }
              in pure (RPTCon ref args)
            Nothing ->
              if isLower c
                then pure (RPTVar name)
                else
                  let ref = RawTypeRef { rtrMode = Nothing, rtrName = name }
                  in pure (RPTCon ref [])

-- Helpers

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"

ident :: Parser Text
ident = lexeme identRaw

identRaw :: Parser Text
identRaw = T.pack <$> ((:) <$> letterChar <*> many identChar)

identChar :: Parser Char
identChar = alphaNumChar <|> char '_' <|> char '-' <|> char '\''
