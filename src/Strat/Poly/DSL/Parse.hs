{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Parse
  ( parseDiagExpr
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
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
  polyMetaVarTerm
    <|> try polyIdTerm
    <|> polySpliceTerm
    <|> polyLoopTerm
    <|> polyBoxTerm
    <|> polyTermRefTerm
    <|> polyGenTerm
    <|> parens polyDiagExpr

polyMetaVarTerm :: Parser RawDiagExpr
polyMetaVarTerm = do
  _ <- symbol "?"
  name <- ident
  pure (RDMetaVar name)

polyIdTerm :: Parser RawDiagExpr
polyIdTerm = do
  _ <- symbol "id"
  ctx <- polyContext
  pure (RDId ctx)

polyGenTerm :: Parser RawDiagExpr
polyGenTerm = do
  name <- ident
  mArgs <- optional (symbol "{" *> polyTypeExpr `sepBy` symbol "," <* symbol "}")
  mAttrArgs <- optional polyAttrArgs
  mBinderArgs <- optional polyBinderArgs
  pure (RDGen name mArgs mAttrArgs mBinderArgs)

polySpliceTerm :: Parser RawDiagExpr
polySpliceTerm = do
  _ <- symbol "splice"
  _ <- symbol "("
  meta <- binderMetaVar
  _ <- symbol ")"
  pure (RDSplice meta)

polyTermRefTerm :: Parser RawDiagExpr
polyTermRefTerm = do
  _ <- symbol "@"
  name <- ident
  pure (RDTermRef name)

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

polyAttrArgs :: Parser [RawAttrArg]
polyAttrArgs = do
  _ <- symbol "("
  args <- polyAttrArg `sepBy` symbol ","
  _ <- symbol ")"
  if mixedArgStyles args
    then fail "generator attribute arguments must be either all named or all positional"
    else pure args
  where
    mixedArgStyles [] = False
    mixedArgStyles xs =
      let named = [ () | RAName _ _ <- xs ]
          positional = [ () | RAPos _ <- xs ]
      in not (null named) && not (null positional)

polyAttrArg :: Parser RawAttrArg
polyAttrArg =
  try named <|> positional
  where
    named = do
      field <- ident
      _ <- symbol "="
      term <- polyAttrTerm
      pure (RAName field term)
    positional = RAPos <$> polyAttrTerm

polyAttrTerm :: Parser RawAttrTerm
polyAttrTerm =
  choice
    [ RATInt . fromIntegral <$> integer
    , RATString <$> stringLiteral
    , RATBool True <$ keyword "true"
    , RATBool False <$ keyword "false"
    , RATVar <$> ident
    ]

polyContext :: Parser RawPolyContext
polyContext = do
  _ <- symbol "["
  tys <- polyTypeExpr `sepBy` symbol ","
  _ <- symbol "]"
  pure tys

polyBinderArgs :: Parser [RawBinderArg]
polyBinderArgs = do
  _ <- symbol "["
  args <- polyBinderArg `sepBy` symbol ","
  _ <- symbol "]"
  pure args

polyBinderArg :: Parser RawBinderArg
polyBinderArg =
  try (RBAMeta <$> binderMetaVar)
    <|> (RBAExpr <$> polyDiagExpr)

binderMetaVar :: Parser Text
binderMetaVar = lexeme (char '?' *> identRaw)

polyTypeExpr :: Parser RawPolyTypeExpr
polyTypeExpr = lexeme (try modApp <|> try bound <|> regular)
  where
    modApp = do
      me <- rawModExprComplex
      _ <- symbol "("
      inner <- polyTypeExpr
      _ <- symbol ")"
      pure (RPTMod me inner)
    bound = do
      _ <- symbol "^"
      idx <- fromIntegral <$> integer
      pure (RPTBound idx)
    rawModExprComplex =
      try rawId <|> rawComp
    rawId = do
      _ <- symbol "id"
      _ <- symbol "@"
      mode <- ident
      pure (RMId mode)
    rawComp = do
      first <- ident
      _ <- symbol "."
      second <- ident
      _ <- symbol "."
      third <- ident
      rest <- many (symbol "." *> ident)
      pure (RMComp (first : second : third : rest))
    regular = do
      name <- identRaw
      mQual <- optional (try (char '.' *> identRaw))
      mArgs <- optional (symbol "(" *> polyTypeExpr `sepBy` symbol "," <* symbol ")")
      case mQual of
        Just qualName ->
          let ref = RawTypeRef { rtrMode = Just name, rtrName = qualName }
          in pure (RPTCon ref (maybe [] id mArgs))
        Nothing ->
          case mArgs of
            Just args ->
              let ref = RawTypeRef { rtrMode = Nothing, rtrName = name }
              in pure (RPTCon ref args)
            Nothing ->
              pure (RPTVar name)

-- Helpers

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

keyword :: Text -> Parser Text
keyword kw = lexeme (try (string kw <* notFollowedBy identChar))

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"

ident :: Parser Text
ident = lexeme identRaw

identRaw :: Parser Text
identRaw = T.pack <$> ((:) <$> letterChar <*> many identChar)

identChar :: Parser Char
identChar = alphaNumChar <|> char '_' <|> char '-' <|> char '\''

stringLiteral :: Parser Text
stringLiteral = lexeme (T.pack <$> (char '"' *> manyTill L.charLiteral (char '"')))

integer :: Parser Integer
integer = lexeme L.decimal
