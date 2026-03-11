{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Literal
  ( LiteralKind(..)
  , Literal(..)
  , literalKind
  , renderLiteralKind
  , renderLiteral
  , escapeStringLiteral
  ) where

import Data.Char (ord)
import Data.Text (Text)
import qualified Data.Text as T
import Numeric (showHex)


data LiteralKind
  = LKInt
  | LKString
  | LKBool
  deriving (Eq, Ord, Show)

data Literal
  = LInt Int
  | LString Text
  | LBool Bool
  deriving (Eq, Ord, Show)

literalKind :: Literal -> LiteralKind
literalKind lit =
  case lit of
    LInt _ -> LKInt
    LString _ -> LKString
    LBool _ -> LKBool

renderLiteralKind :: LiteralKind -> Text
renderLiteralKind kind =
  case kind of
    LKInt -> "int"
    LKString -> "string"
    LKBool -> "bool"

renderLiteral :: Literal -> Text
renderLiteral lit =
  case lit of
    LInt n -> T.pack (show n)
    LString s -> escapeStringLiteral s
    LBool True -> "true"
    LBool False -> "false"

escapeStringLiteral :: Text -> Text
escapeStringLiteral s = "\"" <> T.concatMap escapeChar s <> "\""
  where
    escapeChar c =
      case c of
        '\"' -> "\\\""
        '\\' -> "\\\\"
        '\n' -> "\\n"
        '\r' -> "\\r"
        '\t' -> "\\t"
        _ ->
          if ord c < 0x20
            then "\\u" <> T.pack (pad4 (showHex (ord c) ""))
            else T.singleton c

    pad4 xs = replicate (4 - length xs) '0' <> xs
