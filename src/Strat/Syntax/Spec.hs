{-# LANGUAGE OverloadedStrings #-}
module Strat.Syntax.Spec
  ( Assoc(..)
  , NotationKind(..)
  , NotationSpec(..)
  , SyntaxSpec(..)
  , SyntaxInstance(..)
  , instantiateSyntax
  ) where

import Strat.Surface.Combinator (CombTerm(..))
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.Signature (Signature(..), OpDecl(..))
import Strat.Kernel.Syntax (OpName(..), Term(..), TermNode(..), Var(..), ScopeId(..))
import Strat.Frontend.Resolve (resolveOpText)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.List (sortBy, foldl')
import Data.Char (isAlphaNum)
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)


data Assoc = LeftAssoc | RightAssoc | NonAssoc
  deriving (Eq, Ord, Show)


data NotationKind
  = NAtom
  | NPrefix Int
  | NPostfix Int
  | NInfix Assoc Int
  deriving (Eq, Ord, Show)


data NotationSpec = NotationSpec
  { nsKind  :: NotationKind
  , nsToken :: Text
  , nsOp    :: Text
  , nsPrint :: Bool
  }
  deriving (Eq, Show)


data SyntaxSpec = SyntaxSpec
  { ssName        :: Text
  , ssNotations   :: [NotationSpec]
  , ssAllowCall   :: Bool
  , ssVarPrefix   :: Text
  , ssAllowQualId :: Bool
  }
  deriving (Eq, Show)


data SyntaxInstance = SyntaxInstance
  { siParse :: Text -> Either Text CombTerm
  , siPrint :: Term -> Text
  }

type Parser = Parsec Void Text

instantiateSyntax :: Presentation -> [Text] -> SyntaxSpec -> Either Text SyntaxInstance
instantiateSyntax pres opens spec = do
  resolved <- mapM (resolveNotation sig opens) (ssNotations spec)
  validateNotations resolved
  let parseNotations = resolved
  let printable = filter (rnPrint . snd) resolved
  let printerTable = buildPrinterTable printable
  let resolver name =
        case resolveOpText sig opens name of
          Right op -> Just op
          Left _ -> Nothing
  let parser = buildParser resolver (ssVarPrefix spec) (ssAllowCall spec) (ssAllowQualId spec) parseNotations
  pure SyntaxInstance
    { siParse = parser
    , siPrint = printTerm (ssVarPrefix spec) printerTable
    }
  where
    sig = presSig pres

resolveNotation :: Signature -> [Text] -> NotationSpec -> Either Text (ResolvedNotation, NotationSpec)
resolveNotation sig opens nspec = do
  op <- resolveOpText sig opens (nsOp nspec)
  let arity = opArity sig op
  ensureArity nspec op arity
  pure (ResolvedNotation op (nsKind nspec) (nsToken nspec), nspec)

ensureArity :: NotationSpec -> OpName -> Int -> Either Text ()
ensureArity nspec op arity =
  case nsKind nspec of
    NAtom -> check 0
    NPrefix _ -> check 1
    NPostfix _ -> check 1
    NInfix _ _ -> check 2
  where
    check expected
      | arity == expected = Right ()
      | otherwise = Left ("Arity mismatch for op " <> renderOp op <> ": expected " <> T.pack (show expected) <> ", got " <> T.pack (show arity))

opArity :: Signature -> OpName -> Int
opArity sig op =
  case M.lookup op (sigOps sig) of
    Nothing -> 0
    Just decl -> length (opTele decl)

renderOp :: OpName -> Text
renderOp (OpName t) = t


data ResolvedNotation = ResolvedNotation
  { rnOp    :: OpName
  , rnKind  :: NotationKind
  , rnToken :: Text
  }
  deriving (Eq, Show)

rnPrint :: NotationSpec -> Bool
rnPrint = nsPrint

validateNotations :: [(ResolvedNotation, NotationSpec)] -> Either Text ()
validateNotations resolved = do
  checkPrintDuplicates
  checkTokenCollisions
  where
    checkPrintDuplicates =
      case dupPrintOps of
        [] -> Right ()
        (op:_) -> Left ("Multiple print notations for op " <> renderOp op)

    dupPrintOps =
      let ops = [ rnOp rn | (rn, nspec) <- resolved, nsPrint nspec ]
      in findDup ops

    checkTokenCollisions =
      case collisions of
        [] -> Right ()
        ((tok, kind, prec, op1, op2):_) ->
          Left ("Token collision for " <> tok <> " (" <> kind <> prec <> "): " <> renderOp op1 <> " vs " <> renderOp op2)

    collisions = go M.empty (map toKey resolved)

    go _ [] = []
    go seen ((key, op):rest) =
      case M.lookup key seen of
        Nothing -> go (M.insert key op seen) rest
        Just op'
          | op' == op -> go seen rest
          | otherwise -> (tokenText key, kindText key, precText key, op', op) : go seen rest

    toKey (rn, _) = (keyFrom rn, rnOp rn)

    keyFrom rn =
      case rnKind rn of
        NAtom -> Key "atom" Nothing (rnToken rn)
        NPrefix prec -> Key "prefix" (Just prec) (rnToken rn)
        NPostfix prec -> Key "postfix" (Just prec) (rnToken rn)
        NInfix _ prec -> Key "infix" (Just prec) (rnToken rn)

    tokenText (Key _ _ tok) = tok
    kindText (Key k _ _) = k
    precText (Key _ mp _) = maybe "" (\p -> "@" <> T.pack (show p)) mp

data Key = Key Text (Maybe Int) Text
  deriving (Eq, Ord, Show)

findDup :: Ord a => [a] -> [a]
findDup xs = go M.empty xs
  where
    go _ [] = []
    go seen (y:ys)
      | M.member y seen = y : go seen ys
      | otherwise = go (M.insert y () seen) ys

buildParser :: (Text -> Maybe OpName) -> Text -> Bool -> Bool -> [(ResolvedNotation, NotationSpec)] -> (Text -> Either Text CombTerm)
buildParser resolveName varPrefix allowCall allowQual notations = \input ->
  case runParser (sc *> expr <* eof) "<syntax>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right tm -> Right tm
  where
    expr :: Parser CombTerm
    expr = makeExprParser term (opTable notations)

    term :: Parser CombTerm
    term = choice
      [ parens expr
      , varTerm
      , atomTerm
      , if allowCall then try callTerm else fail "function call disabled"
      , if allowCall then bareCallTerm else fail "function call disabled"
      ]

    parens :: Parser a -> Parser a
    parens = between (symbol "(") (symbol ")")

    varTerm :: Parser CombTerm
    varTerm = do
      _ <- lexeme (string varPrefix)
      name <- identRaw allowQual
      pure (CVar name)

    atomTerm :: Parser CombTerm
    atomTerm = choice (map atomParser atomNotations)
      where
        atomNotations = [ rn | (rn, _) <- notations, rnKind rn == NAtom ]
        atomParser rn = do
          _ <- symbol (rnToken rn)
          pure (COp (renderOp (rnOp rn)) [])

    callTerm :: Parser CombTerm
    callTerm = do
      name <- identRaw allowQual
      _ <- symbol "("
      args <- expr `sepBy` symbol ","
      _ <- symbol ")"
      case resolveName name of
        Nothing -> fail ("unknown op: " <> T.unpack name)
        Just op -> pure (COp (renderOp op) args)

    bareCallTerm :: Parser CombTerm
    bareCallTerm = do
      name <- identRaw allowQual
      case resolveName name of
        Nothing -> fail ("unknown op: " <> T.unpack name)
        Just op -> pure (COp (renderOp op) [])

    opTable ns = map snd (sortByPrec grouped)
      where
        grouped = foldl' insertOp M.empty (concatMap toOp ns)

        toOp (rn, _) =
          case rnKind rn of
            NPrefix prec -> [(prec, Prefix (mkPrefix rn))]
            NPostfix prec -> [(prec, Postfix (mkPostfix rn))]
            NInfix assoc prec -> [(prec, mkInfix assoc rn)]
            NAtom -> []

        insertOp mp (prec, op) = M.insertWith (<>) prec [op] mp

        sortByPrec mp = map (\(p, ops) -> (p, ops)) (sortDesc (M.toList mp))

        sortDesc = sortBy (\(a, _) (b, _) -> compare b a)

        mkPrefix rn = do
          _ <- symbol (rnToken rn)
          pure (\x -> COp (renderOp (rnOp rn)) [x])

        mkPostfix rn = do
          _ <- symbol (rnToken rn)
          pure (\x -> COp (renderOp (rnOp rn)) [x])

        mkInfix assoc rn =
          case assoc of
            LeftAssoc -> InfixL (binary rn)
            RightAssoc -> InfixR (binary rn)
            NonAssoc -> InfixN (binary rn)

        binary rn = do
          _ <- symbol (rnToken rn)
          pure (\a b -> COp (renderOp (rnOp rn)) [a, b])

    sc :: Parser ()
    sc = L.space space1 (L.skipLineComment "--" <|> L.skipLineComment "#") empty
    symbol :: Text -> Parser Text
    symbol = L.symbol sc
    lexeme :: Parser a -> Parser a
    lexeme = L.lexeme sc

    identRaw :: Bool -> Parser Text
    identRaw allowQ = lexeme $ do
      first <- letterChar
      rest <- many (alphaNumChar <|> char '_' <|> char '-')
      let base = T.pack (first : rest)
      if allowQ
        then do
          more <- many (char '.' *> identChunk)
          pure (T.intercalate "." (base : more))
        else pure base

    identChunk :: Parser Text
    identChunk = do
      first <- letterChar
      rest <- many (alphaNumChar <|> char '_' <|> char '-')
      pure (T.pack (first : rest))

buildPrinterTable :: [(ResolvedNotation, NotationSpec)] -> PrinterTable
buildPrinterTable resolved =
  foldl' add emptyTable resolved
  where
    add tbl (rn, _) =
      case rnKind rn of
        NAtom -> tbl { ptAtom = insertOp (rnOp rn) (rnToken rn) (ptAtom tbl) }
        NPrefix prec -> tbl { ptPrefix = insertOp (rnOp rn) (prec, rnToken rn) (ptPrefix tbl) }
        NPostfix prec -> tbl { ptPostfix = insertOp (rnOp rn) (prec, rnToken rn) (ptPostfix tbl) }
        NInfix assoc prec -> tbl { ptInfix = insertOp (rnOp rn) (prec, assoc, rnToken rn) (ptInfix tbl) }

    insertOp op val mp =
      if M.member op mp then mp else M.insert op val mp


data PrinterTable = PrinterTable
  { ptAtom   :: M.Map OpName Text
  , ptPrefix :: M.Map OpName (Int, Text)
  , ptPostfix :: M.Map OpName (Int, Text)
  , ptInfix  :: M.Map OpName (Int, Assoc, Text)
  }

emptyTable :: PrinterTable
emptyTable = PrinterTable M.empty M.empty M.empty M.empty

printTerm :: Text -> PrinterTable -> Term -> Text
printTerm varPrefix table = go 0
  where
    go prec t =
      case termNode t of
        TVar v -> varPrefix <> renderVar v
        TOp op args ->
          case args of
            [] -> fromMaybe (renderOp op) (M.lookup op (ptAtom table))
            [x] ->
              case M.lookup op (ptPrefix table) of
                Just (p, tok) ->
                  let inner = go 0 x
                  in parenIf (p < prec) (tok <> "(" <> inner <> ")")
                Nothing ->
                  case M.lookup op (ptPostfix table) of
                    Just (p, tok) ->
                      let inner = go 0 x
                      in parenIf (p < prec) ("(" <> inner <> ")" <> tok)
                    Nothing -> fallback op args
            [a,b] ->
              case M.lookup op (ptInfix table) of
                Just (p, assoc, tok) ->
                  let (lp, rp) = case assoc of
                        LeftAssoc -> (p, p + 1)
                        RightAssoc -> (p + 1, p)
                        NonAssoc -> (p + 1, p + 1)
                      left = go lp a
                      right = go rp b
                  in parenIf (p < prec) (left <> " " <> tok <> " " <> right)
                Nothing -> fallback op args
            _ -> fallback op args

    fallback op args =
      renderOp op <> "(" <> T.intercalate "," (map (go 0) args) <> ")"

    parenIf True txt = "(" <> txt <> ")"
    parenIf False txt = txt

    renderVar (Var (ScopeId scope) local) =
      "v_" <> sanitize scope <> "_" <> T.pack (show local)

    sanitize = T.map (\c -> if isAlphaNum c || c == '_' || c == '-' then c else '_')

fromMaybe :: a -> Maybe a -> a
fromMaybe def m = case m of
  Nothing -> def
  Just v -> v
