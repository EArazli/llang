{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.DSL.Parse
  ( parseRawFile
  , parseRawExpr
  ) where

import Strat.Kernel.DSL.AST
import Strat.Kernel.Types
import Strat.Model.Spec (MExpr(..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Functor (($>))
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)
import Control.Monad (void)


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
rawFile = do
  decls <- many declNoRun
  mrun <- optional runDecl
  pure (RawFile (decls <> maybe [] (\r -> [DeclRun r]) mrun))


-- Declarations

declNoRun :: Parser RawDecl
declNoRun =
  importDecl
    <|> doctrineDecl
    <|> syntaxDecl
    <|> modelDecl

importDecl :: Parser RawDecl
importDecl = do
  _ <- symbol "import"
  path <- stringLiteral
  optionalSemi
  pure (DeclImport (T.unpack path))

doctrineDecl :: Parser RawDecl
doctrineDecl = do
  _ <- symbol "doctrine"
  name <- ident
  (do
      _ <- symbol "where"
      items <- ruleBlock
      optionalSemi
      pure (DeclWhere name items)
    )
    <|> (do
      _ <- symbol "="
      e <- expr
      optionalSemi
      pure (DeclExpr name e)
    )

syntaxDecl :: Parser RawDecl
syntaxDecl = do
  _ <- symbol "syntax"
  name <- ident
  _ <- symbol "where"
  items <- syntaxBlock
  optionalSemi
  pure (DeclSyntaxWhere name items)

modelDecl :: Parser RawDecl
modelDecl = do
  _ <- symbol "model"
  name <- ident
  _ <- symbol "where"
  items <- modelBlock
  optionalSemi
  pure (DeclModelWhere name items)

runDecl :: Parser RawRun
runDecl = do
  _ <- symbol "run"
  _ <- symbol "where"
  items <- runBlock
  _ <- symbol "---"
  exprText <- T.strip <$> takeRest
  pure (buildRun items exprText)


-- Doctrine blocks

ruleBlock :: Parser [RawItem]
ruleBlock = do
  _ <- symbol "{"
  items <- many itemDecl
  _ <- symbol "}"
  pure items

itemDecl :: Parser RawItem
itemDecl =
  (ItemSort <$> sortDecl)
    <|> (ItemOp <$> opDecl)
    <|> (ItemRule <$> ruleDecl)

sortDecl :: Parser RawSortDecl
sortDecl = do
  _ <- symbol "sort"
  name <- ident
  params <- optional (symbol "(" *> rawSort `sepBy` symbol "," <* symbol ")")
  optionalSemi
  pure RawSortDecl
    { rsName = name
    , rsParams = maybe [] id params
    }

opDecl :: Parser RawOpDecl
opDecl = do
  _ <- symbol "op"
  name <- ident
  _ <- symbol ":"
  tele <- many binder
  res <-
    if null tele
      then rawSort
      else symbol "->" *> rawSort
  optionalSemi
  pure RawOpDecl
    { roName = name
    , roTele = tele
    , roResult = res
    }

ruleDecl :: Parser RawRule
ruleDecl = do
  cls <- (symbol "computational" $> Computational) <|> (symbol "structural" $> Structural)
  name <- ident
  _ <- symbol ":"
  tele <- many binder
  if null tele
    then optional (symbol "|-") $> ()
    else symbol "|-" $> ()
  lhs <- term
  orient <- orientation
  rhs <- term
  optionalSemi
  pure RawRule
    { rrClass = cls
    , rrName = name
    , rrOrient = orient
    , rrTele = tele
    , rrLHS = lhs
    , rrRHS = rhs
    }

binder :: Parser RawBinder
binder = do
  _ <- symbol "("
  name <- ident
  _ <- symbol ":"
  s <- rawSort
  _ <- symbol ")"
  pure RawBinder { rbName = name, rbSort = s }

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
  kind <- (symbol "ops" $> True) <|> (symbol "sorts" $> False)
  pairs <- mapEqPairs
  _ <- symbol "in"
  e <- expr
  pure (if kind then EShareOps pairs e else EShareSorts pairs e)

renameExpr :: Parser RawExpr
renameExpr = do
  _ <- symbol "rename"
  kind <-
    (symbol "ops" $> RenameOps)
      <|> (symbol "sorts" $> RenameSorts)
      <|> (symbol "eqs" $> RenameEqs)
  pairs <- mapArrowPairs
  _ <- symbol "in"
  e <- expr
  pure $ case kind of
    RenameOps -> ERenameOps (M.fromList pairs) e
    RenameSorts -> ERenameSorts (M.fromList pairs) e
    RenameEqs -> ERenameEqs (M.fromList pairs) e

data RenameKind = RenameOps | RenameSorts | RenameEqs

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

rawSort :: Parser RawSort
rawSort = do
  name <- identRaw
  mArgs <- optional (symbol "(" *> term `sepBy` symbol "," <* symbol ")")
  case mArgs of
    Nothing -> pure (RawSort name [])
    Just args -> pure (RawSort name args)


-- Syntax block

syntaxBlock :: Parser [RawSyntaxItem]
syntaxBlock = do
  _ <- symbol "{"
  items <- many syntaxItem
  _ <- symbol "}"
  pure items

syntaxItem :: Parser RawSyntaxItem
syntaxItem =
  printItem <|> parseItem <|> allowCallItem <|> varPrefixItem

printItem :: Parser RawSyntaxItem
printItem = do
  _ <- symbol "print"
  note <- notation
  optionalSemi
  pure (RSPrint note)

parseItem :: Parser RawSyntaxItem
parseItem = do
  _ <- symbol "parse"
  note <- notation
  optionalSemi
  pure (RSParse note)

allowCallItem :: Parser RawSyntaxItem
allowCallItem = do
  _ <- symbol "allow"
  _ <- symbol "call"
  optionalSemi
  pure RSAllowCall

varPrefixItem :: Parser RawSyntaxItem
varPrefixItem = do
  _ <- symbol "varprefix"
  prefix <- stringLiteral
  optionalSemi
  pure (RSVarPrefix prefix)

notation :: Parser RawNotation
notation = atomNote <|> prefixNote <|> postfixNote <|> infixNote

atomNote :: Parser RawNotation
atomNote = do
  _ <- symbol "atom"
  tok <- stringLiteral
  _ <- symbol "="
  op <- qualifiedIdent
  pure (RNAtom tok op)

prefixNote :: Parser RawNotation
prefixNote = do
  _ <- symbol "prefix"
  prec <- integer
  tok <- stringLiteral
  _ <- symbol "="
  op <- qualifiedIdent
  pure (RNPrefix (fromIntegral prec) tok op)

postfixNote :: Parser RawNotation
postfixNote = do
  _ <- symbol "postfix"
  prec <- integer
  tok <- stringLiteral
  _ <- symbol "="
  op <- qualifiedIdent
  pure (RNPostfix (fromIntegral prec) tok op)

infixNote :: Parser RawNotation
infixNote = do
  assoc <-
    (symbol "infixl" $> AssocL)
      <|> (symbol "infixr" $> AssocR)
      <|> (symbol "infix" $> AssocN)
  prec <- integer
  tok <- stringLiteral
  _ <- symbol "="
  op <- qualifiedIdent
  pure (RNInfix assoc (fromIntegral prec) tok op)


-- Model block

modelBlock :: Parser [RawModelItem]
modelBlock = do
  _ <- symbol "{"
  items <- many modelItem
  _ <- symbol "}"
  pure items

modelItem :: Parser RawModelItem
modelItem = defaultItem <|> opItem

defaultItem :: Parser RawModelItem
defaultItem = do
  _ <- symbol "default"
  _ <- symbol "="
  def <- (symbol "symbolic" $> RawDefaultSymbolic) <|> (symbol "error" *> (RawDefaultError <$> stringLiteral))
  optionalSemi
  pure (RMDefault def)

opItem :: Parser RawModelItem
opItem = do
  _ <- symbol "op"
  name <- qualifiedIdent
  args <- optional (symbol "(" *> ident `sepBy` symbol "," <* symbol ")")
  _ <- symbol "="
  expr' <- mexpr
  optionalSemi
  pure (RMOp (RawModelClause name (maybe [] id args) expr'))


-- Run block

runBlock :: Parser [RunItem]
runBlock = do
  _ <- symbol "{"
  items <- many runItem
  _ <- symbol "}"
  pure items

data RunItem
  = RunDoctrine RawExpr
  | RunSyntax Text
  | RunModel Text
  | RunOpen Text
  | RunPolicy Text
  | RunFuel Int
  | RunShow RawRunShow

runItem :: Parser RunItem
runItem =
  doctrineItem <|> syntaxItemRun <|> modelItemRun <|> openItem <|> policyItem <|> fuelItem <|> showItem

doctrineItem :: Parser RunItem
doctrineItem = do
  _ <- symbol "doctrine"
  e <- expr
  optionalSemi
  pure (RunDoctrine e)

syntaxItemRun :: Parser RunItem
syntaxItemRun = do
  _ <- symbol "syntax"
  name <- ident
  optionalSemi
  pure (RunSyntax name)

modelItemRun :: Parser RunItem
modelItemRun = do
  _ <- symbol "model"
  name <- ident
  optionalSemi
  pure (RunModel name)

openItem :: Parser RunItem
openItem = do
  _ <- symbol "open"
  name <- ident
  optionalSemi
  pure (RunOpen name)

policyItem :: Parser RunItem
policyItem = do
  _ <- symbol "policy"
  name <- ident
  optionalSemi
  pure (RunPolicy name)

fuelItem :: Parser RunItem
fuelItem = do
  _ <- symbol "fuel"
  n <- integer
  optionalSemi
  pure (RunFuel (fromIntegral n))

showItem :: Parser RunItem
showItem = do
  _ <- symbol "show"
  flag <- (symbol "normalized" $> RawShowNormalized)
      <|> (symbol "value" $> RawShowValue)
      <|> (symbol "cat" $> RawShowCat)
  optionalSemi
  pure (RunShow flag)

buildRun :: [RunItem] -> Text -> RawRun
buildRun items exprText =
  RawRun
    { rrDoctrine = pickDoctrine
    , rrSyntax = pickSyntax
    , rrModel = pickModel
    , rrOpen = opens
    , rrPolicy = pickPolicy
    , rrFuel = pickFuel
    , rrShowFlags = showFlags
    , rrExprText = exprText
    }
  where
    pickDoctrine = firstJust [ e | RunDoctrine e <- items ]
    pickSyntax = firstJust [ n | RunSyntax n <- items ]
    pickModel = firstJust [ n | RunModel n <- items ]
    pickPolicy = firstJust [ p | RunPolicy p <- items ]
    pickFuel = firstJust [ f | RunFuel f <- items ]
    opens = [ n | RunOpen n <- items ]
    showFlags = [ s | RunShow s <- items ]

    firstJust [] = Nothing
    firstJust (x:_) = Just x


-- Model expressions

mexpr :: Parser MExpr
mexpr = ifExpr <|> makeExprParser mterm mops

ifExpr :: Parser MExpr
ifExpr = do
  _ <- symbol "if"
  cond <- mexpr
  _ <- symbol "then"
  t <- mexpr
  _ <- symbol "else"
  e <- mexpr
  pure (MIf cond t e)

mterm :: Parser MExpr
mterm =
  choice
    [ parens mexpr
    , MInt . fromIntegral <$> integer
    , MBool True <$ symbol "true"
    , MBool False <$ symbol "false"
    , MString <$> stringLiteral
    , listExpr
    , MVar <$> ident
    ]

listExpr :: Parser MExpr
listExpr = do
  _ <- symbol "["
  xs <- mexpr `sepBy` symbol ","
  _ <- symbol "]"
  pure (MList xs)

mops :: [[Operator Parser MExpr]]
mops =
  [ [binary "*" (MBinOp "*")]
  , [binary "++" (MBinOp "++"), binary "+" (MBinOp "+")]
  , [binary "==" (MBinOp "==")]
  ]

binary :: Text -> (MExpr -> MExpr -> MExpr) -> Operator Parser MExpr
binary name f = InfixL (f <$ symbol name)


-- Helpers

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

stringLiteral :: Parser Text
stringLiteral = lexeme (T.pack <$> (char '"' *> manyTill L.charLiteral (char '"')))

integer :: Parser Integer
integer = lexeme L.decimal

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
    (lineComment <|> L.skipLineComment "#")
    empty

lineComment :: Parser ()
lineComment = try $ do
  _ <- string "--"
  notFollowedBy (char '-')
  void (manyTill anySingle (void eol <|> eof))

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
parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"
