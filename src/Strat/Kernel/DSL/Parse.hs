{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.DSL.Parse
  ( parseRawFile
  ) where

import Strat.Kernel.DSL.AST
import Strat.Kernel.Types
import Strat.Model.Spec (MExpr(..))
import Data.Text (Text)
import qualified Data.Text as T
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

rawFile :: Parser RawFile
rawFile = do
  decls <- many (sc *> decl)
  pure (RawFile decls)


-- Declarations

decl :: Parser RawDecl
decl =
  importDecl
    <|> doctrineDecl
    <|> syntaxDecl
    <|> modelDecl
    <|> surfaceDecl
    <|> morphismDecl
    <|> implementsDecl
    <|> runSpecDecl
    <|> runDecl

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
  pushoutDecl name <|> whereDecl name
  where
    whereDecl docName = do
      mExt <- optional (symbol "extends" *> ident)
      _ <- symbol "where"
      items <- ruleBlock
      optionalSemi
      pure (DeclDoctrineWhere docName mExt items)
    pushoutDecl docName = do
      _ <- symbol "="
      _ <- symbol "pushout"
      leftMor <- qualifiedIdent
      rightMor <- qualifiedIdent
      optionalSemi
      pure (DeclDoctrinePushout docName leftMor rightMor)

syntaxDecl :: Parser RawDecl
syntaxDecl = do
  coreSyntaxDecl <|> surfaceSyntaxDecl
  where
    coreSyntaxDecl = do
      _ <- symbol "syntax"
      name <- ident
      _ <- symbol "where"
      items <- syntaxBlock
      optionalSemi
      pure (DeclSyntaxWhere (RawSyntaxDecl name SyntaxDoctrine items))
    surfaceSyntaxDecl = do
      _ <- symbol "surface_syntax"
      name <- ident
      _ <- symbol "for"
      surf <- ident
      _ <- symbol "where"
      items <- syntaxBlock
      optionalSemi
      pure (DeclSyntaxWhere (RawSyntaxDecl name (SyntaxSurface surf) items))

modelDecl :: Parser RawDecl
modelDecl = do
  _ <- symbol "model"
  name <- ident
  _ <- symbol ":"
  doc <- ident
  _ <- symbol "where"
  items <- modelBlock
  optionalSemi
  pure (DeclModelWhere name doc items)

surfaceDecl :: Parser RawDecl
surfaceDecl = do
  _ <- symbol "surface"
  name <- ident
  _ <- symbol "where"
  items <- surfaceBlock
  optionalSemi
  pure (DeclSurfaceWhere (RawSurfaceDecl name items))

morphismDecl :: Parser RawDecl
morphismDecl = do
  _ <- symbol "morphism"
  name <- qualifiedIdent
  _ <- symbol ":"
  src <- ident
  _ <- symbol "->"
  tgt <- ident
  _ <- symbol "where"
  items <- morphismBlock
  mcheck <- optional morphismCheck
  optionalSemi
  pure (DeclMorphismWhere (RawMorphismDecl name src tgt items mcheck))

implementsDecl :: Parser RawDecl
implementsDecl = do
  _ <- symbol "implements"
  iface <- ident
  _ <- symbol "for"
  tgt <- ident
  _ <- symbol "using"
  name <- qualifiedIdent
  optionalSemi
  pure (DeclImplements (RawImplementsDecl iface tgt name))

runSpecDecl :: Parser RawDecl
runSpecDecl = do
  _ <- symbol "run_spec"
  name <- ident
  _ <- symbol "where"
  items <- runBlock
  optionalSemi
  pure (DeclRunSpec name (RawRunSpec (buildRun items "")))

runDecl :: Parser RawDecl
runDecl = do
  _ <- symbol "run"
  name <- ident
  using <- optional (symbol "using" *> ident)
  items <- option [] (symbol "where" *> runBlock)
  exprText <- runBody
  pure (DeclRun (RawNamedRun name using (buildRun items exprText)))

runBody :: Parser Text
runBody = do
  _ <- delimiterLine
  body <- T.pack <$> manyTill anySingle (lookAhead (try delimiterLine <|> eof))
  _ <- optional (try delimiterLine)
  pure (T.strip body)

delimiterLine :: Parser ()
delimiterLine = do
  _ <- optional (many (char ' ' <|> char '\t'))
  _ <- string "---"
  _ <- optional (many (char ' ' <|> char '\t'))
  void eol <|> eof


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
  tele <- many binder
  optionalSemi
  pure RawSortDecl
    { rsName = name
    , rsTele = tele
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

term :: Parser RawTerm
term = lexeme (varTerm <|> appTerm)

varTerm :: Parser RawTerm
varTerm = do
  _ <- char '?'
  name <- identRaw
  pure (RVar name)

appTerm :: Parser RawTerm
appTerm = do
  name <- qualifiedIdentRaw
  mArgs <- optional (symbol "(" *> term `sepBy` symbol "," <* symbol ")")
  case mArgs of
    Nothing -> pure (RApp name [])
    Just args -> pure (RApp name args)

rawSort :: Parser RawSort
rawSort = lexeme $ do
  name <- qualifiedIdentRaw
  mArgs <- optional (symbol "(" *> term `sepBy` symbol "," <* symbol ")")
  pure (RawSort name (maybe [] id mArgs))


-- Syntax block

syntaxBlock :: Parser [RawSyntaxItem]
syntaxBlock = do
  _ <- symbol "{"
  items <- many syntaxItem
  _ <- symbol "}"
  pure items

syntaxItem :: Parser RawSyntaxItem
syntaxItem =
  surfaceTyItem <|> surfaceTmItem <|> printItem <|> parseItem <|> allowCallItem <|> varPrefixItem

surfaceTyItem :: Parser RawSyntaxItem
surfaceTyItem = do
  _ <- symbol "ty"
  _ <- symbol "print"
  note <- surfaceNotation
  optionalSemi
  pure (RSTy note)

surfaceTmItem :: Parser RawSyntaxItem
surfaceTmItem = do
  _ <- symbol "tm"
  _ <- symbol "print"
  note <- surfaceNotation
  optionalSemi
  pure (RSTm note)

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


-- Surface block

surfaceBlock :: Parser [RawSurfaceItem]
surfaceBlock = do
  _ <- symbol "{"
  items <- many surfaceItem
  _ <- symbol "}"
  pure items

surfaceItem :: Parser RawSurfaceItem
surfaceItem =
  requiresItem
    <|> deriveContextsItem
    <|> contextSortItem
    <|> surfaceSortItem
    <|> surfaceConItem
    <|> surfaceJudgItem
    <|> surfaceDefineItem
    <|> surfaceRuleItem

requiresItem :: Parser RawSurfaceItem
requiresItem = do
  _ <- symbol "requires"
  alias <- ident
  _ <- symbol ":"
  doc <- ident
  optionalSemi
  pure (RSRequires alias doc)

deriveContextsItem :: Parser RawSurfaceItem
deriveContextsItem = do
  _ <- symbol "derive"
  _ <- symbol "contexts"
  _ <- symbol "using"
  alias <- ident
  optionalSemi
  pure (RSDeriveContexts alias)

contextSortItem :: Parser RawSurfaceItem
contextSortItem = do
  _ <- symbol "context_sort"
  name <- ident
  optionalSemi
  pure (RSContextSort name)

surfaceSortItem :: Parser RawSurfaceItem
surfaceSortItem = do
  _ <- symbol "sort"
  name <- ident
  optionalSemi
  pure (RSSort name)

surfaceConItem :: Parser RawSurfaceItem
surfaceConItem = do
  _ <- symbol "con"
  name <- ident
  _ <- symbol ":"
  args <- many surfaceConArg
  res <- if null args then ident else symbol "->" *> ident
  optionalSemi
  pure (RSCon (RawSurfaceCon name args res))

surfaceConArg :: Parser RawSurfaceArg
surfaceConArg = do
  _ <- symbol "("
  name <- ident
  _ <- symbol ":"
  binders <- option [] binderList
  s <- ident
  _ <- symbol ")"
  pure (RawSurfaceArg name binders s)
  where
    binderList = do
      _ <- symbol "["
      bs <- binderDecl `sepBy` symbol ","
      _ <- symbol "]"
      pure bs
    binderDecl = do
      bname <- ident
      _ <- symbol ":"
      bty <- surfaceTerm
      pure (bname, bty)

surfaceJudgItem :: Parser RawSurfaceItem
surfaceJudgItem = do
  _ <- symbol "judgement"
  name <- ident
  _ <- symbol ":"
  params <- many surfaceJudgParam
  outs <- option [] (symbol "=>" *> many surfaceJudgParam)
  optionalSemi
  pure (RSJudg (RawSurfaceJudg name params outs))

surfaceJudgParam :: Parser RawSurfaceJudgParam
surfaceJudgParam = do
  _ <- symbol "("
  pname <- ident
  _ <- symbol ":"
  psort <- ident
  _ <- symbol ")"
  pure (RawSurfaceJudgParam pname psort)

surfaceRuleItem :: Parser RawSurfaceItem
surfaceRuleItem = do
  _ <- symbol "rule"
  name <- ident
  _ <- symbol ":"
  premises <- many premiseDecl
  _ <- ruleSeparator
  concl <- surfaceConclusion
  optionalSemi
  pure (RSRule (RawSurfaceRule name premises concl))

premiseDecl :: Parser RawSurfacePremise
premiseDecl = do
  _ <- symbol "premise"
  p <- lookupPremise <|> judgPremise
  optionalSemi
  pure p

lookupPremise :: Parser RawSurfacePremise
lookupPremise = do
  _ <- symbol "lookup"
  _ <- symbol "("
  ctx <- ident
  _ <- symbol ","
  idx <- natPat
  _ <- symbol ")"
  _ <- symbol "="
  out <- ident
  pure (RPremiseLookup ctx idx out)

judgPremise :: Parser RawSurfacePremise
judgPremise = do
  name <- ident
  args <- surfacePatArgs
  outs <- option [] (symbol "=>" *> outputVars)
  under <- optional underClause
  pure (RPremiseJudg name args outs under)
  where
    outputVars = ident `sepBy1` symbol ","

underClause :: Parser (Text, Text, RawSurfaceTerm)
underClause = do
  _ <- symbol "under"
  _ <- symbol "("
  ctx <- ident
  _ <- symbol ","
  vname <- ident
  _ <- symbol ":"
  ty <- surfaceTerm
  _ <- symbol ")"
  pure (ctx, vname, ty)

surfaceConclusion :: Parser RawSurfaceConclusion
surfaceConclusion = do
  name <- ident
  args <- surfacePatArgs
  outs <- option [] (symbol "=>" *> coreExprs)
  pure (RawSurfaceConclusion name args outs)
  where
    coreExprs = coreExpr `sepBy1` symbol ","

surfacePatArgs :: Parser [RawSurfacePat]
surfacePatArgs = do
  _ <- symbol "("
  args <- surfacePat `sepBy` symbol ","
  _ <- symbol ")"
  pure args

surfaceDefineItem :: Parser RawSurfaceItem
surfaceDefineItem = do
  _ <- symbol "define"
  name <- ident
  clause <- defineClause
  optionalSemi
  pure (RSDefine (RawDefine name [clause]))

defineClause :: Parser RawDefineClause
defineClause = do
  args <- defineArgs
  _ <- symbol "="
  body <- coreExpr
  wh <- option [] whereClause
  pure (RawDefineClause args body wh)

defineArgs :: Parser [RawDefinePat]
defineArgs = do
  _ <- symbol "("
  args <- definePat `sepBy` symbol ","
  _ <- symbol ")"
  pure args

definePat :: Parser RawDefinePat
definePat =
  try ctxOnly
    <|> (RDPSurf <$> surfacePatNonVar)
    <|> (RDPNat <$> natPatDefine)
    <|> (RDPVar <$> ident)
  where
    ctxOnly = RDPCtx <$> ctxPatBare

natPatDefine :: Parser RawNatPat
natPatDefine =
  (symbol "0" $> RNPZero)
    <|> try (do
        name <- ident
        _ <- symbol "+"
        _ <- symbol "1"
        pure (RNPSucc name))

surfacePatNonVar :: Parser RawSurfacePat
surfacePatNonVar =
  choice
    [ parens surfacePatNonVar
    , boundPat
    , try conWithArgs
    ]
  where
    parens = between (symbol "(") (symbol ")")
    boundPat = do
      _ <- char '#'
      sc
      (RSPBound . fromIntegral <$> integer)
        <|> (RSPBoundVar <$> ident)
    conWithArgs = do
      name <- ident
      _ <- symbol "("
      args <- surfacePat `sepBy` symbol ","
      _ <- symbol ")"
      pure (RSPCon name args)

whereClause :: Parser [RawWhereClause]
whereClause = do
  _ <- symbol "where"
  clause `sepBy1` symbol ","
  where
    clause = do
      name <- ident
      _ <- symbol "="
      pat <- ctxPat
      pure (RawWhereClause name pat)

ctxPat :: Parser RawCtxPat
ctxPat = ctxPatBare <|> (RCPVar <$> ident)

ctxPatBare :: Parser RawCtxPat
ctxPatBare =
  (symbol "∙" $> RCPEmpty)
    <|> (do
          _ <- symbol "("
          ctx <- ident
          _ <- symbol ","
          vname <- ident
          _ <- symbol ":"
          ty <- surfaceTerm
          _ <- symbol ")"
          pure (RCPExt ctx vname ty))

natPat :: Parser RawNatPat
natPat =
  (symbol "0" $> RNPZero)
    <|> try (do
        name <- ident
        _ <- symbol "+"
        _ <- symbol "1"
        pure (RNPSucc name))
    <|> (RNPVar <$> ident)

surfaceTerm :: Parser RawSurfaceTerm
surfaceTerm =
  choice
    [ parens surfaceTerm
    , conOrVar
    ]
  where
    parens = between (symbol "(") (symbol ")")
    conOrVar = do
      name <- ident
      args <- optional (symbol "(" *> surfaceTerm `sepBy` symbol "," <* symbol ")")
      pure $
        case args of
          Nothing -> RSTVar name
          Just as -> RSTCon name as

surfacePat :: Parser RawSurfacePat
surfacePat =
  choice
    [ parens surfacePat
    , boundPat
    , conOrVar
    ]
  where
    parens = between (symbol "(") (symbol ")")
    boundPat = do
      _ <- char '#'
      sc
      (RSPBound . fromIntegral <$> integer)
        <|> (RSPBoundVar <$> ident)
    conOrVar = do
      name <- ident
      args <- optional (symbol "(" *> surfacePat `sepBy` symbol "," <* symbol ")")
      pure $
        case args of
          Nothing -> RSPVar name
          Just as -> RSPCon name as

ruleSeparator :: Parser ()
ruleSeparator = do
  _ <- some (char '-')
  optional (some (char '-'))
  sc
  pure ()

coreExpr :: Parser RawCoreExpr
coreExpr = do
  name <- qualifiedIdent
  args <- optional (symbol "(" *> coreExpr `sepBy` symbol "," <* symbol ")")
  pure $ case args of
    Nothing -> RCEVar name
    Just as -> RCEApp name as


surfaceNotation :: Parser RawSurfaceNotation
surfaceNotation =
  choice
    [ atomNotation
    , prefixNotation
    , infixNotation
    , binderNotation
    , appNotation
    , tupleNotation
    ]

atomNotation :: Parser RawSurfaceNotation
atomNotation = do
  _ <- symbol "atom"
  tok <- stringLiteral
  _ <- symbol "="
  con <- ident
  pure (RSNAtom tok con)

prefixNotation :: Parser RawSurfaceNotation
prefixNotation = do
  _ <- symbol "prefix"
  tok <- stringLiteral
  _ <- symbol "="
  con <- ident
  pure (RSNPrefix tok con)

infixNotation :: Parser RawSurfaceNotation
infixNotation = do
  assoc <- (symbol "infixl" $> SurfAssocL) <|> (symbol "infixr" $> SurfAssocR) <|> (symbol "infix" $> SurfAssocN)
  prec <- integer
  tok <- stringLiteral
  _ <- symbol "="
  con <- ident
  pure (RSNInfix assoc (fromIntegral prec) tok con)

binderNotation :: Parser RawSurfaceNotation
binderNotation = do
  _ <- symbol "binder"
  tok <- stringLiteral
  tySep <- stringLiteral
  bodySep <- stringLiteral
  _ <- symbol "="
  con <- ident
  pure (RSNBinder tok tySep bodySep con)

appNotation :: Parser RawSurfaceNotation
appNotation = do
  _ <- symbol "app"
  _ <- symbol "="
  con <- ident
  pure (RSNApp con)

tupleNotation :: Parser RawSurfaceNotation
tupleNotation = do
  _ <- symbol "tuple"
  tok <- stringLiteral
  _ <- symbol "="
  con <- ident
  pure (RSNTuple tok con)


-- Morphism block

morphismBlock :: Parser [RawMorphismItem]
morphismBlock = do
  _ <- symbol "{"
  items <- many morphismItem
  _ <- symbol "}"
  pure items

morphismItem :: Parser RawMorphismItem
morphismItem = sortItem <|> opItem
  where
    sortItem = do
      _ <- symbol "sort"
      src <- qualifiedIdent
      _ <- symbol "="
      tgt <- qualifiedIdent
      optionalSemi
      pure (RMISort src tgt)
    opItem = do
      _ <- symbol "op"
      src <- qualifiedIdent
      params <- optional (symbol "(" *> ident `sepBy` symbol "," <* symbol ")")
      _ <- symbol "="
      rhs <- term
      optionalSemi
      pure (RMIOp src params rhs)

morphismCheck :: Parser RawMorphismCheck
morphismCheck = do
  _ <- symbol "check"
  _ <- symbol "{"
  items <- many checkItem
  _ <- symbol "}"
  let policy = firstJust [p | Left p <- items]
  let fuel = firstJust [f | Right f <- items]
  pure RawMorphismCheck { rmcPolicy = policy, rmcFuel = fuel }
  where
    checkItem =
      (symbol "policy" *> (Left <$> ident) <* optionalSemi)
        <|> (symbol "fuel" *> (Right . fromIntegral <$> integer) <* optionalSemi)
    firstJust [] = Nothing
    firstJust (x:_) = Just x


-- Run block

runBlock :: Parser [RunItem]
runBlock = do
  _ <- symbol "{"
  items <- many runItem
  _ <- symbol "}"
  pure items

data RunItem
  = RunDoctrine Text
  | RunSyntax Text
  | RunSurface Text
  | RunSurfaceSyntax Text
  | RunModel Text
  | RunUse Text Text
  | RunOpen Text
  | RunPolicy Text
  | RunFuel Int
  | RunShow RawRunShow

runItem :: Parser RunItem
runItem =
  doctrineItem
    <|> syntaxItemRun
    <|> surfaceSyntaxItemRun
    <|> surfaceItemRun
    <|> modelItemRun
    <|> useItemRun
    <|> openItem
    <|> policyItem
    <|> fuelItem
    <|> showItem

doctrineItem :: Parser RunItem
doctrineItem = do
  _ <- symbol "doctrine"
  e <- ident
  optionalSemi
  pure (RunDoctrine e)

syntaxItemRun :: Parser RunItem
syntaxItemRun = do
  _ <- symbol "syntax"
  name <- ident
  optionalSemi
  pure (RunSyntax name)

surfaceItemRun :: Parser RunItem
surfaceItemRun = do
  _ <- symbol "surface"
  name <- ident
  optionalSemi
  pure (RunSurface name)

surfaceSyntaxItemRun :: Parser RunItem
surfaceSyntaxItemRun = do
  _ <- symbol "surface_syntax"
  name <- ident
  optionalSemi
  pure (RunSurfaceSyntax name)

useItemRun :: Parser RunItem
useItemRun = do
  _ <- symbol "use"
  alias <- ident
  _ <- symbol "="
  name <- qualifiedIdent
  optionalSemi
  pure (RunUse alias name)

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
      <|> (symbol "input" $> RawShowInput)
  optionalSemi
  pure (RunShow flag)

buildRun :: [RunItem] -> Text -> RawRun
buildRun items exprText =
  RawRun
    { rrDoctrine = pickDoctrine
    , rrSyntax = pickSyntax
    , rrSurface = pickSurface
    , rrSurfaceSyntax = pickSurfaceSyntax
    , rrModel = pickModel
    , rrUses = uses
    , rrOpen = opens
    , rrPolicy = pickPolicy
    , rrFuel = pickFuel
    , rrShowFlags = showFlags
    , rrExprText = exprText
    }
  where
    pickDoctrine = firstJust [ e | RunDoctrine e <- items ]
    pickSyntax = firstJust [ n | RunSyntax n <- items ]
    pickSurface = firstJust [ n | RunSurface n <- items ]
    pickSurfaceSyntax = firstJust [ n | RunSurfaceSyntax n <- items ]
    pickModel = firstJust [ n | RunModel n <- items ]
    pickPolicy = firstJust [ p | RunPolicy p <- items ]
    pickFuel = firstJust [ f | RunFuel f <- items ]
    opens = [ n | RunOpen n <- items ]
    uses = [ (alias, name) | RunUse alias name <- items ]
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

qualifiedIdent :: Parser Text
qualifiedIdent = lexeme qualifiedIdentRaw

qualifiedIdentRaw :: Parser Text
qualifiedIdentRaw = do
  first <- identRaw
  rest <- many (char '.' *> identRaw)
  pure (T.intercalate "." (first : rest))

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
    lineComment
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
