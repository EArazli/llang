{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.Parse
  ( SurfaceNode(..)
  , SurfaceParam(..)
  , parseSurfaceSpec
  , parseSurfaceExpr
  , surfaceSpecBlock
  ) where

import Data.Char (isAlphaNum)
import Data.Functor (($>))
import Data.Functor (void)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)

import Strat.Poly.Attr (AttrLit(..))
import Strat.Poly.DSL.AST (RawPolyTypeExpr(..), RawTypeRef(..), RawModExpr(..))
import Strat.Poly.Surface.Spec


-- Surface expression parse tree

data SurfaceParam
  = SPIdent Text
  | SPLit AttrLit
  | SPType RawPolyTypeExpr
  deriving (Eq, Show)

data SurfaceNode = SurfaceNode
  { snTemplate :: TemplateExpr
  , snParams :: M.Map Text SurfaceParam
  , snChildren :: [SurfaceNode]
  , snBinder :: Maybe BinderDecl
  } deriving (Eq, Show)


-- Spec parser

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

keyword :: Text -> Parser Text
keyword kw = lexeme (try (string kw <* notFollowedBy identChar))

identChar :: Parser Char
identChar = satisfy (\x -> isAlphaNum x || x == '_')

identBody :: Parser Text
identBody = do
  c <- letterChar <|> char '_'
  rest <- many identChar
  pure (T.pack (c : rest))

identRaw :: Parser Text
identRaw = lexeme identBody

ident :: Parser Text
ident = identRaw

stringLiteral :: Parser Text
stringLiteral = lexeme $ do
  _ <- char '"'
  content <- manyTill L.charLiteral (char '"')
  pure (T.pack content)

integer :: Parser Integer
integer = lexeme L.decimal

positiveInt :: Parser Int
positiveInt = do
  n <- lexeme L.decimal
  if n > (0 :: Int)
    then pure n
    else fail "expected a positive integer"

parseSurfaceSpec :: Text -> Either Text SurfaceSpec
parseSurfaceSpec input =
  case runParser (sc *> surfaceSpec <* eof) "<surface>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right spec -> Right spec

data SpecItem
  = ItemDoctrine Text
  | ItemBase Text
  | ItemMode Text
  | ItemLexer LexerSpec
  | ItemExpr ExprSpec

surfaceSpec :: Parser SurfaceSpec
surfaceSpec = do
  items <- many surfaceItem
  let spec0 = SurfaceSpec
        { ssName = ""
        , ssDoctrine = ""
        , ssBaseDoctrine = Nothing
        , ssMode = ""
        , ssLexer = Nothing
        , ssExprSpec = Nothing
        }
  let spec = foldl applySpec spec0 items
  if T.null (ssDoctrine spec)
    then fail "surface: missing doctrine"
    else
      if T.null (ssMode spec)
        then fail "surface: missing mode"
        else pure spec
  where
    applySpec spec item =
      case item of
        ItemDoctrine t -> spec { ssDoctrine = t }
        ItemBase t -> spec { ssBaseDoctrine = Just t }
        ItemMode t -> spec { ssMode = t }
        ItemLexer l -> spec { ssLexer = Just l }
        ItemExpr e -> spec { ssExprSpec = Just e }

surfaceItem :: Parser SpecItem
surfaceItem =
  choice
    [ ItemDoctrine <$> (symbol "doctrine" *> ident <* optionalSemi)
    , ItemBase <$> (symbol "base" *> ident <* optionalSemi)
    , ItemMode <$> (symbol "mode" *> ident <* optionalSemi)
    , ItemLexer <$> lexerBlock
    , ItemExpr <$> exprBlock
    ]

optionalSemi :: Parser ()
optionalSemi = void (optional (symbol ";"))

data LexItem = LexKeywords [Text] | LexSymbols [Text]

lexerBlock :: Parser LexerSpec
lexerBlock = do
  _ <- symbol "lexer"
  _ <- symbol "{"
  items <- many lexerItem
  _ <- symbol "}"
  optionalSemi
  let kws = concat [xs | LexKeywords xs <- items]
  let syms = concat [xs | LexSymbols xs <- items]
  pure LexerSpec { lsKeywords = kws, lsSymbols = syms }
  where
    lexerItem =
      (LexKeywords <$> (symbol "keywords" *> symbol ":" *> ident `sepBy` symbol "," <* optionalSemi))
        <|> (LexSymbols <$> (symbol "symbols" *> symbol ":" *> stringLiteral `sepBy` symbol "," <* optionalSemi))

data ExprItem
  = ExprAtoms [ExprRule]
  | ExprPrefixes [ExprRule]
  | ExprInfixes [InfixRule]
  | ExprApp AppRule

exprBlock :: Parser ExprSpec
exprBlock = do
  _ <- symbol "expr"
  _ <- symbol "{"
  items <- many exprItem
  _ <- symbol "}"
  optionalSemi
  let atoms = concat [xs | ExprAtoms xs <- items]
  let prefixes = concat [xs | ExprPrefixes xs <- items]
  let infixes = concat [xs | ExprInfixes xs <- items]
  let apps = [x | ExprApp x <- items]
  let app =
        case apps of
          [] -> Nothing
          (a:_) -> Just a
  pure ExprSpec
    { esAtoms = atoms
    , esPrefixes = prefixes
    , esInfixes = infixes
    , esApp = app
    }
  where
    exprItem =
      atomBlock <|> prefixBlock <|> appBlock <|> infixItem

    atomBlock = do
      _ <- symbol "atom"
      _ <- symbol ":"
      rules <- exprRules
      _ <- symbol ";"
      pure (ExprAtoms rules)

    prefixBlock = do
      _ <- symbol "prefix"
      _ <- symbol ":"
      rules <- exprRules
      _ <- symbol ";"
      pure (ExprPrefixes rules)

    appBlock = do
      _ <- symbol "application"
      _ <- symbol ":"
      _ <- symbol "<"
      _ <- symbol "expr"
      _ <- symbol ">"
      _ <- symbol "<"
      _ <- symbol "expr"
      _ <- symbol ">"
      _ <- symbol "=>"
      act <- action
      _ <- symbol ";"
      pure (ExprApp (AppRule act))

    infixItem = do
      assoc <- (symbol "infixl" $> AssocL) <|> (symbol "infixr" $> AssocR)
      prec <- lexeme L.decimal
      tok <- stringLiteral
      _ <- symbol "=>"
      act <- action
      _ <- symbol ";"
      pure (ExprInfixes [InfixRule assoc prec tok act])

    exprRules = sepBy1 exprRule (symbol "|")

    exprRule = do
      pats <- patternItems
      _ <- symbol "=>"
      act <- action
      binder <- optional binderDecl
      pure ExprRule { erPattern = pats, erAction = act, erBinder = binder }

patternItems :: Parser [PatItem]
patternItems = manyTill patItem (lookAhead (symbol "=>" <|> symbol "|" <|> symbol ";"))

captureName :: Parser (Maybe Text)
captureName = optional (symbol "(" *> identRaw <* symbol ")")

patItem :: Parser PatItem
patItem =
  choice
    [ symbol "ident" *> (PatIdent <$> captureName)
    , symbol "int" *> (PatInt <$> captureName)
    , symbol "string" *> (PatString <$> captureName)
    , symbol "bool" *> (PatBool <$> captureName)
    , try (symbol "<" *> symbol "expr" *> symbol ">" $> PatExpr)
    , try (symbol "<" *> symbol "type" *> symbol ">" *> (PatType <$> captureName))
    , PatLit <$> stringLiteral
    ]

action :: Parser Action
action =
  try (symbol "<" *> symbol "expr" *> symbol ">" $> ActionExpr)
    <|> (ActionTemplate <$> templateExpr)

binderDecl :: Parser BinderDecl
binderDecl = do
  _ <- symbol "bind"
  bindIn <|> bindLet
  where
    bindIn = do
      _ <- symbol "in"
      _ <- symbol "("
      varCap <- ident
      _ <- symbol ","
      typeCap <- ident
      _ <- symbol ","
      bodyHole <- positiveInt
      _ <- symbol ")"
      pure BindIn
        { bdVarCap = varCap
        , bdTypeCap = typeCap
        , bdBodyHole = bodyHole
        }
    bindLet = do
      _ <- symbol "let"
      _ <- symbol "("
      varCap <- ident
      _ <- symbol ","
      valueHole <- positiveInt
      _ <- symbol ","
      bodyHole <- positiveInt
      _ <- symbol ")"
      pure BindLet
        { bdVarCap = varCap
        , bdValueHole = valueHole
        , bdBodyHole = bodyHole
        }

-- Template expressions (diag expr + placeholders)

templateExpr :: Parser TemplateExpr
templateExpr = makeExprParser templateTerm operators
  where
    operators =
      [ [ InfixL (symbol "*" $> TTensor) ]
      , [ InfixL (semiOp $> TComp) ]
      ]
    semiOp = try (symbol ";" <* lookAhead templateTerm)

templateTerm :: Parser TemplateExpr
templateTerm =
  choice
    [ try templateId
    , try templateBox
    , try templateLoop
    , try templateHole
    , try templateTermRef
    , try templateGen
    , parens templateExpr
    ]

templateId :: Parser TemplateExpr
templateId = do
  _ <- symbol "id"
  ctx <- contextExpr
  pure (TId ctx)

templateGen :: Parser TemplateExpr
templateGen = do
  ref <- templateGenRef
  mArgs <- optional (symbol "{" *> typeExpr `sepBy` symbol "," <* symbol "}")
  mAttrArgs <- optional templateAttrArgs
  mBinderArgs <- optional templateBinderArgs
  pure (TGen ref mArgs mAttrArgs mBinderArgs)

templateGenRef :: Parser GenRef
templateGenRef =
  (GenHole <$> hashIdent) <|> (GenLit <$> identTemplate)

hashIdent :: Parser Text
hashIdent = lexeme (char '#' *> identBody)

identTemplate :: Parser Text
identTemplate = do
  name <- ident
  if name `elem` templateReserved
    then fail "reserved keyword in template expression"
    else pure name

templateReserved :: [Text]
templateReserved =
  [ "atom"
  , "prefix"
  , "application"
  , "infixl"
  , "infixr"
  , "bind"
  ]

templateBox :: Parser TemplateExpr
templateBox = do
  _ <- symbol "box"
  name <- ident
  _ <- symbol "{"
  inner <- templateExpr
  _ <- symbol "}"
  pure (TBox name inner)

templateLoop :: Parser TemplateExpr
templateLoop = do
  _ <- symbol "loop"
  _ <- symbol "{"
  inner <- templateExpr
  _ <- symbol "}"
  pure (TLoop inner)

templateHole :: Parser TemplateExpr
templateHole = lexeme $ do
  _ <- char '$'
  number <- optional (some digitChar)
  case number of
    Just ds -> pure (THole (read ds))
    Nothing -> TVar <$> identBody

templateTermRef :: Parser TemplateExpr
templateTermRef = do
  _ <- symbol "@"
  name <- ident
  pure (TTermRef name)

templateAttrArgs :: Parser [TemplateAttrArg]
templateAttrArgs = do
  _ <- symbol "("
  args <- templateAttrArg `sepBy` symbol ","
  _ <- symbol ")"
  if mixedArgStyles args
    then fail "template attribute arguments must be either all named or all positional"
    else pure args
  where
    mixedArgStyles [] = False
    mixedArgStyles xs =
      let named = [() | TAName _ _ <- xs]
          positional = [() | TAPos _ <- xs]
       in not (null named) && not (null positional)

templateAttrArg :: Parser TemplateAttrArg
templateAttrArg =
  try named <|> positional
  where
    named = do
      field <- ident
      _ <- symbol "="
      term <- templateAttrTerm
      pure (TAName field term)
    positional = TAPos <$> templateAttrTerm

templateAttrTerm :: Parser AttrTemplate
templateAttrTerm =
  choice
    [ try attrHole
    , ATLIT . ALInt . fromIntegral <$> integer
    , ATLIT . ALString <$> stringLiteral
    , ATLIT (ALBool True) <$ keyword "true"
    , ATLIT (ALBool False) <$ keyword "false"
    , ATVar <$> ident
    ]
  where
    attrHole = do
      _ <- symbol "#"
      name <- ident
      pure (ATHole name)

templateBinderArgs :: Parser [TemplateBinderArg]
templateBinderArgs = do
  _ <- symbol "["
  args <- templateBinderArg `sepBy` symbol ","
  _ <- symbol "]"
  pure args

templateBinderArg :: Parser TemplateBinderArg
templateBinderArg =
  try (TBAMeta <$> binderMetaVar)
    <|> (TBAExpr <$> templateExpr)

binderMetaVar :: Parser Text
binderMetaVar = lexeme (char '?' *> identBody)

contextExpr :: Parser [RawPolyTypeExpr]
contextExpr = do
  _ <- symbol "["
  tys <- typeExpr `sepBy` symbol ","
  _ <- symbol "]"
  pure tys

typeExpr :: Parser RawPolyTypeExpr
typeExpr = lexeme (try modApp <|> regular)
  where
    modApp = do
      me <- rawModExprComplex
      _ <- symbol "("
      inner <- typeExpr
      _ <- symbol ")"
      pure (RPTMod me inner)
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
      mArgs <- optional (symbol "(" *> typeExpr `sepBy` symbol "," <* symbol ")")
      case mQual of
        Just qualName ->
          let ref = RawTypeRef { rtrMode = Just name, rtrName = qualName }
           in pure (RPTCon ref (maybe [] id mArgs))
        Nothing ->
          case T.uncons name of
            Nothing -> fail "empty type"
            Just (c, _) ->
              case mArgs of
                Just args ->
                  let ref = RawTypeRef { rtrMode = Nothing, rtrName = name }
                   in pure (RPTCon ref args)
                Nothing ->
                  if isLowerChar c
                    then pure (RPTVar name)
                    else
                      let ref = RawTypeRef { rtrMode = Nothing, rtrName = name }
                       in pure (RPTCon ref [])
    isLowerChar ch = ch >= 'a' && ch <= 'z'

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"

-- Surface program parsing (expressions)

parseSurfaceExpr :: SurfaceSpec -> Text -> Either Text SurfaceNode
parseSurfaceExpr spec input =
  case ssExprSpec spec of
    Nothing -> Left "surface: expression grammar missing"
    Just exprSpec ->
      case ssLexer spec of
        Nothing -> Left "surface: lexer missing"
        Just lexSpec ->
          case runParser (sc *> parseExpr lexSpec exprSpec 0 <* eof) "<surface-expr>" input of
            Left err -> Left (T.pack (errorBundlePretty err))
            Right ast -> Right ast

data Capture
  = CapIdent (Maybe Text) Text
  | CapLit (Maybe Text) AttrLit
  | CapType (Maybe Text) RawPolyTypeExpr
  | CapExpr SurfaceNode
  | CapSkip
  deriving (Eq, Show)

parseExpr :: LexerSpec -> ExprSpec -> Int -> Parser SurfaceNode
parseExpr lexSpec exprSpec minPrec = do
  left <- parseTerm lexSpec exprSpec
  parseRest left
  where
    appPrec = maximum (0 : map irPrec (esInfixes exprSpec)) + 1

    parseRest left = do
      mApp <- try (parseApplication lexSpec exprSpec minPrec appPrec left) <|> pure Nothing
      case mApp of
        Just next -> parseRest next
        Nothing -> do
          mInfix <- parseInfix lexSpec exprSpec minPrec left
          case mInfix of
            Just next -> parseRest next
            Nothing -> pure left

parseApplication :: LexerSpec -> ExprSpec -> Int -> Int -> SurfaceNode -> Parser (Maybe SurfaceNode)
parseApplication lexSpec exprSpec minPrec appPrec left =
  case esApp exprSpec of
    Nothing -> pure Nothing
    Just (AppRule act) ->
      if appPrec < minPrec
        then pure Nothing
        else do
          mRight <- optional (try (parseExpr lexSpec exprSpec (appPrec + 1)))
          case mRight of
            Nothing -> pure Nothing
            Just right ->
              case applyAction act Nothing [CapExpr left, CapExpr right] of
                Left err -> fail (T.unpack err)
                Right ast -> pure (Just ast)

parseInfix :: LexerSpec -> ExprSpec -> Int -> SurfaceNode -> Parser (Maybe SurfaceNode)
parseInfix lexSpec exprSpec minPrec left = do
  let rules = esInfixes exprSpec
  parseAny rules
  where
    parseAny [] = pure Nothing
    parseAny (r:rs) = do
      let prec = irPrec r
      if prec < minPrec
        then parseAny rs
        else do
          matched <- optional (try (literalToken lexSpec (irToken r)))
          case matched of
            Nothing -> parseAny rs
            Just _ -> do
              let nextMin =
                    case irAssoc r of
                      AssocL -> prec + 1
                      AssocR -> prec
              right <- parseExpr lexSpec exprSpec nextMin
              case applyAction (irAction r) Nothing [CapExpr left, CapExpr right] of
                Left err -> fail (T.unpack err)
                Right ast -> pure (Just ast)

parseTerm :: LexerSpec -> ExprSpec -> Parser SurfaceNode
parseTerm lexSpec exprSpec =
  choice
    [ try (parsePatternRules lexSpec exprSpec (esPrefixes exprSpec))
    , parsePatternRules lexSpec exprSpec (esAtoms exprSpec)
    ]

parsePatternRules :: LexerSpec -> ExprSpec -> [ExprRule] -> Parser SurfaceNode
parsePatternRules lexSpec exprSpec rules =
  choice (map (try . parsePatternRule lexSpec exprSpec) rules)

parsePatternRule :: LexerSpec -> ExprSpec -> ExprRule -> Parser SurfaceNode
parsePatternRule lexSpec exprSpec rule = do
  caps <- mapM (parseRulePatItem lexSpec exprSpec) (erPattern rule)
  case applyAction (erAction rule) (erBinder rule) caps of
    Left err -> fail (T.unpack err)
    Right ast -> pure ast

parseRulePatItem :: LexerSpec -> ExprSpec -> PatItem -> Parser Capture
parseRulePatItem lexSpec exprSpec item =
  case item of
    PatLit lit -> literalToken lexSpec lit *> pure CapSkip
    PatIdent cap -> CapIdent cap <$> identToken lexSpec
    PatInt cap -> CapLit cap . ALInt . fromIntegral <$> integer
    PatString cap -> CapLit cap . ALString <$> stringLiteral
    PatBool cap ->
      (literalToken lexSpec "true" $> CapLit cap (ALBool True))
        <|> (literalToken lexSpec "false" $> CapLit cap (ALBool False))
    PatExpr -> CapExpr <$> parseExpr lexSpec exprSpec 0
    PatType cap -> CapType cap <$> typeExpr

applyAction :: Action -> Maybe BinderDecl -> [Capture] -> Either Text SurfaceNode
applyAction act binder caps = do
  params <- buildParamMap caps
  let children = [e | CapExpr e <- caps]
  template <-
    case act of
      ActionExpr ->
        case children of
          [_] -> Right (THole 1)
          _ -> Left "surface: <expr> action expects exactly one expression capture"
      ActionTemplate t -> Right t
  pure SurfaceNode
    { snTemplate = template
    , snParams = params
    , snChildren = children
    , snBinder = binder
    }

buildParamMap :: [Capture] -> Either Text (M.Map Text SurfaceParam)
buildParamMap = foldl step (Right M.empty)
  where
    step acc cap = do
      mp <- acc
      case cap of
        CapIdent mName v -> insertNamed mName (SPIdent v) mp
        CapLit mName lit -> insertNamed mName (SPLit lit) mp
        CapType mName ty -> insertNamed mName (SPType ty) mp
        CapExpr _ -> Right mp
        CapSkip -> Right mp

    insertNamed mName value mp =
      case mName of
        Nothing -> Right mp
        Just name ->
          if M.member name mp
            then Left ("surface: duplicate capture name: " <> name)
            else Right (M.insert name value mp)

identToken :: LexerSpec -> Parser Text
identToken lexSpec = do
  name <- identRaw
  if name `elem` lsKeywords lexSpec
    then fail "reserved keyword"
    else pure name

literalToken :: LexerSpec -> Text -> Parser Text
literalToken lexSpec tok =
  if tok `elem` lsSymbols lexSpec
    then symbol tok
    else keyword tok

surfaceSpecBlock :: Parser SurfaceSpec
surfaceSpecBlock = do
  _ <- symbol "{"
  spec <- surfaceSpec
  _ <- symbol "}"
  optionalSemi
  pure spec
