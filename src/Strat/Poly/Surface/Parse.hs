{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.Parse
  ( parseSurfaceSpec
  , parseSurfaceExpr
  , surfaceSpecBlock
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Void (Void)
import Data.Char (isAlphaNum)
import Data.Functor (void)
import Data.Functor (($>))
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)

import Strat.Poly.Surface.Spec
import Strat.Poly.DSL.AST (RawPolyTypeExpr(..), RawTypeRef(..))
import Strat.Poly.Names (GenName(..))


-- Spec parser

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

identRaw :: Parser Text
identRaw = lexeme $ do
  c <- letterChar <|> char '_'
  rest <- many (satisfy (\x -> isAlphaNum x || x == '_'))
  pure (T.pack (c:rest))

ident :: Parser Text
ident = identRaw

stringLiteral :: Parser Text
stringLiteral = lexeme $ do
  _ <- char '"'
  content <- manyTill L.charLiteral (char '"')
  pure (T.pack content)

parseSurfaceSpec :: Text -> Either Text SurfaceSpec
parseSurfaceSpec input =
  case runParser (sc *> surfaceSpec <* eof) "<surface>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right spec -> Right spec

data SpecItem
  = ItemDoctrine Text
  | ItemMode Text
  | ItemContext Text RawPolyTypeExpr
  | ItemStructural StructuralSpec
  | ItemLexer LexerSpec
  | ItemExpr ExprSpec
  | ItemElab [ElabRule]

surfaceSpec :: Parser SurfaceSpec
surfaceSpec = do
  items <- many surfaceItem
  let spec0 = SurfaceSpec
        { ssName = ""
        , ssDoctrine = ""
        , ssMode = ""
        , ssContext = Nothing
        , ssStructural = defaultStructuralSpec
        , ssLexer = Nothing
        , ssExprSpec = Nothing
        , ssElabRules = M.empty
        }
  let spec = foldl applySpec spec0 items
  if T.null (ssDoctrine spec)
    then fail "surface: missing doctrine"
    else if T.null (ssMode spec)
      then fail "surface: missing mode"
      else pure spec
  where
    applySpec spec item =
      case item of
        ItemDoctrine t -> spec { ssDoctrine = t }
        ItemMode t -> spec { ssMode = t }
        ItemContext name ty -> spec { ssContext = Just (name, ty) }
        ItemStructural s -> spec { ssStructural = s }
        ItemLexer l -> spec { ssLexer = Just l }
        ItemExpr e -> spec { ssExprSpec = Just e }
        ItemElab rules -> spec { ssElabRules = foldl insertRule (ssElabRules spec) rules }
    insertRule mp rule =
      M.insert (erCtor rule) rule mp

surfaceItem :: Parser SpecItem
surfaceItem =
  choice
    [ ItemDoctrine <$> (symbol "doctrine" *> ident <* optionalSemi)
    , ItemMode <$> (symbol "mode" *> ident <* optionalSemi)
    , ItemContext <$> (symbol "context" *> ident <* symbol "=") <*> (typeExpr <* optionalSemi)
    , ItemStructural <$> structuralBlock
    , ItemLexer <$> lexerBlock
    , ItemExpr <$> exprBlock
    , ItemElab <$> elaborateBlock
    ]

defaultStructuralSpec :: StructuralSpec
defaultStructuralSpec =
  StructuralSpec
    { ssDiscipline = Cartesian
    , ssDupGen = Just (GenName "dup")
    , ssDropGen = Just (GenName "drop")
    }

data StructuralItem
  = StructDiscipline VarDiscipline
  | StructDup GenName
  | StructDrop GenName

structuralBlock :: Parser StructuralSpec
structuralBlock = do
  _ <- symbol "structural"
  _ <- symbol "{"
  items <- many structuralItem
  _ <- symbol "}"
  let spec0 = StructuralSpec { ssDiscipline = Cartesian, ssDupGen = Nothing, ssDropGen = Nothing }
  pure (foldl applyStructural spec0 items)
  where
    applyStructural spec item =
      case item of
        StructDiscipline d -> spec { ssDiscipline = d }
        StructDup name -> spec { ssDupGen = Just name }
        StructDrop name -> spec { ssDropGen = Just name }

structuralItem :: Parser StructuralItem
structuralItem =
  choice
    [ StructDiscipline <$> (symbol "discipline" *> symbol ":" *> discipline <* optionalSemi)
    , StructDup <$> (symbol "dup" *> symbol ":" *> genName <* optionalSemi)
    , StructDrop <$> (symbol "drop" *> symbol ":" *> genName <* optionalSemi)
    ]

discipline :: Parser VarDiscipline
discipline = do
  name <- ident
  case name of
    "linear" -> pure Linear
    "affine" -> pure Affine
    "relevant" -> pure Relevant
    "cartesian" -> pure Cartesian
    _ -> fail "unknown discipline"

genName :: Parser GenName
genName = GenName <$> ident

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
  let app = case apps of
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
      pure ExprRule { erPattern = pats, erAction = act }

patternItems :: Parser [PatItem]
patternItems = manyTill patItem (lookAhead (symbol "=>" <|> symbol "|" <|> symbol ";"))

patItem :: Parser PatItem
patItem =
  choice
    [ symbol "ident" $> PatIdent
    , try (symbol "<" *> symbol "expr" *> symbol ">" $> PatExpr)
    , try (symbol "<" *> symbol "type" *> symbol ">" $> PatType)
    , PatLit <$> stringLiteral
    ]

action :: Parser Action
action =
  (symbol "<" *> symbol "expr" *> symbol ">" $> ActionExpr)
    <|> do
      ctor <- ident
      args <- option [] (symbol "(" *> ident `sepBy` symbol "," <* symbol ")")
      pure (ActionCtor ctor args)

elaborateBlock :: Parser [ElabRule]
elaborateBlock = do
  _ <- symbol "elaborate"
  _ <- symbol "{"
  rules <- sepEndBy elabRule elabSep
  _ <- symbol "}"
  optionalSemi
  pure rules
  where
    elabSep = symbol ";;"

elabRule :: Parser ElabRule
elabRule = do
  ctor <- ident
  args <- option [] (symbol "(" *> ident `sepBy` symbol "," <* symbol ")")
  _ <- symbol "=>"
  templ <- templateExpr
  pure ElabRule { erCtor = ctor, erArgs = args, erTemplate = templ }

-- Template expressions (diag expr + placeholders)

templateExpr :: Parser TemplateExpr
templateExpr = makeExprParser templateTerm operators
  where
    operators =
      [ [ InfixL (symbol "*" $> TTensor) ]
      , [ InfixL (semiOp $> TComp) ]
      ]
    semiOp = try (symbol ";" <* notFollowedBy (char ';'))

templateTerm :: Parser TemplateExpr
templateTerm =
  choice
    [ try templateId
    , try templateBox
    , try templateLoop
    , try templateHole
    , templateGen
    , parens templateExpr
    ]

templateId :: Parser TemplateExpr
templateId = do
  _ <- symbol "id"
  ctx <- contextExpr
  pure (TId ctx)

templateGen :: Parser TemplateExpr
templateGen = do
  name <- ident
  mArgs <- optional (symbol "{" *> typeExpr `sepBy` symbol "," <* symbol "}")
  pure (TGen name mArgs)

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
    Nothing -> do
      name <- identRaw
      pure (TVar name)

contextExpr :: Parser [RawPolyTypeExpr]
contextExpr = do
  _ <- symbol "["
  tys <- typeExpr `sepBy` symbol ","
  _ <- symbol "]"
  pure tys

typeExpr :: Parser RawPolyTypeExpr
typeExpr = lexeme $ do
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
  where
    isLowerChar ch = ch >= 'a' && ch <= 'z'

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"

-- Surface program parsing (expressions)

parseSurfaceExpr :: SurfaceSpec -> Text -> Either Text SurfaceAST
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
  = CapIdent Text
  | CapType RawPolyTypeExpr
  | CapExpr SurfaceAST
  | CapSkip
  deriving (Eq, Show)

parseExpr :: LexerSpec -> ExprSpec -> Int -> Parser SurfaceAST
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

parseApplication :: LexerSpec -> ExprSpec -> Int -> Int -> SurfaceAST -> Parser (Maybe SurfaceAST)
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
              case applyAction act [CapExpr left, CapExpr right] of
                Left err -> fail (T.unpack err)
                Right ast -> pure (Just ast)

parseInfix :: LexerSpec -> ExprSpec -> Int -> SurfaceAST -> Parser (Maybe SurfaceAST)
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
              let nextMin = case irAssoc r of
                    AssocL -> prec + 1
                    AssocR -> prec
              right <- parseExpr lexSpec exprSpec nextMin
              case applyAction (irAction r) [CapExpr left, CapExpr right] of
                Left err -> fail (T.unpack err)
                Right ast -> pure (Just ast)

parseTerm :: LexerSpec -> ExprSpec -> Parser SurfaceAST
parseTerm lexSpec exprSpec =
  choice
    [ try (parsePatternRules lexSpec exprSpec (esPrefixes exprSpec))
    , parsePatternRules lexSpec exprSpec (esAtoms exprSpec)
    ]

parsePatternRules :: LexerSpec -> ExprSpec -> [ExprRule] -> Parser SurfaceAST
parsePatternRules lexSpec exprSpec rules =
  choice (map (try . parsePatternRule lexSpec exprSpec) rules)

parsePatternRule :: LexerSpec -> ExprSpec -> ExprRule -> Parser SurfaceAST
parsePatternRule lexSpec exprSpec rule = do
  caps <- mapM (parsePatItem lexSpec exprSpec) (erPattern rule)
  case applyAction (erAction rule) caps of
    Left err -> fail (T.unpack err)
    Right ast -> pure ast

parsePatItem :: LexerSpec -> ExprSpec -> PatItem -> Parser Capture
parsePatItem lexSpec exprSpec item =
  case item of
    PatLit lit -> literalToken lexSpec lit *> pure CapSkip
    PatIdent -> CapIdent <$> identToken lexSpec
    PatExpr -> CapExpr <$> parseExpr lexSpec exprSpec 0
    PatType -> CapType <$> typeExpr

applyAction :: Action -> [Capture] -> Either Text SurfaceAST
applyAction act caps =
  case act of
    ActionExpr ->
      case [e | CapExpr e <- caps] of
        [expr] -> Right expr
        _ -> Left "surface: <expr> action expects exactly one expression capture"
    ActionCtor ctor args ->
      let args' = [a | a <- map capToAst caps, a /= SANode "__skip__" []]
      in if null args || length args == length args'
        then Right (SANode ctor args')
        else Left "surface: action constructor arity mismatch"
  where
    capToAst cap =
      case cap of
        CapIdent t -> SAIdent t
        CapType ty -> SAType ty
        CapExpr e -> e
        CapSkip -> SANode "__skip__" []

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
  where
    keyword t = lexeme $ do
      _ <- string t
      notFollowedBy (satisfy (\c -> isAlphaNum c || c == '_'))
      pure t

surfaceSpecBlock :: Parser SurfaceSpec
surfaceSpecBlock = do
  _ <- symbol "{"
  spec <- surfaceSpec
  _ <- symbol "}"
  optionalSemi
  pure spec
