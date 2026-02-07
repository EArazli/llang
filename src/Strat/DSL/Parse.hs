{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Parse
  ( parseRawFile
  ) where

import Strat.DSL.AST
import Strat.Common.Rules
import Strat.Model.Spec (MExpr(..))
import qualified Strat.Poly.DSL.AST as PolyAST
import Strat.Poly.Surface.Parse (surfaceSpecBlock)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (fromMaybe)
import Data.Functor (($>))
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)
import Control.Monad (void)
import Data.Char (isLower)

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
    <|> doctrineTemplateDecl
    <|> doctrineDecl
    <|> morphismDecl
    <|> surfaceDecl
    <|> modelDecl
    <|> implementsDecl
    <|> runSpecDecl
    <|> termDecl
    <|> runDecl

importDecl :: Parser RawDecl
importDecl = do
  _ <- symbol "import"
  path <- stringLiteral
  optionalSemi
  pure (DeclImport (T.unpack path))

doctrineTemplateDecl :: Parser RawDecl
doctrineTemplateDecl = do
  _ <- symbol "doctrine_template"
  name <- ident
  params <- option [] (symbol "(" *> ident `sepBy` symbol "," <* symbol ")")
  _ <- symbol "where"
  body <- templateBody
  optionalSemi
  pure (DeclDoctrineTemplate (RawDoctrineTemplate name params body))
  where
    templateBody = do
      _ <- symbol "{"
      _ <- symbol "doctrine"
      innerName <- ident
      mExt <- optional (symbol "extends" *> ident)
      _ <- symbol "where"
      items <- polyBlock
      optionalSemi
      _ <- symbol "}"
      pure (PolyAST.RawPolyDoctrine innerName mExt items)

doctrineDecl :: Parser RawDecl
doctrineDecl = do
  _ <- symbol "doctrine"
  name <- ident
  (effectsDecl name <|> pushoutDecl name <|> coproductDecl name <|> instantiateDecl name <|> whereDecl name)
  where
    whereDecl docName = do
      mExt <- optional (symbol "extends" *> ident)
      _ <- symbol "where"
      items <- polyBlock
      optionalSemi
      pure (DeclDoctrine (PolyAST.RawPolyDoctrine docName mExt items))
    pushoutDecl docName = try $ do
      _ <- symbol "="
      _ <- symbol "pushout"
      leftMor <- qualifiedIdent
      rightMor <- qualifiedIdent
      optionalSemi
      pure (DeclDoctrinePushout docName leftMor rightMor)
    coproductDecl docName = try $ do
      _ <- symbol "="
      _ <- symbol "coproduct"
      leftDoc <- qualifiedIdent
      rightDoc <- qualifiedIdent
      optionalSemi
      pure (DeclDoctrineCoproduct docName leftDoc rightDoc)
    effectsDecl docName = try $ do
      _ <- symbol "="
      _ <- symbol "effects"
      baseDoc <- ident
      _ <- symbol "{"
      effects <- ident `sepBy` symbol ","
      _ <- symbol "}"
      optionalSemi
      pure (DeclDoctrineEffects docName baseDoc effects)
    instantiateDecl docName = try $ do
      _ <- symbol "="
      _ <- symbol "instantiate"
      tmpl <- ident
      args <- symbol "(" *> ident `sepBy` symbol "," <* symbol ")"
      optionalSemi
      pure (DeclDoctrineInstantiate (RawDoctrineInstantiate docName tmpl args))

surfaceDecl :: Parser RawDecl
surfaceDecl = do
  _ <- symbol "surface"
  name <- ident
  _ <- symbol "where"
  spec <- surfaceSpecBlock
  optionalSemi
  pure (DeclSurface name spec)

modelDecl :: Parser RawDecl
modelDecl = do
  _ <- symbol "model"
  name <- ident
  _ <- symbol ":"
  doc <- ident
  _ <- symbol "where"
  items <- modelBlock
  optionalSemi
  pure (DeclModel name doc items)

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
  optionalSemi
  case buildPolyMorphism name src tgt items of
    Left err -> fail (T.unpack err)
    Right decl' -> pure (DeclMorphism decl')

implementsDecl :: Parser RawDecl
implementsDecl = do
  _ <- symbol "implements"
  iface <- ident
  _ <- symbol "for"
  tgt <- ident
  _ <- symbol "using"
  name <- qualifiedIdent
  optionalSemi
  pure (DeclImplements iface tgt name)

runSpecDecl :: Parser RawDecl
runSpecDecl = do
  _ <- symbol "run_spec"
  name <- ident
  mUsing <- optional (symbol "using" *> ident)
  _ <- symbol "where"
  items <- runBlock
  mExprText <- optional (try runBody)
  optionalSemi
  pure (DeclRunSpec name (RawRunSpec mUsing (buildRun items mExprText)))

runDecl :: Parser RawDecl
runDecl = do
  _ <- symbol "run"
  name <- ident
  using <- optional (symbol "using" *> ident)
  items <- option [] (symbol "where" *> runBlock)
  mExprText <- optional (try runBody)
  optionalSemi
  pure (DeclRun (RawNamedRun name using (buildRun items mExprText)))

termDecl :: Parser RawDecl
termDecl = do
  _ <- symbol "term"
  name <- ident
  items <- option [] (symbol "where" *> termBlock)
  exprText <- runBody
  pure (DeclTerm (RawNamedTerm name (buildTerm items exprText)))

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

-- Poly doctrine blocks

polyBlock :: Parser [PolyAST.RawPolyItem]
polyBlock = do
  _ <- symbol "{"
  items <- many polyItem
  _ <- symbol "}"
  pure items

polyItem :: Parser PolyAST.RawPolyItem
polyItem =
  polyModeDecl
    <|> polyAttrSortDecl
    <|> (PolyAST.RPType <$> polyTypeDecl)
    <|> (PolyAST.RPData <$> polyDataDecl)
    <|> (PolyAST.RPGen <$> polyGenDecl)
    <|> (PolyAST.RPRule <$> polyRuleDecl)

polyModeDecl :: Parser PolyAST.RawPolyItem
polyModeDecl = do
  _ <- symbol "mode"
  name <- ident
  optionalSemi
  pure (PolyAST.RPMode name)

polyAttrSortDecl :: Parser PolyAST.RawPolyItem
polyAttrSortDecl = do
  _ <- symbol "attrsort"
  name <- ident
  mKind <- optional (symbol "=" *> attrKind)
  optionalSemi
  pure (PolyAST.RPAttrSort (PolyAST.RawAttrSortDecl name mKind))
  where
    attrKind = symbol "int" <|> symbol "string" <|> symbol "bool"

polyTypeDecl :: Parser PolyAST.RawPolyTypeDecl
polyTypeDecl = do
  _ <- symbol "type"
  name <- ident
  vars <- polyTyVarList
  _ <- symbol "@"
  mode <- ident
  optionalSemi
  pure PolyAST.RawPolyTypeDecl
    { PolyAST.rptName = name
    , PolyAST.rptVars = vars
    , PolyAST.rptMode = mode
    }

polyDataDecl :: Parser PolyAST.RawPolyDataDecl
polyDataDecl = do
  _ <- symbol "data"
  name <- ident
  vars <- polyTyVarList
  _ <- symbol "@"
  mode <- ident
  _ <- symbol "where"
  _ <- symbol "{"
  ctors <- many polyCtorDecl
  _ <- symbol "}"
  optionalSemi
  pure PolyAST.RawPolyDataDecl
    { PolyAST.rpdTyName = name
    , PolyAST.rpdTyVars = vars
    , PolyAST.rpdTyMode = mode
    , PolyAST.rpdCtors = ctors
    }

polyCtorDecl :: Parser PolyAST.RawPolyCtorDecl
polyCtorDecl = do
  name <- ident
  _ <- symbol ":"
  args <- polyContext
  optionalSemi
  pure PolyAST.RawPolyCtorDecl
    { PolyAST.rpcName = name
    , PolyAST.rpcArgs = args
    }

polyGenDecl :: Parser PolyAST.RawPolyGenDecl
polyGenDecl = do
  _ <- symbol "gen"
  name <- ident
  vars <- polyTyVarList
  attrs <- option [] (symbol "{" *> polyGenAttrDecl `sepBy` symbol "," <* symbol "}")
  _ <- symbol ":"
  dom <- polyContext
  _ <- symbol "->"
  cod <- polyContext
  _ <- symbol "@"
  mode <- ident
  optionalSemi
  pure PolyAST.RawPolyGenDecl
    { PolyAST.rpgName = name
    , PolyAST.rpgVars = vars
    , PolyAST.rpgAttrs = attrs
    , PolyAST.rpgDom = dom
    , PolyAST.rpgCod = cod
    , PolyAST.rpgMode = mode
    }

polyGenAttrDecl :: Parser (Text, Text)
polyGenAttrDecl = do
  field <- ident
  _ <- symbol ":"
  sortName <- ident
  pure (field, sortName)

polyRuleDecl :: Parser PolyAST.RawPolyRuleDecl
polyRuleDecl = do
  _ <- symbol "rule"
  cls <- (symbol "computational" $> Computational) <|> (symbol "structural" $> Structural)
  name <- ident
  orient <- orientation
  vars <- polyTyVarList
  _ <- symbol ":"
  dom <- polyContext
  _ <- symbol "->"
  cod <- polyContext
  _ <- symbol "@"
  mode <- ident
  _ <- symbol "="
  lhs <- polyDiagExpr
  _ <- symbol "=="
  rhs <- polyDiagExpr
  optionalSemi
  pure PolyAST.RawPolyRuleDecl
    { PolyAST.rprClass = cls
    , PolyAST.rprName = name
    , PolyAST.rprOrient = orient
    , PolyAST.rprVars = vars
    , PolyAST.rprDom = dom
    , PolyAST.rprCod = cod
    , PolyAST.rprMode = mode
    , PolyAST.rprLHS = lhs
    , PolyAST.rprRHS = rhs
    }

polyContext :: Parser PolyAST.RawPolyContext
polyContext = do
  _ <- symbol "["
  tys <- polyTypeExpr `sepBy` symbol ","
  _ <- symbol "]"
  pure tys

polyTyVarDecl :: Parser PolyAST.RawTyVarDecl
polyTyVarDecl = do
  name <- ident
  mMode <- optional (symbol "@" *> ident)
  pure PolyAST.RawTyVarDecl { PolyAST.rtvName = name, PolyAST.rtvMode = mMode }

polyTyVarDeclBare :: Parser PolyAST.RawTyVarDecl
polyTyVarDeclBare = do
  name <- ident
  pure PolyAST.RawTyVarDecl { PolyAST.rtvName = name, PolyAST.rtvMode = Nothing }

polyTyVarList :: Parser [PolyAST.RawTyVarDecl]
polyTyVarList =
  try (symbol "(" *> polyTyVarDecl `sepBy` symbol "," <* symbol ")")
    <|> many polyTyVarDeclBare

polyTypeExpr :: Parser PolyAST.RawPolyTypeExpr
polyTypeExpr = lexeme $ do
  name <- identRaw
  mQual <- optional (try (char '.' *> identRaw))
  mArgs <- optional (symbol "(" *> polyTypeExpr `sepBy` symbol "," <* symbol ")")
  case mQual of
    Just qualName ->
      let ref = PolyAST.RawTypeRef { PolyAST.rtrMode = Just name, PolyAST.rtrName = qualName }
      in pure (PolyAST.RPTCon ref (fromMaybe [] mArgs))
    Nothing ->
      case T.uncons name of
        Nothing -> fail "empty type name"
        Just (c, _) ->
          case mArgs of
            Just args ->
              let ref = PolyAST.RawTypeRef { PolyAST.rtrMode = Nothing, PolyAST.rtrName = name }
              in pure (PolyAST.RPTCon ref args)
            Nothing ->
              if isLower c
                then pure (PolyAST.RPTVar name)
                else
                  let ref = PolyAST.RawTypeRef { PolyAST.rtrMode = Nothing, PolyAST.rtrName = name }
                  in pure (PolyAST.RPTCon ref [])

polyDiagExpr :: Parser PolyAST.RawDiagExpr
polyDiagExpr = makeExprParser polyDiagTerm operators
  where
    operators =
      [ [ InfixL (symbol "*" $> PolyAST.RDTensor) ]
      , [ InfixL (symbol ";" $> PolyAST.RDComp) ]
      ]

polyDiagTerm :: Parser PolyAST.RawDiagExpr
polyDiagTerm =
  polyTermRefTerm <|> try polyIdTerm <|> polyLoopTerm <|> polyBoxTerm <|> polyGenTerm <|> parens polyDiagExpr

polyIdTerm :: Parser PolyAST.RawDiagExpr
polyIdTerm = do
  _ <- symbol "id"
  ctx <- polyContext
  pure (PolyAST.RDId ctx)

polyGenTerm :: Parser PolyAST.RawDiagExpr
polyGenTerm = do
  name <- ident
  mArgs <- optional (symbol "{" *> polyTypeExpr `sepBy` symbol "," <* symbol "}")
  mAttrArgs <- optional polyAttrArgs
  pure (PolyAST.RDGen name mArgs mAttrArgs)

polyAttrArgs :: Parser [PolyAST.RawAttrArg]
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
      let named = [ () | PolyAST.RAName _ _ <- xs ]
          positional = [ () | PolyAST.RAPos _ <- xs ]
      in not (null named) && not (null positional)

polyAttrArg :: Parser PolyAST.RawAttrArg
polyAttrArg =
  try named <|> positional
  where
    named = do
      field <- ident
      _ <- symbol "="
      term <- polyAttrTerm
      pure (PolyAST.RAName field term)
    positional = PolyAST.RAPos <$> polyAttrTerm

polyAttrTerm :: Parser PolyAST.RawAttrTerm
polyAttrTerm =
  choice
    [ PolyAST.RATInt . fromIntegral <$> integer
    , PolyAST.RATString <$> stringLiteral
    , PolyAST.RATBool True <$ keyword "true"
    , PolyAST.RATBool False <$ keyword "false"
    , PolyAST.RATVar <$> ident
    ]

polyTermRefTerm :: Parser PolyAST.RawDiagExpr
polyTermRefTerm = do
  _ <- symbol "@"
  name <- ident
  pure (PolyAST.RDTermRef name)

polyBoxTerm :: Parser PolyAST.RawDiagExpr
polyBoxTerm = do
  _ <- symbol "box"
  name <- ident
  _ <- symbol "{"
  inner <- polyDiagExpr
  _ <- symbol "}"
  pure (PolyAST.RDBox name inner)

polyLoopTerm :: Parser PolyAST.RawDiagExpr
polyLoopTerm = do
  _ <- symbol "loop"
  _ <- symbol "{"
  inner <- polyDiagExpr
  _ <- symbol "}"
  pure (PolyAST.RDLoop inner)

orientation :: Parser Orientation
orientation =
  (symbol "<->" $> Bidirectional)
    <|> (symbol "->" $> LR)
    <|> (symbol "<-" $> RL)
    <|> (symbol "=" $> Unoriented)

-- Morphism block

data MorphismItem
  = MorphismMode RawPolyModeMap
  | MorphismAttrSort RawPolyAttrSortMap
  | MorphismType RawPolyTypeMap
  | MorphismGen RawPolyGenMap
  | MorphismCoercion
  | MorphismPolicy Text
  | MorphismFuel Int

morphismBlock :: Parser [MorphismItem]
morphismBlock = do
  _ <- symbol "{"
  items <- many morphismItem
  _ <- symbol "}"
  pure items

morphismItem :: Parser MorphismItem
morphismItem =
  morphismModeMap
    <|> morphismAttrSortMap
    <|> morphismTypeMap
    <|> morphismGenMap
    <|> morphismCoercionItem
    <|> morphismPolicy
    <|> morphismFuel

morphismModeMap :: Parser MorphismItem
morphismModeMap = do
  _ <- symbol "mode"
  src <- ident
  _ <- symbol "->"
  tgt <- ident
  optionalSemi
  pure (MorphismMode (RawPolyModeMap src tgt))

morphismAttrSortMap :: Parser MorphismItem
morphismAttrSortMap = do
  _ <- symbol "attrsort"
  src <- ident
  _ <- symbol "->"
  tgt <- ident
  optionalSemi
  pure (MorphismAttrSort (RawPolyAttrSortMap src tgt))

morphismTypeMap :: Parser MorphismItem
morphismTypeMap = do
  _ <- symbol "type"
  src <- ident
  params <- option [] (symbol "(" *> polyTyVarDecl `sepBy` symbol "," <* symbol ")")
  _ <- symbol "@"
  srcMode <- ident
  _ <- symbol "->"
  tgt <- polyTypeExpr
  _ <- symbol "@"
  tgtMode <- ident
  optionalSemi
  pure (MorphismType (RawPolyTypeMap src params srcMode tgt tgtMode))

morphismGenMap :: Parser MorphismItem
morphismGenMap = do
  _ <- symbol "gen"
  src <- ident
  _ <- symbol "@"
  mode <- ident
  _ <- symbol "->"
  rhs <- polyDiagExpr
  optionalSemi
  pure (MorphismGen (RawPolyGenMap src mode rhs))

morphismCoercionItem :: Parser MorphismItem
morphismCoercionItem = do
  _ <- symbol "coercion"
  optionalSemi
  pure MorphismCoercion

morphismPolicy :: Parser MorphismItem
morphismPolicy = do
  _ <- symbol "policy"
  name <- ident
  optionalSemi
  pure (MorphismPolicy name)

morphismFuel :: Parser MorphismItem
morphismFuel = do
  _ <- symbol "fuel"
  n <- fromIntegral <$> integer
  optionalSemi
  pure (MorphismFuel n)

buildPolyMorphism :: Text -> Text -> Text -> [MorphismItem] -> Either Text RawPolyMorphism
buildPolyMorphism name src tgt items =
  Right RawPolyMorphism
    { rpmName = name
    , rpmSrc = src
    , rpmTgt = tgt
    , rpmItems =
        [ RPMMode m | MorphismMode m <- items ]
          <> [ RPMAttrSort m | MorphismAttrSort m <- items ]
          <> [ RPMType i | MorphismType i <- items ]
          <> [ RPMGen j | MorphismGen j <- items ]
          <> [ RPMCoercion | MorphismCoercion <- items ]
    , rpmPolicy = firstJust [ p | MorphismPolicy p <- items ]
    , rpmFuel = firstJust [ f | MorphismFuel f <- items ]
    }
  where
    firstJust [] = Nothing
    firstJust (x:_) = Just x

-- Run block

data RunItem
  = RunDoctrine Text
  | RunMode Text
  | RunSurface Text
  | RunModel Text
  | RunApply Text
  | RunUses [Text]
  | RunPolicy Text
  | RunFuel Int
  | RunShow RawRunShow

runBlock :: Parser [RunItem]
runBlock = do
  _ <- symbol "{"
  items <- many runItem
  _ <- symbol "}"
  pure items

runItem :: Parser RunItem
runItem =
  runDoctrineItem
    <|> runModeItem
    <|> runSurfaceItem
    <|> runModelItem
    <|> runApplyItem
    <|> runUsesItem
    <|> runPolicyItem
    <|> runFuelItem
    <|> runShowItem

runDoctrineItem :: Parser RunItem
runDoctrineItem = do
  _ <- symbol "doctrine"
  name <- ident
  optionalSemi
  pure (RunDoctrine name)

runModeItem :: Parser RunItem
runModeItem = do
  _ <- keyword "mode"
  name <- ident
  optionalSemi
  pure (RunMode name)

runSurfaceItem :: Parser RunItem
runSurfaceItem = do
  _ <- symbol "surface"
  name <- ident
  optionalSemi
  pure (RunSurface name)

runModelItem :: Parser RunItem
runModelItem = do
  _ <- keyword "model"
  name <- ident
  optionalSemi
  pure (RunModel name)

runApplyItem :: Parser RunItem
runApplyItem = do
  _ <- symbol "apply"
  name <- ident
  optionalSemi
  pure (RunApply name)

runUsesItem :: Parser RunItem
runUsesItem = do
  _ <- symbol "uses"
  _ <- optional (symbol ":")
  names <- ident `sepBy1` symbol ","
  optionalSemi
  pure (RunUses names)

runPolicyItem :: Parser RunItem
runPolicyItem = do
  _ <- symbol "policy"
  name <- ident
  optionalSemi
  pure (RunPolicy name)

runFuelItem :: Parser RunItem
runFuelItem = do
  _ <- symbol "fuel"
  n <- fromIntegral <$> integer
  optionalSemi
  pure (RunFuel n)

runShowItem :: Parser RunItem
runShowItem = do
  _ <- symbol "show"
  flag <- showFlag
  optionalSemi
  pure (RunShow flag)

buildRun :: [RunItem] -> Maybe Text -> RawRun
buildRun items mExprText =
  RawRun
    { rrDoctrine = firstJust [ d | RunDoctrine d <- items ]
    , rrMode = firstJust [ m | RunMode m <- items ]
    , rrSurface = firstJust [ s | RunSurface s <- items ]
    , rrModel = firstJust [ m | RunModel m <- items ]
    , rrMorphisms = [ n | RunApply n <- items ]
    , rrUses = concat [ ns | RunUses ns <- items ]
    , rrPolicy = firstJust [ p | RunPolicy p <- items ]
    , rrFuel = firstJust [ f | RunFuel f <- items ]
    , rrShowFlags = [ s | RunShow s <- items ]
    , rrExprText = mExprText
    }
  where
    firstJust [] = Nothing
    firstJust (x:_) = Just x

-- Term block

data TermItem
  = TermDoctrine Text
  | TermMode Text
  | TermSurface Text
  | TermApply Text
  | TermUses [Text]
  | TermPolicy Text
  | TermFuel Int

termBlock :: Parser [TermItem]
termBlock = do
  _ <- symbol "{"
  items <- many termItem
  _ <- symbol "}"
  pure items

termItem :: Parser TermItem
termItem =
  termDoctrineItem
    <|> termModeItem
    <|> termSurfaceItem
    <|> termApplyItem
    <|> termUsesItem
    <|> termPolicyItem
    <|> termFuelItem
    <|> termModelForbidden
    <|> termShowForbidden

termDoctrineItem :: Parser TermItem
termDoctrineItem = do
  _ <- symbol "doctrine"
  name <- ident
  optionalSemi
  pure (TermDoctrine name)

termModeItem :: Parser TermItem
termModeItem = do
  _ <- keyword "mode"
  name <- ident
  optionalSemi
  pure (TermMode name)

termSurfaceItem :: Parser TermItem
termSurfaceItem = do
  _ <- symbol "surface"
  name <- ident
  optionalSemi
  pure (TermSurface name)

termApplyItem :: Parser TermItem
termApplyItem = do
  _ <- symbol "apply"
  name <- ident
  optionalSemi
  pure (TermApply name)

termUsesItem :: Parser TermItem
termUsesItem = do
  _ <- symbol "uses"
  _ <- optional (symbol ":")
  names <- ident `sepBy1` symbol ","
  optionalSemi
  pure (TermUses names)

termPolicyItem :: Parser TermItem
termPolicyItem = do
  _ <- symbol "policy"
  name <- ident
  optionalSemi
  pure (TermPolicy name)

termFuelItem :: Parser TermItem
termFuelItem = do
  _ <- symbol "fuel"
  n <- fromIntegral <$> integer
  optionalSemi
  pure (TermFuel n)

termModelForbidden :: Parser TermItem
termModelForbidden = do
  _ <- keyword "model"
  fail "term: model is not allowed"

termShowForbidden :: Parser TermItem
termShowForbidden = do
  _ <- keyword "show"
  fail "term: show is not allowed"

buildTerm :: [TermItem] -> Text -> RawTerm
buildTerm items exprText =
  RawTerm
    { rtDoctrine = firstJust [ d | TermDoctrine d <- items ]
    , rtMode = firstJust [ m | TermMode m <- items ]
    , rtSurface = firstJust [ s | TermSurface s <- items ]
    , rtMorphisms = [ n | TermApply n <- items ]
    , rtUses = concat [ ns | TermUses ns <- items ]
    , rtPolicy = firstJust [ p | TermPolicy p <- items ]
    , rtFuel = firstJust [ f | TermFuel f <- items ]
    , rtExprText = exprText
    }
  where
    firstJust [] = Nothing
    firstJust (x:_) = Just x

showFlag :: Parser RawRunShow
showFlag =
  (symbol "normalized" $> RawShowNormalized)
    <|> (symbol "value" $> RawShowValue)
    <|> (symbol "cat" $> RawShowCat)
    <|> (symbol "input" $> RawShowInput)
    <|> (symbol "coherence" $> RawShowCoherence)

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

sc :: Parser ()
sc = L.space space1 lineComment empty

lineComment :: Parser ()
lineComment = try $ do
  _ <- string "--"
  notFollowedBy (char '-')
  void (manyTill anySingle (void eol <|> eof))

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"

optionalSemi :: Parser ()
optionalSemi = void (optional (symbol ";"))

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

keyword :: Text -> Parser Text
keyword kw = lexeme (try (string kw <* notFollowedBy identChar))

stringLiteral :: Parser Text
stringLiteral = lexeme (T.pack <$> (char '"' *> manyTill L.charLiteral (char '"')))

integer :: Parser Integer
integer = lexeme L.decimal
