{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Parse
  ( parseRawFile
  ) where

import Strat.DSL.AST
import Strat.Common.Rules
import qualified Strat.Poly.DSL.AST as PolyAST
import Strat.Poly.Surface.Parse (surfaceSpecBlock)
import qualified Strat.Poly.ModeTheory
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
    <|> derivedDoctrineDecl
    <|> morphismDecl
    <|> surfaceDecl
    <|> pipelineDecl
    <|> implementsDecl
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

derivedDoctrineDecl :: Parser RawDecl
derivedDoctrineDecl = do
  _ <- symbol "derived"
  _ <- symbol "doctrine"
  name <- ident
  _ <- symbol "="
  _ <- symbol "foliated"
  base <- ident
  _ <- symbol "mode"
  modeName <- ident
  opts <- option (RawFoliationOpts Nothing Nothing []) (symbol "with" *> foliationOptsBlock)
  optionalSemi
  pure (DeclDerivedDoctrine (RawDerivedDoctrine name base modeName opts))

pipelineDecl :: Parser RawDecl
pipelineDecl = do
  _ <- symbol "pipeline"
  name <- ident
  _ <- symbol "where"
  phases <- pipelineBlock
  optionalSemi
  pure (DeclPipeline (RawPipeline name phases))

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

runDecl :: Parser RawDecl
runDecl = do
  _ <- symbol "run"
  name <- ident
  using <- symbol "using" *> ident
  items <- symbol "where" *> runBlock
  mExprText <- optional (try runBody)
  optionalSemi
  pure (DeclRun (RawNamedRun name (buildRun (Just using) items mExprText)))

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
  try polyIndexModeDecl
    <|> try polyIndexFunDecl
    <|> try polyIndexRuleDecl
    <|> polyModeDecl
    <|> polyStructureDecl
    <|> polyModalityDecl
    <|> polyModEqDecl
    <|> polyAdjDecl
    <|> polyAttrSortDecl
    <|> (PolyAST.RPType <$> polyTypeDecl)
    <|> (PolyAST.RPData <$> polyDataDecl)
    <|> (PolyAST.RPGen <$> polyGenDecl)
    <|> (PolyAST.RPRule <$> polyRuleDecl)

polyModeDecl :: Parser PolyAST.RawPolyItem
polyModeDecl = do
  _ <- symbol "mode"
  name <- ident
  acyclic <- option False (True <$ symbol "acyclic")
  optionalSemi
  pure (PolyAST.RPMode (PolyAST.RawModeDecl name acyclic))

polyIndexModeDecl :: Parser PolyAST.RawPolyItem
polyIndexModeDecl = do
  _ <- symbol "index_mode"
  name <- ident
  optionalSemi
  pure (PolyAST.RPIndexMode name)

polyIndexFunDecl :: Parser PolyAST.RawPolyItem
polyIndexFunDecl = do
  _ <- symbol "index_fun"
  name <- ident
  vars <- option [] (symbol "(" *> polyIxVarDecl `sepBy` symbol "," <* symbol ")")
  _ <- symbol ":"
  res <- polyTypeExpr
  _ <- symbol "@"
  mode <- ident
  optionalSemi
  pure (PolyAST.RPIndexFun PolyAST.RawIndexFunDecl
    { PolyAST.rifName = name
    , PolyAST.rifArgs = vars
    , PolyAST.rifRes = res
    , PolyAST.rifMode = mode
    })

polyIndexRuleDecl :: Parser PolyAST.RawPolyItem
polyIndexRuleDecl = do
  _ <- symbol "index_rule"
  name <- ident
  vars <- option [] (symbol "(" *> polyIxVarDecl `sepBy` symbol "," <* symbol ")")
  _ <- symbol ":"
  lhs <- polyTypeExpr
  _ <- symbol "->"
  rhs <- polyTypeExpr
  _ <- symbol "@"
  mode <- ident
  optionalSemi
  pure (PolyAST.RPIndexRule PolyAST.RawIndexRuleDecl
    { PolyAST.rirName = name
    , PolyAST.rirVars = vars
    , PolyAST.rirLHS = lhs
    , PolyAST.rirRHS = rhs
    , PolyAST.rirMode = mode
    })

polyStructureDecl :: Parser PolyAST.RawPolyItem
polyStructureDecl = do
  _ <- symbol "structure"
  mode <- ident
  _ <- symbol "="
  disc <- discipline
  optionalSemi
  pure (PolyAST.RPStructure (PolyAST.RawStructureDecl mode disc))
  where
    discipline =
      (symbol "linear" $> Strat.Poly.ModeTheory.Linear)
        <|> (symbol "affine" $> Strat.Poly.ModeTheory.Affine)
        <|> (symbol "relevant" $> Strat.Poly.ModeTheory.Relevant)
        <|> (symbol "cartesian" $> Strat.Poly.ModeTheory.Cartesian)

polyModalityDecl :: Parser PolyAST.RawPolyItem
polyModalityDecl = do
  _ <- symbol "modality"
  name <- ident
  _ <- symbol ":"
  src <- ident
  _ <- symbol "->"
  tgt <- ident
  optionalSemi
  pure (PolyAST.RPModality (PolyAST.RawModalityDecl name src tgt))

polyModEqDecl :: Parser PolyAST.RawPolyItem
polyModEqDecl = do
  _ <- symbol "mod_eq"
  lhs <- rawModExpr
  _ <- symbol "->"
  rhs <- rawModExpr
  optionalSemi
  pure (PolyAST.RPModEq (PolyAST.RawModEqDecl lhs rhs))

polyAdjDecl :: Parser PolyAST.RawPolyItem
polyAdjDecl = do
  _ <- symbol "adjunction"
  left <- ident
  _ <- symbol "dashv"
  right <- ident
  optionalSemi
  pure (PolyAST.RPAdjunction (PolyAST.RawAdjDecl left right))

rawModExpr :: Parser PolyAST.RawModExpr
rawModExpr =
  try rawId <|> rawComp
  where
    rawId = do
      _ <- symbol "id"
      _ <- symbol "@"
      mode <- ident
      pure (PolyAST.RMId mode)
    rawComp = PolyAST.RMComp <$> (ident `sepBy1` symbol ".")

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
  vars <- polyParamList
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
  vars <- polyParamList
  attrs <- option [] (symbol "{" *> polyGenAttrDecl `sepBy` symbol "," <* symbol "}")
  _ <- symbol ":"
  dom <- polyInputShapes
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
  vars <- polyParamList
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

polyInputShapes :: Parser [PolyAST.RawInputShape]
polyInputShapes = do
  _ <- symbol "["
  shapes <- polyInputShape `sepBy` symbol ","
  _ <- symbol "]"
  pure shapes

polyInputShape :: Parser PolyAST.RawInputShape
polyInputShape =
  try polyBinderShape <|> (PolyAST.RIPort <$> polyTypeExpr)

polyBinderShape :: Parser PolyAST.RawInputShape
polyBinderShape = do
  _ <- symbol "binder"
  _ <- symbol "{"
  vars <- polyBinderVarDecl `sepBy` symbol ","
  _ <- symbol "}"
  _ <- symbol ":"
  cod <- polyContext
  pure (PolyAST.RIBinder vars cod)

polyBinderVarDecl :: Parser PolyAST.RawBinderVarDecl
polyBinderVarDecl = do
  name <- ident
  _ <- symbol ":"
  ty <- polyTypeExpr
  pure PolyAST.RawBinderVarDecl { PolyAST.rbvName = name, PolyAST.rbvType = ty }

polyIxVarDecl :: Parser PolyAST.RawIxVarDecl
polyIxVarDecl = do
  name <- ident
  _ <- symbol ":"
  sortTy <- polyTypeExpr
  pure PolyAST.RawIxVarDecl { PolyAST.rivName = name, PolyAST.rivSort = sortTy }

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

polyParamDecl :: Parser PolyAST.RawParamDecl
polyParamDecl =
  try polyIxParam <|> polyTyParam
  where
    polyTyParam = PolyAST.RPDType <$> polyTyVarDecl
    polyIxParam = PolyAST.RPDIndex <$> polyIxVarDecl

polyParamList :: Parser [PolyAST.RawParamDecl]
polyParamList =
  try (symbol "(" *> polyParamDecl `sepBy` symbol "," <* symbol ")")
    <|> (map PolyAST.RPDType <$> many polyTyVarDeclBare)

polyTypeExpr :: Parser PolyAST.RawPolyTypeExpr
polyTypeExpr = lexeme (try modApp <|> try bound <|> regular)
  where
    modApp = do
      me <- rawModExprComplex
      _ <- symbol "("
      inner <- polyTypeExpr
      _ <- symbol ")"
      pure (PolyAST.RPTMod me inner)
    bound = do
      _ <- symbol "^"
      idx <- fromIntegral <$> integer
      pure (PolyAST.RPTBound idx)
    rawModExprComplex =
      try rawId <|> rawComp
    rawId = do
      _ <- symbol "id"
      _ <- symbol "@"
      mode <- ident
      pure (PolyAST.RMId mode)
    rawComp = do
      first <- ident
      _ <- symbol "."
      second <- ident
      _ <- symbol "."
      third <- ident
      rest <- many (symbol "." *> ident)
      pure (PolyAST.RMComp (first : second : third : rest))
    regular = do
      name <- identRaw
      mQual <- optional (try (char '.' *> identRaw))
      mArgs <- optional (symbol "(" *> polyTypeExpr `sepBy` symbol "," <* symbol ")")
      case mQual of
        Just qualName ->
          let ref = PolyAST.RawTypeRef { PolyAST.rtrMode = Just name, PolyAST.rtrName = qualName }
          in pure (PolyAST.RPTCon ref (fromMaybe [] mArgs))
        Nothing ->
          case mArgs of
            Just args ->
              let ref = PolyAST.RawTypeRef { PolyAST.rtrMode = Nothing, PolyAST.rtrName = name }
              in pure (PolyAST.RPTCon ref args)
            Nothing ->
              pure (PolyAST.RPTVar name)

polyDiagExpr :: Parser PolyAST.RawDiagExpr
polyDiagExpr = makeExprParser polyDiagTerm operators
  where
    operators =
      [ [ InfixL (symbol "*" $> PolyAST.RDTensor) ]
      , [ InfixL (symbol ";" $> PolyAST.RDComp) ]
      ]

polyDiagTerm :: Parser PolyAST.RawDiagExpr
polyDiagTerm =
  polyTermRefTerm <|> try polyIdTerm <|> polySpliceTerm <|> polyLoopTerm <|> polyBoxTerm <|> polyGenTerm <|> parens polyDiagExpr

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
  mBinderArgs <- optional polyBinderArgs
  pure (PolyAST.RDGen name mArgs mAttrArgs mBinderArgs)

polySpliceTerm :: Parser PolyAST.RawDiagExpr
polySpliceTerm = do
  _ <- symbol "splice"
  _ <- symbol "("
  meta <- binderMetaVar
  _ <- symbol ")"
  pure (PolyAST.RDSplice meta)

polyBinderArgs :: Parser [PolyAST.RawBinderArg]
polyBinderArgs = do
  _ <- symbol "["
  args <- polyBinderArg `sepBy` symbol ","
  _ <- symbol "]"
  pure args

polyBinderArg :: Parser PolyAST.RawBinderArg
polyBinderArg =
  try (PolyAST.RBAMeta <$> binderMetaVar)
    <|> (PolyAST.RBAExpr <$> polyDiagExpr)

binderMetaVar :: Parser Text
binderMetaVar = lexeme (char '?' *> identRaw)

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
  | MorphismModality RawPolyModalityMap
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
    <|> morphismModalityMap
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

morphismModalityMap :: Parser MorphismItem
morphismModalityMap = do
  _ <- symbol "modality"
  src <- ident
  _ <- symbol "->"
  tgt <- rawModExpr
  optionalSemi
  pure (MorphismModality (RawPolyModalityMap src tgt))

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
  params <- option [] (symbol "(" *> polyParamDecl `sepBy` symbol "," <* symbol ")")
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
          <> [ RPMModality m | MorphismModality m <- items ]
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

-- Pipeline block

pipelineBlock :: Parser [RawPhase]
pipelineBlock = do
  _ <- symbol "{"
  items <- many pipelineItem
  _ <- symbol "}"
  pure items

pipelineItem :: Parser RawPhase
pipelineItem =
  pipelineApplyItem
    <|> pipelineNormalizeItem
    <|> try pipelineExtractFoliateItem
    <|> pipelineExtractItem

pipelineApplyItem :: Parser RawPhase
pipelineApplyItem = do
  _ <- symbol "apply"
  name <- qualifiedIdent
  optionalSemi
  pure (RPApply name)

pipelineNormalizeItem :: Parser RawPhase
pipelineNormalizeItem = do
  _ <- symbol "normalize"
  opts <- option (RawNormalizeOpts Nothing Nothing) normalizeOptsBlock
  optionalSemi
  pure (RPNormalize opts)

normalizeOptsBlock :: Parser RawNormalizeOpts
normalizeOptsBlock = do
  _ <- symbol "{"
  items <- many normalizeItem
  _ <- symbol "}"
  pure
    RawNormalizeOpts
      { rnoPolicy = firstJust [ p | NormPolicy p <- items ]
      , rnoFuel = firstJust [ n | NormFuel n <- items ]
      }
  where
    firstJust [] = Nothing
    firstJust (x:_) = Just x

data NormalizeItem
  = NormPolicy Text
  | NormFuel Int

normalizeItem :: Parser NormalizeItem
normalizeItem =
  normPolicy <|> normFuel
  where
    normPolicy = do
      _ <- symbol "policy"
      _ <- symbol "="
      txt <- stringLiteral
      optionalSemi
      pure (NormPolicy txt)
    normFuel = do
      _ <- symbol "fuel"
      _ <- symbol "="
      n <- fromIntegral <$> integer
      optionalSemi
      pure (NormFuel n)

pipelineExtractFoliateItem :: Parser RawPhase
pipelineExtractFoliateItem = do
  _ <- symbol "extract"
  _ <- symbol "foliate"
  _ <- symbol "into"
  target <- ident
  opts <- optional (symbol "with" *> foliationOptsBlock)
  optionalSemi
  pure (RPExtractFoliate target opts)

pipelineExtractItem :: Parser RawPhase
pipelineExtractItem = do
  _ <- symbol "extract"
  (do
      _ <- symbol "diagram"
      optionalSemi
      pure RPExtractDiagramPretty)
    <|> do
      doctrineName <- ident
      opts <- option (RawValueExtractOpts Nothing Nothing) valueExtractOptsBlock
      optionalSemi
      pure (RPExtractValue doctrineName opts)

foliationOptsBlock :: Parser RawFoliationOpts
foliationOptsBlock = do
  _ <- symbol "{"
  items <- many foliationOptItem
  _ <- symbol "}"
  pure
    RawFoliationOpts
      { rfoPolicy = firstJust [ p | FOPolicy p <- items ]
      , rfoNaming = firstJust [ p | FONaming p <- items ]
      , rfoReserved = concat [ xs | FOReserved xs <- items ]
      }
  where
    firstJust [] = Nothing
    firstJust (x:_) = Just x

data FoliationOptItem
  = FOPolicy Text
  | FONaming Text
  | FOReserved [Text]

foliationOptItem :: Parser FoliationOptItem
foliationOptItem =
  foPolicy <|> foNaming <|> foReserved
  where
    foPolicy = do
      _ <- symbol "policy"
      _ <- symbol "="
      txt <- stringLiteral
      optionalSemi
      pure (FOPolicy txt)
    foNaming = do
      _ <- symbol "naming"
      _ <- symbol "="
      txt <- stringLiteral
      optionalSemi
      pure (FONaming txt)
    foReserved = do
      _ <- symbol "reserved"
      _ <- symbol "="
      _ <- symbol "["
      xs <- stringLiteral `sepBy` symbol ","
      _ <- symbol "]"
      optionalSemi
      pure (FOReserved xs)

valueExtractOptsBlock :: Parser RawValueExtractOpts
valueExtractOptsBlock = do
  _ <- symbol "{"
  items <- many valueExtractOptItem
  _ <- symbol "}"
  pure
    RawValueExtractOpts
      { rveStdout = firstJust [ b | VEStdout b <- items ]
      , rveRoot = firstJust [ T.unpack p | VERoot p <- items ]
      }
  where
    firstJust [] = Nothing
    firstJust (x:_) = Just x

data ValueExtractOptItem
  = VEStdout Bool
  | VERoot Text

valueExtractOptItem :: Parser ValueExtractOptItem
valueExtractOptItem =
  veStdout <|> veRoot
  where
    veStdout = do
      _ <- symbol "stdout"
      _ <- symbol "="
      b <- boolLiteral
      optionalSemi
      pure (VEStdout b)
    veRoot = do
      _ <- symbol "root"
      _ <- symbol "="
      p <- stringLiteral
      optionalSemi
      pure (VERoot p)

-- Run block

data RunItem
  = RunSourceDoctrine Text
  | RunSourceMode Text
  | RunSourceSurface Text
  | RunUses [Text]

runBlock :: Parser [RunItem]
runBlock = do
  _ <- symbol "{"
  items <- many runItem
  _ <- symbol "}"
  pure items

runItem :: Parser RunItem
runItem =
  runUsesItem
    <|> runSourceItem

runSourceItem :: Parser RunItem
runSourceItem = do
  _ <- symbol "source"
  ( do
      _ <- symbol "doctrine"
      name <- ident
      optionalSemi
      pure (RunSourceDoctrine name)
    )
    <|> ( do
            _ <- symbol "mode"
            name <- ident
            optionalSemi
            pure (RunSourceMode name)
        )
    <|> ( do
            _ <- symbol "surface"
            name <- ident
            optionalSemi
            pure (RunSourceSurface name)
        )

runUsesItem :: Parser RunItem
runUsesItem = do
  _ <- symbol "uses"
  _ <- symbol "["
  files <- stringLiteral `sepBy` symbol ","
  _ <- symbol "]"
  optionalSemi
  pure (RunUses files)

buildRun :: Maybe Text -> [RunItem] -> Maybe Text -> RawRun
buildRun mPipeline items mExprText =
  RawRun
    { rrPipeline = mPipeline
    , rrDoctrine = firstJust [ d | RunSourceDoctrine d <- items ]
    , rrMode = firstJust [ m | RunSourceMode m <- items ]
    , rrSurface = firstJust [ s | RunSourceSurface s <- items ]
    , rrUses = concat [ ns | RunUses ns <- items ]
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

boolLiteral :: Parser Bool
boolLiteral =
  (True <$ keyword "true")
    <|> (False <$ keyword "false")

integer :: Parser Integer
integer = lexeme L.decimal
