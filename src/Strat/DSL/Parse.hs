{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Parse
  ( parseRawFile
  ) where

import Strat.DSL.AST
import Strat.Common.Rules
import qualified Strat.Poly.DSL.AST as PolyAST
import Strat.Poly.Surface.Parse (surfaceSpecBlock)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
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
    <|> doctrineFunctorDecl
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

doctrineFunctorDecl :: Parser RawDecl
doctrineFunctorDecl = do
  _ <- symbol "doctrine_functor"
  name <- scopedIdent
  _ <- symbol "("
  params <- functorParam `sepBy1` symbol ","
  _ <- symbol ")"
  _ <- symbol "where"
  items <- polyBlock
  optionalSemi
  let bodyName = name <> ".__body"
  pure
    ( DeclDoctrineFunctor
        RawDoctrineFunctor
          { rdfName = name
          , rdfParams = params
          , rdfBody = PolyAST.RawPolyDoctrine bodyName Nothing items
          }
    )
  where
    functorParam = do
      paramName <- plainIdent
      _ <- symbol ":"
      schemaName <- scopedIdent
      pure (RawFunctorParam paramName schemaName)

doctrineDecl :: Parser RawDecl
doctrineDecl = do
  _ <- symbol "doctrine"
  name <- ident
  (effectsDecl name <|> pushoutDecl name <|> coproductDecl name <|> applyDecl name <|> whereDecl name)
  where
    whereDecl docName = do
      mExt <- optional (symbol "extends" *> scopedIdent)
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
      baseDoc <- scopedIdent
      _ <- symbol "{"
      effects <- scopedIdent `sepBy` symbol ","
      _ <- symbol "}"
      optionalSemi
      pure (DeclDoctrineEffects docName baseDoc effects)
    applyDecl docName = try $ do
      _ <- symbol "="
      _ <- symbol "apply"
      functorName <- scopedIdent
      _ <- symbol "to"
      target <- scopedIdent
      usingMap <- symbol "using" *> applyUsingBlock
      optionalSemi
      pure
        ( DeclDoctrineApply
            RawDoctrineApply
              { rdaName = docName
              , rdaFunctor = functorName
              , rdaTarget = target
              , rdaUsing = usingMap
              }
        )
    applyUsingBlock = do
      _ <- symbol "{"
      entries <- many applyUsingEntry
      _ <- symbol "}"
      ensureUniqueEntries entries
    applyUsingEntry = do
      paramName <- plainIdent
      _ <- symbol "="
      morphName <- qualifiedIdent
      _ <- symbol ";"
      pure (paramName, morphName)
    ensureUniqueEntries entries = go S.empty M.empty entries
      where
        go _ mp [] = pure mp
        go seen mp ((k, v):rest)
          | k `S.member` seen = fail ("duplicate apply mapping key: " <> T.unpack k)
          | otherwise = go (S.insert k seen) (M.insert k v mp) rest

surfaceDecl :: Parser RawDecl
surfaceDecl = do
  _ <- symbol "surface"
  name <- scopedIdent
  _ <- symbol "where"
  spec <- surfaceSpecBlock
  optionalSemi
  pure (DeclSurface name spec)

derivedDoctrineDecl :: Parser RawDecl
derivedDoctrineDecl = do
  _ <- symbol "derived"
  _ <- symbol "doctrine"
  name <- scopedIdent
  _ <- symbol "="
  _ <- symbol "foliated"
  base <- scopedIdent
  _ <- symbol "mode"
  modeName <- scopedIdent
  opts <- option (RawFoliationOpts Nothing Nothing []) (symbol "with" *> foliationOptsBlock)
  optionalSemi
  pure (DeclDerivedDoctrine (RawDerivedDoctrine name base modeName opts))

pipelineDecl :: Parser RawDecl
pipelineDecl = do
  _ <- symbol "pipeline"
  name <- scopedIdent
  _ <- symbol "where"
  phases <- pipelineBlock
  optionalSemi
  pure (DeclPipeline (RawPipeline name phases))

morphismDecl :: Parser RawDecl
morphismDecl = do
  _ <- symbol "morphism"
  name <- qualifiedIdent
  _ <- symbol ":"
  src <- scopedIdent
  _ <- symbol "->"
  tgt <- scopedIdent
  _ <- symbol "where"
  items <- morphismBlock
  optionalSemi
  case buildPolyMorphism name src tgt items of
    Left err -> fail (T.unpack err)
    Right decl' -> pure (DeclMorphism decl')

implementsDecl :: Parser RawDecl
implementsDecl = do
  _ <- symbol "implements"
  iface <- scopedIdent
  _ <- symbol "for"
  tgt <- scopedIdent
  _ <- symbol "using"
  name <- qualifiedIdent
  optionalSemi
  pure (DeclImplements iface tgt name)

runDecl :: Parser RawDecl
runDecl = do
  _ <- symbol "run"
  name <- scopedIdent
  using <- symbol "using" *> scopedIdent
  items <- symbol "where" *> runBlock
  mExprText <- optional (try runBody)
  optionalSemi
  pure (DeclRun (RawNamedRun name (buildRun (Just using) items mExprText)))

termDecl :: Parser RawDecl
termDecl = do
  _ <- symbol "term"
  name <- scopedIdent
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
    <|> polyComprehensionDecl
    <|> polyClassifierLiftDecl
    <|> polyModalityDecl
    <|> polyModEqDecl
    <|> polyModTransformDecl
    <|> polyActionDecl
    <|> polyObligationDecl
    <|> polyAttrSortDecl
    <|> (PolyAST.RPData <$> polyDataDecl)
    <|> (PolyAST.RPGen <$> polyGenDecl)
    <|> (PolyAST.RPRule <$> polyRuleDecl)

polyModeDecl :: Parser PolyAST.RawPolyItem
polyModeDecl = do
  _ <- symbol "mode"
  name <- ident
  acyclic <- option False (True <$ symbol "acyclic")
  mDefEq <- optional $ do
    _ <- symbol "defeq"
    (PolyAST.RDETRS <$ symbol "trs")
      <|> (PolyAST.RDENBE <$ symbol "nbe")
  mClass <- optional $ do
    _ <- symbol "classifiedBy"
    cls <- ident
    _ <- symbol "via"
    uni <- polyObjExpr
    mTag <- optional (symbol "as" *> ident)
    pure
      PolyAST.RawClassifiedByDecl
        { PolyAST.rcdClassifier = cls
        , PolyAST.rcdUniverse = uni
        , PolyAST.rcdTag = mTag
        }
  optionalSemi
  pure (PolyAST.RPMode (PolyAST.RawModeDecl name acyclic mDefEq mClass))

polyComprehensionDecl :: Parser PolyAST.RawPolyItem
polyComprehensionDecl = do
  _ <- symbol "comprehension"
  mode <- ident
  _ <- symbol "where"
  _ <- symbol "{"
  fields <- many compField
  _ <- symbol "}"
  optionalSemi
  (ctxExt, varName, reindexName) <- ensureCompFields fields
  pure
    ( PolyAST.RPComprehension
        PolyAST.RawCompDecl
          { PolyAST.rcmpMode = mode
          , PolyAST.rcmpCtxExt = ctxExt
          , PolyAST.rcmpVar = varName
          , PolyAST.rcmpReindex = reindexName
          }
    )
  where
    compField = do
      key <- ident
      _ <- symbol "="
      value <- ident
      optionalSemi
      pure (key, value)

    ensureCompFields fields = do
      ctxExt <- requireField "ctx_ext" fields
      varName <- requireField "var" fields
      reindexName <- requireField "reindex" fields
      let validKeys = S.fromList ["ctx_ext", "var", "reindex"]
          unknown = [k | (k, _) <- fields, not (k `S.member` validKeys)]
      case unknown of
        [] -> pure ()
        (k:_) -> fail ("unknown comprehension field: " <> T.unpack k)
      pure (ctxExt, varName, reindexName)

    requireField key fields =
      case [v | (k, v) <- fields, k == key] of
        [v] -> pure v
        [] -> fail ("missing comprehension field: " <> T.unpack key)
        _ -> fail ("duplicate comprehension field: " <> T.unpack key)

polyClassifierLiftDecl :: Parser PolyAST.RawPolyItem
polyClassifierLiftDecl = do
  _ <- symbol "lift_classifier"
  modName <- ident
  _ <- symbol "="
  liftExpr <- rawModExpr
  optionalSemi
  pure
    ( PolyAST.RPClassifierLift
        PolyAST.RawClassifierLiftDecl
          { PolyAST.rclModality = modName
          , PolyAST.rclLift = liftExpr
          }
    )

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

polyModTransformDecl :: Parser PolyAST.RawPolyItem
polyModTransformDecl = do
  _ <- symbol "mod_transform"
  name <- ident
  _ <- symbol ":"
  fromMe <- rawModExpr
  _ <- symbol "=>"
  toMe <- rawModExpr
  mWitness <- optional (symbol "witness" *> ident)
  _ <- symbol ";"
  pure
    ( PolyAST.RPModTransform
        PolyAST.RawModTransformDecl
          { PolyAST.rmtName = name
          , PolyAST.rmtFrom = fromMe
          , PolyAST.rmtTo = toMe
          , PolyAST.rmtWitness = mWitness
          }
    )

polyActionDecl :: Parser PolyAST.RawPolyItem
polyActionDecl = do
  _ <- symbol "action"
  modName <- ident
  _ <- symbol "where"
  _ <- symbol "{"
  mappings <- many actionGenMap
  _ <- symbol "}"
  optionalSemi
  pure (PolyAST.RPAction (PolyAST.RawActionDecl modName mappings))
  where
    actionGenMap = do
      _ <- symbol "gen"
      g <- ident
      _ <- symbol "->"
      rhs <- polyDiagExpr
      optionalSemi
      pure (g, rhs)

polyObligationDecl :: Parser PolyAST.RawPolyItem
polyObligationDecl = do
  _ <- symbol "obligation"
  name <- ident
  mForGen <- optional (keyword "for_gen")
  case mForGen of
    Just _ -> do
      _ <- symbol "@"
      mode <- ident
      _ <- symbol "="
      lhs <- oblExpr
      _ <- symbol "=="
      rhs <- oblExpr
      optionalSemi
      pure
        ( PolyAST.RPObligation
            PolyAST.RawObligationDecl
              { PolyAST.rodName = name
              , PolyAST.rodForGen = True
              , PolyAST.rodVars = []
              , PolyAST.rodDom = []
              , PolyAST.rodCod = []
              , PolyAST.rodMode = mode
              , PolyAST.rodLHS = lhs
              , PolyAST.rodRHS = rhs
              }
        )
    Nothing -> do
      vars <- polyParamList
      _ <- symbol ":"
      dom <- polyContext
      _ <- symbol "->"
      cod <- polyContext
      _ <- symbol "@"
      mode <- ident
      _ <- symbol "="
      lhs <- oblExpr
      _ <- symbol "=="
      rhs <- oblExpr
      optionalSemi
      pure
        ( PolyAST.RPObligation
            PolyAST.RawObligationDecl
              { PolyAST.rodName = name
              , PolyAST.rodForGen = False
              , PolyAST.rodVars = vars
              , PolyAST.rodDom = dom
              , PolyAST.rodCod = cod
              , PolyAST.rodMode = mode
              , PolyAST.rodLHS = lhs
              , PolyAST.rodRHS = rhs
              }
        )

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
  tys <- polyObjExpr `sepBy` symbol ","
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
  try polyBinderShape <|> (PolyAST.RIPort <$> polyObjExpr)

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
  _ <- optional (keyword "tm")
  name <- ident
  _ <- symbol ":"
  ty <- polyObjExpr
  pure PolyAST.RawBinderVarDecl { PolyAST.rbvName = name, PolyAST.rbvType = ty }

polyTmVarDecl :: Parser PolyAST.RawTmVarDecl
polyTmVarDecl = do
  name <- ident
  _ <- symbol ":"
  sortTy <- polyObjExpr
  pure PolyAST.RawTmVarDecl { PolyAST.rtvdName = name, PolyAST.rtvdSort = sortTy }

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
  try polyTmParam <|> polyTyParam
  where
    polyTyParam = PolyAST.RPDType <$> polyTyVarDecl
    polyTmParam = PolyAST.RPDTerm <$> polyTmVarDecl

polyParamList :: Parser [PolyAST.RawParamDecl]
polyParamList =
  try (symbol "(" *> polyParamDecl `sepBy` symbol "," <* symbol ")")
    <|> (map PolyAST.RPDType <$> many polyTyVarDeclBare)

polyObjExpr :: Parser PolyAST.RawPolyObjExpr
polyObjExpr = lexeme regular
  where
    regular = do
      name <- scopedIdentRaw
      mQual <- optional (try (char '.' *> scopedIdentRaw))
      mArgs <- optional (symbol "(" *> polyObjExpr `sepBy` symbol "," <* symbol ")")
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
  polyMetaVarTerm
    <|> polyTermRefTerm
    <|> polyMapTerm
    <|> try polyIdTerm
    <|> polySpliceTerm
    <|> polyLoopTerm
    <|> polyBoxTerm
    <|> polyGenTerm
    <|> parens polyDiagExpr

polyMetaVarTerm :: Parser PolyAST.RawDiagExpr
polyMetaVarTerm = do
  _ <- symbol "?"
  name <- ident
  pure (PolyAST.RDMetaVar name)

polyIdTerm :: Parser PolyAST.RawDiagExpr
polyIdTerm = do
  _ <- symbol "id"
  ctx <- polyContext
  pure (PolyAST.RDId ctx)

polyGenTerm :: Parser PolyAST.RawDiagExpr
polyGenTerm = do
  name <- ident
  mArgs <- optional (symbol "{" *> polyObjExpr `sepBy` symbol "," <* symbol "}")
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

polyMapTerm :: Parser PolyAST.RawDiagExpr
polyMapTerm = do
  _ <- symbol "map"
  _ <- symbol "["
  me <- rawModExpr
  _ <- symbol "]"
  _ <- symbol "("
  inner <- polyDiagExpr
  _ <- symbol ")"
  pure (PolyAST.RDMap me inner)

oblExpr :: Parser PolyAST.RawOblExpr
oblExpr = makeExprParser oblTerm operators
  where
    operators =
      [ [ InfixL (symbol "*" $> PolyAST.ROETensor) ]
      , [ InfixL (symbol ";" $> PolyAST.ROEComp) ]
      ]

oblTerm :: Parser PolyAST.RawOblExpr
oblTerm =
  try oblMapTerm
    <|> try oblGenTerm
    <|> try oblLiftDomTerm
    <|> try oblLiftCodTerm
    <|> parens oblExpr
    <|> (PolyAST.ROEDiag <$> polyDiagTerm)

oblMapTerm :: Parser PolyAST.RawOblExpr
oblMapTerm = do
  _ <- symbol "map"
  _ <- symbol "["
  me <- rawModExpr
  _ <- symbol "]"
  _ <- symbol "("
  inner <- oblExpr
  _ <- symbol ")"
  pure (PolyAST.ROEMap me inner)

oblGenTerm :: Parser PolyAST.RawOblExpr
oblGenTerm = PolyAST.ROEGen <$ symbol "@gen"

oblLiftDomTerm :: Parser PolyAST.RawOblExpr
oblLiftDomTerm = do
  _ <- symbol "lift_dom"
  _ <- symbol "("
  op <- polyDiagExpr
  _ <- symbol ")"
  pure (PolyAST.ROELiftDom op)

oblLiftCodTerm :: Parser PolyAST.RawOblExpr
oblLiftCodTerm = do
  _ <- symbol "lift_cod"
  _ <- symbol "("
  op <- polyDiagExpr
  _ <- symbol ")"
  pure (PolyAST.ROELiftCod op)

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
  | MorphismCheck Text
  | MorphismPolicy Text
  | MorphismMaxDepth Int
  | MorphismMaxStates Int
  | MorphismTimeoutMs Int

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
    <|> morphismCheck
    <|> morphismPolicy
    <|> morphismMaxDepth
    <|> morphismMaxStates
    <|> morphismTimeoutMs

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
  tgt <- polyObjExpr
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

morphismCheck :: Parser MorphismItem
morphismCheck = do
  _ <- symbol "check"
  name <- ident
  optionalSemi
  pure (MorphismCheck name)

morphismMaxDepth :: Parser MorphismItem
morphismMaxDepth = do
  _ <- symbol "max_depth"
  n <- fromIntegral <$> integer
  optionalSemi
  pure (MorphismMaxDepth n)

morphismMaxStates :: Parser MorphismItem
morphismMaxStates = do
  _ <- symbol "max_states"
  n <- fromIntegral <$> integer
  optionalSemi
  pure (MorphismMaxStates n)

morphismTimeoutMs :: Parser MorphismItem
morphismTimeoutMs = do
  _ <- symbol "timeout_ms"
  n <- fromIntegral <$> integer
  optionalSemi
  pure (MorphismTimeoutMs n)

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
    , rpmCheck = firstJust [ c | MorphismCheck c <- items ]
    , rpmPolicy = firstJust [ p | MorphismPolicy p <- items ]
    , rpmMaxDepth = firstJust [ d | MorphismMaxDepth d <- items ]
    , rpmMaxStates = firstJust [ s | MorphismMaxStates s <- items ]
    , rpmTimeoutMs = firstJust [ t | MorphismTimeoutMs t <- items ]
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
  first <- scopedIdentRaw
  rest <- many (char '.' *> scopedIdentRaw)
  pure (T.intercalate "." (first : rest))

plainIdent :: Parser Text
plainIdent = lexeme identRaw

scopedIdent :: Parser Text
scopedIdent = lexeme scopedIdentRaw

scopedIdentRaw :: Parser Text
scopedIdentRaw = T.intercalate "::" <$> sepBy1 identRaw (string "::")

ident :: Parser Text
ident = scopedIdent

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
