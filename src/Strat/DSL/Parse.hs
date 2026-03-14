{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Parse
  ( parseRawFile
  , parseInterfaceItemsText
  , parseModuleItemsText
  ) where

import Strat.DSL.AST
import Strat.Common.Rules
import qualified Strat.Poly.DSL.AST as PolyAST
import Strat.Poly.Literal (Literal(..), LiteralKind(..))
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


parseInterfaceItemsText :: Text -> Either Text [RawInterfaceItem]
parseInterfaceItemsText =
  parseTextWith "<interface custom>" (sc *> many interfaceItem <* eof)


parseModuleItemsText :: Text -> Either Text [RawModuleItem]
parseModuleItemsText =
  parseTextWith "<module custom>" (sc *> many (try (sc *> moduleItem)) <* eof)


parseTextWith :: String -> Parser a -> Text -> Either Text a
parseTextWith sourceLabel parser input =
  case runParser parser sourceLabel input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right ok -> Right ok

rawFile :: Parser RawFile
rawFile = do
  decls <- many (try (sc *> decl))
  pure (RawFile decls)

-- Declarations

decl :: Parser RawDecl
decl =
  importDecl
    <|> doctrineFunctorDecl
    <|> doctrineDecl
    <|> fragmentDecl
    <|> derivedDoctrineDecl
    <|> moduleElaboratorDecl
    <|> moduleDataReprDecl
    <|> morphismDecl
    <|> moduleSurfaceDecl
    <|> languageDecl
    <|> interfaceDecl
    <|> moduleDecl
    <|> buildDecl
    <|> surfaceDecl
    <|> pipelineDecl
    <|> implementsDecl

importDecl :: Parser RawDecl
importDecl = do
  _ <- symbol "include"
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
  _ <- (symbol "expr_surface" <|> symbol "surface")
  name <- scopedIdent
  _ <- symbol "where"
  spec <- surfaceSpecBlock
  optionalSemi
  pure (DeclSurface name spec)

moduleSurfaceDecl :: Parser RawDecl
moduleSurfaceDecl = do
  _ <- symbol "module_surface"
  name <- scopedIdent
  _ <- symbol "where"
  items <- moduleSurfaceBlock
  doctrineName <-
    case [d | MSDoctrine d <- items] of
      [d] -> pure d
      [] -> fail "module_surface: missing doctrine"
      _ -> fail "module_surface: duplicate doctrine item"
  optionalSemi
  pure
    ( DeclModuleSurface
        RawModuleSurface
          { rmsName = name
          , rmsDoctrine = doctrineName
          , rmsElaborator = firstJust [elab | MSElaborator elab <- items]
          , rmsMode = firstJust [m | MSMode m <- items]
          , rmsExprSurface = firstJust [s | MSExprSurface s <- items]
          , rmsDefaultDataRepr = firstJust [r | MSDataRepr r <- items]
          , rmsUses = concat [ns | MSUses ns <- items]
          , rmsCapabilities = [cap | MSAllow cap <- items]
          }
    )
  where
    firstJust [] = Nothing
    firstJust (x:_) = Just x

data ModuleSurfaceItem
  = MSDoctrine Text
  | MSElaborator Text
  | MSMode Text
  | MSExprSurface Text
  | MSDataRepr Text
  | MSUses [Text]
  | MSAllow RawModuleSurfaceCapability

moduleSurfaceBlock :: Parser [ModuleSurfaceItem]
moduleSurfaceBlock = do
  _ <- symbol "{"
  items <- many moduleSurfaceItem
  _ <- symbol "}"
  pure items

moduleSurfaceItem :: Parser ModuleSurfaceItem
moduleSurfaceItem =
  moduleSurfaceDoctrineItem
    <|> moduleSurfaceElaboratorItem
    <|> moduleSurfaceModeItem
    <|> moduleSurfaceExprSurfaceItem
    <|> moduleSurfaceDataReprItem
    <|> moduleSurfaceUsesItem
    <|> moduleSurfaceAllowItem

moduleSurfaceDoctrineItem :: Parser ModuleSurfaceItem
moduleSurfaceDoctrineItem = do
  _ <- symbol "doctrine"
  name <- scopedIdent
  optionalSemi
  pure (MSDoctrine name)

moduleSurfaceElaboratorItem :: Parser ModuleSurfaceItem
moduleSurfaceElaboratorItem = do
  _ <- symbol "elaborator"
  name <- scopedIdent
  optionalSemi
  pure (MSElaborator name)

moduleSurfaceModeItem :: Parser ModuleSurfaceItem
moduleSurfaceModeItem = do
  _ <- symbol "mode"
  name <- scopedIdent
  optionalSemi
  pure (MSMode name)

moduleSurfaceExprSurfaceItem :: Parser ModuleSurfaceItem
moduleSurfaceExprSurfaceItem = do
  _ <- (symbol "expr_surface" <|> symbol "surface")
  name <- scopedIdent
  optionalSemi
  pure (MSExprSurface name)

moduleSurfaceDataReprItem :: Parser ModuleSurfaceItem
moduleSurfaceDataReprItem = do
  _ <- symbol "data_repr"
  name <- scopedIdent
  optionalSemi
  pure (MSDataRepr name)

moduleSurfaceUsesItem :: Parser ModuleSurfaceItem
moduleSurfaceUsesItem = do
  _ <- symbol "uses"
  _ <- optional (symbol ":")
  names <- ident `sepBy1` symbol ","
  optionalSemi
  pure (MSUses names)

moduleSurfaceAllowItem :: Parser ModuleSurfaceItem
moduleSurfaceAllowItem = do
  _ <- symbol "allow"
  cap <-
    (RMSCForeignImport <$ symbol "foreign_import")
      <|> (RMSCExportInterface <$ symbol "export_interface")
      <|> (RMSCExportType <$ (symbol "export_type" <|> symbol "type_export"))
      <|> (RMSCImport <$ symbol "import")
      <|> (RMSCType <$ symbol "type")
      <|> (RMSCData <$ symbol "data")
      <|> (RMSCValue <$ symbol "value")
      <|> (RMSCExport <$ symbol "export")
      <|> (RMSCCustom <$ symbol "custom")
  optionalSemi
  pure (MSAllow cap)

languageDecl :: Parser RawDecl
languageDecl = do
  _ <- symbol "language"
  name <- scopedIdent
  _ <- symbol "where"
  items <- languageBlock
  doctrineName <-
    case [d | LangDoctrine d <- items] of
      [d] -> pure d
      [] -> fail "language: missing doctrine"
      _ -> fail "language: duplicate doctrine item"
  optionalSemi
  pure
    ( DeclLanguage
        RawLanguage
          { rlangName = name
          , rlangDoctrine = doctrineName
          , rlangModuleSurface = firstJust [s | LangModuleSurface s <- items]
          }
    )
  where
    firstJust [] = Nothing
    firstJust (x:_) = Just x

data LanguageItem
  = LangDoctrine Text
  | LangModuleSurface Text

languageBlock :: Parser [LanguageItem]
languageBlock = do
  _ <- symbol "{"
  items <- many languageItem
  _ <- symbol "}"
  pure items

languageItem :: Parser LanguageItem
languageItem =
  languageDoctrineItem
    <|> languageModuleSurfaceItem

languageDoctrineItem :: Parser LanguageItem
languageDoctrineItem = do
  _ <- symbol "doctrine"
  name <- scopedIdent
  optionalSemi
  pure (LangDoctrine name)

languageModuleSurfaceItem :: Parser LanguageItem
languageModuleSurfaceItem = do
  _ <- symbol "module_surface"
  name <- scopedIdent
  optionalSemi
  pure (LangModuleSurface name)

interfaceDecl :: Parser RawDecl
interfaceDecl = do
  _ <- symbol "interface"
  name <- scopedIdent
  _ <- symbol "in"
  target <- scopedIdent
  _ <- symbol "where"
  items <- interfaceBlock
  optionalSemi
  pure
    ( DeclInterface
        RawInterface
          { riName = name
          , riTarget = target
          , riItems = items
          }
    )

interfaceBlock :: Parser [RawInterfaceItem]
interfaceBlock = do
  _ <- symbol "{"
  items <- many interfaceItem
  _ <- symbol "}"
  pure items

interfaceItem :: Parser RawInterfaceItem
interfaceItem =
  try interfaceCustomItem
    <|> try interfaceOpaqueTypeItem
    <|> try interfaceTypeAliasItem
    <|> interfaceValueItem

interfaceCustomItem :: Parser RawInterfaceItem
interfaceCustomItem = do
  _ <- symbol "custom"
  tag <- scopedIdent
  body <- runBody
  optionalSemi
  pure (RIICustom (RawCustomItem tag body))

interfaceOpaqueTypeItem :: Parser RawInterfaceItem
interfaceOpaqueTypeItem = do
  _ <- symbol "opaque"
  _ <- symbol "type"
  name <- scopedIdent
  mMode <- optional (symbol "@" *> scopedIdent)
  optionalSemi
  pure (RIIType (RITOpaque name mMode))

interfaceTypeAliasItem :: Parser RawInterfaceItem
interfaceTypeAliasItem = do
  _ <- symbol "type"
  name <- scopedIdent
  mMode <- optional (symbol "@" *> scopedIdent)
  _ <- symbol "="
  body <- polyObjExpr
  optionalSemi
  pure (RIIType (RITAlias name mMode body))

rawValueSig :: Parser RawValueSig
rawValueSig = do
  _ <- symbol ":"
  dom <- polyContext
  _ <- symbol "->"
  cod <- polyContext
  mMode <- optional (symbol "@" *> scopedIdent)
  pure
    RawValueSig
      { rvsMode = mMode
      , rvsDom = dom
      , rvsCod = cod
      }

interfaceValueItem :: Parser RawInterfaceItem
interfaceValueItem = do
  _ <- symbol "val"
  name <- scopedIdent
  sig <- rawValueSig
  optionalSemi
  pure
    ( RIIValue
        RawInterfaceValue
          { rivName = name
          , rivMode = rvsMode sig
          , rivDom = rvsDom sig
          , rivCod = rvsCod sig
          }
    )

moduleDecl :: Parser RawDecl
moduleDecl = do
  _ <- symbol "module"
  name <- scopedIdent
  _ <- symbol "in"
  lang <- scopedIdent
  _ <- symbol "where"
  items <- moduleBlock
  optionalSemi
  pure
    ( DeclModule
        RawModule
          { rmName = name
          , rmLanguage = lang
          , rmItems = items
          }
    )

moduleBlock :: Parser [RawModuleItem]
moduleBlock = do
  _ <- symbol "{"
  items <- many (try (sc *> moduleItem))
  _ <- symbol "}"
  pure items

moduleItem :: Parser RawModuleItem
moduleItem =
  try moduleImportItem
    <|> try moduleDataItem
    <|> try moduleTypeItem
    <|> try moduleExportItem
    <|> try moduleCustomItem
    <|> moduleValueItem

moduleCustomItem :: Parser RawModuleItem
moduleCustomItem = do
  _ <- symbol "custom"
  tag <- scopedIdent
  body <- runBody
  optionalSemi
  pure (RMCustom (RawCustomItem tag body))

moduleImportItem :: Parser RawModuleItem
moduleImportItem = do
  _ <- symbol "import"
  item <-
    try foreignImportItem
      <|> localImportItem
  optionalSemi
  pure (RMImport item)
  where
    localImportItem = do
      name <- scopedIdent
      mAlias <- optional (symbol "as" *> scopedIdent)
      mIface <- optional (symbol ":" *> scopedIdent)
      mAdapter <- optional (symbol "using" *> scopedIdent)
      pure
        RawModuleImport
          { rmiModule = name
          , rmiAlias = mAlias
          , rmiInterface = mIface
          , rmiAdapter = mAdapter
          }

    foreignImportItem = do
      _ <- symbol "foreign"
      name <- scopedIdent
      _ <- symbol ":"
      iface <- scopedIdent
      _ <- symbol "via"
      provider <- stringLiteral
      mAdapter <- optional (symbol "using" *> scopedIdent)
      pure
        RawForeignImport
          { rfiName = name
          , rfiInterface = iface
          , rfiProvider = T.unpack provider
          , rfiAdapter = mAdapter
          }

moduleTypeItem :: Parser RawModuleItem
moduleTypeItem = do
  _ <- symbol "type"
  name <- scopedIdent
  mMode <- optional (symbol "@" *> scopedIdent)
  _ <- symbol "="
  body <- polyObjExpr
  optionalSemi
  pure
    ( RMType
        RawModuleType
          { rmtName = name
          , rmtMode = mMode
          , rmtBody = body
          }
    )


moduleDataItem :: Parser RawModuleItem
moduleDataItem = do
  _ <- symbol "data"
  name <- scopedIdent
  mMode <- optional (symbol "@" *> scopedIdent)
  mRepr <- optional (symbol "using" *> scopedIdent)
  _ <- symbol "where"
  _ <- symbol "{"
  ctors <- many moduleCtorDecl
  _ <- symbol "}"
  optionalSemi
  pure
    ( RMData
        RawModuleData
          { rmdName = name
          , rmdMode = mMode
          , rmdRepr = mRepr
          , rmdCtors = ctors
          }
    )


moduleCtorDecl :: Parser RawModuleCtor
moduleCtorDecl = do
  _ <- symbol "ctor"
  name <- scopedIdent
  sig <- rawValueSig
  optionalSemi
  pure
    RawModuleCtor
      { rmcName = name
      , rmcSig = sig
      }

moduleExportItem :: Parser RawModuleItem
moduleExportItem = do
  _ <- symbol "export"
  ( do
      _ <- symbol "interface"
      iface <- scopedIdent
      optionalSemi
      pure (RMExportInterface iface)
    )
    <|> do
      _ <- symbol "type"
      _ <- symbol "{"
      names <- moduleTypeExportSpec `sepBy1` symbol ","
      _ <- symbol "}"
      optionalSemi
      pure (RMTypeExport names)
    <|> do
      _ <- symbol "{"
      names <- moduleExportSpec `sepBy1` symbol ","
      _ <- symbol "}"
      optionalSemi
      pure (RMExport names)

moduleExportSpec :: Parser RawModuleExport
moduleExportSpec = do
  localName <- scopedIdent
  publicName <- option localName (symbol "as" *> scopedIdent)
  pure
    RawModuleExport
      { rmeLocal = localName
      , rmePublic = publicName
      }

moduleTypeExportSpec :: Parser RawModuleTypeExport
moduleTypeExportSpec = do
  localName <- scopedIdent
  publicName <- option localName (symbol "as" *> scopedIdent)
  pure
    RawModuleTypeExport
      { rmteLocal = localName
      , rmtePublic = publicName
      }

moduleValueItem :: Parser RawModuleItem
moduleValueItem =
  RMValue <$> moduleValueDecl


moduleValueDecl :: Parser RawModuleValue
moduleValueDecl = do
  _ <- symbol "let"
  name <- scopedIdent
  mSig <- optional (try rawValueSig)
  items <- option [] (symbol "where" *> valueBlock)
  exprText <- runBody
  optionalSemi
  pure (buildModuleValue name mSig items exprText)

buildDecl :: Parser RawDecl
buildDecl = do
  _ <- symbol "build"
  name <- scopedIdent
  _ <- symbol "from"
  moduleName <- scopedIdent
  _ <- symbol "using"
  pipelineName <- scopedIdent
  optionalSemi
  pure (DeclBuild (RawBuild name moduleName pipelineName))

fragmentDecl :: Parser RawDecl
fragmentDecl = do
  _ <- symbol "fragment"
  name <- scopedIdent
  _ <- symbol "in"
  base <- scopedIdent
  _ <- symbol "mode"
  modeName <- scopedIdent
  _ <- symbol "where"
  items <- fragmentBlock
  optionalSemi
  pure (DeclFragment (RawFragmentDecl name base modeName items))

derivedDoctrineDecl :: Parser RawDecl
derivedDoctrineDecl = do
  _ <- symbol "derived"
  _ <- symbol "doctrine"
  name <- scopedIdent
  _ <- symbol "="
  _ <- symbol "reflect"
  _ <- symbol "quotation"
  _ <- symbol "of"
  baseName <- scopedIdent
  _ <- symbol "mode"
  modeName <- scopedIdent
  optionalSemi
  pure (DeclDerivedDoctrine (RawDerivedDoctrine name baseName modeName))


moduleElaboratorDecl :: Parser RawDecl
moduleElaboratorDecl = do
  _ <- symbol "module_elaborator"
  name <- scopedIdent
  _ <- symbol "where"
  items <- moduleElaboratorBlock
  baseName <-
    case [base | MEBase base <- items] of
      [base] -> pure base
      [] -> fail "module_elaborator: missing extends item"
      _ -> fail "module_elaborator: duplicate extends item"
  ifaceCustom <- uniquePairs "module_elaborator: duplicate interface custom tag" [(tag, expansion) | MEInterfaceCustom tag expansion <- items]
  moduleCustom <- uniquePairs "module_elaborator: duplicate module custom tag" [(tag, expansion) | MEModuleCustom tag expansion <- items]
  optionalSemi
  pure
    ( DeclModuleElaborator
        RawModuleElaborator
          { rmeName = name
          , rmeBase = baseName
          , rmeInterfaceCustom = ifaceCustom
          , rmeModuleCustom = moduleCustom
          }
    )
  where
    uniquePairs errLabel pairs =
      if S.size (S.fromList (map fst pairs)) == length pairs
        then pure (M.fromList pairs)
        else fail errLabel


data ModuleElaboratorItem
  = MEBase Text
  | MEInterfaceCustom Text RawCustomExpansion
  | MEModuleCustom Text RawCustomExpansion


moduleElaboratorBlock :: Parser [ModuleElaboratorItem]
moduleElaboratorBlock = do
  _ <- symbol "{"
  items <- many moduleElaboratorItem
  _ <- symbol "}"
  pure items


moduleElaboratorItem :: Parser ModuleElaboratorItem
moduleElaboratorItem =
  moduleElaboratorBaseItem
    <|> try moduleElaboratorInterfaceCustomItem
    <|> moduleElaboratorModuleCustomItem


moduleElaboratorBaseItem :: Parser ModuleElaboratorItem
moduleElaboratorBaseItem = do
  _ <- symbol "extends"
  name <- scopedIdent
  optionalSemi
  pure (MEBase name)


moduleElaboratorInterfaceCustomItem :: Parser ModuleElaboratorItem
moduleElaboratorInterfaceCustomItem = do
  _ <- symbol "interface"
  _ <- symbol "custom"
  tag <- scopedIdent
  _ <- symbol "as"
  expansion <- customExpansion
  optionalSemi
  pure (MEInterfaceCustom tag expansion)


moduleElaboratorModuleCustomItem :: Parser ModuleElaboratorItem
moduleElaboratorModuleCustomItem = do
  _ <- symbol "module"
  _ <- symbol "custom"
  tag <- scopedIdent
  _ <- symbol "as"
  expansion <- customExpansion
  optionalSemi
  pure (MEModuleCustom tag expansion)


customExpansion :: Parser RawCustomExpansion
customExpansion =
  RCXInlineItems <$ (symbol "items" <|> symbol "inline_items")


moduleDataReprDecl :: Parser RawDecl
moduleDataReprDecl = do
  _ <- symbol "data_repr"
  name <- scopedIdent
  _ <- symbol "where"
  items <- moduleDataReprBlock
  baseName <-
    case [base | MDRBase base <- items] of
      [base] -> pure base
      [] -> fail "data_repr: missing extends item"
      _ -> fail "data_repr: duplicate extends item"
  providerInterface <- atMostOne "data_repr: duplicate provider_interface item" [iface | MDRProviderInterface iface <- items]
  descriptorPrefix <- atMostOne "data_repr: duplicate descriptor_prefix item" [prefix | MDRDescriptorPrefix prefix <- items]
  optionalSemi
  pure
    ( DeclModuleDataRepr
        RawModuleDataReprDecl
          { rmdrName = name
          , rmdrBase = baseName
          , rmdrProviderInterface = providerInterface
          , rmdrDescriptorPrefix = descriptorPrefix
          }
    )
  where
    atMostOne _ [] = pure Nothing
    atMostOne _ [x] = pure (Just x)
    atMostOne errLabel _ = fail errLabel


data ModuleDataReprItem
  = MDRBase Text
  | MDRProviderInterface Text
  | MDRDescriptorPrefix Text


moduleDataReprBlock :: Parser [ModuleDataReprItem]
moduleDataReprBlock = do
  _ <- symbol "{"
  items <- many moduleDataReprItem
  _ <- symbol "}"
  pure items


moduleDataReprItem :: Parser ModuleDataReprItem
moduleDataReprItem =
  moduleDataReprBaseItem
    <|> moduleDataReprProviderInterfaceItem
    <|> moduleDataReprDescriptorPrefixItem


moduleDataReprBaseItem :: Parser ModuleDataReprItem
moduleDataReprBaseItem = do
  _ <- symbol "extends"
  name <- scopedIdent
  optionalSemi
  pure (MDRBase name)


moduleDataReprProviderInterfaceItem :: Parser ModuleDataReprItem
moduleDataReprProviderInterfaceItem = do
  _ <- symbol "provider_interface"
  name <- scopedIdent
  optionalSemi
  pure (MDRProviderInterface name)


moduleDataReprDescriptorPrefixItem :: Parser ModuleDataReprItem
moduleDataReprDescriptorPrefixItem = do
  _ <- symbol "descriptor_prefix"
  prefix <- stringLiteral
  optionalSemi
  pure (MDRDescriptorPrefix prefix)

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
    <|> polyLiteralDecl
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
    pure
      PolyAST.RawClassifiedByDecl
        { PolyAST.rcdClassifier = cls
        , PolyAST.rcdUniverse = uni
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

polyLiteralDecl :: Parser PolyAST.RawPolyItem
polyLiteralDecl = do
  _ <- symbol "literal"
  typeName <- ident
  _ <- symbol "@"
  ownerMode <- ident
  _ <- symbol "="
  kind <- literalKind
  optionalSemi
  pure
    ( PolyAST.RPLiteral
        PolyAST.RawLiteralDecl
          { PolyAST.rldTypeName = typeName
          , PolyAST.rldOwnerMode = ownerMode
          , PolyAST.rldKind = kind
          }
    )
  where
    literalKind =
      (symbol "int" $> LKInt)
        <|> (symbol "string" $> LKString)
        <|> (symbol "bool" $> LKBool)

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
    , PolyAST.rpgDom = dom
    , PolyAST.rpgCod = cod
    , PolyAST.rpgMode = mode
    }

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
polyObjExpr = lexeme (literalExpr <|> regular)
  where
    literalExpr =
      (PolyAST.RPLit . LInt . fromIntegral <$> integer)
        <|> (PolyAST.RPLit . LString <$> stringLiteral)
        <|> (PolyAST.RPLit (LBool True) <$ keyword "true")
        <|> (PolyAST.RPLit (LBool False) <$ keyword "false")

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
    <|> polyMapTerm
    <|> try polyIdTerm
    <|> polySpliceTerm
    <|> polyTraceTerm
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
  mArgs <- optional polyGenArgs
  mBinderArgs <- optional polyBinderArgs
  pure (PolyAST.RDGen name mArgs mBinderArgs)

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

polyGenArgs :: Parser [PolyAST.RawGenArg]
polyGenArgs = do
  _ <- symbol "("
  args <- polyGenArg `sepBy` symbol ","
  _ <- symbol ")"
  if mixedArgStyles args
    then fail "generator arguments must be either all named or all positional"
    else pure args
  where
    mixedArgStyles [] = False
    mixedArgStyles xs =
      let named = [ () | PolyAST.RGNamed _ _ <- xs ]
          positional = [ () | PolyAST.RGPos _ <- xs ]
      in not (null named) && not (null positional)

polyGenArg :: Parser PolyAST.RawGenArg
polyGenArg =
  try named <|> positional
  where
    named = do
      field <- ident
      _ <- symbol "="
      term <- polyObjExpr
      pure (PolyAST.RGNamed field term)
    positional = PolyAST.RGPos <$> polyObjExpr

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

polyTraceTerm :: Parser PolyAST.RawDiagExpr
polyTraceTerm = do
  _ <- keyword "trace"
  k <- parseTraceArity
  _ <- symbol "{"
  inner <- polyDiagExpr
  _ <- symbol "}"
  pure (PolyAST.RDTrace k inner)
  where
    parseTraceArity = do
      n <- integer
      if n > fromIntegral (maxBound :: Int)
        then fail "trace arity is too large"
        else pure (fromInteger n)

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
    <|> try pipelineQuoteItem
    <|> try pipelineLinkItem
    <|> try pipelineBundleItem
    <|> try pipelineProjectItem
    <|> pipelineEmitItem

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

pipelineQuoteItem :: Parser RawPhase
pipelineQuoteItem = do
  _ <- symbol "quote"
  _ <- symbol "using"
  fragment <- ident
  _ <- symbol "into"
  target <- ident
  optionalSemi
  pure (RPQuoteInto fragment target)

pipelineLinkItem :: Parser RawPhase
pipelineLinkItem = do
  _ <- symbol "link"
  name <- scopedIdent
  optionalSemi
  pure (RPLink name)

pipelineBundleItem :: Parser RawPhase
pipelineBundleItem = do
  _ <- symbol "bundle"
  ( do
      _ <- symbol "all"
      optionalSemi
      pure RPBundleAll
    )
    <|> do
      _ <- symbol "{"
      items <- bundleItem `sepBy1` symbol ","
      _ <- symbol "}"
      optionalSemi
      pure (RPBundle items)

bundleItem :: Parser RawBundleItem
bundleItem = do
  sourceName <- scopedIdent
  targetName <- option sourceName (symbol "as" *> scopedIdent)
  pure
    RawBundleItem
      { rbiSource = sourceName
      , rbiTarget = targetName
      }

pipelineProjectItem :: Parser RawPhase
pipelineProjectItem = do
  _ <- symbol "project"
  _ <- symbol "export"
  name <- scopedIdent
  optionalSemi
  pure (RPProjectExport name)

pipelineEmitItem :: Parser RawPhase
pipelineEmitItem = do
  _ <- symbol "emit"
  _ <- symbol "via"
  backendName <- scopedIdent
  opts <- option (RawValueExtractOpts Nothing Nothing) valueExtractOptsBlock
  optionalSemi
  pure (RPEmitVia backendName opts)

fragmentBlock :: Parser [RawFragmentItem]
fragmentBlock = do
  _ <- symbol "{"
  items <- many fragmentItem
  _ <- symbol "}"
  pure items

fragmentItem :: Parser RawFragmentItem
fragmentItem =
  fragmentIncludeItem <|> fragmentCrossItem

fragmentIncludeItem :: Parser RawFragmentItem
fragmentIncludeItem = do
  _ <- symbol "include"
  _ <- symbol "gen"
  name <- ident
  optionalSemi
  pure (RFIncludeGen name)

fragmentCrossItem :: Parser RawFragmentItem
fragmentCrossItem = do
  _ <- symbol "cross"
  item <-
    (RFCrossBinders <$> (symbol "binders" *> symbol "=" *> boolLiteral))
      <|> (RFCrossBoxes <$> (symbol "boxes" *> symbol "=" *> boolLiteral))
      <|> (RFCrossFeedback <$> (symbol "feedback" *> symbol "=" *> boolLiteral))
  optionalSemi
  pure item

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

data ValueItem
  = ValueMode Text
  | ValueSurface Text
  | ValueApply Text
  | ValueUses [Text]
  | ValuePolicy Text
  | ValueFuel Int

valueBlock :: Parser [ValueItem]
valueBlock = do
  _ <- symbol "{"
  items <- many valueItem
  _ <- symbol "}"
  pure items

valueItem :: Parser ValueItem
valueItem =
  valueModeItem
    <|> valueSurfaceItem
    <|> valueApplyItem
    <|> valueUsesItem
    <|> valuePolicyItem
    <|> valueFuelItem

valueModeItem :: Parser ValueItem
valueModeItem = do
  _ <- keyword "mode"
  name <- ident
  optionalSemi
  pure (ValueMode name)

valueSurfaceItem :: Parser ValueItem
valueSurfaceItem = do
  _ <- (symbol "expr_surface" <|> symbol "surface")
  name <- ident
  optionalSemi
  pure (ValueSurface name)

valueApplyItem :: Parser ValueItem
valueApplyItem = do
  _ <- symbol "apply"
  name <- ident
  optionalSemi
  pure (ValueApply name)

valueUsesItem :: Parser ValueItem
valueUsesItem = do
  _ <- symbol "uses"
  _ <- optional (symbol ":")
  names <- ident `sepBy1` symbol ","
  optionalSemi
  pure (ValueUses names)

valuePolicyItem :: Parser ValueItem
valuePolicyItem = do
  _ <- symbol "policy"
  name <- ident
  optionalSemi
  pure (ValuePolicy name)

valueFuelItem :: Parser ValueItem
valueFuelItem = do
  _ <- symbol "fuel"
  n <- fromIntegral <$> integer
  optionalSemi
  pure (ValueFuel n)

buildModuleValue :: Text -> Maybe RawValueSig -> [ValueItem] -> Text -> RawModuleValue
buildModuleValue name mSig items exprText =
  RawModuleValue
    { rmvName = name
    , rmvSig = mSig
    , rmvMode = firstJust [m | ValueMode m <- items]
    , rmvSurface = firstJust [s | ValueSurface s <- items]
    , rmvMorphisms = [n | ValueApply n <- items]
    , rmvUses = concat [ns | ValueUses ns <- items]
    , rmvPolicy = firstJust [p | ValuePolicy p <- items]
    , rmvFuel = firstJust [f | ValueFuel f <- items]
    , rmvExprText = exprText
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
identRaw = T.pack <$> ((:) <$> (letterChar <|> char '_') <*> many identChar)

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
