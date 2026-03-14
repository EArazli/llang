{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.AST
  ( RawDecl(..)
  , RawFile(..)
  , RawPipeline(..)
  , RawPhase(..)
  , RawNormalizeOpts(..)
  , RawValueExtractOpts(..)
  , RawFragmentItem(..)
  , RawFragmentDecl(..)
  , RawDerivedDoctrine(..)
  , RawCustomExpansion(..)
  , RawModuleElaborator(..)
  , RawModuleDataReprDecl(..)
  , RawLanguage(..)
  , RawModuleSurfaceCapability(..)
  , RawModuleSurface(..)
  , RawCustomItem(..)
  , RawInterface(..)
  , RawInterfaceItem(..)
  , RawInterfaceType(..)
  , RawInterfaceValue(..)
  , RawModule(..)
  , RawModuleItem(..)
  , RawModuleImport(..)
  , RawModuleData(..)
  , RawModuleCtor(..)
  , RawModuleType(..)
  , RawModuleExport(..)
  , RawModuleTypeExport(..)
  , RawModuleValue(..)
  , RawValueSig(..)
  , RawBuild(..)
  , RawDoctrineFunctor(..)
  , RawFunctorParam(..)
  , RawDoctrineApply(..)
  , RawPolyMorphism(..)
  , RawPolyMorphismItem(..)
  , RawPolyModeMap(..)
  , RawPolyModalityMap(..)
  , RawPolyTypeMap(..)
  , RawPolyGenMap(..)
  , RawBundleItem(..)
  ) where

import Data.Text (Text)
import Data.Map.Strict (Map)
import Strat.Poly.Surface.Spec (SurfaceSpec)
import qualified Strat.Poly.DSL.AST as PolyAST


data RawDecl
  = DeclImport FilePath
  | DeclDoctrine PolyAST.RawPolyDoctrine
  | DeclDoctrinePushout Text Text Text
  | DeclDoctrineCoproduct Text Text Text
  | DeclDoctrineEffects
      { rdeName :: Text
      , rdeBase :: Text
      , rdeEffects :: [Text]
      }
  | DeclDoctrineFunctor RawDoctrineFunctor
  | DeclDoctrineApply RawDoctrineApply
  | DeclFragment RawFragmentDecl
  | DeclDerivedDoctrine RawDerivedDoctrine
  | DeclModuleElaborator RawModuleElaborator
  | DeclModuleDataRepr RawModuleDataReprDecl
  | DeclSurface Text SurfaceSpec
  | DeclModuleSurface RawModuleSurface
  | DeclLanguage RawLanguage
  | DeclInterface RawInterface
  | DeclModule RawModule
  | DeclBuild RawBuild
  | DeclPipeline RawPipeline
  | DeclMorphism RawPolyMorphism
  | DeclImplements Text Text Text
  deriving (Eq, Show)

newtype RawFile = RawFile [RawDecl]
  deriving (Eq, Show)


data RawPipeline = RawPipeline
  { rplName :: Text
  , rplPhases :: [RawPhase]
  } deriving (Eq, Show)


data RawNormalizeOpts = RawNormalizeOpts
  { rnoPolicy :: Maybe Text
  , rnoFuel :: Maybe Int
  } deriving (Eq, Show)


data RawValueExtractOpts = RawValueExtractOpts
  { rveStdout :: Maybe Bool
  , rveRoot :: Maybe FilePath
  } deriving (Eq, Show)


data RawPhase
  = RPApply Text
  | RPNormalize RawNormalizeOpts
  | RPQuoteInto Text Text
  | RPLink Text
  | RPBundleAll
  | RPBundle [RawBundleItem]
  | RPProjectExport Text
  | RPEmitVia Text RawValueExtractOpts
  deriving (Eq, Show)


data RawBundleItem = RawBundleItem
  { rbiSource :: Text
  , rbiTarget :: Text
  } deriving (Eq, Show)

data RawFragmentItem
  = RFIncludeGen Text
  | RFCrossBinders Bool
  | RFCrossBoxes Bool
  | RFCrossFeedback Bool
  deriving (Eq, Show)

data RawFragmentDecl = RawFragmentDecl
  { rfdName :: Text
  , rfdBase :: Text
  , rfdMode :: Text
  , rfdItems :: [RawFragmentItem]
  } deriving (Eq, Show)


data RawDerivedDoctrine = RawDerivedDoctrine
  { rddName :: Text
  , rddBase :: Text
  , rddMode :: Text
  } deriving (Eq, Show)


data RawCustomExpansion
  = RCXInlineItems
  deriving (Eq, Ord, Show)


data RawModuleElaborator = RawModuleElaborator
  { rmeName :: Text
  , rmeBase :: Text
  , rmeInterfaceCustom :: Map Text RawCustomExpansion
  , rmeModuleCustom :: Map Text RawCustomExpansion
  } deriving (Eq, Show)


data RawModuleDataReprDecl = RawModuleDataReprDecl
  { rmdrName :: Text
  , rmdrBase :: Text
  , rmdrProviderInterface :: Maybe Text
  , rmdrDescriptorPrefix :: Maybe Text
  } deriving (Eq, Show)


data RawLanguage = RawLanguage
  { rlangName :: Text
  , rlangDoctrine :: Text
  , rlangModuleSurface :: Maybe Text
  } deriving (Eq, Show)


data RawModuleSurfaceCapability
  = RMSCImport
  | RMSCForeignImport
  | RMSCType
  | RMSCData
  | RMSCValue
  | RMSCExport
  | RMSCExportType
  | RMSCExportInterface
  | RMSCCustom
  deriving (Eq, Ord, Show)


data RawModuleSurface = RawModuleSurface
  { rmsName :: Text
  , rmsDoctrine :: Text
  , rmsElaborator :: Maybe Text
  , rmsMode :: Maybe Text
  , rmsExprSurface :: Maybe Text
  , rmsDefaultDataRepr :: Maybe Text
  , rmsUses :: [Text]
  , rmsCapabilities :: [RawModuleSurfaceCapability]
  } deriving (Eq, Show)


data RawInterfaceType
  = RITOpaque
      { ritName :: Text
      , ritMode :: Maybe Text
      }
  | RITAlias
      { ritName :: Text
      , ritMode :: Maybe Text
      , ritBody :: PolyAST.RawPolyObjExpr
      }
  deriving (Eq, Show)


data RawInterfaceValue = RawInterfaceValue
  { rivName :: Text
  , rivMode :: Maybe Text
  , rivDom :: PolyAST.RawPolyContext
  , rivCod :: PolyAST.RawPolyContext
  } deriving (Eq, Show)


data RawInterface = RawInterface
  { riName :: Text
  , riTarget :: Text
  , riItems :: [RawInterfaceItem]
  } deriving (Eq, Show)


data RawCustomItem = RawCustomItem
  { rciTag :: Text
  , rciBody :: Text
  } deriving (Eq, Show)


data RawInterfaceItem
  = RIIType RawInterfaceType
  | RIIValue RawInterfaceValue
  | RIICustom RawCustomItem
  deriving (Eq, Show)


data RawModuleImport
  = RawModuleImport
      { rmiModule :: Text
      , rmiAlias :: Maybe Text
      , rmiInterface :: Maybe Text
      , rmiAdapter :: Maybe Text
      }
  | RawForeignImport
      { rfiName :: Text
      , rfiInterface :: Text
      , rfiProvider :: FilePath
      , rfiAdapter :: Maybe Text
      }
  deriving (Eq, Show)


data RawModuleType = RawModuleType
  { rmtName :: Text
  , rmtMode :: Maybe Text
  , rmtBody :: PolyAST.RawPolyObjExpr
  } deriving (Eq, Show)


data RawModuleCtor = RawModuleCtor
  { rmcName :: Text
  , rmcSig :: RawValueSig
  } deriving (Eq, Show)


data RawModuleData = RawModuleData
  { rmdName :: Text
  , rmdMode :: Maybe Text
  , rmdRepr :: Maybe Text
  , rmdCtors :: [RawModuleCtor]
  } deriving (Eq, Show)


data RawModuleExport = RawModuleExport
  { rmeLocal :: Text
  , rmePublic :: Text
  } deriving (Eq, Show)


data RawModuleTypeExport = RawModuleTypeExport
  { rmteLocal :: Text
  , rmtePublic :: Text
  } deriving (Eq, Show)


data RawValueSig = RawValueSig
  { rvsMode :: Maybe Text
  , rvsDom :: PolyAST.RawPolyContext
  , rvsCod :: PolyAST.RawPolyContext
  } deriving (Eq, Show)


data RawModuleValue = RawModuleValue
  { rmvName :: Text
  , rmvSig :: Maybe RawValueSig
  , rmvMode :: Maybe Text
  , rmvSurface :: Maybe Text
  , rmvUses :: [Text]
  , rmvMorphisms :: [Text]
  , rmvPolicy :: Maybe Text
  , rmvFuel :: Maybe Int
  , rmvExprText :: Text
  } deriving (Eq, Show)


data RawModule = RawModule
  { rmName :: Text
  , rmLanguage :: Text
  , rmItems :: [RawModuleItem]
  } deriving (Eq, Show)


data RawModuleItem
  = RMImport RawModuleImport
  | RMData RawModuleData
  | RMType RawModuleType
  | RMValue RawModuleValue
  | RMCustom RawCustomItem
  | RMTypeExport [RawModuleTypeExport]
  | RMExport [RawModuleExport]
  | RMExportInterface Text
  deriving (Eq, Show)


data RawBuild = RawBuild
  { rbName :: Text
  , rbModule :: Text
  , rbPipeline :: Text
  } deriving (Eq, Show)

data RawFunctorParam = RawFunctorParam
  { rfpName :: Text
  , rfpSchema :: Text
  } deriving (Eq, Show)

data RawDoctrineFunctor = RawDoctrineFunctor
  { rdfName :: Text
  , rdfParams :: [RawFunctorParam]
  , rdfBody :: PolyAST.RawPolyDoctrine
  } deriving (Eq, Show)

data RawDoctrineApply = RawDoctrineApply
  { rdaName :: Text
  , rdaFunctor :: Text
  , rdaTarget :: Text
  , rdaUsing :: Map Text Text
  } deriving (Eq, Show)

data RawPolyMorphism = RawPolyMorphism
  { rpmName :: Text
  , rpmSrc :: Text
  , rpmTgt :: Text
  , rpmItems :: [RawPolyMorphismItem]
  , rpmCheck :: Maybe Text
  , rpmPolicy :: Maybe Text
  , rpmMaxDepth :: Maybe Int
  , rpmMaxStates :: Maybe Int
  , rpmTimeoutMs :: Maybe Int
  } deriving (Eq, Show)


data RawPolyMorphismItem
  = RPMMode RawPolyModeMap
  | RPMModality RawPolyModalityMap
  | RPMType RawPolyTypeMap
  | RPMGen RawPolyGenMap
  | RPMCoercion
  deriving (Eq, Show)

data RawPolyModeMap = RawPolyModeMap
  { rpmmSrc :: Text
  , rpmmTgt :: Text
  } deriving (Eq, Show)

data RawPolyModalityMap = RawPolyModalityMap
  { rpmmSrc :: Text
  , rpmmTgt :: PolyAST.RawModExpr
  } deriving (Eq, Show)

data RawPolyTypeMap = RawPolyTypeMap
  { rpmtSrcType :: Text
  , rpmtParams :: [PolyAST.RawParamDecl]
  , rpmtSrcMode :: Text
  , rpmtTgtType :: PolyAST.RawPolyObjExpr
  , rpmtTgtMode :: Text
  } deriving (Eq, Show)


data RawPolyGenMap = RawPolyGenMap
  { rpmgSrcGen :: Text
  , rpmgMode :: Text
  , rpmgRhs :: PolyAST.RawDiagExpr
  } deriving (Eq, Show)
