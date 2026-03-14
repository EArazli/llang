{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Model
  ( LanguageDef(..)
  , CustomExpansionDef(..)
  , ModuleElaboratorDef(..)
  , ModuleDataReprDef(..)
  , ModuleSurfaceCapability(..)
  , ModuleSurfaceDef(..)
  , InterfaceItemDef(..)
  , InterfaceTypeSig(..)
  , InterfaceValueSig(..)
  , InterfaceDef(..)
  , ModuleProvider(..)
  , ProviderRef(..)
  , ModuleImport(..)
  , ModuleItemDef(..)
  , ModuleDataDef(..)
  , ModuleTypeDef(..)
  , ModuleValueDef(..)
  , ModuleDef(..)
  , BuildDef(..)
  ) where

import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Text (Text)
import Strat.Common.Rules (RewritePolicy)
import Strat.Common.Provider (ModuleProvider(..), ProviderRef(..))
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Obj (Context, Obj)
import Strat.Poly.ModeTheory (ModeName)


data LanguageDef = LanguageDef
  { ldName :: Text
  , ldDoctrine :: Text
  , ldModuleSurface :: Maybe Text
  }
  deriving (Eq, Read, Show)


data CustomExpansionDef
  = CEDInlineItems
  deriving (Eq, Ord, Read, Show)


data ModuleElaboratorDef = ModuleElaboratorDef
  { medName :: Text
  , medBase :: Text
  , medInterfaceCustom :: Map Text CustomExpansionDef
  , medModuleCustom :: Map Text CustomExpansionDef
  }
  deriving (Eq, Read, Show)


data ModuleDataReprDef = ModuleDataReprDef
  { mdrName :: Text
  , mdrBase :: Text
  , mdrProviderInterface :: Maybe Text
  , mdrDescriptorPrefix :: Maybe Text
  }
  deriving (Eq, Read, Show)


data ModuleSurfaceCapability
  = MSCImport
  | MSCForeignImport
  | MSCType
  | MSCData
  | MSCValue
  | MSCExport
  | MSCExportType
  | MSCExportInterface
  | MSCCustom
  deriving (Eq, Ord, Read, Show)


data ModuleSurfaceDef = ModuleSurfaceDef
  { msdName :: Text
  , msdDoctrine :: Text
  , msdElaborator :: Text
  , msdMode :: Maybe Text
  , msdExprSurface :: Maybe Text
  , msdDefaultDataRepr :: Maybe Text
  , msdUses :: [Text]
  , msdCapabilities :: Set ModuleSurfaceCapability
  }
  deriving (Eq, Read, Show)


data InterfaceTypeSig = InterfaceTypeSig
  { itsName :: Text
  , itsMode :: ModeName
  , itsRepr :: Obj
  , itsBody :: Maybe Obj
  }
  deriving (Eq, Read, Show)


data InterfaceValueSig = InterfaceValueSig
  { ivsName :: Text
  , ivsMode :: ModeName
  , ivsDom :: Context
  , ivsCod :: Context
  }
  deriving (Eq, Read, Show)


data InterfaceItemDef
  = IIDType Text
  | IIDValue Text
  deriving (Eq, Read, Show)


data InterfaceDef = InterfaceDef
  { idefName :: Text
  , idefDoctrine :: Text
  , idefItems :: [InterfaceItemDef]
  , idefTypes :: Map Text InterfaceTypeSig
  , idefValues :: Map Text InterfaceValueSig
  }
  deriving (Eq, Read, Show)


data ModuleImport
  = ModuleImport
      { miModule :: Text
      , miAlias :: Maybe Text
      , miInterface :: Maybe Text
      , miAdapters :: [Text]
      }
  | ModuleForeignImport
      { miForeignName :: Text
      , miForeignInterface :: Text
      , miForeignDescriptor :: FilePath
      , miForeignAdapters :: [Text]
      }
  deriving (Eq, Ord, Read, Show)


data ModuleDataDef = ModuleDataDef
  { mddName :: Text
  , mddDoctrine :: Text
  , mddMode :: ModeName
  , mddRepr :: Text
  , mddTypeDef :: ModuleTypeDef
  , mddCtorDefs :: Map Text ModuleValueDef
  , mddCtorNames :: [Text]
  }
  deriving (Eq, Read, Show)


data ModuleTypeDef = ModuleTypeDef
  { mtdName :: Text
  , mtdDoctrine :: Text
  , mtdMode :: ModeName
  , mtdBody :: Obj
  }
  deriving (Eq, Read, Show)


data ModuleValueDef = ModuleValueDef
  { mvdName :: Text
  , mvdDoctrine :: Text
  , mvdMode :: ModeName
  , mvdDiagram :: Diagram
  , mvdPolicy :: RewritePolicy
  , mvdFuel :: Int
  }
  deriving (Eq, Read, Show)


data ModuleItemDef
  = MIDImport ModuleImport
  | MIDData Text [Text]
  | MIDType Text
  | MIDValue Text
  | MIDExportType Text Text
  | MIDExport Text Text
  | MIDExportInterface Text
  deriving (Eq, Read, Show)


data ModuleDef = ModuleDef
  { mdName :: Text
  , mdLanguage :: Text
  , mdDoctrine :: Text
  , mdImports :: [ModuleImport]
  , mdItems :: [ModuleItemDef]
  , mdProviders :: [ModuleProvider]
  , mdDataPackages :: Map Text ModuleDataDef
  , mdTypes :: Map Text ModuleTypeDef
  , mdValues :: Map Text ModuleValueDef
  , mdExportTypes :: Map Text ModuleTypeDef
  , mdExportValueSigs :: Map Text InterfaceValueSig
  , mdExports :: Map Text ModuleValueDef
  , mdExportInterfaces :: [Text]
  }
  deriving (Eq, Read, Show)


data BuildDef = BuildDef
  { bdName :: Text
  , bdModule :: Text
  , bdPipeline :: Text
  }
  deriving (Eq, Read, Show)
