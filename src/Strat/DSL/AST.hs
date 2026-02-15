{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.AST
  ( RawDecl(..)
  , RawFile(..)
  , RawPipeline(..)
  , RawPhase(..)
  , RawNormalizeOpts(..)
  , RawFoliationOpts(..)
  , RawValueExtractOpts(..)
  , RawDerivedDoctrine(..)
  , RawRun(..)
  , RawNamedRun(..)
  , RawDoctrineTemplate(..)
  , RawDoctrineInstantiate(..)
  , RawTerm(..)
  , RawNamedTerm(..)
  , RawPolyMorphism(..)
  , RawPolyMorphismItem(..)
  , RawPolyModeMap(..)
  , RawPolyModalityMap(..)
  , RawPolyAttrSortMap(..)
  , RawPolyTypeMap(..)
  , RawPolyGenMap(..)
  ) where

import Data.Text (Text)
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
  | DeclDoctrineTemplate RawDoctrineTemplate
  | DeclDoctrineInstantiate RawDoctrineInstantiate
  | DeclDerivedDoctrine RawDerivedDoctrine
  | DeclSurface Text SurfaceSpec
  | DeclPipeline RawPipeline
  | DeclMorphism RawPolyMorphism
  | DeclImplements Text Text Text
  | DeclRun RawNamedRun
  | DeclTerm RawNamedTerm
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


data RawFoliationOpts = RawFoliationOpts
  { rfoPolicy :: Maybe Text
  , rfoNaming :: Maybe Text
  , rfoReserved :: [Text]
  } deriving (Eq, Show)


data RawValueExtractOpts = RawValueExtractOpts
  { rveStdout :: Maybe Bool
  , rveRoot :: Maybe FilePath
  } deriving (Eq, Show)


data RawPhase
  = RPApply Text
  | RPNormalize RawNormalizeOpts
  | RPExtractFoliate Text (Maybe RawFoliationOpts)
  | RPExtractValue Text RawValueExtractOpts
  | RPExtractDiagramPretty
  deriving (Eq, Show)


data RawDerivedDoctrine = RawDerivedDoctrine
  { rddName :: Text
  , rddBase :: Text
  , rddMode :: Text
  , rddPolicy :: RawFoliationOpts
  } deriving (Eq, Show)


data RawRun = RawRun
  { rrPipeline :: Maybe Text
  , rrDoctrine :: Maybe Text
  , rrMode :: Maybe Text
  , rrSurface :: Maybe Text
  , rrUses :: [Text]
  , rrExprText :: Maybe Text
  } deriving (Eq, Show)


data RawNamedRun = RawNamedRun
  { rnrName :: Text
  , rnrRun :: RawRun
  } deriving (Eq, Show)

data RawDoctrineTemplate = RawDoctrineTemplate
  { rdtName :: Text
  , rdtParams :: [Text]
  , rdtBody :: PolyAST.RawPolyDoctrine
  } deriving (Eq, Show)

data RawDoctrineInstantiate = RawDoctrineInstantiate
  { rdiName :: Text
  , rdiTemplate :: Text
  , rdiArgs :: [Text]
  } deriving (Eq, Show)

data RawTerm = RawTerm
  { rtDoctrine :: Maybe Text
  , rtMode :: Maybe Text
  , rtSurface :: Maybe Text
  , rtUses :: [Text]
  , rtMorphisms :: [Text]
  , rtPolicy :: Maybe Text
  , rtFuel :: Maybe Int
  , rtExprText :: Text
  } deriving (Eq, Show)

data RawNamedTerm = RawNamedTerm
  { rntName :: Text
  , rntTerm :: RawTerm
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
  | RPMAttrSort RawPolyAttrSortMap
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

data RawPolyAttrSortMap = RawPolyAttrSortMap
  { rpmasSrc :: Text
  , rpmasTgt :: Text
  } deriving (Eq, Show)


data RawPolyTypeMap = RawPolyTypeMap
  { rpmtSrcType :: Text
  , rpmtParams :: [PolyAST.RawParamDecl]
  , rpmtSrcMode :: Text
  , rpmtTgtType :: PolyAST.RawPolyTypeExpr
  , rpmtTgtMode :: Text
  } deriving (Eq, Show)


data RawPolyGenMap = RawPolyGenMap
  { rpmgSrcGen :: Text
  , rpmgMode :: Text
  , rpmgRhs :: PolyAST.RawDiagExpr
  } deriving (Eq, Show)
