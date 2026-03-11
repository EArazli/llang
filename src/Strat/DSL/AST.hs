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
  , RawTransformTypeParam(..)
  , RawTransformObjectDecl(..)
  , RawTransformUtility(..)
  , RawTransformLoopItem(..)
  , RawTransformerItem(..)
  , RawTransformerDecl(..)
  , RawDerivedDoctrine(..)
  , RawRun(..)
  , RawNamedRun(..)
  , RawDoctrineFunctor(..)
  , RawFunctorParam(..)
  , RawDoctrineApply(..)
  , RawTerm(..)
  , RawNamedTerm(..)
  , RawPolyMorphism(..)
  , RawPolyMorphismItem(..)
  , RawPolyModeMap(..)
  , RawPolyModalityMap(..)
  , RawPolyTypeMap(..)
  , RawPolyGenMap(..)
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
  | DeclTransformer RawTransformerDecl
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


data RawValueExtractOpts = RawValueExtractOpts
  { rveStdout :: Maybe Bool
  , rveRoot :: Maybe FilePath
  } deriving (Eq, Show)


data RawPhase
  = RPApply Text
  | RPNormalize RawNormalizeOpts
  | RPQuoteInto Text
  | RPExtractValue Text RawValueExtractOpts
  | RPExtractDiagramPretty
  deriving (Eq, Show)

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

data RawTransformTypeParam = RawTransformTypeParam
  { rttpName :: Text
  , rttpModeVar :: Text
  } deriving (Eq, Show)

data RawTransformObjectDecl = RawTransformObjectDecl
  { rtodName :: Text
  , rtodParams :: [RawTransformTypeParam]
  } deriving (Eq, Show)

data RawTransformUtility
  = RTUInputRefs
  | RTURefsNil
  | RTURefsCons
  | RTURefsHead
  | RTURefsTail
  | RTUDupRefs
  | RTUDropRefs
  | RTUReturnRefs
  | RTUResidualBox
  | RTUResidualFeedback
  deriving (Eq, Show)

data RawTransformLoopItem
  = RTLBindingPrefix Text
  | RTLResidualPrefix Text
  deriving (Eq, Show)

data RawTransformerItem
  = RTISourceDoctrine Text
  | RTISourceMode Text
  | RTISourceFragment Text
  | RTICopyDoctrine Text
  | RTIEmitObject RawTransformObjectDecl
  | RTIEmitUtility RawTransformUtility
  | RTIForIncludedGenerators Text Text [RawTransformLoopItem]
  | RTIForExcludedGenerators Text Text Text Text [RawTransformLoopItem]
  deriving (Eq, Show)

data RawTransformerDecl = RawTransformerDecl
  { rtdName :: Text
  , rtdItems :: [RawTransformerItem]
  } deriving (Eq, Show)


data RawDerivedDoctrine = RawDerivedDoctrine
  { rddName :: Text
  , rddTransformer :: Text
  , rddFragment :: Text
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
