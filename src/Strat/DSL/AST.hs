{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.AST
  ( RawDecl(..)
  , RawFile(..)
  , RawModelItem(..)
  , RawDefault(..)
  , RawModelClause(..)
  , RawRunShow(..)
  , RawRun(..)
  , RawRunSpec(..)
  , RawNamedRun(..)
  , RawDoctrineTemplate(..)
  , RawDoctrineInstantiate(..)
  , RawTerm(..)
  , RawNamedTerm(..)
  , RawPolyMorphism(..)
  , RawPolyMorphismItem(..)
  , RawPolyModeMap(..)
  , RawPolyTypeMap(..)
  , RawPolyGenMap(..)
  ) where

import Data.Text (Text)
import Strat.Model.Spec (MExpr)
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
  | DeclSurface Text SurfaceSpec
  | DeclModel Text Text [RawModelItem]
  | DeclMorphism RawPolyMorphism
  | DeclImplements Text Text Text
  | DeclRunSpec Text RawRunSpec
  | DeclRun RawNamedRun
  | DeclTerm RawNamedTerm
  deriving (Eq, Show)

newtype RawFile = RawFile [RawDecl]
  deriving (Eq, Show)


data RawModelItem
  = RMDefault RawDefault
  | RMOp RawModelClause
  deriving (Eq, Show)

data RawDefault
  = RawDefaultSymbolic
  | RawDefaultError Text
  deriving (Eq, Show)

data RawModelClause = RawModelClause
  { rmcOp :: Text
  , rmcArgs :: [Text]
  , rmcExpr :: MExpr
  } deriving (Eq, Show)


data RawRunShow
  = RawShowNormalized
  | RawShowValue
  | RawShowCat
  | RawShowInput
  | RawShowCoherence
  deriving (Eq, Ord, Show)


data RawRun = RawRun
  { rrDoctrine :: Maybe Text
  , rrMode :: Maybe Text
  , rrSurface :: Maybe Text
  , rrModel :: Maybe Text
  , rrMorphisms :: [Text]
  , rrUses :: [Text]
  , rrPolicy :: Maybe Text
  , rrFuel :: Maybe Int
  , rrShowFlags :: [RawRunShow]
  , rrExprText :: Text
  } deriving (Eq, Show)

newtype RawRunSpec = RawRunSpec
  { rrsRun :: RawRun
  } deriving (Eq, Show)

data RawNamedRun = RawNamedRun
  { rnrName :: Text
  , rnrUsing :: Maybe Text
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
  , rpmPolicy :: Maybe Text
  , rpmFuel :: Maybe Int
  } deriving (Eq, Show)


data RawPolyMorphismItem
  = RPMMode RawPolyModeMap
  | RPMType RawPolyTypeMap
  | RPMGen RawPolyGenMap
  | RPMCoercion
  deriving (Eq, Show)

data RawPolyModeMap = RawPolyModeMap
  { rpmmSrc :: Text
  , rpmmTgt :: Text
  } deriving (Eq, Show)


data RawPolyTypeMap = RawPolyTypeMap
  { rpmtSrcType :: Text
  , rpmtParams :: [PolyAST.RawTyVarDecl]
  , rpmtSrcMode :: Text
  , rpmtTgtType :: PolyAST.RawPolyTypeExpr
  , rpmtTgtMode :: Text
  } deriving (Eq, Show)


data RawPolyGenMap = RawPolyGenMap
  { rpmgSrcGen :: Text
  , rpmgMode :: Text
  , rpmgRhs :: PolyAST.RawDiagExpr
  } deriving (Eq, Show)
