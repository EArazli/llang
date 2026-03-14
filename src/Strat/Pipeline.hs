{-# LANGUAGE OverloadedStrings #-}
module Strat.Pipeline
  ( FragmentDecl(..)
  , BackendSpec(..)
  , BundleItem(..)
  , BuildProductKind(..)
  , Phase(..)
  , Pipeline(..)
  , DerivedDoctrine(..)
  , phaseTransition
  ) where

import Data.Text (Text)
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy)
import Strat.Poly.Names (GenName)


data FragmentDecl = FragmentDecl
  { frName :: Text
  , frBase :: Text
  , frMode :: Text
  , frIncludedGens :: S.Set GenName
  , frCrossBinders :: Bool
  , frCrossBoxes :: Bool
  , frCrossFeedback :: Bool
  }
  deriving (Eq, Read, Show)

data BackendSpec = BackendSpec
  { bsName :: Text
  , bsStdout :: Maybe Bool
  , bsRoot :: Maybe FilePath
  }
  deriving (Eq, Read, Show)


data BundleItem = BundleItem
  { biSource :: Text
  , biTarget :: Text
  }
  deriving (Eq, Read, Show)

data BuildProductKind
  = PKModule
  | PKBundle
  | PKDiagram
  | PKHost
  deriving (Eq, Ord, Read, Show)


data Phase
  = ApplyMorph Text
  | Normalize RewritePolicy Int
  | QuoteInto { fragment :: Text, target :: Text }
  | LinkModule Text
  | BundleAll
  | BundleExports [BundleItem]
  | ProjectExport Text
  | EmitVia BackendSpec
  deriving (Eq, Read, Show)


data Pipeline = Pipeline
  { plName :: Text
  , plPhases :: [Phase]
  }
  deriving (Eq, Read, Show)


phaseTransition :: Phase -> BuildProductKind -> Either Text BuildProductKind
phaseTransition phase kind =
  case phase of
    ApplyMorph _ ->
      case kind of
        PKModule -> Right PKModule
        PKBundle -> Right PKBundle
        PKDiagram -> Right PKDiagram
        PKHost -> Left "apply expects a module, bundle, or diagram"
    Normalize _ _ ->
      case kind of
        PKModule -> Right PKModule
        PKBundle -> Right PKBundle
        PKDiagram -> Right PKDiagram
        PKHost -> Left "normalize expects a module, bundle, or diagram"
    QuoteInto {} ->
      case kind of
        PKModule -> Right PKModule
        PKBundle -> Right PKBundle
        PKDiagram -> Right PKDiagram
        PKHost -> Left "quote expects a module, bundle, or diagram"
    LinkModule _ ->
      case kind of
        PKModule -> Right PKModule
        _ -> Left "link expects a module"
    BundleAll ->
      case kind of
        PKModule -> Right PKBundle
        _ -> Left "bundle expects a module"
    BundleExports _ ->
      case kind of
        PKModule -> Right PKBundle
        _ -> Left "bundle expects a module"
    ProjectExport _ ->
      case kind of
        PKModule -> Right PKDiagram
        PKBundle -> Right PKDiagram
        PKDiagram -> Left "project export expects a module or bundle"
        PKHost -> Left "project export expects a module or bundle"
    EmitVia _ ->
      case kind of
        PKModule -> Right PKHost
        PKBundle -> Right PKHost
        PKDiagram -> Right PKHost
        PKHost -> Left "emit via expects a module, bundle, or diagram"


data DerivedDoctrine
  = DerivedReflectQuotation
      { ddName :: Text
      , ddBase :: Text
      , ddMode :: Text
      }
  deriving (Eq, Read, Show)
