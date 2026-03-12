{-# LANGUAGE OverloadedStrings #-}
module Strat.Pipeline
  ( FragmentDecl(..)
  , ValueExtractorSpec(..)
  , Phase(..)
  , Pipeline(..)
  , Run(..)
  , DerivedDoctrine(..)
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
  deriving (Eq, Show)

data ValueExtractorSpec
  = ExtractDoc { veStdout :: Bool }
  | ExtractFileTree { veRoot :: FilePath }
  deriving (Eq, Show)


data Phase
  = ApplyMorph Text
  | Normalize RewritePolicy Int
  | QuoteInto { fragment :: Text, target :: Text }
  | ExtractValue { doctrine :: Text, extractor :: ValueExtractorSpec }
  | ExtractDiagramPretty
  deriving (Eq, Show)


data Pipeline = Pipeline
  { plName :: Text
  , plPhases :: [Phase]
  }
  deriving (Eq, Show)


data Run = Run
  { runName :: Text
  , runUses :: [Text]
  , runPipeline :: Text
  , runDoctrine :: Text
  , runMode :: Maybe Text
  , runSurface :: Maybe Text
  , runExprText :: Text
  }
  deriving (Eq, Show)


data DerivedDoctrine
  = DerivedReflectQuotation
      { ddName :: Text
      , ddBase :: Text
      , ddMode :: Text
      }
  deriving (Eq, Show)
