{-# LANGUAGE OverloadedStrings #-}
module Strat.Pipeline
  ( OrderKey(..)
  , NamingPolicy(..)
  , FoliationPolicy(..)
  , defaultFoliationPolicy
  , ValueExtractorSpec(..)
  , Phase(..)
  , Pipeline(..)
  , Run(..)
  , DerivedDoctrine(..)
  ) where

import Data.Text (Text)
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy)


data OrderKey
  = StableEdgeId
  deriving (Eq, Ord, Show)


data NamingPolicy
  = BoundaryLabelsFirst
  deriving (Eq, Ord, Show)


data FoliationPolicy = FoliationPolicy
  { fpOrderKey :: OrderKey
  , fpNaming :: NamingPolicy
  , fpReserved :: S.Set Text
  }
  deriving (Eq, Show)


defaultFoliationPolicy :: FoliationPolicy
defaultFoliationPolicy =
  FoliationPolicy
    { fpOrderKey = StableEdgeId
    , fpNaming = BoundaryLabelsFirst
    , fpReserved = S.empty
    }


data ValueExtractorSpec
  = ExtractDoc { veStdout :: Bool }
  | ExtractFileTree { veRoot :: FilePath }
  deriving (Eq, Show)


data Phase
  = ApplyMorph Text
  | Normalize RewritePolicy Int
  | ExtractFoliation { target :: Text, policy :: Maybe FoliationPolicy }
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
  = DerivedFoliated
      { ddName :: Text
      , ddBase :: Text
      , ddMode :: Text
      , ddDefaultPolicy :: FoliationPolicy
      }
  deriving (Eq, Show)
