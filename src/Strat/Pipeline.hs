{-# LANGUAGE OverloadedStrings #-}
module Strat.Pipeline
  ( OrderKey(..)
  , NamingPolicy(..)
  , FragmentRole(..)
  , FragmentProduct(..)
  , FragmentDecl(..)
  , QuotePolicy(..)
  , defaultQuotePolicy
  , TransformerKind(..)
  , ValueExtractorSpec(..)
  , Phase(..)
  , Pipeline(..)
  , Run(..)
  , DerivedDoctrine(..)
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy)
import Strat.Poly.Names (GenName)


data OrderKey
  = StableEdgeId
  deriving (Eq, Ord, Show)


data NamingPolicy
  = BoundaryLabelsFirst
  deriving (Eq, Ord, Show)

data FragmentRole
  = FragShare
  | FragAlias
  | FragDuplicate
  | FragDiscard
  | FragResidual
  deriving (Eq, Ord, Show)

data FragmentProduct = FragmentProduct
  { fpPairCtor :: GenName
  , fpProjLeft :: GenName
  , fpProjRight :: GenName
  }
  deriving (Eq, Ord, Show)

data FragmentDecl = FragmentDecl
  { frName :: Text
  , frBase :: Text
  , frMode :: Text
  , frGenRoles :: M.Map GenName FragmentRole
  , frProducts :: [FragmentProduct]
  , frRecurseBinders :: Bool
  , frRecurseBoxes :: Bool
  , frRecurseFeedback :: Bool
  }
  deriving (Eq, Show)

data QuotePolicy = QuotePolicy
  { qpOrderKey :: OrderKey
  , qpNaming :: NamingPolicy
  , qpReserved :: S.Set Text
  }
  deriving (Eq, Show)


defaultQuotePolicy :: QuotePolicy
defaultQuotePolicy =
  QuotePolicy
    { qpOrderKey = StableEdgeId
    , qpNaming = BoundaryLabelsFirst
    , qpReserved = S.empty
    }


data TransformerKind
  = TkLetGraph
  deriving (Eq, Ord, Show)


data ValueExtractorSpec
  = ExtractDoc { veStdout :: Bool }
  | ExtractFileTree { veRoot :: FilePath }
  deriving (Eq, Show)


data Phase
  = ApplyMorph Text
  | Normalize RewritePolicy Int
  | QuoteInto { target :: Text, policy :: Maybe QuotePolicy }
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
  = DerivedTransform
      { ddName :: Text
      , ddBase :: Text
      , ddMode :: Text
      , ddFragment :: Text
      , ddKind :: TransformerKind
      , ddDefaultQuotePolicy :: QuotePolicy
      }
  deriving (Eq, Show)
