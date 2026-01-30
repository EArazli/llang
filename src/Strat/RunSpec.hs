module Strat.RunSpec
  ( RunSpec(..)
  , RunShow(..)
  ) where

import Data.Text (Text)
import Strat.Common.Rules (RewritePolicy)


data RunShow
  = ShowNormalized
  | ShowValue
  | ShowCat
  | ShowInput
  | ShowCoherence
  deriving (Eq, Ord, Show)


data RunSpec = RunSpec
  { prName :: Text
  , prDoctrine :: Text
  , prMode :: Maybe Text
  , prSurface :: Maybe Text
  , prModel :: Maybe Text
  , prMorphisms :: [Text]
  , prUses :: [Text]
  , prPolicy :: RewritePolicy
  , prFuel :: Int
  , prShowFlags :: [RunShow]
  , prExprText :: Text
  } deriving (Eq, Show)
