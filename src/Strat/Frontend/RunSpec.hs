module Strat.Frontend.RunSpec
  ( RunSpec(..)
  , RunShow(..)
  ) where

import Strat.Kernel.RewriteSystem (RewritePolicy)
import Data.Text (Text)


data RunShow
  = ShowNormalized
  | ShowValue
  | ShowCat
  | ShowInput
  deriving (Eq, Ord, Show)


data RunSpec = RunSpec
  { runDoctrine  :: Text
  , runSyntax    :: Maybe Text
  , runSurface   :: Maybe Text
  , runSurfaceSyntax :: Maybe Text
  , runModel     :: Text
  , runUses      :: [(Text, Text)]
  , runOpen      :: [Text]
  , runPolicy    :: RewritePolicy
  , runFuel      :: Int
  , runShowFlags :: [RunShow]
  , runExprText  :: Text
  }
  deriving (Eq, Show)
