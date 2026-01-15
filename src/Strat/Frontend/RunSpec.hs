module Strat.Frontend.RunSpec
  ( RunSpec(..)
  , RunShow(..)
  ) where

import Strat.Kernel.DSL.AST (RawExpr)
import Strat.Kernel.RewriteSystem (RewritePolicy)
import Data.Text (Text)


data RunShow
  = ShowNormalized
  | ShowValue
  | ShowCat
  | ShowInput
  deriving (Eq, Ord, Show)


data RunSpec = RunSpec
  { runDoctrine  :: RawExpr
  , runSyntax    :: Maybe Text
  , runCoreSyntax :: Maybe Text
  , runSurface   :: Maybe Text
  , runSurfaceSyntax :: Maybe Text
  , runInterface :: Maybe Text
  , runModel     :: Text
  , runOpen      :: [Text]
  , runPolicy    :: RewritePolicy
  , runFuel      :: Int
  , runShowFlags :: [RunShow]
  , runExprText  :: Text
  }
  deriving (Eq, Show)
