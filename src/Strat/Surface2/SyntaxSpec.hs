module Strat.Surface2.SyntaxSpec
  ( SurfaceSyntaxSpec(..)
  , SurfaceNotation(..)
  , SurfaceAssoc(..)
  ) where

import Data.Text (Text)

data SurfaceSyntaxSpec = SurfaceSyntaxSpec
  { sssName :: Text
  , sssSurface :: Text
  , sssTyNotations :: [SurfaceNotation]
  , sssTmNotations :: [SurfaceNotation]
  } deriving (Eq, Show)

data SurfaceNotation
  = SAtom Text Text
  | SPrefix Text Text
  | SInfix SurfaceAssoc Int Text Text
  | SBinder Text Text Text Text
  | SApp Text
  | STuple Text Text
  deriving (Eq, Show)

data SurfaceAssoc = SLeft | SRight | SNon
  deriving (Eq, Show)
