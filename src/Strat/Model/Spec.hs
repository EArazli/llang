{-# LANGUAGE OverloadedStrings #-}
module Strat.Model.Spec
  ( ModelSpec(..)
  , ModelBackend(..)
  , OpClause(..)
  , DefaultBehavior(..)
  , MExpr(..)
  ) where

import Data.Text (Text)


data ModelBackend
  = BackendAlgebra
  | BackendFoldSSA
  deriving (Eq, Ord, Show)

data ModelSpec = ModelSpec
  { msName    :: Text
  , msClauses :: [OpClause]
  , msDefault :: DefaultBehavior
  , msBackend :: ModelBackend
  }
  deriving (Eq, Show)


data OpClause = OpClause
  { ocOp   :: Text
  , ocArgs :: [Text]
  , ocExpr :: MExpr
  }
  deriving (Eq, Show)


data DefaultBehavior
  = DefaultSymbolic
  | DefaultError Text
  deriving (Eq, Show)


data MExpr
  = MVar Text
  | MInt Int
  | MString Text
  | MBool Bool
  | MList [MExpr]
  | MIf MExpr MExpr MExpr
  | MBinOp Text MExpr MExpr
  deriving (Eq, Show)
