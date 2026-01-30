{-# LANGUAGE OverloadedStrings #-}
module Strat.Model.Spec
  ( ModelSpec(..)
  , OpClause(..)
  , DefaultBehavior(..)
  , MExpr(..)
  ) where

import Data.Text (Text)


data ModelSpec = ModelSpec
  { msName    :: Text
  , msClauses :: [OpClause]
  , msDefault :: DefaultBehavior
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
