{-# LANGUAGE OverloadedStrings #-}
module Strat.Model.Spec
  ( ModelSpec(..)
  , ModelBackend(..)
  , FoldSpec(..)
  , OpClause(..)
  , DefaultBehavior(..)
  , MExpr(..)
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S


data ModelBackend
  = BackendAlgebra
  | BackendFold
  deriving (Eq, Ord, Show)

data FoldSpec = FoldSpec
  { fsIndent   :: Text
  , fsReserved :: S.Set Text
  , fsHooks    :: M.Map Text OpClause
  }
  deriving (Eq, Show)

data ModelSpec = ModelSpec
  { msName    :: Text
  , msOps     :: [OpClause]
  , msDefault :: DefaultBehavior
  , msBackend :: ModelBackend
  , msFold    :: Maybe FoldSpec
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
