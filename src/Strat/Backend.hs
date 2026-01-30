{-# LANGUAGE OverloadedStrings #-}
module Strat.Backend
  ( Value(..)
  , SortValue(..)
  , RuntimeError(..)
  ) where

import Data.Text (Text)


data Value
  = VAtom Text
  | VList [Value]
  | VInt Int
  | VString Text
  | VBool Bool
  deriving (Eq, Show)

newtype SortValue = SortValue Text
  deriving (Eq, Show)

newtype RuntimeError = RuntimeError Text
  deriving (Eq, Show)
