{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
module Strat.Common.ModuleRef
  ( ModuleValueRef(..)
  , appendModuleValueRefAdapter
  , renderModuleValueRefAdapterChain
  ) where

import Data.Text (Text)
import qualified Data.Text as T


data ModuleValueRef = ModuleValueRef
  { mvrModule :: Text
  , mvrValueName :: Text
  , mvrAdapters :: [Text]
  }
  deriving (Eq, Ord, Read, Show)


appendModuleValueRefAdapter :: Maybe Text -> ModuleValueRef -> ModuleValueRef
appendModuleValueRefAdapter mAdapter ref =
  ref
    { mvrAdapters =
        case mAdapter of
          Nothing -> mvrAdapters ref
          Just adapter -> mvrAdapters ref <> [adapter]
    }


renderModuleValueRefAdapterChain :: ModuleValueRef -> Text
renderModuleValueRefAdapterChain ref =
  case mvrAdapters ref of
    [] -> ""
    adapters -> " using " <> T.intercalate " |> " adapters
