{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
module Strat.Common.Provider
  ( ModuleProvider(..)
  , ProviderRef(..)
  , appendProviderAdapter
  , renderProviderAdapterChain
  ) where

import Data.Text (Text)
import qualified Data.Text as T


data ModuleProvider = ModuleProvider
  { mpName :: Text
  , mpInterface :: Text
  , mpDescriptor :: FilePath
  , mpAdapters :: [Text]
  }
  deriving (Eq, Ord, Read, Show)


data ProviderRef = ProviderRef
  { prProvider :: ModuleProvider
  , prValueName :: Text
  }
  deriving (Eq, Ord, Read, Show)


appendProviderAdapter :: Maybe Text -> ModuleProvider -> ModuleProvider
appendProviderAdapter mAdapter provider =
  provider
    { mpAdapters =
        case mAdapter of
          Nothing -> mpAdapters provider
          Just adapter -> mpAdapters provider <> [adapter]
    }


renderProviderAdapterChain :: ModuleProvider -> Text
renderProviderAdapterChain provider =
  case mpAdapters provider of
    [] -> ""
    adapters -> " using " <> T.intercalate " |> " adapters
