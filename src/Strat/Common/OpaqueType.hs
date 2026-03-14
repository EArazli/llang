{-# LANGUAGE OverloadedStrings #-}
module Strat.Common.OpaqueType
  ( opaqueInterfaceTypeName
  , opaqueModuleDataTypeName
  , opaqueModuleDataProviderInterface
  , opaqueModuleDataDescriptorPrefix
  , opaqueModuleDataProviderDescriptor
  , opaqueModuleDataProviderDescriptorWithPrefix
  , isOpaqueTypeName
  ) where

import Data.Text (Text)
import qualified Data.Text as T


opaqueInterfaceTypeName :: Text -> Text
opaqueInterfaceTypeName name =
  "iface::" <> name


opaqueModuleDataTypeName :: Text -> Text
opaqueModuleDataTypeName name =
  "module_data::" <> name


opaqueModuleDataProviderInterface :: Text
opaqueModuleDataProviderInterface =
  "module_data"


opaqueModuleDataDescriptorPrefix :: Text
opaqueModuleDataDescriptorPrefix =
  "module-data"


opaqueModuleDataProviderDescriptor :: Text -> FilePath
opaqueModuleDataProviderDescriptor name =
  opaqueModuleDataProviderDescriptorWithPrefix opaqueModuleDataDescriptorPrefix name


opaqueModuleDataProviderDescriptorWithPrefix :: Text -> Text -> FilePath
opaqueModuleDataProviderDescriptorWithPrefix prefix name =
  T.unpack (prefix <> ":" <> name)


isOpaqueTypeName :: Text -> Bool
isOpaqueTypeName name =
  any (`T.isPrefixOf` name) prefixes
  where
    prefixes =
      [ "iface::"
      , "module_data::"
      ]
