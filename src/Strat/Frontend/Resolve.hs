{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Resolve
  ( resolveOpText
  , resolveSortText
  ) where

import Strat.Kernel.Signature (Signature(..))
import Strat.Kernel.Syntax (OpName(..), SortName(..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M

resolveOpText :: Signature -> [Text] -> Text -> Either Text OpName
resolveOpText sig opens name
  | T.isInfixOf "." name =
      if M.member (OpName name) (sigOps sig)
        then Right (OpName name)
        else Left ("Unknown op: " <> name)
  | M.member (OpName name) (sigOps sig) = Right (OpName name)
  | otherwise =
      case candidates of
        [] -> Left ("Unknown op: " <> name)
        [op] -> Right op
        _ -> Left ("Ambiguous op name: " <> name)
  where
    candidates = [ OpName (ns <> "." <> name) | ns <- opens, M.member (OpName (ns <> "." <> name)) (sigOps sig) ]

resolveSortText :: Signature -> [Text] -> Text -> Either Text SortName
resolveSortText sig opens name
  | T.isInfixOf "." name =
      if M.member (SortName name) (sigSortCtors sig)
        then Right (SortName name)
        else Left ("Unknown sort: " <> name)
  | M.member (SortName name) (sigSortCtors sig) = Right (SortName name)
  | otherwise =
      case candidates of
        [] -> Left ("Unknown sort: " <> name)
        [sn] -> Right sn
        _ -> Left ("Ambiguous sort name: " <> name)
  where
    candidates = [ SortName (ns <> "." <> name) | ns <- opens, M.member (SortName (ns <> "." <> name)) (sigSortCtors sig) ]
