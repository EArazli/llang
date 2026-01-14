{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Resolve
  ( resolveOpText
  ) where

import Strat.Kernel.Signature (Signature(..))
import Strat.Kernel.Syntax (OpName(..))
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
