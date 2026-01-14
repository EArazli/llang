{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Env
  ( ModuleEnv(..)
  , emptyEnv
  , mergeEnv
  ) where

import Strat.Kernel.DoctrineExpr (DocExpr)
import Strat.Kernel.Presentation (Presentation)
import Strat.Syntax.Spec (SyntaxSpec)
import Strat.Model.Spec (ModelSpec)
import Strat.Frontend.RunSpec (RunSpec)
import Data.Text (Text)
import qualified Data.Map.Strict as M


data ModuleEnv = ModuleEnv
  { meDoctrines     :: M.Map Text DocExpr
  , mePresentations :: M.Map Text Presentation
  , meSyntaxes      :: M.Map Text SyntaxSpec
  , meModels        :: M.Map Text ModelSpec
  , meRun           :: Maybe RunSpec
  }
  deriving (Eq, Show)

emptyEnv :: ModuleEnv
emptyEnv = ModuleEnv
  { meDoctrines = M.empty
  , mePresentations = M.empty
  , meSyntaxes = M.empty
  , meModels = M.empty
  , meRun = Nothing
  }

mergeEnv :: ModuleEnv -> ModuleEnv -> Either Text ModuleEnv
mergeEnv a b = do
  docs <- mergeMap "doctrine" meDoctrines
  pres <- mergeMap "presentation" mePresentations
  syns <- mergeMap "syntax" meSyntaxes
  mods <- mergeMap "model" meModels
  run <- mergeRun (meRun a) (meRun b)
  pure ModuleEnv
    { meDoctrines = docs
    , mePresentations = pres
    , meSyntaxes = syns
    , meModels = mods
    , meRun = run
    }
  where
    mergeMap label f = mergeNamed label (f a) (f b)

mergeNamed :: Text -> M.Map Text v -> M.Map Text v -> Either Text (M.Map Text v)
mergeNamed label left right =
  case dupKeys of
    [] -> Right (M.union left right)
    (k:_) -> Left ("Duplicate " <> label <> " name: " <> k)
  where
    dupKeys = M.keys (M.intersection left right)

mergeRun :: Maybe RunSpec -> Maybe RunSpec -> Either Text (Maybe RunSpec)
mergeRun Nothing r = Right r
mergeRun r Nothing = Right r
mergeRun (Just _) (Just _) = Left "Multiple run blocks found"
