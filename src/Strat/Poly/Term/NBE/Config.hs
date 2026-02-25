{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.NBE.Config
  ( NbeConfig(..)
  , defaultNbeConfig
  ) where

import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj (ObjName(..))

data NbeConfig = NbeConfig
  { nbeLamGen :: GenName
  , nbeAppGen :: GenName
  , nbeArrTyCon :: ObjName
  , nbeAllowEta :: Bool
  } deriving (Eq, Show)

defaultNbeConfig :: NbeConfig
defaultNbeConfig =
  NbeConfig
    { nbeLamGen = GenName "lam"
    , nbeAppGen = GenName "app"
    , nbeArrTyCon = ObjName "Arr"
    , nbeAllowEta = True
    }
