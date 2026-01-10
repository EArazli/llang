module Strat.Doctrine.Stub where

import Strat.Meta.Presentation

-- Eventually: richer doctrine API. For now: doctrine = presentation.
newtype Doctrine t = Doctrine { doctrinePres :: Presentation t }
