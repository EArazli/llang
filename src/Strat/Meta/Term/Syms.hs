module Strat.Meta.Term.Syms where

import Data.Text (Text)
import qualified Data.Set as S

class SymRenamable t where
  -- rename symbols in a term
  renameSyms :: (Text -> Text) -> t -> t

  -- collect symbol names appearing in a term (for validation)
  syms :: t -> S.Set Text
