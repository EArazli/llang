module Strat.Meta.Term.Syms where

import Data.Text (Text)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

class SymRenamable t where
  -- rename symbols in a term
  renameSyms :: (Text -> Text) -> t -> t

  -- collect symbol names appearing in a term (for validation)
  syms :: t -> S.Set Text

  -- collect arities (number of arguments) per symbol name
  symArities :: t -> M.Map Text (S.Set Int)
