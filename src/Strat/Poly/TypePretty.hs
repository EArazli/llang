{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypePretty
  ( renderType
  , renderTypeRef
  , renderTypeName
  , renderMode
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.TypeExpr
import Strat.Poly.ModeTheory (ModeName(..))


renderMode :: ModeName -> Text
renderMode (ModeName t) = t

renderType :: TypeExpr -> Text
renderType ty =
  case ty of
    TVar v -> tvName v <> "@" <> renderMode (tvMode v)
    TCon ref [] -> renderTypeRef ref
    TCon ref args ->
      renderTypeRef ref <> "(" <> T.intercalate ", " (map renderType args) <> ")"

renderTypeRef :: TypeRef -> Text
renderTypeRef ref =
  renderMode (trMode ref) <> "." <> renderTypeName (trName ref)

renderTypeName :: TypeName -> Text
renderTypeName (TypeName n) = n
