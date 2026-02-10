{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypePretty
  ( renderType
  , renderTypeArg
  , renderIxTerm
  , renderTypeRef
  , renderTypeName
  , renderMode
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.TypeExpr
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..))


renderMode :: ModeName -> Text
renderMode (ModeName t) = t

renderType :: TypeExpr -> Text
renderType ty =
  case ty of
    TVar v -> tvName v <> "@" <> renderMode (tvMode v)
    TCon ref [] -> renderTypeRef ref
    TCon ref args ->
      renderTypeRef ref <> "(" <> T.intercalate ", " (map renderTypeArg args) <> ")"
    TMod me inner ->
      renderModExpr me <> "(" <> renderType inner <> ")"

renderTypeArg :: TypeArg -> Text
renderTypeArg arg =
  case arg of
    TAType ty -> renderType ty
    TAIndex ix -> renderIxTerm ix

renderIxTerm :: IxTerm -> Text
renderIxTerm ix =
  case ix of
    IXVar v -> ixvName v
    IXBound i -> "^" <> T.pack (show i)
    IXFun name [] -> renderIxFunName name
    IXFun name args ->
      renderIxFunName name <> "(" <> T.intercalate ", " (map renderIxTerm args) <> ")"

renderIxFunName :: IxFunName -> Text
renderIxFunName (IxFunName name) = name

renderModExpr :: ModExpr -> Text
renderModExpr me =
  case reverse (mePath me) of
    [] -> "id@" <> renderMode (meSrc me)
    names -> T.intercalate "." (map renderModName names)

renderModName :: ModName -> Text
renderModName (ModName n) = n

renderTypeRef :: TypeRef -> Text
renderTypeRef ref =
  renderMode (trMode ref) <> "." <> renderTypeName (trName ref)

renderTypeName :: TypeName -> Text
renderTypeName (TypeName n) = n
