{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ObjPretty
  ( renderType
  , renderTypeArg
  , renderTmTerm
  , renderTypeRef
  , renderTypeName
  , renderMode
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.Obj
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..))


renderMode :: ModeName -> Text
renderMode (ModeName t) = t

renderType :: Obj -> Text
renderType ty =
  case ty of
    OVar v -> ovName v <> "@" <> renderMode (ovMode v)
    OCon ref [] -> renderTypeRef ref
    OCon ref args ->
      renderTypeRef ref <> "(" <> T.intercalate ", " (map renderTypeArg args) <> ")"
    OMod me inner ->
      renderModExpr me <> "(" <> renderType inner <> ")"
    OLift me inner ->
      "lift[" <> renderModExpr me <> "](" <> renderType inner <> ")"

renderTypeArg :: ObjArg -> Text
renderTypeArg arg =
  case arg of
    OAObj ty -> renderType ty
    OATm tm -> renderTmTerm tm

renderTmTerm :: TermDiagram -> Text
renderTmTerm _ = "<tm>"

renderModExpr :: ModExpr -> Text
renderModExpr me =
  case reverse (mePath me) of
    [] -> "id@" <> renderMode (meSrc me)
    names -> T.intercalate "." (map renderModName names)

renderModName :: ModName -> Text
renderModName (ModName n) = n

renderTypeRef :: ObjRef -> Text
renderTypeRef ref =
  renderMode (orMode ref) <> "." <> renderTypeName (orName ref)

renderTypeName :: ObjName -> Text
renderTypeName (ObjName n) = n
