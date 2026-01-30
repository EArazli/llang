{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface
  ( PolySurfaceDef(..)
  , SurfaceSpec(..)
  , LexerSpec(..)
  , ExprSpec(..)
  , ExprRule(..)
  , InfixAssoc(..)
  , InfixRule(..)
  , AppRule(..)
  , PatItem(..)
  , Action(..)
  , ElabRule(..)
  , TemplateExpr(..)
  , SurfaceAST(..)
  , elabPolySurfaceDecl
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..), mtModes)
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.Surface.Spec


elabPolySurfaceDecl :: Text -> Doctrine -> SurfaceSpec -> Either Text PolySurfaceDef
elabPolySurfaceDecl name doc spec = do
  let mode = ModeName (ssMode spec)
  if mode `S.member` mtModes (dModes doc)
    then validateSpec spec >> pure PolySurfaceDef
      { psName = name
      , psDoctrine = ssDoctrine spec
      , psMode = mode
      , psSpec = spec { ssName = name }
      }
    else Left "surface: unknown mode"

validateSpec :: SurfaceSpec -> Either Text ()
validateSpec spec =
  do
    require "lexer" (ssLexer spec)
    require "expr" (ssExprSpec spec)
    if M.null (ssElabRules spec)
      then Left "surface: elaborate block is required"
      else Right ()
  where
    require label field =
      case field of
        Nothing -> Left ("surface: missing " <> label)
        Just _ -> Right ()
