{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface
  ( PolySurfaceDef(..)
  , SurfaceSpec(..)
  , LexerSpec(..)
  , ExprSpec(..)
  , ExprRule(..)
  , BinderDecl(..)
  , InfixAssoc(..)
  , InfixRule(..)
  , AppRule(..)
  , PatItem(..)
  , Action(..)
  , GenRef(..)
  , TemplateExpr(..)
  , TemplateBinderArg(..)
  , SurfaceParamKind(..)
  , elabPolySurfaceDecl
  ) where

import Data.List (intercalate)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory (ModeName(..), mtModes)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Surface.Spec


data SurfaceParamKind
  = SPKIdent
  | SPKLiteral
  | SPKType
  deriving (Eq, Show)

elabPolySurfaceDecl :: Text -> Doctrine -> Maybe Doctrine -> SurfaceSpec -> Either Text PolySurfaceDef
elabPolySurfaceDecl name doc mBaseDoc spec = do
  let mode = ModeName (ssMode spec)
  if M.member mode (mtModes (dModes doc))
    then Right ()
    else Left "surface: unknown mode"
  case (ssBaseDoctrine spec, mBaseDoc) of
    (Just _, Nothing) -> Left "surface: unknown base doctrine"
    _ -> Right ()
  validateSpec mode spec
  case mBaseDoc of
    Nothing -> pure ()
    Just docBase -> do
      if M.member mode (mtModes (dModes docBase))
        then Right ()
        else Left "surface: base doctrine is missing surface mode"
      ensureBaseInclusion mode docBase doc
  pure
    PolySurfaceDef
      { psName = name
      , psDoctrine = ssDoctrine spec
      , psBaseDoctrine = ssBaseDoctrine spec
      , psMode = mode
      , psSpec = spec { ssName = name }
      }

validateSpec :: ModeName -> SurfaceSpec -> Either Text ()
validateSpec _mode spec = do
  _ <- require "lexer" (ssLexer spec)
  expr <- require "expr" (ssExprSpec spec)
  mapM_ validateExprRule (esAtoms expr)
  mapM_ validateExprRule (esPrefixes expr)
  mapM_ validateInfixRule (esInfixes expr)
  case esApp expr of
    Nothing -> pure ()
    Just app -> validateAppRule app
  where
    require label field =
      case field of
        Nothing -> Left ("surface: missing " <> label)
        Just x -> Right x

validateExprRule :: ExprRule -> Either Text ()
validateExprRule rule = do
  info <- patternInfo (erPattern rule)
  validateAction info (erAction rule)
  validateBinder info (erBinder rule)

validateInfixRule :: InfixRule -> Either Text ()
validateInfixRule rule =
  validateAction emptyRuleInfo { riExprCount = 2 } (irAction rule)

validateAppRule :: AppRule -> Either Text ()
validateAppRule (AppRule act) =
  validateAction emptyRuleInfo { riExprCount = 2 } act

ensureBaseInclusion :: ModeName -> Doctrine -> Doctrine -> Either Text ()
ensureBaseInclusion mode docBase docSurface =
  if S.isSubsetOf baseGens surfaceGens
    then Right ()
    else
      let missing = S.toList (S.difference baseGens surfaceGens)
          render (GenName g) = T.unpack g
          msg = "surface: base generators are not included in surface doctrine for mode "
                <> T.unpack (renderMode mode)
                <> ": "
                <> intercalate ", " (map render missing)
       in Left (T.pack msg)
  where
    baseGens = maybe S.empty M.keysSet (M.lookup mode (dGens docBase))
    surfaceGens = maybe S.empty M.keysSet (M.lookup mode (dGens docSurface))
    renderMode (ModeName m) = m


data RuleInfo = RuleInfo
  { riNamedKinds :: M.Map Text SurfaceParamKind
  , riExprCount :: Int
  } deriving (Eq, Show)

emptyRuleInfo :: RuleInfo
emptyRuleInfo = RuleInfo
  { riNamedKinds = M.empty
  , riExprCount = 0
  }

patternInfo :: [PatItem] -> Either Text RuleInfo
patternInfo = foldl step (Right emptyRuleInfo)
  where
    step acc pat = do
      info <- acc
      case pat of
        PatLit _ -> Right info
        PatExpr -> Right info { riExprCount = riExprCount info + 1 }
        PatIdent mCap -> insertCapture info mCap SPKIdent
        PatType mCap -> insertCapture info mCap SPKType
        PatInt mCap -> insertCapture info mCap SPKLiteral
        PatString mCap -> insertCapture info mCap SPKLiteral
        PatBool mCap -> insertCapture info mCap SPKLiteral

insertCapture :: RuleInfo -> Maybe Text -> SurfaceParamKind -> Either Text RuleInfo
insertCapture info mCap kind =
  case mCap of
    Nothing -> Right info
    Just cap ->
      if M.member cap (riNamedKinds info)
        then Left ("surface: duplicate capture name: " <> cap)
        else Right info { riNamedKinds = M.insert cap kind (riNamedKinds info) }

validateBinder :: RuleInfo -> Maybe BinderDecl -> Either Text ()
validateBinder _ Nothing = Right ()
validateBinder info (Just binder) =
  case binder of
    BindIn varCap tyCap bodyHole -> do
      requireIdentCap info varCap
      requireTypeCap info tyCap
      requireExprHole info bodyHole "body"
    BindLet varCap valueHole bodyHole -> do
      requireIdentCap info varCap
      requireExprHole info valueHole "value"
      requireExprHole info bodyHole "body"

requireIdentCap :: RuleInfo -> Text -> Either Text ()
requireIdentCap info cap =
  case M.lookup cap (riNamedKinds info) of
    Just SPKIdent -> Right ()
    _ -> Left ("surface: binder capture is not an ident(...) capture: " <> cap)

requireTypeCap :: RuleInfo -> Text -> Either Text ()
requireTypeCap info cap =
  case M.lookup cap (riNamedKinds info) of
    Just SPKType -> Right ()
    _ -> Left ("surface: binder capture is not a <type>(...) capture: " <> cap)

requireExprHole :: RuleInfo -> Int -> Text -> Either Text ()
requireExprHole info hole label =
  if hole >= 1 && hole <= riExprCount info
    then Right ()
    else Left ("surface: binder " <> label <> " hole term-context position out of range")

validateAction :: RuleInfo -> Action -> Either Text ()
validateAction info act =
  case act of
    ActionExpr ->
      if riExprCount info == 1
        then Right ()
        else Left "surface: <expr> action expects exactly one expression capture"
    ActionTemplate templ -> validateTemplate info templ

validateTemplate :: RuleInfo -> TemplateExpr -> Either Text ()
validateTemplate info templ =
  case templ of
    TId _ -> Right ()
    TTermRef _ -> Right ()
    TBox _ inner -> validateTemplate info inner
    TLoop inner -> validateTemplate info inner
    TComp a b -> validateTemplate info a >> validateTemplate info b
    TTensor a b -> validateTemplate info a >> validateTemplate info b
    THole n ->
      if n >= 1 && n <= riExprCount info
        then Right ()
        else Left "surface: template hole out of range"
    TVar cap -> requireNamedIdent info cap
    TGen ref _ mAttrArgs mBinderArgs -> do
      case ref of
        GenLit _ -> Right ()
        GenHole cap -> requireNamedIdent info cap
      mapM_ (validateTemplateAttrArg info) (maybe [] id mAttrArgs)
      mapM_ (validateTemplateBinderArg info) (maybe [] id mBinderArgs)

validateTemplateBinderArg :: RuleInfo -> TemplateBinderArg -> Either Text ()
validateTemplateBinderArg info arg =
  case arg of
    TBAExpr expr -> validateTemplate info expr
    TBAMeta _ -> Right ()

validateTemplateAttrArg :: RuleInfo -> TemplateAttrArg -> Either Text ()
validateTemplateAttrArg info arg =
  case arg of
    TAName _ term -> validateAttrTemplate info term
    TAPos term -> validateAttrTemplate info term

validateAttrTemplate :: RuleInfo -> AttrTemplate -> Either Text ()
validateAttrTemplate info term =
  case term of
    ATLIT _ -> Right ()
    ATHole cap -> requireNamedLiteralLike info cap
    ATVar _ -> Right ()

requireNamedIdent :: RuleInfo -> Text -> Either Text ()
requireNamedIdent info cap =
  case M.lookup cap (riNamedKinds info) of
    Just SPKIdent -> Right ()
    _ -> Left ("surface: template capture requires ident(...): " <> cap)

requireNamedLiteralLike :: RuleInfo -> Text -> Either Text ()
requireNamedLiteralLike info cap =
  case M.lookup cap (riNamedKinds info) of
    Just SPKIdent -> Right ()
    Just SPKLiteral -> Right ()
    _ -> Left ("surface: attribute hole capture requires ident/int/string/bool capture: " <> cap)
