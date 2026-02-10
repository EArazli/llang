{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.IndexTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , IxTheory(..)
  , IxFunSig(..)
  , IxRule(..)
  , normalizeIx
  ) where

import Control.Applicative ((<|>))
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName, ModeTheory)
import Strat.Poly.TypeExpr


data TypeTheory = TypeTheory
  { ttModes :: ModeTheory
  , ttIndex :: M.Map ModeName IxTheory
  , ttTypeParams :: M.Map TypeRef [TypeParamSig]
  , ttIxFuel :: Int
  } deriving (Eq, Show)

data TypeParamSig
  = TPS_Ty ModeName
  | TPS_Ix TypeExpr
  deriving (Eq, Ord, Show)


data IxTheory = IxTheory
  { itFuns :: M.Map IxFunName IxFunSig
  , itRules :: [IxRule]
  } deriving (Eq, Ord, Show)

data IxFunSig = IxFunSig
  { ifArgs :: [TypeExpr]
  , ifRes :: TypeExpr
  } deriving (Eq, Ord, Show)

data IxRule = IxRule
  { irVars :: [IxVar]
  , irLHS :: IxTerm
  , irRHS :: IxTerm
  } deriving (Eq, Ord, Show)

normalizeIx :: TypeTheory -> TypeExpr -> IxTerm -> Either Text IxTerm
normalizeIx tt expectedSort tm = do
  ixTheory <- requireTheoryForSort expectedSort
  normalizeLoop (ttIxFuel tt) ixTheory tm
  where
    requireTheoryForSort sortTy =
      let mode = typeMode sortTy
       in case M.lookup mode (ttIndex tt) of
            Just ixTheory -> Right ixTheory
            Nothing -> Left "normalizeIx: expected sort is not in an index mode"

normalizeLoop :: Int -> IxTheory -> IxTerm -> Either Text IxTerm
normalizeLoop fuel ixTheory tm
  | fuel < 0 = Left "normalizeIx: negative fuel"
  | fuel == 0 = Left "normalizeIx: fuel exhausted"
  | otherwise =
      case rewriteOnceIx ixTheory tm of
        Nothing -> Right tm
        Just tm' -> normalizeLoop (fuel - 1) ixTheory tm'

rewriteOnceIx :: IxTheory -> IxTerm -> Maybe IxTerm
rewriteOnceIx ixTheory tm =
  tryRules tm <|> descend tm
  where
    tryRules t = firstJust (map (`applyRuleAt` t) (itRules ixTheory))
    descend t =
      case t of
        IXFun f args -> fmap (IXFun f) (rewriteArgs args)
        _ -> Nothing
    rewriteArgs [] = Nothing
    rewriteArgs (arg:rest) =
      case rewriteOnceIx ixTheory arg of
        Just arg' -> Just (arg' : rest)
        Nothing -> fmap (arg :) (rewriteArgs rest)

applyRuleAt :: IxRule -> IxTerm -> Maybe IxTerm
applyRuleAt rule tm = do
  sub <- matchPattern (S.fromList (irVars rule)) (irLHS rule) tm M.empty
  pure (instantiate sub (irRHS rule))

type IxPatternSubst = M.Map IxVar IxTerm

matchPattern :: S.Set IxVar -> IxTerm -> IxTerm -> IxPatternSubst -> Maybe IxPatternSubst
matchPattern patternVars lhs rhs sub =
  case lhs of
    IXVar v
      | v `S.member` patternVars ->
          case M.lookup v sub of
            Nothing -> Just (M.insert v rhs sub)
            Just rhs0 ->
              if rhs0 == rhs
                then Just sub
                else Nothing
      | otherwise ->
          if lhs == rhs
            then Just sub
            else Nothing
    IXBound i ->
      case rhs of
        IXBound j | i == j -> Just sub
        _ -> Nothing
    IXFun f xs ->
      case rhs of
        IXFun g ys
          | f == g && length xs == length ys ->
              foldl step (Just sub) (zip xs ys)
        _ -> Nothing
  where
    step acc (x, y) = do
      sub' <- acc
      matchPattern patternVars x y sub'

instantiate :: IxPatternSubst -> IxTerm -> IxTerm
instantiate sub tm =
  case tm of
    IXVar v -> M.findWithDefault tm v sub
    IXBound _ -> tm
    IXFun name args -> IXFun name (map (instantiate sub) args)

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (x:xs) =
  case x of
    Just _ -> x
    Nothing -> firstJust xs
