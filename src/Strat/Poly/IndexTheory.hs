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
  _ <- requireTheoryForSort tt expectedSort
  normalizeLoop (ttIxFuel tt) tt expectedSort tm
  where
    requireTheoryForSort theory sortTy =
      let mode = typeMode sortTy
       in case M.lookup mode (ttIndex theory) of
            Just ixTheory -> Right ixTheory
            Nothing -> Left "normalizeIx: expected sort is not in an index mode"

normalizeLoop :: Int -> TypeTheory -> TypeExpr -> IxTerm -> Either Text IxTerm
normalizeLoop fuel tt expectedSort tm
  | fuel < 0 = Left "normalizeIx: negative fuel"
  | fuel == 0 = Left "normalizeIx: fuel exhausted"
  | otherwise = do
      mStep <- rewriteOnceIx tt expectedSort tm
      case mStep of
        Nothing -> Right tm
        Just tm' -> normalizeLoop (fuel - 1) tt expectedSort tm'

rewriteOnceIx :: TypeTheory -> TypeExpr -> IxTerm -> Either Text (Maybe IxTerm)
rewriteOnceIx tt expectedSort tm = do
  ixTheory <- requireTheoryForSort tt expectedSort
  case firstJust (map (`applyRuleAt` tm) (itRules ixTheory)) of
    Just tm' -> Right (Just tm')
    Nothing ->
      case tm of
        IXFun f args -> do
          sig <- requireFunSig expectedSort ixTheory f args
          rewritten <- rewriteArgsBySort (zip (ifArgs sig) args)
          pure (fmap (IXFun f) rewritten)
        _ -> Right Nothing
  where
    requireTheoryForSort theory sortTy =
      let mode = typeMode sortTy
       in case M.lookup mode (ttIndex theory) of
            Just ixTheory -> Right ixTheory
            Nothing -> Left "normalizeIx: expected sort is not in an index mode"

    requireFunSig sortTy ixTheory f args =
      case M.lookup f (itFuns ixTheory) of
        Nothing -> Left "normalizeIx: unknown index function"
        Just sig ->
          if length (ifArgs sig) /= length args
            then Left "normalizeIx: index function arity mismatch"
            else
              if typeMode (ifRes sig) == typeMode sortTy
                then Right sig
                else Left "normalizeIx: index function result sort mode mismatch"

    rewriteArgsBySort [] = Right Nothing
    rewriteArgsBySort ((argSort, arg):rest) = do
      mHead <- rewriteOnceIx tt argSort arg
      case mHead of
        Just arg' -> Right (Just (arg' : map snd rest))
        Nothing -> do
          mTail <- rewriteArgsBySort rest
          pure (fmap (arg :) mTail)

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
