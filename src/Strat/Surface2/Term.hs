{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.Term
  ( Sort2Name(..)
  , Con2Name(..)
  , JudgName(..)
  , Ix(..)
  , STerm(..)
  , SArg(..)
  , weaken
  , shift
  , subst0
  , substMany
  ) where

import Data.Text (Text)
import qualified Data.List as L

newtype Sort2Name = Sort2Name Text
  deriving (Eq, Ord, Show)

newtype Con2Name = Con2Name Text
  deriving (Eq, Ord, Show)

newtype JudgName = JudgName Text
  deriving (Eq, Ord, Show)

newtype Ix = Ix Int
  deriving (Eq, Ord, Show)

data STerm
  = SBound Ix
  | SFree Text
  | SCon Con2Name [SArg]
  deriving (Eq, Ord, Show)

data SArg = SArg
  { saBinders :: [STerm]
  , saBody :: STerm
  } deriving (Eq, Ord, Show)

weaken :: Int -> STerm -> Either Text STerm
weaken n = shift n 0

shift :: Int -> Int -> STerm -> Either Text STerm
shift d cutoff = go cutoff
  where
    go c tm =
      case tm of
        SBound (Ix k)
          | k >= c ->
              let k' = k + d
              in if k' < 0 then Left "shift: negative index" else Right (SBound (Ix k'))
          | otherwise -> Right (SBound (Ix k))
        SFree t -> Right (SFree t)
        SCon con args -> SCon con <$> mapM (goArg c) args

    goArg c (SArg binders body) =
      SArg <$> mapM (go c) binders <*> go (c + length binders) body

subst0 :: STerm -> STerm -> Either Text STerm
subst0 = subst 0

substMany :: [STerm] -> STerm -> Either Text STerm
substMany args body =
  L.foldl' step (Right body) args
  where
    step accE arg = do
      acc <- accE
      arg' <- shift 1 0 arg
      acc' <- subst0 arg' acc
      shift (-1) 0 acc'

subst :: Int -> STerm -> STerm -> Either Text STerm
subst j s = go 0
  where
    go c tm =
      case tm of
        SBound (Ix k)
          | k == j + c -> shift c 0 s
          | otherwise -> Right (SBound (Ix k))
        SFree t -> Right (SFree t)
        SCon con args -> SCon con <$> mapM (goArg c) args

    goArg c (SArg binders body) =
      SArg <$> mapM (go c) binders <*> go (c + length binders) body
