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

weaken :: Int -> STerm -> STerm
weaken n = shift n 0

shift :: Int -> Int -> STerm -> STerm
shift d cutoff = go cutoff
  where
    go c tm =
      case tm of
        SBound (Ix k)
          | k >= c ->
              let k' = k + d
              in if k' < 0 then error "shift: negative index" else SBound (Ix k')
          | otherwise -> SBound (Ix k)
        SFree t -> SFree t
        SCon con args -> SCon con (map (goArg c) args)

    goArg c (SArg binders body) =
      let binders' = map (go c) binders
          body' = go (c + length binders) body
      in SArg binders' body'

subst0 :: STerm -> STerm -> STerm
subst0 = subst 0

substMany :: [STerm] -> STerm -> STerm
substMany args body =
  L.foldl' (\acc arg -> shift (-1) 0 (subst0 (shift 1 0 arg) acc)) body args

subst :: Int -> STerm -> STerm -> STerm
subst j s = go 0
  where
    go c tm =
      case tm of
        SBound (Ix k)
          | k == j + c -> shift c 0 s
          | otherwise -> SBound (Ix k)
        SFree t -> SFree t
        SCon con args -> SCon con (map (goArg c) args)

    goArg c (SArg binders body) =
      let binders' = map (go c) binders
          body' = go (c + length binders) body
      in SArg binders' body'
