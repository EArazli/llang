module Strat.Kernel.Signature
  ( SortCtor(..)
  , OpDecl(..)
  , Signature(..)
  , SortError(..)
  , mkSort
  ) where

import Strat.Kernel.Subst (applySubstSort)
import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M

data SortCtor = SortCtor
  { scName      :: SortName
  , scTele      :: [Binder]
  }
  deriving (Eq, Show)

data OpDecl = OpDecl
  { opName   :: OpName
  , opTele   :: [Binder]
  , opResult :: Sort
  }
  deriving (Eq, Show)

data Signature = Signature
  { sigSortCtors :: M.Map SortName SortCtor
  , sigOps       :: M.Map OpName OpDecl
  }
  deriving (Eq, Show)

data SortError
  = UnknownSort SortName
  | SortArityMismatch SortName Int Int
  | SortIndexSortMismatch SortName Int Sort Sort
  deriving (Eq, Show)

mkSort :: Signature -> SortName -> [Term] -> Either SortError Sort
mkSort sig name idxTerms =
  case M.lookup name (sigSortCtors sig) of
    Nothing -> Left (UnknownSort name)
    Just ctor ->
      let expected = length (scTele ctor)
          actual = length idxTerms
      in if expected /= actual
           then Left (SortArityMismatch name expected actual)
           else do
             go expected actual M.empty 0 (scTele ctor) idxTerms
             pure (Sort name idxTerms)
  where
    go _ _ _ _ [] [] = Right ()
    go expected actual subst ix (Binder v expectedSort : tele) (term : rest) =
      let expected' = applySubstSort subst expectedSort
          actualSort = termSort term
      in if expected' == actualSort
           then go expected actual (M.insert v term subst) (ix + 1) tele rest
           else Left (SortIndexSortMismatch name ix expected' actualSort)
    go expected actual _ _ _ _ = Left (SortArityMismatch name expected actual)
