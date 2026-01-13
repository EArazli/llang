module Strat.Kernel.Signature
  ( SortCtor(..)
  , OpDecl(..)
  , Signature(..)
  , SortError(..)
  , mkSort
  ) where

import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M

data SortCtor = SortCtor
  { scName      :: SortName
  , scParamSort :: [Sort]
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
      let expected = length (scParamSort ctor)
          actual = length idxTerms
      in if expected /= actual
           then Left (SortArityMismatch name expected actual)
           else do
             mapM_ (checkIdx name) (zip3 [0 ..] (scParamSort ctor) idxTerms)
             pure (Sort name idxTerms)
  where
    checkIdx sname (ix, expectedSort, term) =
      let actualSort = termSort term
      in if expectedSort == actualSort
           then Right ()
           else Left (SortIndexSortMismatch sname ix expectedSort actualSort)
