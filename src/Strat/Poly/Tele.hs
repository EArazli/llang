{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Tele
  ( GenParam(..)
  , CtorSig(..)
  , teleTyVars
  , teleTmVars
  , teleVars
  , teleNames
  , teleDistinctNames
  , telePrefixTyVars
  , telePrefixTmVars
  ) where

import Data.Text (Text)
import qualified Data.Set as S
import Strat.Poly.Obj (TmVar(..))

data GenParam
  = GP_Ty TmVar
  | GP_Tm TmVar
  deriving (Eq, Ord, Read, Show)

newtype CtorSig = CtorSig
  { csParams :: [GenParam]
  }
  deriving (Eq, Ord, Read, Show)

teleTyVars :: [GenParam] -> [TmVar]
teleTyVars ps = [v | GP_Ty v <- ps]

teleTmVars :: [GenParam] -> [TmVar]
teleTmVars ps = [v | GP_Tm v <- ps]

teleVars :: [GenParam] -> [TmVar]
teleVars ps = [v | GP_Ty v <- ps] <> [v | GP_Tm v <- ps]

teleNames :: [GenParam] -> [Text]
teleNames = map tmvName . teleVars

teleDistinctNames :: [GenParam] -> Either Text ()
teleDistinctNames params =
  let names = teleNames params
   in if S.size (S.fromList names) == length names
        then Right ()
        else Left "duplicate parameter name"

telePrefixTyVars :: [GenParam] -> Int -> [TmVar]
telePrefixTyVars params n = teleTyVars (take n params)

telePrefixTmVars :: [GenParam] -> Int -> [TmVar]
telePrefixTmVars params n = teleTmVars (take n params)
