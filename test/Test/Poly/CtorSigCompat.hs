{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.CtorSigCompat
  ( TypeParamSig(..)
  , flatParamsToGenParams
  , flatParamsToCtorSig
  ) where

import qualified Data.Text as T
import Strat.Poly.Alpha (canonicalizeCtorSig)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj (CodeTerm(..), Obj, Obj(..), ObjName(..), ObjRef(..), TmVar(..))
import Strat.Poly.Tele (CtorSig(..), GenParam(..))

data TypeParamSig
  = TPS_Ty ModeName
  | TPS_Tm Obj
  deriving (Eq, Ord, Read, Show)

flatParamsToGenParams :: ModeName -> [TypeParamSig] -> [GenParam]
flatParamsToGenParams ctorMode sig =
  [ case ps of
      TPS_Ty _ -> GP_Ty (lookupByPos pos tyPos)
      TPS_Tm _ -> GP_Tm (lookupByPos pos tmPos)
  | (pos, ps) <- zip [0 :: Int ..] sig
  ]
  where
    tyPos =
      [ (pos, v)
      | (pos, TPS_Ty m) <- zip [0 :: Int ..] sig
      , let v =
              TmVar
                { tmvName = "a" <> T.pack (show pos)
                , tmvSort = Obj { objOwnerMode = m, objCode = CTCon (ObjRef m (ObjName "__obj_meta_sort")) [] }
                , tmvScope = 0
                , tmvOwnerMode = Just m
                }
      ]
    tmPos =
      [ (pos, v)
      | (pos, TPS_Tm sortTy) <- zip [0 :: Int ..] sig
      , let v =
              TmVar
                { tmvName = "x" <> T.pack (show pos)
                , tmvSort = sortTy
                , tmvScope = 0
                , tmvOwnerMode = Just ctorMode
                }
      ]
    lookupByPos pos xs =
      case lookup pos xs of
        Just v -> v
        Nothing -> error "flatParamsToGenParams: missing parameter position"

flatParamsToCtorSig :: ModeName -> [TypeParamSig] -> CtorSig
flatParamsToCtorSig ctorMode =
  either (error . T.unpack) id . canonicalizeCtorSig . flatParamsToGenParams ctorMode
