{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.PendingUniverse
  ( mkPendingUniverseSeed
  , pendingUniverseSeedInnerRef
  ) where

import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj
  ( CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , ObjName(..)
  , ObjRef(..)
  )

pendingUniverseSeedName :: ObjName
pendingUniverseSeedName = ObjName "__pending_universe_seed"

mkPendingUniverseSeed :: ModeName -> ObjRef -> Obj
mkPendingUniverseSeed classifierMode ref =
  Obj
    { objOwnerMode = classifierMode
    , objCode =
        CTCon
          ObjRef
            { orMode = classifierMode
            , orName = pendingUniverseSeedName
            }
          [ CAObj
              Obj
                { objOwnerMode = orMode ref
                , objCode = CTCon ref []
                }
          ]
    }

pendingUniverseSeedInnerRef :: CodeTerm -> Maybe ObjRef
pendingUniverseSeedInnerRef code =
  case code of
    CTCon seedRef [CAObj (Obj _ (CTCon ref []))]
      | orName seedRef == pendingUniverseSeedName ->
          Just ref
    CTLift _ inner ->
      pendingUniverseSeedInnerRef inner
    _ ->
      Nothing
