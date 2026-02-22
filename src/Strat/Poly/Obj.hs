{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Obj
  ( ObjVar(..)
  , ObjName(..)
  , ObjRef(..)
  , TmFunName(..)
  , TmVar(..)
  , TermDiagram(..)
  , ObjArg(..)
  , Obj(..)
  , Context
  , mapTermDiagram
  , mapObjExpr
  , freeObjVarsObj
  , freeObjVarsTerm
  , freeTmVarsObj
  , freeTmVarsTerm
  , occursObjVar
  , boundTmIndicesObj
  , boundTmIndicesTerm
  , resolveTmCtxIndex
  , tmCtxForMode
  , objMode
  , normalizeObjExpr
  ) where

import Data.Text (Text)
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Strat.Poly.ModeTheory (ModeName, ModExpr(..), ModeTheory, composeMod, normalizeModExpr)
import Strat.Poly.Syntax
  ( ObjVar(..)
  , ObjName(..)
  , ObjRef(..)
  , TmFunName(..)
  , TmVar(..)
  , TermDiagram(..)
  , ObjArg(..)
  , Obj(..)
  , Context
  , Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , unPortId
  , unEdgeId
  )

mapTermDiagram :: (TermDiagram -> TermDiagram) -> TermDiagram -> TermDiagram
mapTermDiagram f tm = f tm

mapObjExpr :: (Obj -> Obj) -> (TermDiagram -> TermDiagram) -> Obj -> Obj
mapObjExpr fTy fTm = goTy
  where
    goTy ty =
      fTy $
        case ty of
          OVar _ -> ty
          OCon ref args -> OCon ref (map goArg args)
          OMod me inner -> OMod me (goTy inner)
    goArg arg =
      case arg of
        OAObj ty -> OAObj (goTy ty)
        OATm tm -> OATm (mapTermDiagram fTm tm)

freeObjVarsObj :: Obj -> S.Set ObjVar
freeObjVarsObj ty =
  case ty of
    OVar v -> S.singleton v
    OCon _ args -> S.unions (map freeObjVarsArg args)
    OMod _ inner -> freeObjVarsObj inner
  where
    freeObjVarsArg arg =
      case arg of
        OAObj innerObj -> freeObjVarsObj innerObj
        OATm tm -> freeObjVarsTerm tm

freeObjVarsTerm :: TermDiagram -> S.Set ObjVar
freeObjVarsTerm (TermDiagram diag) =
  S.unions
    [ S.unions (map freeObjVarsObj (IM.elems (dPortObj diag)))
    , S.unions (map freeObjVarsObj (dTmCtx diag))
    , S.unions (map edgeObjVars (IM.elems (dEdges diag)))
    ]
  where
    edgeObjVars edge =
      case ePayload edge of
        PTmMeta v -> freeObjVarsObj (tmvSort v)
        _ -> S.empty

freeTmVarsTerm :: TermDiagram -> S.Set TmVar
freeTmVarsTerm (TermDiagram diag) =
  S.unions
    [ S.unions (map freeTmVarsObj (IM.elems (dPortObj diag)))
    , S.unions (map freeTmVarsObj (dTmCtx diag))
    , S.unions (map edgeTmVars (IM.elems (dEdges diag)))
    ]
  where
    edgeTmVars edge =
      case ePayload edge of
        PTmMeta v -> S.singleton v
        _ -> S.empty

freeTmVarsObj :: Obj -> S.Set TmVar
freeTmVarsObj ty =
  case ty of
    OVar _ -> S.empty
    OCon _ args -> S.unions (map freeTmVarsArg args)
    OMod _ inner -> freeTmVarsObj inner
  where
    freeTmVarsArg arg =
      case arg of
        OAObj innerObj -> freeTmVarsObj innerObj
        OATm tm -> freeTmVarsTerm tm

occursObjVar :: ObjVar -> Obj -> Bool
occursObjVar v ty =
  case ty of
    OVar v' -> v == v'
    OCon _ args -> any occursArg args
    OMod _ inner -> occursObjVar v inner
  where
    occursArg arg =
      case arg of
        OAObj innerObj -> occursObjVar v innerObj
        OATm tmArg -> v `S.member` freeObjVarsTerm tmArg

boundTmIndicesTerm :: TermDiagram -> S.Set Int
boundTmIndicesTerm (TermDiagram diag) =
  S.fromList
    [ globalTm
    | localPos <- S.toList usedLocals
    , Just globalTm <- [resolveTmCtxIndex (dTmCtx diag) (dMode diag) localPos]
    ]
  where
    inputLocals = M.fromList (zip (dIn diag) [0 :: Int ..])
    usedLocals = collect S.empty S.empty (dOut diag)

    collect _seen locals [] = locals
    collect seen locals (pid:rest)
      | pid `S.member` seen = collect seen locals rest
      | otherwise =
          let seen' = S.insert pid seen
           in case M.lookup pid inputLocals of
                Just localPos ->
                  collect seen' (S.insert localPos locals) rest
                Nothing ->
                  case IM.lookup (unPortId pid) (dProd diag) of
                    Just (Just eid) ->
                      case IM.lookup (unEdgeId eid) (dEdges diag) of
                        Just edge ->
                          collect seen' locals (eIns edge <> rest)
                        Nothing ->
                          collect seen' locals rest
                    _ ->
                      collect seen' locals rest

resolveTmCtxIndex :: [Obj] -> ModeName -> Int -> Maybe Int
resolveTmCtxIndex tmCtx mode localPos =
  case drop localPos globals of
    (globalTm:_) -> Just globalTm
    [] -> Nothing
  where
    globals =
      [ i
      | (i, ty) <- zip [0 :: Int ..] tmCtx
      , objMode ty == mode
      ]

boundTmIndicesObj :: Obj -> S.Set Int
boundTmIndicesObj ty =
  case ty of
    OVar _ -> S.empty
    OCon _ args -> S.unions (map boundTmIndicesArg args)
    OMod _ inner -> boundTmIndicesObj inner
  where
    boundTmIndicesArg arg =
      case arg of
        OAObj innerObj -> boundTmIndicesObj innerObj
        OATm tm -> boundTmIndicesTerm tm

tmCtxForMode :: [Obj] -> ModeName -> [Obj]
tmCtxForMode tele mode =
  [ ty
  | ty <- tele
  , objMode ty == mode
  ]

objMode :: Obj -> ModeName
objMode ty =
  case ty of
    OVar v -> ovMode v
    OCon r _ -> orMode r
    OMod me _ -> meTgt me

normalizeObjExpr :: ModeTheory -> Obj -> Either Text Obj
normalizeObjExpr mt ty =
  case ty of
    OVar _ -> Right ty
    OCon ref args -> do
      args' <- mapM normalizeArg args
      Right (OCon ref args')
    OMod me inner0 -> do
      inner <- normalizeObjExpr mt inner0
      (meComposed, innerBase) <-
        case inner of
          OMod me2 inner2 -> do
            me' <- composeMod mt me2 me
            Right (me', inner2)
          _ -> Right (me, inner)
      if objMode innerBase /= meSrc meComposed
        then Left "normalizeObjExpr: modality source does not match inner object mode"
        else do
          let meNorm = normalizeModExpr mt meComposed
          if null (mePath meNorm)
            then Right innerBase
            else Right (OMod meNorm innerBase)
  where
    normalizeArg arg =
      case arg of
        OAObj innerTy -> OAObj <$> normalizeObjExpr mt innerTy
        OATm tm -> Right (OATm tm)
