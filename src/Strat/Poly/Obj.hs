{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Strat.Poly.Obj
  ( ObjVar(..)
  , ObjName(..)
  , ObjRef(..)
  , TmFunName(..)
  , TmVar(..)
  , TermDiagram(..)
  , CodeArg(..)
  , CodeTerm(..)
  , ObjArg
  , pattern OAObj
  , pattern OATm
  , Obj(Obj, objOwnerMode, objCode, OVar, OCon, OMod)
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
  , codeMode0
  , objMode
  , normalizeCodeTerm
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
  , CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , Context
  , Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , unPortId
  , unEdgeId
  )

type ObjArg = CodeArg

pattern OAObj :: Obj -> ObjArg
pattern OAObj ty = CAObj ty

pattern OATm :: TermDiagram -> ObjArg
pattern OATm tm = CATm tm

pattern OVar :: ObjVar -> Obj
pattern OVar v <- Obj _ (CTVar v)
  where
    OVar v = Obj { objOwnerMode = ovMode v, objCode = CTVar v }

pattern OCon :: ObjRef -> [ObjArg] -> Obj
pattern OCon ref args <- Obj _ (CTCon ref args)
  where
    OCon ref args = Obj { objOwnerMode = orMode ref, objCode = CTCon ref args }

pattern OMod :: ModExpr -> Obj -> Obj
pattern OMod me inner <- Obj _ (CTMod me (codeAsObj (meSrc me) -> inner))
  where
    OMod me inner = Obj { objOwnerMode = meTgt me, objCode = CTMod me (objCode inner) }

{-# COMPLETE OAObj, OATm #-}
{-# COMPLETE OVar, OCon, OMod #-}

codeAsObj :: ModeName -> CodeTerm -> Obj
codeAsObj owner code = Obj { objOwnerMode = owner, objCode = code }

mapTermDiagram :: (TermDiagram -> TermDiagram) -> TermDiagram -> TermDiagram
mapTermDiagram f tm = f tm

mapObjExpr :: (Obj -> Obj) -> (TermDiagram -> TermDiagram) -> Obj -> Obj
mapObjExpr fTy fTm = goObj
  where
    goObj obj =
      fTy $
        obj
          { objCode = goCode (objOwnerMode obj) (objCode obj)
          }
    goCode owner code =
      case code of
        CTVar _ -> code
        CTCon ref args -> CTCon ref (map goArg args)
        CTMod me inner ->
          let innerObj = goObj Obj { objOwnerMode = owner, objCode = inner }
          in CTMod me (objCode innerObj)
    goArg arg =
      case arg of
        CAObj ty -> CAObj (goObj ty)
        CATm tm -> CATm (mapTermDiagram fTm tm)

freeObjVarsObj :: Obj -> S.Set ObjVar
freeObjVarsObj obj =
  freeObjVarsCode (objCode obj)
  where
    freeObjVarsCode code =
      case code of
        CTVar v -> S.singleton v
        CTCon _ args -> S.unions (map freeObjVarsArg args)
        CTMod _ inner -> freeObjVarsCode inner
    freeObjVarsArg arg =
      case arg of
        CAObj innerObj -> freeObjVarsObj innerObj
        -- Object metavariables are tracked through object arguments only.
        -- Term arguments carry term metavariables/sorts and are handled separately.
        CATm _ -> S.empty

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
freeTmVarsObj obj =
  freeTmVarsCode (objCode obj)
  where
    freeTmVarsCode code =
      case code of
        CTVar _ -> S.empty
        CTCon _ args -> S.unions (map freeTmVarsArg args)
        CTMod _ inner -> freeTmVarsCode inner
    freeTmVarsArg arg =
      case arg of
        CAObj innerObj -> freeTmVarsObj innerObj
        CATm tm -> freeTmVarsTerm tm

occursObjVar :: ObjVar -> Obj -> Bool
occursObjVar v obj =
  occursInCode (objCode obj)
  where
    occursInCode code =
      case code of
        CTVar v' -> v == v'
        CTCon _ args -> any occursArg args
        CTMod _ inner -> occursInCode inner
    occursArg arg =
      case arg of
        CAObj innerObj -> occursObjVar v innerObj
        -- Term arguments are ignored for object-variable occurs checks.
        CATm _ -> False

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
boundTmIndicesObj obj =
  boundInCode (objCode obj)
  where
    boundInCode code =
      case code of
        CTVar _ -> S.empty
        CTCon _ args -> S.unions (map boundTmIndicesArg args)
        CTMod _ inner -> boundInCode inner
    boundTmIndicesArg arg =
      case arg of
        CAObj innerObj -> boundTmIndicesObj innerObj
        CATm tm -> boundTmIndicesTerm tm

tmCtxForMode :: [Obj] -> ModeName -> [Obj]
tmCtxForMode tele mode =
  [ ty
  | ty <- tele
  , objMode ty == mode
  ]

codeMode0 :: CodeTerm -> ModeName
codeMode0 code =
  case code of
    CTVar v -> ovMode v
    CTCon r _ -> orMode r
    CTMod me _ -> meTgt me

objMode :: Obj -> ModeName
objMode = objOwnerMode

normalizeCodeTerm :: ModeTheory -> CodeTerm -> Either Text CodeTerm
normalizeCodeTerm mt code =
  case code of
    CTVar _ -> Right code
    CTCon ref args -> do
      args' <- mapM normalizeArg args
      Right (CTCon ref args')
    CTMod me inner0 -> do
      inner <- normalizeCodeTerm mt inner0
      (meComposed, innerBase) <-
        case inner of
          CTMod me2 inner2 -> do
            me' <- composeMod mt me2 me
            Right (me', inner2)
          _ -> Right (me, inner)
      if codeMode0 innerBase /= meSrc meComposed
        then Left "normalizeObjExpr: modality source does not match inner object mode"
        else do
          let meNorm = normalizeModExpr mt meComposed
          if null (mePath meNorm)
            then Right innerBase
            else Right (CTMod meNorm innerBase)
  where
    normalizeArg arg =
      case arg of
        CAObj innerTy -> CAObj <$> normalizeObjExpr mt innerTy
        CATm tm -> Right (CATm tm)

normalizeObjExpr :: ModeTheory -> Obj -> Either Text Obj
normalizeObjExpr mt obj = do
  code' <- normalizeCodeTerm mt (objCode obj)
  Right obj { objCode = code' }
