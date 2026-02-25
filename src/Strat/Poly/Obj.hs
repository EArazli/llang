{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Strat.Poly.Obj
  ( ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
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
  , mkObj
  , mkCon
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
import Strat.Poly.ModeTheory (ModeName, ModExpr(..), ModeTheory(..), ClassificationDecl(..), composeMod, normalizeModExpr)
import Strat.Poly.Syntax
  ( ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
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

mkObj :: ModeName -> CodeTerm -> Obj
mkObj owner code = Obj { objOwnerMode = owner, objCode = code }

mkCon :: ObjRef -> [ObjArg] -> Obj
mkCon ref args = mkObj (orMode ref) (CTCon ref args)

pattern OVar :: ObjVar -> Obj
pattern OVar v <- Obj _ (CTMeta v)
  where
    OVar v = mkObj owner (CTMeta v)
      where
        owner =
          case tmvOwnerMode v of
            Just m -> m
            Nothing -> objOwnerMode (tmvSort v)

pattern OCon :: ObjRef -> [ObjArg] -> Obj
pattern OCon ref args <- Obj _ (CTCon ref args)

pattern OMod :: ModExpr -> Obj -> Obj
pattern OMod me inner <- Obj _ (CTMod me (codeAsObj (meSrc me) -> inner))
  where
    OMod me inner = mkObj (meTgt me) (CTMod me (objCode inner))

{-# COMPLETE OAObj, OATm #-}
{-# COMPLETE OVar, OCon, OMod #-}

codeAsObj :: ModeName -> CodeTerm -> Obj
codeAsObj = mkObj

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
        CTMeta _ -> code
        CTCon ref args -> CTCon ref (map goArg args)
        CTMod me inner ->
          let innerObj = goObj Obj { objOwnerMode = meSrc me, objCode = inner }
          in CTMod me (objCode innerObj)
        CTLift me inner ->
          let innerObj = goObj Obj { objOwnerMode = meSrc me, objCode = inner }
           in CTLift me (objCode innerObj)
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
        CTMeta v -> S.singleton v
        CTCon _ args -> S.unions (map freeObjVarsArg args)
        CTMod _ inner -> freeObjVarsCode inner
        CTLift _ inner -> freeObjVarsCode inner
    freeObjVarsArg arg =
      case arg of
        CAObj innerObj -> freeObjVarsObj innerObj
        CATm tmArg -> freeObjVarsTerm tmArg

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
        CTMeta _ -> S.empty
        CTCon _ args -> S.unions (map freeTmVarsArg args)
        CTMod _ inner -> freeTmVarsCode inner
        CTLift _ inner -> freeTmVarsCode inner
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
        CTMeta v' -> v == v'
        CTCon _ args -> any occursArg args
        CTMod _ inner -> occursInCode inner
        CTLift _ inner -> occursInCode inner
    occursArg arg =
      case arg of
        CAObj innerObj -> occursObjVar v innerObj
        CATm tmArg -> v `S.member` freeObjVarsTerm tmArg

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
        CTMeta _ -> S.empty
        CTCon _ args -> S.unions (map boundTmIndicesArg args)
        CTMod _ inner -> boundInCode inner
        CTLift _ inner -> boundInCode inner
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
    CTMeta v ->
      case tmvOwnerMode v of
        Just owner -> owner
        Nothing -> objOwnerMode (tmvSort v)
    CTCon r _ -> orMode r
    CTMod me _ -> meTgt me
    CTLift me _ -> meTgt me

objMode :: Obj -> ModeName
objMode = objOwnerMode

normalizeCodeTerm :: ModeTheory -> CodeTerm -> Either Text CodeTerm
normalizeCodeTerm mt code =
  case code of
    CTMeta _ -> Right code
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
      let meNorm = normalizeModExpr mt meComposed
      if null (mePath meNorm)
        then Right innerBase
        else Right (CTMod meNorm innerBase)
    CTLift me inner0 -> do
      inner <- normalizeCodeTerm mt inner0
      (meComposed, innerBase) <-
        case inner of
          CTLift me2 inner2 -> do
            me' <- composeMod mt me2 me
            Right (me', inner2)
          _ -> Right (me, inner)
      let meNorm = normalizeModExpr mt meComposed
      if null (mePath meNorm)
        then Right innerBase
        else
          if liftMayReuseMod meNorm
            then collapseModLike meNorm innerBase
            else Right (CTLift meNorm innerBase)
  where
    normalizeArg arg =
      case arg of
        CAObj innerTy -> CAObj <$> normalizeObjExpr mt innerTy
        CATm tm -> Right (CATm tm)

    liftMayReuseMod me =
      modeIsSelfClassified (meSrc me) && modeIsSelfClassified (meTgt me)

    modeIsSelfClassified mode =
      case M.lookup mode (mtClassifiedBy mt) of
        Just decl -> cdClassifier decl == mode
        Nothing -> False

    collapseModLike me code =
      case code of
        CTMod me2 inner2 -> do
          me' <- composeMod mt me2 me
          let meNorm = normalizeModExpr mt me'
          if null (mePath meNorm)
            then Right inner2
            else Right (CTMod meNorm inner2)
        _ -> Right (CTMod me code)

normalizeObjExpr :: ModeTheory -> Obj -> Either Text Obj
normalizeObjExpr mt obj =
  case objCode obj of
    CTMeta _ -> Right obj
    CTCon ref args -> do
      args' <- mapM normalizeArg args
      Right obj { objCode = CTCon ref args' }
    CTMod me innerCode -> do
      if meTgt me /= objOwnerMode obj
        then Left "normalizeObjExpr: modality target does not match object owner mode"
        else Right ()
      inner <- normalizeObjExpr mt Obj { objOwnerMode = meSrc me, objCode = innerCode }
      collapse me (objCode inner)
    CTLift me innerCode -> do
      if meTgt me /= objOwnerMode obj
        then Left "normalizeObjExpr: lift target does not match object owner mode"
        else Right ()
      inner <- normalizeObjExpr mt Obj { objOwnerMode = meSrc me, objCode = innerCode }
      collapseLift me (objCode inner)
  where
    normalizeArg arg =
      case arg of
        CAObj innerObj -> CAObj <$> normalizeObjExpr mt innerObj
        CATm tm -> Right (CATm tm)

    collapse me code =
      case code of
        CTMod me2 inner2 -> do
          me' <- composeMod mt me2 me
          collapse me' inner2
        _ -> do
          let meNorm = normalizeModExpr mt me
          if null (mePath meNorm)
            then Right obj { objCode = code }
            else Right obj { objCode = CTMod meNorm code }

    collapseLift me code =
      case code of
        CTLift me2 inner2 -> do
          me' <- composeMod mt me2 me
          collapseLift me' inner2
        _ -> do
          let meNorm = normalizeModExpr mt me
          if null (mePath meNorm)
            then Right obj { objCode = code }
            else
              if liftMayReuseMod meNorm
                then collapse meNorm code
                else Right obj { objCode = CTLift meNorm code }

    liftMayReuseMod me =
      modeIsSelfClassified (meSrc me) && modeIsSelfClassified (meTgt me)

    modeIsSelfClassified mode =
      case M.lookup mode (mtClassifiedBy mt) of
        Just decl -> cdClassifier decl == mode
        Nothing -> False
