{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Alpha
  ( renameTyVarAlpha
  , renameTmVarAlpha
  , renameParamAlpha
  , renameTypeAlpha
  , renameHeadArgAlpha
  , renameTermExprAlpha
  , renameCodeArgAlpha
  , renameBinderArgAlpha
  , renameDiagramAlpha
  , renameTermDiagramAlpha
  , canonicalizeCtorSig
  , freshenCtorSigAgainstWithMaps
  , freshenCtorSigAgainst
  , freshenTmHeadSigAgainstWithMaps
  , freshenTmHeadSigAgainst
  ) where

import Data.Functor.Identity (runIdentity)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import Strat.Poly.Graph (BinderArg(..), Diagram(..), EdgePayload(..))
import Strat.Poly.Obj
  ( CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , TermDiagram(..)
  , TmVar(..)
  , tmVarOwner
  )
import Strat.Poly.Tele (CtorSig(..), GenParam(..), teleDistinctNames)
import Strat.Poly.Traversal (traverseDiagram)
import Strat.Poly.Term.AST (TermExpr(..), TermHeadArg(..))
import Strat.Poly.TypeTheory (TmHeadSig(..))

renameParamAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> GenParam -> GenParam
renameParamAlpha tyMap tmMap param =
  case param of
    GP_Ty v -> GP_Ty (renameTyVarAlpha tyMap v)
    GP_Tm v -> GP_Tm (renameTmVarAlpha tyMap tmMap v)

renameTyVarAlpha :: M.Map TmVar TmVar -> TmVar -> TmVar
renameTyVarAlpha tyMap v =
  M.findWithDefault v v tyMap

renameTmVarAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> TmVar -> TmVar
renameTmVarAlpha tyMap tmMap v =
  case M.lookup v tmMap of
    Just v' -> v'
    Nothing -> v { tmvSort = renameTypeAlpha tyMap tmMap (tmvSort v) }

renameTypeAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> Obj -> Obj
renameTypeAlpha tyMap tmMap = goObj
  where
    goObj ty =
      ty { objCode = goCode (objCode ty) }

    goCode code =
      case code of
        CTMeta v ->
          CTMeta (renameTyVarAlpha tyMap v)
        CTCon ref args ->
          CTCon ref (map goArg args)
        CTLift me inner ->
          CTLift me (goCode inner)

    goArg arg =
      renameCodeArgAlpha tyMap tmMap arg

renameDiagramAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> Diagram -> Diagram
renameDiagramAlpha tyMap tmMap =
  runIdentity . traverseDiagram onDiag onPayload onCodeArg onBinderArg
  where
    onDiag d =
      pure d
        { dTmCtx = map (renameTypeAlpha tyMap tmMap) (dTmCtx d)
        , dPortObj = IM.map (renameTypeAlpha tyMap tmMap) (dPortObj d)
        }

    onPayload payload =
      pure $
        case payload of
          PTmMeta v ->
            PTmMeta (renameTmVarAlpha tyMap tmMap v)
          other ->
            other

    onCodeArg arg =
      pure (renameCodeArgAlpha tyMap tmMap arg)

    onBinderArg barg =
      pure (renameBinderArgAlpha tyMap tmMap barg)

renameCodeArgAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> CodeArg -> CodeArg
renameCodeArgAlpha tyMap tmMap arg =
  case arg of
    CAObj ty -> CAObj (renameTypeAlpha tyMap tmMap ty)
    CATm tm -> CATm (renameTermDiagramAlpha tyMap tmMap tm)

renameHeadArgAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> TermHeadArg -> TermHeadArg
renameHeadArgAlpha tyMap tmMap arg =
  case arg of
    THAObj ty -> THAObj (renameTypeAlpha tyMap tmMap ty)
    THATm tm -> THATm (renameTermExprAlpha tyMap tmMap tm)

renameTermExprAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> TermExpr -> TermExpr
renameTermExprAlpha tyMap tmMap expr =
  case expr of
    TMBound i -> TMBound i
    TMMeta v args -> TMMeta (renameTmVarAlpha tyMap tmMap v) args
    TMGen g args -> TMGen g (map (renameHeadArgAlpha tyMap tmMap) args)
    TMLit lit -> TMLit lit

renameBinderArgAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> BinderArg -> BinderArg
renameBinderArgAlpha tyMap tmMap barg =
  case barg of
    BAConcrete inner -> BAConcrete (renameDiagramAlpha tyMap tmMap inner)
    BAMeta x -> BAMeta x

renameTermDiagramAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> TermDiagram -> TermDiagram
renameTermDiagramAlpha tyMap tmMap (TermDiagram diag) =
  TermDiagram (renameDiagramAlpha tyMap tmMap diag)

canonicalizeCtorSig :: [GenParam] -> Either T.Text CtorSig
canonicalizeCtorSig params = do
  teleDistinctNames params
  CtorSig . reverse <$> go (0 :: Int) (0 :: Int) M.empty M.empty [] params
  where
    go _ _ _ _ acc [] =
      Right acc
    go tyIx tmIx tyMap tmMap acc (param:rest) =
      case param of
        GP_Ty v -> do
          let name = "a" <> T.pack (show tyIx)
          let v' =
                v
                  { tmvName = name
                  , tmvSort = renameTypeAlpha tyMap tmMap (tmvSort v)
                  , tmvOwnerMode = Just (tmVarOwner v)
                  }
          go (tyIx + 1) tmIx (M.insert v v' tyMap) tmMap (GP_Ty v' : acc) rest
        GP_Tm v -> do
          let name = "t" <> T.pack (show tmIx)
          let v' =
                v
                  { tmvName = name
                  , tmvSort = renameTypeAlpha tyMap tmMap (tmvSort v)
                  }
          go tyIx (tmIx + 1) tyMap (M.insert v v' tmMap) (GP_Tm v' : acc) rest

freshenCtorSigAgainst :: S.Set TmVar -> CtorSig -> CtorSig
freshenCtorSigAgainst used0 =
  (\(sig, _, _) -> sig) . freshenCtorSigAgainstWithMaps used0

freshenCtorSigAgainstWithMaps
  :: S.Set TmVar
  -> CtorSig
  -> (CtorSig, M.Map TmVar TmVar, M.Map TmVar TmVar)
freshenCtorSigAgainstWithMaps used0 (CtorSig params) =
  (CtorSig params', tyMap, tmMap)
  where
    (params', tyMap, tmMap, _) = freshenParamsAgainst used0 params

freshenTmHeadSigAgainst :: S.Set TmVar -> TmHeadSig -> TmHeadSig
freshenTmHeadSigAgainst used0 =
  (\(sig, _, _) -> sig) . freshenTmHeadSigAgainstWithMaps used0

freshenTmHeadSigAgainstWithMaps
  :: S.Set TmVar
  -> TmHeadSig
  -> (TmHeadSig, M.Map TmVar TmVar, M.Map TmVar TmVar)
freshenTmHeadSigAgainstWithMaps used0 sig =
  ( sig
      { thsParams = params'
      , thsInputs = map (renameTypeAlpha tyMap tmMap) (thsInputs sig)
      , thsRes = renameTypeAlpha tyMap tmMap (thsRes sig)
      }
  , tyMap
  , tmMap
  )
  where
    (params', tyMap, tmMap, _) = freshenParamsAgainst used0 (thsParams sig)

freshenParamsAgainst
  :: S.Set TmVar
  -> [GenParam]
  -> ([GenParam], M.Map TmVar TmVar, M.Map TmVar TmVar, S.Set TmVar)
freshenParamsAgainst used0 =
  go used0 M.empty M.empty []
  where
    go used tyMap tmMap acc [] =
      (reverse acc, tyMap, tmMap, used)
    go used tyMap tmMap acc (param : rest) =
      case param of
        GP_Ty v ->
          let v' = freshenTyParam used tyMap tmMap v
           in go
                (S.insert v' used)
                (M.insert v v' tyMap)
                tmMap
                (GP_Ty v' : acc)
                rest
        GP_Tm v ->
          let v' = freshenTmParam used tyMap tmMap v
           in go
                (S.insert v' used)
                tyMap
                (M.insert v v' tmMap)
                (GP_Tm v' : acc)
                rest

freshenTyParam :: S.Set TmVar -> M.Map TmVar TmVar -> M.Map TmVar TmVar -> TmVar -> TmVar
freshenTyParam used tyMap tmMap v =
  fresh
    { tmvSort = renameTypeAlpha tyMap tmMap (tmvSort v)
    , tmvOwnerMode = Just (tmVarOwner fresh)
    }
  where
    fresh = v { tmvName = pickFreshName used v 0 }

freshenTmParam :: S.Set TmVar -> M.Map TmVar TmVar -> M.Map TmVar TmVar -> TmVar -> TmVar
freshenTmParam used tyMap tmMap v =
  fresh { tmvSort = renameTypeAlpha tyMap tmMap (tmvSort v) }
  where
    fresh = v { tmvName = pickFreshName used v 0 }

pickFreshName :: S.Set TmVar -> TmVar -> Int -> T.Text
pickFreshName used v n =
  let base = tmvName v
      name =
        if n == 0
          then base
          else base <> "#" <> T.pack (show (n - 1))
      candidate = v { tmvName = name }
   in if candidate `S.member` used
        then pickFreshName used v (n + 1)
        else name
