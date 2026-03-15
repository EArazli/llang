{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Alpha
  ( renameTyVarAlpha
  , renameTmVarAlpha
  , renameParamAlpha
  , renameTypeAlpha
  , renameCodeArgAlpha
  , renameBinderArgAlpha
  , renameDiagramAlpha
  , renameTermDiagramAlpha
  , canonicalizeCtorSig
  ) where

import Data.Functor.Identity (runIdentity)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
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
