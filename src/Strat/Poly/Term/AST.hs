{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.Term.AST
  ( TermHeadArg(..)
  , TermBinderArg(..)
  , TermExpr(..)
  , pattern TMGen
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , boundGlobalsObj
  , maxTmScopeObj
  , isPureMetaExpr
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Poly.Literal (Literal)
import Strat.Poly.ModeSyntax (ModeName, ModExpr)
import Strat.Poly.Names (GenName)
import Strat.Poly.Syntax
  ( BinderArg(..)
  , BinderMetaVar
  , CodeArg(..)
  , CodeTerm(..)
  , Diagram(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , Obj
  , Obj(..)
  , PortId(..)
  , TermDiagram(..)
  , TmVar(..)
  )


data TermHeadArg
  = THAObj Obj
  | THATm TermExpr
  deriving (Eq, Ord, Show)

data TermBinderArg
  = TBABody Diagram
  | TBAHole BinderMetaVar
  deriving (Eq, Ord, Show)

data TermExpr
  = TMBound Int
  | TMMeta TmVar [Int]
  | TMHead GenName [TermHeadArg] [TermBinderArg]
  | TMSplice BinderMetaVar ModExpr [TermExpr]
  | TMLit Literal
  deriving (Eq, Ord, Show)

pattern TMGen :: GenName -> [TermHeadArg] -> TermExpr
pattern TMGen f args = TMHead f args []

freeTmVarsExpr :: TermExpr -> S.Set TmVar
freeTmVarsExpr tm =
  case tm of
    TMBound _ -> S.empty
    TMMeta v _ -> S.singleton v
    TMHead _ args bargs -> S.unions (map freeHeadArg args <> map freeBinderArg bargs)
    TMSplice _ _ args -> S.unions (map freeTmVarsExpr args)
    TMLit _ -> S.empty
  where
    freeHeadArg arg =
      case arg of
        THAObj obj -> freeVarsObj obj
        THATm inner -> freeTmVarsExpr inner
    freeBinderArg (TBABody inner) = freeVarsDiagram inner
    freeBinderArg (TBAHole _) = S.empty

boundGlobalsExpr :: TermExpr -> S.Set Int
boundGlobalsExpr tm =
  case tm of
    TMBound i -> S.singleton i
    TMMeta _ args -> S.fromList args
    TMHead _ args bargs -> S.unions (map boundHeadArg args <> map boundBinderArg bargs)
    TMSplice _ _ args -> S.unions (map boundGlobalsExpr args)
    TMLit _ -> S.empty
  where
    boundHeadArg arg =
      case arg of
        THAObj obj -> boundGlobalsObj obj
        THATm inner -> boundGlobalsExpr inner
    boundBinderArg (TBABody inner) = boundGlobalsDiagram inner
    boundBinderArg (TBAHole _) = S.empty

maxTmScopeExpr :: TermExpr -> Int
maxTmScopeExpr tm =
  case tm of
    TMBound _ -> 0
    TMMeta v _ -> tmvScope v
    TMHead _ args bargs -> maximum (0 : map maxHeadArg args <> map maxBinderArg bargs)
    TMSplice _ _ args -> maximum (0 : map maxTmScopeExpr args)
    TMLit _ -> 0
  where
    maxHeadArg arg =
      case arg of
        THAObj obj -> maxTmScopeObj obj
        THATm inner -> maxTmScopeExpr inner
    maxBinderArg (TBABody inner) = maxTmScopeDiagram inner
    maxBinderArg (TBAHole _) = 0

isPureMetaExpr :: TermExpr -> Bool
isPureMetaExpr tm =
  case tm of
    TMMeta _ _ -> True
    TMBound _ -> False
    TMHead _ _ _ -> False
    TMSplice _ _ _ -> False
    TMLit _ -> False

freeVarsDiagram :: Diagram -> S.Set TmVar
freeVarsDiagram diag =
  S.unions
    [ S.unions (map freeVarsObj (IM.elems (dPortObj diag)))
    , S.unions (map freeVarsObj (dTmCtx diag))
    , S.unions (map edgeVars (IM.elems (dEdges diag)))
    ]
  where
    edgeVars edge =
      case ePayload edge of
        PTmMeta v -> S.singleton v
        PGen _ args bargs ->
          S.unions
            (map codeArgVars args <> map binderArgVars bargs)
        PBox _ inner -> freeVarsDiagram inner
        PFeedback inner -> freeVarsDiagram inner
        PSplice _ _ -> S.empty
        PTmLit _ -> S.empty
        PProvider _ -> S.empty
        PModuleRef _ -> S.empty
        PInternalDrop -> S.empty
    codeArgVars arg =
      case arg of
        CAObj obj -> freeVarsObj obj
        CATm tm -> freeVarsDiagram (unTerm tm)
    binderArgVars barg =
      case barg of
        BAConcrete inner -> freeVarsDiagram inner
        BAMeta _ -> S.empty

boundGlobalsDiagram :: Diagram -> S.Set Int
boundGlobalsDiagram diag =
  S.union direct nested
  where
    inputLocals = IM.fromList (zipWith (\i pid -> (fromPort pid, i)) [0 :: Int ..] (dIn diag))
    direct =
      S.fromList
        [ globalTm
        | localPos <- S.toList usedLocals
        , Just globalTm <- [resolveTmCtxIndex (dTmCtx diag) (dMode diag) localPos]
        ]
    nested = S.unions (map edgeGlobals (IM.elems (dEdges diag)))
    usedLocals = collect S.empty S.empty (dOut diag)
    collect _seen locals [] = locals
    collect seen locals (pid:rest)
      | fromPort pid `S.member` seen = collect seen locals rest
      | otherwise =
          let seen' = S.insert (fromPort pid) seen
           in case IM.lookup (fromPort pid) inputLocals of
                Just localPos ->
                  collect seen' (S.insert localPos locals) rest
                Nothing ->
                  case IM.lookup (fromPort pid) (dProd diag) of
                    Just (Just eid) ->
                      case IM.lookup (fromEdge eid) (dEdges diag) of
                        Just edge ->
                          collect seen' locals (eIns edge <> rest)
                        Nothing ->
                          collect seen' locals rest
                    _ ->
                      collect seen' locals rest
    edgeGlobals edge =
      case ePayload edge of
        PGen _ args bargs ->
          S.unions
            (map codeArgGlobals args <> map binderArgGlobals bargs)
        PBox _ inner -> boundGlobalsDiagram inner
        PFeedback inner -> boundGlobalsDiagram inner
        _ -> S.empty
    codeArgGlobals arg =
      case arg of
        CAObj _ -> S.empty
        CATm tm -> boundGlobalsDiagram (unTerm tm)
    binderArgGlobals barg =
      case barg of
        BAConcrete inner -> boundGlobalsDiagram inner
        BAMeta _ -> S.empty
    fromPort (PortId i) = i
    fromEdge (EdgeId i) = i

maxTmScopeDiagram :: Diagram -> Int
maxTmScopeDiagram diag =
  maximum
    ( 0
        : map tmvScope (S.toList (freeVarsDiagram diag))
    )

boundGlobalsObj :: Obj -> S.Set Int
boundGlobalsObj obj =
  boundGlobalsCode (objCode obj)
  where
    boundGlobalsCode code =
      case code of
        CTMeta _ -> S.empty
        CTCon _ args -> S.unions (map boundGlobalsCodeArg args)
        CTLift _ inner -> boundGlobalsCode inner

    boundGlobalsCodeArg arg =
      case arg of
        CAObj inner -> boundGlobalsObj inner
        CATm tm -> boundGlobalsDiagram (unTerm tm)

maxTmScopeObj :: Obj -> Int
maxTmScopeObj obj =
  maximum
    ( 0
        : map tmvScope (S.toList (freeVarsObj obj))
    )

freeVarsObj :: Obj -> S.Set TmVar
freeVarsObj obj =
  freeVarsCode (objCode obj)
  where
    freeVarsCode code =
      case code of
        CTMeta v -> S.singleton v
        CTCon _ args -> S.unions (map freeVarsCodeArg args)
        CTLift _ inner -> freeVarsCode inner

    freeVarsCodeArg arg =
      case arg of
        CAObj inner -> freeVarsObj inner
        CATm tm -> freeVarsDiagram (unTerm tm)

resolveTmCtxIndex :: [Obj] -> ModeName -> Int -> Maybe Int
resolveTmCtxIndex tmCtx mode localPos =
  case drop localPos [ i | (i, ty) <- zip [0 :: Int ..] tmCtx, objOwnerMode ty == mode ] of
    (globalTm:_) -> Just globalTm
    [] -> Nothing
