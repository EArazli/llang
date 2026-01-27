{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.CoreTerm
  ( elabCoreTerm
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Strat.Kernel.Syntax (Term(..), TermNode(..), Var(..), Sort(..), SortName(..), OpName(..), ScopeId(..), Binder(..))
import Strat.Kernel.FreeTele (freeTeleOfTerm)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..))
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr, TypeName(..), TyVar(..))
import qualified Strat.Poly.TypeExpr as Ty
import Strat.Poly.UnifyTy (unifyCtx, applySubstCtx, composeSubst)
import Strat.Poly.Graph
  ( Diagram(..)
  , EdgePayload(..)
  , PortId
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , diagramPortType
  , validateDiagram
  )
import Strat.Poly.Diagram (compD, idD)


data VarState = VarState
  { vsPort :: PortId
  , vsType :: TypeExpr
  , vsRemaining :: Int
  } deriving (Eq, Show)

elabCoreTerm :: Doctrine -> ModeName -> Term -> Either Text Diagram
elabCoreTerm doc mode term = do
  (counts, sorts) <- countTermVars doc mode term
  let useOrder = firstUseOrder doc mode term
  let ctxOrder = filter (`M.member` counts) (ctxOrderFrom term)
  ctxTypes <- mapM (varType sorts) ctxOrder
  permuteDiag <- buildPermutation doc mode (zip ctxOrder ctxTypes) useOrder
  let used = filter (`M.member` counts) useOrder
  usedTypes <- mapM (varType sorts) used
  termDiag <- compileCore doc mode used usedTypes counts term
  if null ctxOrder
    then pure termDiag
    else compD termDiag permuteDiag
  where
    ctxOrderFrom t =
      case freeTeleOfTerm t of
        Left _ -> []
        Right binders -> [ v | b <- binders, let v = bVar b ]
    varType sorts v =
      case M.lookup v sorts of
        Nothing -> Left "core term: missing variable sort"
        Just s -> sortToType doc mode s

countTermVars :: Doctrine -> ModeName -> Term -> Either Text (M.Map Var Int, M.Map Var Sort)
countTermVars doc mode term = do
  (_, counts, sorts) <- go True (S.empty, M.empty, M.empty) term
  pure (counts, sorts)
  where
    go isTerm (seen, counts, sorts) t =
      case termNode t of
        TVar v ->
          if isTerm
            then do
              let s = termSort t
              case M.lookup v sorts of
                Nothing -> Right ()
                Just s' | s' == s -> Right ()
                Just _ -> Left "core term: variable sort mismatch"
              let counts' = M.insertWith (+) v 1 counts
              let sorts' = M.insert v s sorts
              Right (S.insert v seen, counts', sorts')
            else Right (seen, counts, sorts)
        TOp name args ->
          case lookupGen doc mode (GenName (opText name)) of
            Nothing ->
              -- type-level term, skip
              Right (seen, counts, sorts)
            Just gen -> do
              let domLen = length (gdDom gen)
              if length args < domLen
                then Left "core term: generator arity mismatch"
                else do
                  let (tyArgs, termArgs) = splitAt (length args - domLen) args
                  (seen1, counts1, sorts1) <- foldlM (go False) (seen, counts, sorts) tyArgs
                  foldlM (go True) (seen1, counts1, sorts1) termArgs

firstUseOrder :: Doctrine -> ModeName -> Term -> [Var]
firstUseOrder doc mode term = reverse (snd (go True (S.empty, []) term))
  where
    go isTerm (seen, acc) t =
      case termNode t of
        TVar v ->
          if isTerm && v `S.notMember` seen
            then (S.insert v seen, v:acc)
            else (seen, acc)
        TOp name args ->
          case lookupGen doc mode (GenName (opText name)) of
            Nothing -> (seen, acc)
            Just gen ->
              let domLen = length (gdDom gen)
              in if length args < domLen
                then (seen, acc)
                else
                  let (tyArgs, termArgs) = splitAt (length args - domLen) args
                      (seen1, acc1) = foldl (go False) (seen, acc) tyArgs
                  in foldl (go True) (seen1, acc1) termArgs

compileCore :: Doctrine -> ModeName -> [Var] -> [TypeExpr] -> M.Map Var Int -> Term -> Either Text Diagram
compileCore doc mode vars types counts term = do
  let (ports, diag0) = allocPorts types (emptyDiagram mode)
  let env0 = M.fromList
        [ (v, VarState pid ty (M.findWithDefault 0 v counts))
        | (v, pid, ty) <- zip3 vars ports types
        ]
  (diag1, env1, outPort) <- compileTerm doc mode env0 diag0 term
  diag2 <- dropUnused doc mode env1 diag1
  let diag3 = diag2 { dIn = ports, dOut = [outPort] }
  validateDiagram diag3
  pure diag3

compileTerm :: Doctrine -> ModeName -> M.Map Var VarState -> Diagram -> Term -> Either Text (Diagram, M.Map Var VarState, PortId)
compileTerm doc mode env diag term =
  case termNode term of
    TVar v -> useVar doc mode env diag v
    TOp name args -> do
      gen <- maybe (Left ("core term: unknown generator " <> opText name)) Right (lookupGen doc mode (GenName (opText name)))
      let domLen = length (gdDom gen)
      if length args < domLen
        then Left "core term: generator arity mismatch"
        else do
          let (tyArgsTerms, termArgs) = splitAt (length args - domLen) args
          tyArgs <- mapM (termToType doc mode) tyArgsTerms
          let tyVars = gdTyVars gen
          if length tyArgs /= length tyVars
            then Left "core term: type argument mismatch"
            else do
              let subst0 = M.fromList (zip tyVars tyArgs)
              (diag', env', argPorts) <- compileArgs doc mode env diag termArgs
              argTypes <- mapM (requirePortType diag') argPorts
              let dom = applySubstCtx subst0 (gdDom gen)
              subst1 <- unifyCtx dom argTypes
              let subst = composeSubst subst1 subst0
              let cod = applySubstCtx subst (gdCod gen)
              if length cod /= 1
                then Left "core term: generator must have single output"
                else do
                  let (outPort, diag'') = freshPort (head cod) diag'
                  diag''' <- addEdgePayload (PGen (gdName gen)) argPorts [outPort] diag''
                  pure (diag''', env', outPort)

compileArgs :: Doctrine -> ModeName -> M.Map Var VarState -> Diagram -> [Term] -> Either Text (Diagram, M.Map Var VarState, [PortId])
compileArgs _ _ env diag [] = Right (diag, env, [])
compileArgs doc mode env diag (t:ts) = do
  (diag', env', p) <- compileTerm doc mode env diag t
  (diag'', env'', ps) <- compileArgs doc mode env' diag' ts
  pure (diag'', env'', p:ps)

useVar :: Doctrine -> ModeName -> M.Map Var VarState -> Diagram -> Var -> Either Text (Diagram, M.Map Var VarState, PortId)
useVar doc mode env diag v =
  case M.lookup v env of
    Nothing -> Left "core term: unknown variable"
    Just st ->
      case vsRemaining st of
        0 -> Left "core term: variable not in scope"
        1 -> Right (diag, M.delete v env, vsPort st)
        n -> do
          dupGen <- requireGen doc mode "dup"
          (p1, p2, diag') <- dupPort dupGen diag (vsPort st) (vsType st)
          let env' = M.insert v st { vsPort = p2, vsRemaining = n - 1 } env
          pure (diag', env', p1)


dropUnused :: Doctrine -> ModeName -> M.Map Var VarState -> Diagram -> Either Text Diagram
dropUnused doc mode env diag = do
  dropGen <- requireGen doc mode "drop"
  ensureDropShape dropGen
  let dropOne acc st = do
        d <- acc
        if vsRemaining st == 0
          then Right d
          else addEdgePayload (PGen (gdName dropGen)) [vsPort st] [] d
  foldl dropOne (Right diag) (M.elems env)

buildPermutation :: Doctrine -> ModeName -> [(Var, TypeExpr)] -> [Var] -> Either Text Diagram
buildPermutation doc mode ctxVars useVars = do
  let ctxOrder = map fst ctxVars
  if ctxOrder == useVars
    then pure (idD mode (map snd ctxVars))
    else do
      let used = filter (`elem` useVars) ctxOrder
      if not (all (`elem` used) useVars)
        then Left "core term: permutation mismatch"
        else do
          let types = map snd ctxVars
          let (ports, diag0) = allocPorts types (emptyDiagram mode)
          let order0 = zip ctxOrder ports
          (diag1, order1) <- reorder diag0 order0 (zip [0..] useVars)
          diag2 <- dropUnusedPorts doc mode diag1 order1 useVars
          let outPorts = [ p | (v, p) <- order1, v `elem` useVars ]
          let diag3 = diag2 { dIn = ports, dOut = outPorts }
          validateDiagram diag3
          pure diag3
  where
    reorder diag order [] = Right (diag, order)
    reorder diag order ((target, v):vs) = do
      idx <- findIndex v order
      (diag', order') <- bubble diag order idx target
      reorder diag' order' vs

    bubble diag order idx target
      | idx <= target = Right (diag, order)
      | otherwise = do
          let (vPrev, pPrev) = order !! (idx - 1)
          let (vCurr, pCurr) = order !! idx
          (diag', pOut1, pOut2) <- applySwap doc mode diag pPrev pCurr
          let order' =
                take (idx - 1) order
                <> [(vCurr, pOut1), (vPrev, pOut2)]
                <> drop (idx + 1) order
          bubble diag' order' (idx - 1) target

    dropUnusedPorts _ _ diag [] _ = Right diag
    dropUnusedPorts doc' mode' diag order usedVars = do
      let unused = [ (v, p) | (v, p) <- order, v `notElem` usedVars ]
      if null unused
        then Right diag
        else do
          dropGen <- requireGen doc' mode' "drop"
          ensureDropShape dropGen
          foldl (\acc (_, p) -> do d <- acc; addEdgePayload (PGen (gdName dropGen)) [p] [] d) (Right diag) unused

allocPorts :: [TypeExpr] -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
      (pids, diag2) = allocPorts rest diag1
  in (pid : pids, diag2)

applySwap :: Doctrine -> ModeName -> Diagram -> PortId -> PortId -> Either Text (Diagram, PortId, PortId)
applySwap doc mode diag p1 p2 = do
  swapGen <- requireGen doc mode "swap"
  t1 <- requirePortType diag p1
  t2 <- requirePortType diag p2
  let (pOut1, diag1) = freshPort t2 diag
  let (pOut2, diag2) = freshPort t1 diag1
  diag3 <- addEdgePayload (PGen (gdName swapGen)) [p1, p2] [pOut1, pOut2] diag2
  pure (diag3, pOut1, pOut2)

requireGen :: Doctrine -> ModeName -> Text -> Either Text GenDecl
requireGen doc mode name =
  case lookupGen doc mode (GenName name) of
    Nothing -> Left ("core term: missing generator " <> name)
    Just g -> Right g

ensureDupShape :: GenDecl -> Either Text ()
ensureDupShape gen =
  case (gdDom gen, gdCod gen, gdTyVars gen) of
    ([Ty.TVar v1], [Ty.TVar v2, Ty.TVar v3], _) | v1 == v2 && v1 == v3 -> Right ()
    _ -> Left "core term: dup has wrong type"

ensureDropShape :: GenDecl -> Either Text ()
ensureDropShape gen =
  case (gdDom gen, gdCod gen) of
    ([Ty.TVar _], []) -> Right ()
    _ -> Left "core term: drop has wrong type"

dupPort :: GenDecl -> Diagram -> PortId -> TypeExpr -> Either Text (PortId, PortId, Diagram)
dupPort dupGen diag inPort ty = do
  ensureDupShape dupGen
  let (p1, diag1) = freshPort ty diag
  let (p2, diag2) = freshPort ty diag1
  diag3 <- addEdgePayload (PGen (gdName dupGen)) [inPort] [p1, p2] diag2
  pure (p1, p2, diag3)

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "core term: missing port type"
    Just ty -> Right ty

lookupGen :: Doctrine -> ModeName -> GenName -> Maybe GenDecl
lookupGen doc mode name =
  M.lookup mode (dGens doc) >>= M.lookup name

sortToType :: Doctrine -> ModeName -> Sort -> Either Text TypeExpr
sortToType doc mode (Sort (SortName name) idxTerms) = do
  let tname = TypeName (stripQual name)
  arity <- requireTypeCtor doc mode tname
  args <- mapM (termToType doc mode) idxTerms
  if arity /= length args
    then Left "core term: sort arity mismatch"
    else Right (Ty.TCon tname args)

termToType :: Doctrine -> ModeName -> Term -> Either Text TypeExpr
termToType doc mode t =
  case termNode t of
    TVar v -> Right (Ty.TVar (varToTyVar v))
    TOp (OpName name) args -> do
      let tname = TypeName (stripQual name)
      arity <- requireTypeCtor doc mode tname
      args' <- mapM (termToType doc mode) args
      if arity /= length args'
        then Left "core term: type constructor arity mismatch"
        else Right (Ty.TCon tname args')

requireTypeCtor :: Doctrine -> ModeName -> TypeName -> Either Text Int
requireTypeCtor doc mode name =
  case M.lookup mode (dTypes doc) >>= M.lookup name of
    Nothing -> Left ("core term: unknown type constructor " <> renderTypeName name)
    Just a -> Right a

varToTyVar :: Var -> TyVar
varToTyVar (Var scope ix) =
  TyVar (renderScope scope <> "#" <> T.pack (show ix))

renderScope :: ScopeId -> Text
renderScope (ScopeId t) = t

renderTypeName :: TypeName -> Text
renderTypeName (TypeName t) = t

opText :: OpName -> Text
opText (OpName t) = stripQual t

stripQual :: Text -> Text
stripQual t =
  case reverse (T.splitOn "." t) of
    (x:_) -> x
    [] -> t

findIndex :: Eq a => a -> [(a, b)] -> Either Text Int
findIndex x xs = go 0 xs
  where
    go _ [] = Left "core term: permutation element missing"
    go i ((y,_):rest)
      | x == y = Right i
      | otherwise = go (i + 1) rest

foldlM :: (a -> b -> Either Text a) -> a -> [b] -> Either Text a
foldlM _ acc [] = Right acc
foldlM f acc (x:xs) = do
  acc' <- f acc x
  foldlM f acc' xs
