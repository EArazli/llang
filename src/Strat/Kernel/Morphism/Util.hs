{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Morphism.Util
  ( identityMorphism
  , symbolMapMorphism
  , composeMorphism
  , isSymbolMap
  ) where

import Strat.Kernel.Morphism
import Strat.Kernel.Presentation
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term (TypeError(..), mkOp, mkVar)
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Data.Text (Text)

identityMorphism :: Presentation -> Morphism
identityMorphism pres =
  case symbolMapMorphism pres pres sortMap opMap of
    Left err -> error (show err)
    Right mor -> mor { morName = "identity" }
  where
    sorts = M.keys (sigSortCtors (presSig pres))
    ops = M.keys (sigOps (presSig pres))
    sortMap = M.fromList [ (s, s) | s <- sorts ]
    opMap = M.fromList [ (o, o) | o <- ops ]

symbolMapMorphism :: Presentation -> Presentation -> M.Map SortName SortName -> M.Map OpName OpName -> Either Text Morphism
symbolMapMorphism src tgt sortMap opMap = do
  ensureSortCoverage
  ensureOpCoverage
  opMap' <- buildOpMap
  pure Morphism
    { morName = "symbolMap"
    , morSrc = src
    , morTgt = tgt
    , morSortMap = sortMap
    , morOpMap = opMap'
    , morCheck = MorphismCheck { mcPolicy = UseStructuralAsBidirectional, mcFuel = 200 }
    }
  where
    sigSrc = presSig src
    sigTgt = presSig tgt

    ensureSortCoverage =
      mapM_ checkSort (M.keys (sigSortCtors sigSrc))
    checkSort name =
      case M.lookup name sortMap of
        Nothing -> Left ("Missing sort mapping: " <> renderSortName name)
        Just tgtName ->
          if M.member tgtName (sigSortCtors sigTgt)
            then Right ()
            else Left ("Unknown target sort: " <> renderSortName tgtName)

    ensureOpCoverage =
      mapM_ checkOp (M.keys (sigOps sigSrc))
    checkOp name =
      case M.lookup name opMap of
        Nothing -> Left ("Missing op mapping: " <> renderOpName name)
        Just tgtName ->
          if M.member tgtName (sigOps sigTgt)
            then Right ()
            else Left ("Unknown target op: " <> renderOpName tgtName)

    buildOpMap =
      fmap M.fromList $
        mapM buildInterp (M.elems (sigOps sigSrc))

    buildInterp decl = do
      let op = opName decl
      case M.lookup op opMap of
        Nothing -> Left ("Missing op mapping: " <> renderOpName op)
        Just opTgt -> do
          let teleSrc = opTele decl
          let teleTgt = map (mapBinderSort sortMap opMap) teleSrc
          args <- mapM argFromBinder teleTgt
          rhs <- mkOp sigTgt opTgt args
            `mapLeft` (\e -> "symbol map failed to construct op: " <> renderOpName op <> " (" <> renderTypeError e <> ")")
          pure (op, OpInterp { oiTele = teleTgt, oiRhs = rhs })

    argFromBinder b =
      case b of
        Binder v s -> Right (mkVar s v)

    mapLeft (Left e) f = Left (f e)
    mapLeft (Right v) _ = Right v

composeMorphism :: Morphism -> Morphism -> Either Text Morphism
composeMorphism m1 m2 =
  if morTgt m1 /= morSrc m2
    then Left "Cannot compose morphisms: target/source mismatch"
    else do
      opMap' <- buildOpMap
      pure Morphism
        { morName = morName m1 <> ";" <> morName m2
        , morSrc = morSrc m1
        , morTgt = morTgt m2
        , morSortMap = sortMap'
        , morOpMap = opMap'
        , morCheck = MorphismCheck { mcPolicy = UseStructuralAsBidirectional, mcFuel = 200 }
        }
  where
    sigSrc = presSig (morSrc m1)
    sortMap' =
      M.fromList
        [ (s, applySortName m2 (applySortName m1 s))
        | s <- M.keys (sigSortCtors sigSrc)
        ]

    applySortName mor s = M.findWithDefault s s (morSortMap mor)

    buildOpMap =
      fmap M.fromList $
        mapM buildInterp (M.keys (sigOps sigSrc))

    buildInterp op =
      case M.lookup op (morOpMap m1) of
        Nothing -> Left ("Missing op mapping in composed morphism: " <> renderOpName op)
        Just interp1 -> do
          let teleTgt = map (mapBinderSortWith m2) (oiTele interp1)
          let rhs = applyMorphismTerm m2 (oiRhs interp1)
          pure (op, OpInterp { oiTele = teleTgt, oiRhs = rhs })

    mapBinderSortWith mor b =
      b { bSort = applyMorphismSort mor (bSort b) }

isSymbolMap :: Morphism -> Either Text (M.Map OpName OpName)
isSymbolMap mor = do
  opPairs <- mapM checkOp (M.keys (sigOps (presSig (morSrc mor))))
  pure (M.fromList opPairs)
  where
    checkOp op =
      case M.lookup op (morOpMap mor) of
        Nothing -> Left ("Missing op mapping: " <> renderOpName op)
        Just interp ->
          case termNode (oiRhs interp) of
            TOp op' args ->
              if argsMatch interp args
                then Right (op, op')
                else Left ("Non-symbol op mapping for " <> renderOpName op)
            _ -> Left ("Non-symbol op mapping for " <> renderOpName op)

    argsMatch interp args =
      let vars = [ v | Binder v _ <- oiTele interp ]
      in length args == length vars
         && and (zipWith argIsVar args vars)

    argIsVar tm v =
      case termNode tm of
        TVar v' -> v' == v
        _ -> False

mapBinderSort :: M.Map SortName SortName -> M.Map OpName OpName -> Binder -> Binder
mapBinderSort sortMap opMap b =
  b { bSort = mapSort sortMap opMap (bSort b) }

mapSort :: M.Map SortName SortName -> M.Map OpName OpName -> Sort -> Sort
mapSort sortMap opMap (Sort name idx) =
  Sort (mapSortName sortMap name) (map (mapTerm sortMap opMap) idx)

mapTerm :: M.Map SortName SortName -> M.Map OpName OpName -> Term -> Term
mapTerm sortMap opMap tm =
  Term
    { termSort = mapSort sortMap opMap (termSort tm)
    , termNode =
        case termNode tm of
          TVar v -> TVar v
          TOp op args -> TOp (mapOpName opMap op) (map (mapTerm sortMap opMap) args)
    }

mapSortName :: M.Map SortName SortName -> SortName -> SortName
mapSortName m name = M.findWithDefault name name m

mapOpName :: M.Map OpName OpName -> OpName -> OpName
mapOpName m name = M.findWithDefault name name m

renderOpName :: OpName -> Text
renderOpName (OpName t) = t

renderSortName :: SortName -> Text
renderSortName (SortName t) = t

renderTypeError :: TypeError -> Text
renderTypeError err = case err of
  UnknownOp op -> "unknown op " <> renderOpName op
  ArityMismatch op expected actual ->
    "arity mismatch for " <> renderOpName op <> " (" <> tshow expected <> " vs " <> tshow actual <> ")"
  ArgSortMismatch op ix expected actual ->
    "arg sort mismatch for " <> renderOpName op <> " at " <> tshow ix <> " (" <> tshow expected <> " vs " <> tshow actual <> ")"

tshow :: Show a => a -> Text
tshow = T.pack . show
