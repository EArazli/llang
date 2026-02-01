{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Coerce
  ( findUniqueCoercionPath
  , applyCoercionPath
  , coerceDiagramTo
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Seq
import qualified Data.List as List
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Morphism (Morphism(..), applyMorphismDiagram)


findUniqueCoercionPath :: ModuleEnv -> Text -> Text -> Either Text [Text]
findUniqueCoercionPath env srcName tgtName
  | srcName == tgtName = Right []
  | otherwise =
      case results of
        [] -> Left ("no coercion path from " <> srcName <> " to " <> tgtName)
        [p] -> Right p
        ps -> Left ("ambiguous coercion paths from " <> srcName <> " to " <> tgtName <> ": " <> renderPaths ps)
  where
    morphs = [ m | m <- M.elems (meMorphisms env), morIsCoercion m ]
    adj0 = M.fromListWith (<>) [ (dName (morSrc m), [(morName m, dName (morTgt m))]) | m <- morphs ]
    adj = M.map (List.sortOn fst) adj0
    results = bfs adj

    bfs graph = go (Seq.singleton (srcName, [])) (M.singleton srcName 0) Nothing []
      where
        go queue visited foundDist acc =
          case Seq.viewl queue of
            Seq.EmptyL -> acc
            (node, path) Seq.:< rest ->
              let dist = length path
              in case foundDist of
                Just d | dist > d -> go rest visited foundDist acc
                _ ->
                  if node == tgtName
                    then
                      let found' = Just (maybe dist id foundDist)
                      in if maybe True (== dist) foundDist
                        then go rest visited found' (path:acc)
                        else go rest visited foundDist acc
                    else
                      let (queue', visited') = expand node path dist rest visited foundDist
                      in go queue' visited' foundDist acc

        expand node path dist queue visited foundDist =
          let nexts = M.findWithDefault [] node graph
          in foldl (enqueue path dist foundDist) (queue, visited) nexts

        enqueue path dist foundDist (queue, visited) (morName, next) =
          let newDist = dist + 1
          in case foundDist of
            Just d | newDist > d -> (queue, visited)
            _ ->
              case M.lookup next visited of
                Nothing ->
                  (queue Seq.|> (next, path <> [morName]), M.insert next newDist visited)
                Just prev ->
                  if newDist <= prev
                    then (queue Seq.|> (next, path <> [morName]), M.insert next newDist visited)
                    else (queue, visited)

    renderPaths ps =
      let rendered = map renderPath ps
          sorted = List.sort rendered
      in T.intercalate "; " sorted

    renderPath path =
      "[" <> T.intercalate ", " path <> "]"

applyCoercionPath :: ModuleEnv -> Doctrine -> Diagram -> [Text] -> Either Text (Doctrine, Diagram)
applyCoercionPath env doc diag names =
  foldl step (Right (doc, diag)) names
  where
    step acc name = do
      (doc0, diag0) <- acc
      mor <- lookupMorphism env name
      if not (morIsCoercion mor)
        then Left ("coercion path includes non-coercion morphism: " <> name)
        else if dName (morSrc mor) /= dName doc0
          then Left ("coercion morphism source mismatch for " <> name)
          else do
            diag' <- applyMorphismDiagram mor diag0
            pure (morTgt mor, diag')

coerceDiagramTo :: ModuleEnv -> Doctrine -> Diagram -> Text -> Either Text (Doctrine, Diagram)
coerceDiagramTo env doc diag targetName =
  if dName doc == targetName
    then Right (doc, diag)
    else do
      path <- findUniqueCoercionPath env (dName doc) targetName
      (doc', diag') <- applyCoercionPath env doc diag path
      if dName doc' == targetName
        then Right (doc', diag')
        else Left ("coercion path did not reach target doctrine " <> targetName)

lookupMorphism :: ModuleEnv -> Text -> Either Text Morphism
lookupMorphism env name =
  case M.lookup name (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> name)
    Just mor -> Right mor
