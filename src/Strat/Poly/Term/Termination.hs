{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.Termination
  ( checkTerminatingSCT
  , renderSCTDebug
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Term.AST (TermExpr(..), TermHeadArg(..))
import Strat.Poly.Term.RewriteSystem (TRS(..), TRule(..))


data SCRel
  = SCStrict
  | SCWeak
  deriving (Eq, Ord, Show)

data SCGraph = SCGraph
  { scFrom :: GenName
  , scTo :: GenName
  , scFromArity :: Int
  , scToArity :: Int
  , scEdges :: M.Map (Int, Int) SCRel
  } deriving (Eq, Ord, Show)


checkTerminatingSCT :: TRS -> Either Text ()
checkTerminatingSCT trs = do
  base <- buildBaseGraphs trs
  let closure = closureGraphs base
  let idempotent = filter isIdempotent (S.toList closure)
  let bad = filter (not . hasStrictSelfLoop) idempotent
  if null bad
    then Right ()
    else
      Left
        ( "termination not proven by SCT for mode "
            <> renderMode trs
            <> ": found idempotent call graph without strict self-decrease\n"
            <> renderGraphs bad
        )

renderSCTDebug :: TRS -> Text
renderSCTDebug trs =
  case buildBaseGraphs trs of
    Left err -> "SCT build failed: " <> err
    Right base ->
      let closure = closureGraphs base
       in T.unlines
            [ "SCT debug for mode " <> renderMode trs
            , "base graphs:"
            , indent (renderGraphs (S.toList (S.fromList base)))
            , "closure graphs:"
            , indent (renderGraphs (S.toList closure))
            ]


buildBaseGraphs :: TRS -> Either Text [SCGraph]
buildBaseGraphs trs = concat <$> mapM ruleGraphs (trsRules trs)

ruleGraphs :: TRule -> Either Text [SCGraph]
ruleGraphs rule = do
  (f, lhsArgs) <-
    case trLHS rule of
      TMGen fn args -> Right (fn, args)
      _ -> Left ("termination checker requires function-headed lhs in rule " <> trName rule)
  let calls = collectCalls (trRHS rule)
  pure
    [ mkGraph f lhsArgs g qArgs
    | (g, qArgs) <- calls
    ]

collectCalls :: TermExpr -> [(GenName, [TermHeadArg])]
collectCalls tm =
  case tm of
    TMGen f args -> (f, args) : concatMap collectHeadArgCalls args
    TMMeta _ _ -> []
    TMBound _ -> []
    TMLit _ -> []

collectHeadArgCalls :: TermHeadArg -> [(GenName, [TermHeadArg])]
collectHeadArgCalls arg =
  case arg of
    THAObj _ -> []
    THATm tm -> collectCalls tm

mkGraph :: GenName -> [TermHeadArg] -> GenName -> [TermHeadArg] -> SCGraph
mkGraph f lhsArgs g qArgs =
  SCGraph
    { scFrom = f
    , scTo = g
    , scFromArity = length lhsTerms
    , scToArity = length qTerms
    , scEdges = edgeMap
    }
  where
    lhsTerms = [ tm | THATm tm <- lhsArgs ]
    qTerms = [ tm | THATm tm <- qArgs ]

    edgeMap =
      M.fromList
        [ ((i, j), rel)
        | (i, p) <- zip [0 :: Int ..] lhsTerms
        , (j, q) <- zip [0 :: Int ..] qTerms
        , Just rel <- [edgeRel p q]
        ]

    edgeRel tmP tmQ
      | strictSubterm tmQ tmP = Just SCStrict
      | subterm tmQ tmP = Just SCWeak
      | otherwise = Nothing

closureGraphs :: [SCGraph] -> S.Set SCGraph
closureGraphs base = go (S.fromList base)
  where
    go current =
      let composed =
            S.fromList
              [ g
              | g1 <- S.toList current
              , g2 <- S.toList current
              , scTo g1 == scFrom g2
              , Just g <- [composeGraph g1 g2]
              ]
          next = S.union current composed
       in if next == current
            then current
            else go next

composeGraph :: SCGraph -> SCGraph -> Maybe SCGraph
composeGraph g1 g2
  | scToArity g1 /= scFromArity g2 = Nothing
  | otherwise =
      Just
        SCGraph
          { scFrom = scFrom g1
          , scTo = scTo g2
          , scFromArity = scFromArity g1
          , scToArity = scToArity g2
          , scEdges = composeEdges
          }
  where
    composeEdges =
      M.fromList
        [ ((i, k), rel)
        | i <- [0 .. scFromArity g1 - 1]
        , k <- [0 .. scToArity g2 - 1]
        , Just rel <- [composeRelAt i k]
        ]

    composeRelAt i k =
      let rels =
            [ composeRel r1 r2
            | j <- [0 .. scToArity g1 - 1]
            , Just r1 <- [M.lookup (i, j) (scEdges g1)]
            , Just r2 <- [M.lookup (j, k) (scEdges g2)]
            ]
       in if null rels
            then Nothing
            else
              if SCStrict `elem` rels
                then Just SCStrict
                else Just SCWeak

composeRel :: SCRel -> SCRel -> SCRel
composeRel SCStrict _ = SCStrict
composeRel _ SCStrict = SCStrict
composeRel SCWeak SCWeak = SCWeak

isIdempotent :: SCGraph -> Bool
isIdempotent g =
  not (M.null (scEdges g))
    && case composeGraph g g of
      Nothing -> False
      Just gg -> gg == g

hasStrictSelfLoop :: SCGraph -> Bool
hasStrictSelfLoop g
  | scFrom g /= scTo g = True
  | otherwise =
      any
        (\i -> M.lookup (i, i) (scEdges g) == Just SCStrict)
        [0 .. min (scFromArity g) (scToArity g) - 1]

subterm :: TermExpr -> TermExpr -> Bool
subterm needle tm
  | needle == tm = True
  | otherwise =
      case tm of
        TMGen _ args -> any (subtermHeadArg needle) args
        TMMeta _ _ -> False
        TMBound _ -> False
        TMLit _ -> False

subtermHeadArg :: TermExpr -> TermHeadArg -> Bool
subtermHeadArg needle arg =
  case arg of
    THAObj _ -> False
    THATm tm -> subterm needle tm

strictSubterm :: TermExpr -> TermExpr -> Bool
strictSubterm needle tm = needle /= tm && subterm needle tm

renderMode :: TRS -> Text
renderMode trs =
  case trsMode trs of
    -- Show instance of ModeName is stable and sufficient for diagnostics.
    m -> T.pack (show m)

renderGraphs :: [SCGraph] -> Text
renderGraphs gs
  | null gs = "(none)"
  | otherwise = T.intercalate "\n" (map renderGraph gs)

renderGraph :: SCGraph -> Text
renderGraph g =
  renderFun (scFrom g)
    <> "/"
    <> T.pack (show (scFromArity g))
    <> " -> "
    <> renderFun (scTo g)
    <> "/"
    <> T.pack (show (scToArity g))
    <> " {"
    <> T.intercalate ", " (map renderEdge (L.sort (M.toList (scEdges g))))
    <> "}"

renderEdge :: ((Int, Int), SCRel) -> Text
renderEdge ((i, j), rel) =
  T.pack (show i)
    <> symbol
    <> T.pack (show j)
  where
    symbol =
      case rel of
        SCStrict -> "-<"
        SCWeak -> "<="

renderFun :: GenName -> Text
renderFun (GenName t) = t

indent :: Text -> Text
indent t =
  T.unlines
    [ "  " <> line
    | line <- T.lines t
    ]
