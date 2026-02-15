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
import Strat.Poly.TypeExpr (TmFunName(..))
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.Term.RewriteSystem (TRS(..), TRule(..))


data SCRel
  = SCStrict
  | SCWeak
  deriving (Eq, Ord, Show)

data SCGraph = SCGraph
  { scFrom :: TmFunName
  , scTo :: TmFunName
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
      TMFun fn args -> Right (fn, args)
      _ -> Left ("termination checker requires function-headed lhs in rule " <> trName rule)
  let calls = collectCalls (trRHS rule)
  pure
    [ mkGraph f lhsArgs g qArgs
    | (g, qArgs) <- calls
    ]

collectCalls :: TermExpr -> [(TmFunName, [TermExpr])]
collectCalls tm =
  case tm of
    TMFun f args -> (f, args) : concatMap collectCalls args
    TMVar _ -> []
    TMBound _ -> []

mkGraph :: TmFunName -> [TermExpr] -> TmFunName -> [TermExpr] -> SCGraph
mkGraph f lhsArgs g qArgs =
  SCGraph
    { scFrom = f
    , scTo = g
    , scFromArity = length lhsArgs
    , scToArity = length qArgs
    , scEdges = edgeMap
    }
  where
    edgeMap =
      M.fromList
        [ ((i, j), rel)
        | (i, p) <- zip [0 :: Int ..] lhsArgs
        , (j, q) <- zip [0 :: Int ..] qArgs
        , Just rel <- [edgeRel p q]
        ]

    edgeRel p q
      | strictSubterm q p = Just SCStrict
      | subterm q p = Just SCWeak
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
  case composeGraph g g of
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
        TMFun _ args -> any (subterm needle) args
        TMVar _ -> False
        TMBound _ -> False

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

renderFun :: TmFunName -> Text
renderFun (TmFunName t) = t

indent :: Text -> Text
indent t =
  T.unlines
    [ "  " <> line
    | line <- T.lines t
    ]
