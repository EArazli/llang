{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Strat.Meta.DoctrineExpr where

import Strat.Meta.Presentation
import Strat.Meta.RewriteSystem
import Strat.Meta.Rule
import Strat.Meta.Term.Class
import Strat.Meta.Term.Syms
import Strat.Meta.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)

data DocExpr t
  = Atom Text (Presentation t)
  | And (DocExpr t) (DocExpr t)
  | RenameEqs  (M.Map Text Text) (DocExpr t)
  | RenameSyms (M.Map Text Text) (DocExpr t)
  | ShareSyms [(Text, Text)] (DocExpr t)
  deriving (Eq, Show)

atom0 :: Presentation t -> DocExpr t
atom0 pres = Atom (presName pres) pres

infixl 6 .&.
(.&.) :: DocExpr t -> DocExpr t -> DocExpr t
(.&.) = And

q :: Text -> Text -> Text
q ns x = qualifyName ns x

qualifyName :: Text -> Text -> Text
qualifyName ns x = ns <> "." <> x

qualifyEquation :: (SymRenamable t, TermLike t, ScopedVar (Var t)) => Text -> Equation t -> Equation t
qualifyEquation ns e =
  let qn = qualifyName ns (eqName e)
      nsEq = Ns (RuleId qn DirLR) 0
      renameVarsNs = renameVars (setNs nsEq)
      renameSym = qualifyName ns
  in e
      { eqName = qn
      , eqLHS  = renameVarsNs (renameSyms renameSym (eqLHS e))
      , eqRHS  = renameVarsNs (renameSyms renameSym (eqRHS e))
      }

qualifyPresentation :: (SymRenamable t, TermLike t, ScopedVar (Var t)) => Text -> Presentation t -> Presentation t
qualifyPresentation ns pres =
  pres
    { presName = ns
    , presEqs = map (qualifyEquation ns) (presEqs pres)
    }

elabDocExpr :: (SymRenamable t, TermLike t, ScopedVar (Var t)) => DocExpr t -> Either Text (Presentation t)
elabDocExpr expr =
  case expr of
    Atom ns pres -> do
      let p = qualifyPresentation ns pres
      checkUniqueEqNames (presEqs p)
      pure p
    And a b -> do
      pa <- elabDocExpr a
      pb <- elabDocExpr b
      let merged =
            Presentation
              { presName = presName pa <> "&" <> presName pb
              , presEqs = presEqs pa ++ presEqs pb
              }
      checkUniqueEqNames (presEqs merged)
      pure merged
    RenameEqs m e -> do
      p <- elabDocExpr e
      let renameEqName n = M.findWithDefault n n m
      let eqs =
            [ let qn = renameEqName (eqName eq)
                  nsEq = Ns (RuleId qn DirLR) 0
                  renameVarsNs = renameVars (setNs nsEq)
              in eq
                  { eqName = qn
                  , eqLHS = renameVarsNs (eqLHS eq)
                  , eqRHS = renameVarsNs (eqRHS eq)
                  }
            | eq <- presEqs p ]
      checkUniqueEqNames eqs
      pure p { presEqs = eqs }
    RenameSyms m e -> do
      p <- elabDocExpr e
      let renameSym s = M.findWithDefault s s m
      let eqs =
            [ eq
                { eqLHS = renameSyms renameSym (eqLHS eq)
                , eqRHS = renameSyms renameSym (eqRHS eq)
                }
            | eq <- presEqs p
            ]
      pure p { presEqs = eqs }
    ShareSyms pairs e -> do
      p <- elabDocExpr e
      let allSyms = symsInPresentation p
      let names = [n | (a, b) <- pairs, n <- [a, b]]
      case firstUnknown allSyms names of
        Just bad -> Left ("Unknown symbol in ShareSyms: " <> bad)
        Nothing -> do
          let arities = symAritiesInPresentation p
          case firstArityMismatch arities (shareComponents pairs) of
            Just bad -> Left ("Arity mismatch in ShareSyms: " <> bad)
            Nothing -> do
              let repMap = buildShareMap pairs
              let renameSym s = M.findWithDefault s s repMap
              let eqs =
                    [ eq
                        { eqLHS = renameSyms renameSym (eqLHS eq)
                        , eqRHS = renameSyms renameSym (eqRHS eq)
                        }
                    | eq <- presEqs p
                    ]
              pure p { presEqs = eqs }

compileDocExpr :: (SymRenamable t, TermLike t, ScopedVar (Var t)) => RewritePolicy -> DocExpr t -> Either Text (RewriteSystem t)
compileDocExpr pol expr = elabDocExpr expr >>= compileRewriteSystem pol

checkUniqueEqNames :: [Equation t] -> Either Text ()
checkUniqueEqNames eqs =
  case findDuplicate (map eqName eqs) of
    Nothing -> Right ()
    Just dup -> Left ("Duplicate equation name: " <> dup)
  where
    findDuplicate names = go S.empty names
    go _ [] = Nothing
    go seen (n : ns)
      | n `S.member` seen = Just n
      | otherwise = go (S.insert n seen) ns

symsInPresentation :: SymRenamable t => Presentation t -> S.Set Text
symsInPresentation pres =
  S.unions
    [ syms (eqLHS eq) `S.union` syms (eqRHS eq)
    | eq <- presEqs pres
    ]

symAritiesInPresentation :: SymRenamable t => Presentation t -> M.Map Text (S.Set Int)
symAritiesInPresentation pres =
  M.unionsWith S.union
    [ M.unionWith S.union (symArities (eqLHS eq)) (symArities (eqRHS eq))
    | eq <- presEqs pres
    ]

firstUnknown :: S.Set Text -> [Text] -> Maybe Text
firstUnknown known names = go names
  where
    go [] = Nothing
    go (n : ns)
      | n `S.member` known = go ns
      | otherwise = Just n

buildShareMap :: [(Text, Text)] -> M.Map Text Text
buildShareMap pairs =
  M.fromList
    [ (n, rep)
    | comp <- components
    , let rep = S.findMin comp
    , n <- S.toList comp
    ]
  where
    nodes = S.fromList [n | (a, b) <- pairs, n <- [a, b]]
    adj = buildAdj nodes pairs
    components = connectedComponents nodes adj

shareComponents :: [(Text, Text)] -> [S.Set Text]
shareComponents pairs =
  let nodes = S.fromList [n | (a, b) <- pairs, n <- [a, b]]
      adj = buildAdj nodes pairs
  in connectedComponents nodes adj

firstArityMismatch :: M.Map Text (S.Set Int) -> [S.Set Text] -> Maybe Text
firstArityMismatch arities comps = go comps
  where
    go [] = Nothing
    go (c : cs) =
      case aritySets c of
        [] -> go cs
        (s : ss) ->
          if all (== s) ss
            then go cs
            else Just (S.findMin c)
    aritySets c = [M.findWithDefault S.empty n arities | n <- S.toList c]

buildAdj :: S.Set Text -> [(Text, Text)] -> M.Map Text (S.Set Text)
buildAdj nodes pairs =
  foldl addEdge initial pairs
  where
    initial = M.fromList [(n, S.empty) | n <- S.toList nodes]
    addEdge m (a, b) =
      let m1 = M.insertWith S.union a (S.singleton b) m
      in M.insertWith S.union b (S.singleton a) m1

connectedComponents :: S.Set Text -> M.Map Text (S.Set Text) -> [S.Set Text]
connectedComponents nodes adj = go nodes S.empty []
  where
    go remaining visited comps
      | S.null remaining = reverse comps
      | otherwise =
          let start = S.findMin remaining
              (comp, visited') = dfs [start] S.empty visited
              remaining' = remaining `S.difference` comp
          in go remaining' visited' (comp : comps)

    dfs [] comp visited = (comp, visited)
    dfs (n : ns) comp visited
      | n `S.member` visited = dfs ns comp visited
      | otherwise =
          let neighbors = S.toList (M.findWithDefault S.empty n adj)
              visited' = S.insert n visited
              comp' = S.insert n comp
          in dfs (neighbors ++ ns) comp' visited'
