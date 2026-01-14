{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.CriticalPairsDependent
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.CriticalPairs
import Strat.Kernel.Presentation
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Data.Text (Text)

tests :: TestTree
tests =
  testGroup
    "Kernel.CriticalPairsDependent"
    [ testCase "dependent CP exists" testDependentCPExists
    , testCase "dependent CP soundness" testDependentCPSoundness
    ]

objName :: SortName
objName = SortName "Obj"

homName :: SortName
homName = SortName "Hom"

objSort :: Sort
objSort = Sort objName []

homSort :: Term -> Term -> Sort
homSort a b = Sort homName [a, b]

sigDep :: Signature
sigDep =
  Signature
    { sigSortCtors =
        M.fromList
          [ (objName, SortCtor objName [])
          , (homName, SortCtor homName [objSort, objSort])
          ]
    , sigOps =
        M.fromList
          [ (OpName "a", OpDecl (OpName "a") [] objSort)
          , (OpName "b", OpDecl (OpName "b") [] objSort)
          , (OpName "id", idDecl)
          , (OpName "k", kDecl)
          , (OpName "p", pDecl)
          ]
    }
  where
    idDecl =
      let v = Var (ScopeId "op:id") 0
          x = mkVar objSort v
      in OpDecl (OpName "id") [Binder v objSort] (homSort x x)

    kDecl =
      let v = Var (ScopeId "op:k") 0
          x = mkVar objSort v
      in OpDecl (OpName "k") [Binder v objSort] (homSort x x)

    pDecl =
      let vx = Var (ScopeId "op:p") 0
          vh = Var (ScopeId "op:p") 1
          x = mkVar objSort vx
          hSort = homSort x x
      in OpDecl (OpName "p") [Binder vx objSort, Binder vh hSort] objSort

mkTerm :: Text -> [Term] -> Term
mkTerm name args =
  case mkOp sigDep (OpName name) args of
    Left err -> error (show err)
    Right t -> t

mkEq1 :: Equation
mkEq1 =
  let scope = ScopeId "eq:r1"
      vx = Var scope 0
      x = mkVar objSort vx
  in Equation
      { eqName = "r1"
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = mkTerm "id" [x]
      , eqRHS = mkTerm "k" [x]
      }

mkEq2 :: Equation
mkEq2 =
  let scope = ScopeId "eq:r2"
      vy = Var scope 0
      y = mkVar objSort vy
      idy = mkTerm "id" [y]
      ky = mkTerm "k" [y]
  in Equation
      { eqName = "r2"
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vy objSort]
      , eqLHS = mkTerm "p" [y, idy]
      , eqRHS = mkTerm "p" [y, ky]
      }

mkRS :: RewriteSystem
mkRS =
  case compileRewriteSystem UseAllOriented (Presentation "P" sigDep [mkEq1, mkEq2]) of
    Left err -> error (show err)
    Right rs -> rs

findDepCP :: [CriticalPair] -> Maybe CriticalPair
findDepCP =
  L.find (\cp -> cpRule1 cp == RuleId "r1" DirLR && cpRule2 cp == RuleId "r2" DirLR && cpPosIn2 cp == [1])

testDependentCPExists :: Assertion
testDependentCPExists = do
  case criticalPairs CP_All mkRS of
    Left err -> assertFailure (show err)
    Right cps ->
      case findDepCP cps of
        Nothing -> assertFailure "expected dependent critical pair"
        Just _ -> pure ()

testDependentCPSoundness :: Assertion
testDependentCPSoundness = do
  case criticalPairs CP_All mkRS of
    Left err -> assertFailure (show err)
    Right cps ->
      case findDepCP cps of
        Nothing -> assertFailure "expected dependent critical pair"
        Just cp -> do
          let reds = rewriteOnce mkRS (cpPeak cp)
          let leftStep =
                L.find
                  (\r -> stepRule (redexStep r) == cpRule1 cp && stepPos (redexStep r) == cpPosIn2 cp && redexTo r == cpLeft cp)
                  reds
          let rightStep =
                L.find
                  (\r -> stepRule (redexStep r) == cpRule2 cp && stepPos (redexStep r) == [] && redexTo r == cpRight cp)
                  reds
          assertBool "expected left step from peak" (leftStep /= Nothing)
          assertBool "expected right step from peak" (rightStep /= Nothing)
