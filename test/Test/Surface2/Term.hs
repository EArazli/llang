{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Test.Surface2.Term
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Strat.Surface2.Term

tests :: TestTree
tests =
  testGroup
    "Surface2.Term"
    [ testCase "subst0 (SBound 0) t == t" $
        case subst0 (SBound (Ix 0)) sampleTerm of
          Left err -> assertFailure (show err)
          Right tm -> tm @?= sampleTerm
    , QC.testProperty "subst0 keeps term when substituting bound 0 by itself" $
        \t -> subst0 (SBound (Ix 0)) t == Right t
    , QC.testProperty "subst0 replaces bound 0" $
        \t -> subst0 t (SBound (Ix 0)) == Right t
    ]

sampleTerm :: STerm
sampleTerm =
  SCon (Con2Name "Lam")
    [ SArg [SFree "A"] (SBound (Ix 0)) ]

instance Arbitrary STerm where
  arbitrary = sized (genTerm 0)

genTerm :: Int -> Int -> Gen STerm
genTerm depth n
  | n <= 0 = oneof (baseTerms depth)
  | otherwise =
      frequency
        [ (3, oneof (baseTerms depth))
        , (2, do
              arity <- chooseInt (0, 2)
              args <- vectorOf arity (genArg depth (n - 1))
              pure (SCon (Con2Name "C") args))
        ]

baseTerms :: Int -> [Gen STerm]
baseTerms depth =
  [ pure (SFree "x")
  , pure (SFree "y")
  , if depth > 0 then SBound . Ix <$> chooseInt (0, depth - 1) else pure (SFree "z")
  ]

genArg :: Int -> Int -> Gen SArg
genArg depth n = do
  binderCount <- chooseInt (0, 2)
  let depth' = depth + binderCount
  binders <- vectorOf binderCount (genTerm depth n)
  body <- genTerm depth' n
  pure (SArg binders body)
