{-# LANGUAGE OverloadedStrings #-}
module Test.Surface2.Pattern
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Surface2.Term
import Strat.Surface2.Pattern

tests :: TestTree
tests =
  testGroup
    "Surface2.Pattern"
    [ testCase "match meta no args" $ do
        let p = PMeta (MVar "M") []
        let t = SFree "x"
        case matchPTerm p t of
          Nothing -> assertFailure "expected match"
          Just s -> applySubstPTerm s p @?= t
    , testCase "match meta bound arg" $ do
        let p = PMeta (MVar "M") [Ix 0]
        let t = SBound (Ix 0)
        case matchPTerm p t of
          Nothing -> assertFailure "expected match"
          Just s -> applySubstPTerm s p @?= t
    , testCase "match constructor with binder" $ do
        let p =
              PCon (Con2Name "Lam")
                [ PArg [PFree "A"] (PMeta (MVar "M") [Ix 0]) ]
        let t =
              SCon (Con2Name "Lam")
                [ SArg [SFree "A"] (SBound (Ix 0)) ]
        case matchPTerm p t of
          Nothing -> assertFailure "expected match"
          Just s -> applySubstPTerm s p @?= t
    ]
