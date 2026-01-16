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
        let t = SCon (Con2Name "X") []
        case matchPTerm p t of
          Left err -> assertFailure (show err)
          Right Nothing -> assertFailure "expected match"
          Right (Just s) ->
            case applySubstPTerm s p of
              Left err -> assertFailure (show err)
              Right tm -> tm @?= t
    , testCase "match meta rejects rigid free" $ do
        let p = PMeta (MVar "M") []
        let t = SFree "x"
        case matchPTerm p t of
          Left err -> assertFailure (show err)
          Right Nothing -> pure ()
          Right (Just _) -> assertFailure "expected mismatch for rigid free"
    , testCase "match meta bound arg" $ do
        let p = PMeta (MVar "M") [Ix 0]
        let t = SBound (Ix 0)
        case matchPTerm p t of
          Left err -> assertFailure (show err)
          Right Nothing -> assertFailure "expected match"
          Right (Just s) ->
            case applySubstPTerm s p of
              Left err -> assertFailure (show err)
              Right tm -> tm @?= t
    , testCase "match constructor with binder" $ do
        let p =
              PCon (Con2Name "Lam")
                [ PArg [PFree "A"] (PMeta (MVar "M") [Ix 0]) ]
        let t =
              SCon (Con2Name "Lam")
                [ SArg [SFree "A"] (SBound (Ix 0)) ]
        case matchPTerm p t of
          Left err -> assertFailure (show err)
          Right Nothing -> assertFailure "expected match"
          Right (Just s) ->
            case applySubstPTerm s p of
              Left err -> assertFailure (show err)
              Right tm -> tm @?= t
    ]
