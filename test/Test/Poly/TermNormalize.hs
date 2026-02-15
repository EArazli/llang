{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.TermNormalize
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TyVar(..), TmFunName(..), TmVar(..))
import Strat.Poly.TypeTheory (TypeTheory(..), modeOnlyTypeTheory)
import qualified Strat.Poly.TypeTheory as TT
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram)
import Strat.Poly.Term.Normalize (normalizeTermExpr)
import qualified Strat.Poly.Term.RewriteSystem as TRS
import Strat.Poly.Term.RewriteCompile (compileTermRules)
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.TermNormalize"
    [ testCase "rewrite substitution does not recurse into substitution image" testNonRecursiveSubst
    , testCase "repeated-pattern-variable matching is consistent" testRepeatedVarMatch
    , testCase "compile rejects rhs variables not appearing in lhs" testCompileRejectsFreshRhsVars
    ]

testNonRecursiveSubst :: Assertion
testNonRecursiveSubst = do
  let trs = TRS.mkTRS modeM [projRule]
  let tm = TMFun (TmFunName "g") [TMBound 1, TMBound 0]
  normalizeTermExpr trs tm @?= TMBound 1
  where
    modeM = ModeName "M"
    projRule =
      TRS.TRule
        { TRS.trName = "proj"
        , TRS.trLHS = TMFun (TmFunName "g") [TMBound 0, TMBound 1]
        , TRS.trRHS = TMBound 0
        }

testRepeatedVarMatch :: Assertion
testRepeatedVarMatch = do
  let trs = TRS.mkTRS modeM [diagRule]
  let noRewrite = TMFun (TmFunName "h") [TMBound 0, TMBound 1]
  let rewrite = TMFun (TmFunName "h") [TMBound 0, TMBound 0]
  normalizeTermExpr trs noRewrite @?= noRewrite
  normalizeTermExpr trs rewrite @?= TMBound 0
  where
    modeM = ModeName "M"
    diagRule =
      TRS.TRule
        { TRS.trName = "diag"
        , TRS.trLHS = TMFun (TmFunName "h") [TMBound 0, TMBound 0]
        , TRS.trRHS = TMBound 0
        }

testCompileRejectsFreshRhsVars :: Assertion
testCompileRejectsFreshRhsVars = do
  lhs <- requireEither (termExprToDiagram ttBase [] sortTy (TMFun fName [TMVar xVar]))
  rhs <- requireEither (termExprToDiagram ttBase [] sortTy (TMVar yVar))
  let rule = TT.TmRule { TT.trVars = [xVar, yVar], TT.trLHS = lhs, TT.trRHS = rhs }
  let tt = ttBase { ttTmRules = M.singleton modeM [rule] }
  case compileTermRules tt modeM of
    Left err ->
      assertBool
        ("unexpected compile error: " <> T.unpack err)
        ("rhs introduces fresh variables" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected term-rule compilation to reject rhs fresh variables"
  where
    modeM = ModeName "M"
    fName = TmFunName "f"
    sortTy = TVar TyVar { tvName = "a", tvMode = modeM }
    xVar = TmVar { tmvName = "x", tmvSort = sortTy, tmvScope = 0 }
    yVar = TmVar { tmvName = "y", tmvSort = sortTy, tmvScope = 0 }
    funSigs = M.fromList [(fName, TT.TmFunSig { TT.tfsArgs = [sortTy], TT.tfsRes = sortTy })]
    ttBase = (modeOnlyTypeTheory (mkModes [modeM])) { ttTmFuns = M.singleton modeM funSigs }

requireEither :: Either Text a -> IO a
requireEither result =
  case result of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right v -> pure v
