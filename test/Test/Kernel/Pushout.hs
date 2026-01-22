{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Pushout
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.Pushout
import Strat.Kernel.Morphism
import Strat.Kernel.Morphism.Util (symbolMapMorphism)
import Strat.Kernel.Presentation
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term (TypeError(..), mkOp, mkVar)
import Strat.Kernel.Types (RuleClass(..), Orientation(..))
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Data.Text (Text)


tests :: TestTree
tests =
  testGroup
    "Kernel.Pushout"
    [ testCase "pushout unifies interface ops" testPushoutUnifies
    , testCase "pushout injections validate" testPushoutInjections
    , testCase "pushout injections commute" testPushoutCommutes
    , testCase "pushout rejects non-symbol map" testPushoutRejectsNonSymbol
    , testCase "pushout rejects non-injective op map" testPushoutRejectsNonInjective
    ]


testPushoutUnifies :: Assertion
testPushoutUnifies = do
  let (aPres, bPres, cPres) = samplePres
  f <- requireRight (symbolMapMorphism aPres bPres (mkSortMap "A" "B") (mkOpMap "A" "B"))
  g <- requireRight (symbolMapMorphism aPres cPres (mkSortMap "A" "C") (mkOpMap "A" "C"))
  PushoutResult pres _ _ _ <- requireRight (computePushout "P" f g)
  let lhsOps = mapMaybe termRootOp (map eqLHS (presEqs pres))
  assertBool "expected two rules" (length lhsOps == 2)
  assertBool "expected LHS ops unified to A.f" (all (== OpName "A.f") lhsOps)

testPushoutInjections :: Assertion
testPushoutInjections = do
  let (aPres, bPres, cPres) = samplePres
  f <- requireRight (symbolMapMorphism aPres bPres (mkSortMap "A" "B") (mkOpMap "A" "B"))
  g <- requireRight (symbolMapMorphism aPres cPres (mkSortMap "A" "C") (mkOpMap "A" "C"))
  PushoutResult pres inl inr glue <- requireRight (computePushout "P" f g)
  requireRight (checkMorphism (mcPolicy (morCheck inl)) (mcFuel (morCheck inl)) inl)
  requireRight (checkMorphism (mcPolicy (morCheck inr)) (mcFuel (morCheck inr)) inr)
  requireRight (checkMorphism (mcPolicy (morCheck glue)) (mcFuel (morCheck glue)) glue)
  assertBool "pres name set" (presName pres == "P")

testPushoutCommutes :: Assertion
testPushoutCommutes = do
  let (aPres, bPres, cPres) = samplePres
  f <- requireRight (symbolMapMorphism aPres bPres (mkSortMap "A" "B") (mkOpMap "A" "B"))
  g <- requireRight (symbolMapMorphism aPres cPres (mkSortMap "A" "C") (mkOpMap "A" "C"))
  PushoutResult _ inl inr glue <- requireRight (computePushout "P" f g)
  t <- requireRight (mkUnaryTerm "A.f" aPres)
  let viaInl = applyMorphismTerm inl (applyMorphismTerm f t)
  let viaInr = applyMorphismTerm inr (applyMorphismTerm g t)
  let viaGlue = applyMorphismTerm glue t
  viaInl @?= viaGlue
  viaInr @?= viaGlue

testPushoutRejectsNonSymbol :: Assertion
testPushoutRejectsNonSymbol = do
  let (aPres, bPres, cPres) = samplePres
  fBad <- requireRight (nonSymbolMap aPres bPres)
  g <- requireRight (symbolMapMorphism aPres cPres (mkSortMap "A" "C") (mkOpMap "A" "C"))
  case computePushout "P" fBad g of
    Left err ->
      assertBool "expected symbol-map error" ("pushout currently requires symbol-map morphisms" `T.isInfixOf` err)
    Right _ -> assertFailure "expected pushout to fail for non-symbol map"

testPushoutRejectsNonInjective :: Assertion
testPushoutRejectsNonInjective = do
  let aPres = presWithOps "A" ["f", "g"]
  let bPres = presWithOps "B" ["f"]
  let cPres = presWithOps "C" ["f", "g"]
  let sortMapA = mkSortMap "A" "B"
  let opMapA = M.fromList [(OpName "A.f", OpName "B.f"), (OpName "A.g", OpName "B.f")]
  f <- requireRight (symbolMapMorphism aPres bPres sortMapA opMapA)
  let opMapC = M.fromList [(OpName "A.f", OpName "C.f"), (OpName "A.g", OpName "C.g")]
  g <- requireRight (symbolMapMorphism aPres cPres (mkSortMap "A" "C") opMapC)
  case computePushout "P" f g of
    Left err ->
      assertBool "expected injective error" ("injective op mapping" `T.isInfixOf` err)
    Right _ -> assertFailure "expected pushout to fail for non-injective op map"


samplePres :: (Presentation, Presentation, Presentation)
samplePres =
  let aPres = presWithOps "A" ["f"]
      bPres = presWithOps "B" ["f", "g"]
      cPres = presWithOps "C" ["f", "h"]
      bEq = unsafeRight (mkUnaryRule "B.rB" "B" "B.f" "B.g" bPres)
      cEq = unsafeRight (mkUnaryRule "C.rN" "C" "C.f" "C.h" cPres)
      bPres' = bPres { presEqs = [bEq] }
      cPres' = cPres { presEqs = [cEq] }
  in (aPres, bPres', cPres')

presWithOps :: Text -> [Text] -> Presentation
presWithOps ns ops =
  let obj = SortName (ns <> ".Obj")
      sortCtor = SortCtor { scName = obj, scTele = [] }
      sig = Signature
        { sigSortCtors = M.fromList [(obj, sortCtor)]
        , sigOps = M.fromList [ (OpName (ns <> "." <> o), unaryOpDecl ns (ns <> "." <> o)) | o <- ops ]
        }
  in Presentation { presName = ns, presSig = sig, presEqs = [] }

unaryOpDecl :: Text -> Text -> OpDecl
unaryOpDecl ns opText =
  let scope = ScopeId ("op:" <> opText)
      v = Var scope 0
      s = Sort (SortName (ns <> ".Obj")) []
      tele = [Binder v s]
  in OpDecl { opName = OpName opText, opTele = tele, opResult = s }

mkUnaryRule :: Text -> Text -> Text -> Text -> Presentation -> Either Text Equation
mkUnaryRule name ns lhsOp rhsOp pres = do
  let scope = ScopeId ("eq:" <> name)
  let v = Var scope 0
  let s = Sort (SortName (ns <> ".Obj")) []
  let tele = [Binder v s]
  let sig = presSig pres
  lhs <- mapLeft (mkOp sig (OpName lhsOp) [mkVar s v]) renderTypeError
  rhs <- mapLeft (mkOp sig (OpName rhsOp) [mkVar s v]) renderTypeError
  pure Equation
    { eqName = name
    , eqClass = Computational
    , eqOrient = LR
    , eqTele = tele
    , eqLHS = lhs
    , eqRHS = rhs
    }

nonSymbolMap :: Presentation -> Presentation -> Either Text Morphism
nonSymbolMap src tgt = do
  let sortMap = mkSortMap "A" "B"
  let sigTgt = presSig tgt
  let scope = ScopeId "mor:bad"
  let v = Var scope 0
  let s = Sort (SortName "B.Obj") []
  let tele = [Binder v s]
  arg <- Right (mkVar s v)
  inner <- mapLeft (mkOp sigTgt (OpName "B.g") [arg]) renderTypeError
  rhs <- mapLeft (mkOp sigTgt (OpName "B.g") [inner]) renderTypeError
  let opMap = M.fromList [(OpName "A.f", OpInterp { oiTele = tele, oiRhs = rhs })]
  pure Morphism
    { morName = "bad"
    , morSrc = src
    , morTgt = tgt
    , morSortMap = sortMap
    , morOpMap = opMap
    , morCheck = MorphismCheck { mcPolicy = UseStructuralAsBidirectional, mcFuel = 200 }
    }

mkSortMap :: Text -> Text -> M.Map SortName SortName
mkSortMap src tgt = M.fromList [(SortName (src <> ".Obj"), SortName (tgt <> ".Obj"))]

mkOpMap :: Text -> Text -> M.Map OpName OpName
mkOpMap src tgt = M.fromList [(OpName (src <> ".f"), OpName (tgt <> ".f"))]

mkUnaryTerm :: Text -> Presentation -> Either Text Term
mkUnaryTerm opText pres = do
  let sig = presSig pres
  let scope = ScopeId ("term:" <> opText)
  let v = Var scope 0
  let s = Sort (SortName (presName pres <> ".Obj")) []
  let arg = mkVar s v
  mapLeft (mkOp sig (OpName opText) [arg]) renderTypeError

termRootOp :: Term -> Maybe OpName
termRootOp tm =
  case termNode tm of
    TOp op _ -> Just op
    _ -> Nothing

renderTypeError :: TypeError -> Text
renderTypeError = T.pack . show

mapLeft :: Either a b -> (a -> c) -> Either c b
mapLeft (Left e) f = Left (f e)
mapLeft (Right v) _ = Right v

requireRight :: Show e => Either e a -> IO a
requireRight (Left err) = assertFailure (show err) >> fail "unreachable"
requireRight (Right v) = pure v

unsafeRight :: Either Text a -> a
unsafeRight (Left err) = error (T.unpack err)
unsafeRight (Right v) = v

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f = foldr (\x acc -> maybe acc (:acc) (f x)) []
