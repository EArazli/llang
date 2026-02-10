{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Eval
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModeInfo(..), VarDiscipline(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TypeArg(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), InputShape(..))
import Strat.Poly.Graph (Diagram(..), emptyDiagram, freshPort, addEdgePayload, EdgePayload(..), validateDiagram)
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.Eval (evalDiagram)
import Strat.Model.Spec (ModelSpec(..), ModelBackend(..), DefaultBehavior(..))
import Strat.Backend (Value(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Eval"
    [ testCase "eval fails when generator is undeclared" testEvalUnknownGen
    , testCase "eval fails when model is missing and default is error" testEvalMissingModel
    , testCase "cyclic eval returns letrec" testEvalCycleLetrec
    , testCase "cyclic eval returns multiple bindings" testEvalCycleBindings
    , testCase "cycle inside box returns letrec" testEvalCycleInBox
    ]

tcon :: ModeName -> T.Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) (map TAType args)

mkModes :: S.Set ModeName -> ModeTheory
mkModes modes =
  ModeTheory
    (M.fromList [ (m, ModeInfo m Linear) | m <- S.toList modes ])
    M.empty
    []
    []


testEvalUnknownGen :: Assertion
testEvalUnknownGen = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  diag <- case mkDupDiagram mode a of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let doc = Doctrine
        { dName = "NoDup"
        , dModes = mkModes (S.singleton mode)
        , dIndexModes = S.empty
        , dIxTheory = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
        , dGens = M.empty
        , dCells2 = []
        , dAttrSorts = M.empty
        }
  let model = ModelSpec "Empty" [] DefaultSymbolic BackendAlgebra Nothing
  case evalDiagram doc model diag [VInt 1] of
    Left _ -> pure ()
    Right _ -> assertFailure "expected eval failure for unknown generator"


testEvalMissingModel :: Assertion
testEvalMissingModel = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  diag <- case mkDupDiagram mode a of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let dupGen = GenDecl
        { gdName = GenName "dup"
        , gdMode = mode
        , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [a]
        , gdCod = [a, a]
        , gdAttrs = []
        }
  let doc = Doctrine
        { dName = "WithDup"
        , dModes = mkModes (S.singleton mode)
        , dIndexModes = S.empty
        , dIxTheory = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(GenName "dup", dupGen)])]
        , dCells2 = []
        , dAttrSorts = M.empty
        }
  let model = ModelSpec "NoDupModel" [] (DefaultError "missing") BackendAlgebra Nothing
  case evalDiagram doc model diag [VInt 1] of
    Left _ -> pure ()
    Right _ -> assertFailure "expected eval failure for missing model clause"


mkDupDiagram :: ModeName -> TypeExpr -> Either T.Text Diagram
mkDupDiagram mode a = do
  let (p0, d0) = freshPort a (emptyDiagram mode [])
  let (p1, d1) = freshPort a d0
  let (p2, d2) = freshPort a d1
  d3 <- addEdgePayload (PGen (GenName "dup") M.empty []) [p0] [p1, p2] d2
  let diag = d3 { dIn = [p0], dOut = [p1, p2] }
  validateDiagram diag
  pure diag

testEvalCycleLetrec :: Assertion
testEvalCycleLetrec = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  diag <- case mkCycleDiagram mode a of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let doc = mkCycleDoctrine mode a
  let model = ModelSpec "NoModel" [] DefaultSymbolic BackendAlgebra Nothing
  res <- case evalDiagram doc model diag [] of
    Left err -> assertFailure (T.unpack err)
    Right vals -> pure vals
  case res of
    [VList (VAtom "letrec" : _)] -> pure ()
    _ -> assertFailure "expected letrec wrapper in cyclic eval output"

testEvalCycleBindings :: Assertion
testEvalCycleBindings = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  diag <- case mkCycleDiagram mode a of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let doc = mkCycleDoctrine mode a
  let model = ModelSpec "NoModel" [] DefaultSymbolic BackendAlgebra Nothing
  res <- case evalDiagram doc model diag [] of
    Left err -> assertFailure (T.unpack err)
    Right vals -> pure vals
  case res of
    [VList (VAtom "letrec" : VList binds : _)] ->
      if length binds >= 2 then pure () else assertFailure "expected multiple bindings"
    _ -> assertFailure "expected letrec with bindings"

testEvalCycleInBox :: Assertion
testEvalCycleInBox = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  inner <- case mkCycleDiagram mode a of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let (outP, d0) = freshPort a (emptyDiagram mode [])
  d1 <- case addEdgePayload (PBox (BoxName "Box") inner) [] [outP] d0 of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let outer = d1 { dIn = [], dOut = [outP] }
  let doc = mkCycleDoctrine mode a
  let model = ModelSpec "NoModel" [] DefaultSymbolic BackendAlgebra Nothing
  res <- case evalDiagram doc model outer [] of
    Left err -> assertFailure (T.unpack err)
    Right vals -> pure vals
  case res of
    [VList (VAtom "letrec" : _)] -> pure ()
    _ -> assertFailure "expected letrec wrapper for boxed cycle"

mkCycleDoctrine :: ModeName -> TypeExpr -> Doctrine
mkCycleDoctrine mode a =
  let fGen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [a]
        , gdCod = [a]
        , gdAttrs = []
        }
      dupGen = GenDecl
        { gdName = GenName "dup"
        , gdMode = mode
        , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [a]
        , gdCod = [a, a]
        , gdAttrs = []
        }
  in Doctrine
      { dName = "Cycle"
      , dModes = mkModes (S.singleton mode)
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
      , dGens = M.fromList [(mode, M.fromList [(gdName fGen, fGen), (gdName dupGen, dupGen)])]
      , dCells2 = []
      , dAttrSorts = M.empty
      }

mkCycleDiagram :: ModeName -> TypeExpr -> Either T.Text Diagram
mkCycleDiagram mode a = do
  let (p0, d0) = freshPort a (emptyDiagram mode [])
  let (p1, d1) = freshPort a d0
  let (p2, d2) = freshPort a d1
  d3 <- addEdgePayload (PGen (GenName "f") M.empty []) [p1] [p0] d2
  d4 <- addEdgePayload (PGen (GenName "dup") M.empty []) [p0] [p1, p2] d3
  let diag = d4 { dIn = [], dOut = [p2] }
  validateDiagram diag
  pure diag
