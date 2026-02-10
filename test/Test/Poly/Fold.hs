{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Fold
  ( foldTests
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import Strat.Backend (Value(..))
import Strat.Model.Spec (DefaultBehavior(..), FoldSpec(..), MExpr(..), ModelBackend(..), ModelSpec(..), OpClause(..))
import Strat.Poly.Diagram (genD)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), InputShape(..))
import Strat.Poly.Eval (evalDiagram)
import Strat.Poly.Graph (dIn, dOut, setPortLabel)
import Strat.Poly.ModeTheory (ModeInfo(..), ModeName(..), ModeTheory(..), VarDiscipline(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TypeArg(..))
import Test.Tasty
import Test.Tasty.HUnit


foldTests :: TestTree
foldTests =
  testGroup
    "Poly.Fold"
    [ testCase "fold uses labels for open-diagram names" testFoldUsesLabels
    , testCase "fold emits statements for codomain-0 generators" testFoldStmtEmission
    , testCase "fold avoids parameter/output name collision" testFoldSSAAvoidsParamCollision
    , testCase "fold handles collision after suffix disambiguation" testFoldSSAHandlesCollisionAfterSuffix
    , testCase "fold indents multiline statements" testFoldSSAIndentsMultilineStmt
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

mkDoctrine :: ModeName -> [GenDecl] -> M.Map ModeName (M.Map TypeName TypeSig) -> Doctrine
mkDoctrine mode gens typesTable =
  Doctrine
    { dName = "D"
    , dModes = mkModes (S.singleton mode)
    , dIndexModes = S.empty
    , dIxTheory = M.empty
    , dTypes = typesTable
    , dGens = M.fromList [(mode, M.fromList [ (gdName g, g) | g <- gens ])]
    , dCells2 = []
    , dAttrSorts = M.empty
    }

mkFoldModel :: [OpClause] -> DefaultBehavior -> ModelSpec
mkFoldModel ops def =
  ModelSpec
    { msName = "Fold"
    , msOps = ops
    , msDefault = def
    , msBackend = BackendFold
    , msFold = Just jsLikeFoldSpec
    }

jsLikeFoldSpec :: FoldSpec
jsLikeFoldSpec =
  FoldSpec
    { fsIndent = "  "
    , fsReserved = S.empty
    , fsHooks = M.fromList [ (ocOp c, c) | c <- hooks ]
    }
  where
    hooks =
      [ OpClause "prologue_closed" [] (MString "(() => {")
      , OpClause "epilogue_closed" [] (MString "})()")
      , OpClause "prologue_open" ["params", "paramDecls"] (mconcatExpr [MString "(", MVar "params", MString ") => {"])
      , OpClause "epilogue_open" [] (MString "}")
      , OpClause "bind0" ["stmt"] (MVar "stmt")
      , OpClause "bind1" ["out", "ty", "expr"] (mconcatExpr [MString "const ", MVar "out", MString " = ", MVar "expr", MString ";"])
      , OpClause "bindN" ["outs", "decls", "expr"] (mconcatExpr [MString "const [", MVar "outs", MString "] = ", MVar "expr", MString ";"])
      , OpClause "return0" [] (MString "")
      , OpClause "return1" ["out", "ty"] (mconcatExpr [MString "return ", MVar "out", MString ";"])
      , OpClause "returnN" ["outs", "decls"] (mconcatExpr [MString "return [", MVar "outs", MString "];"])
      ]

mconcatExpr :: [MExpr] -> MExpr
mconcatExpr [] = MString ""
mconcatExpr [x] = x
mconcatExpr (x:xs) = MBinOp "++" x (mconcatExpr xs)

testFoldUsesLabels :: Assertion
testFoldUsesLabels = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  diag0 <- case genD mode [a] [a] (GenName "g") of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  inPort <- case dIn diag0 of
    [p] -> pure p
    _ -> assertFailure "expected one input" >> fail "unreachable"
  outPort <- case dOut diag0 of
    [p] -> pure p
    _ -> assertFailure "expected one output" >> fail "unreachable"
  diag1 <- case setPortLabel inPort "x" diag0 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  diag2 <- case setPortLabel outPort "y" diag1 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let gDecl =
        GenDecl
          { gdName = GenName "g"
          , gdMode = mode
          , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [a]
          , gdCod = [a]
          , gdAttrs = []
          }
  let doc = mkDoctrine mode [gDecl] (M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])])
  let model = mkFoldModel [] DefaultSymbolic
  vals <- case evalDiagram doc model diag2 [] of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right xs -> pure xs
  vals @?=
    [ VString
        ( T.intercalate
            "\n"
            [ "(x) => {"
            , "  const y = g(x);"
            , "  return y;"
            , "}"
            ]
        )
    ]

testFoldStmtEmission :: Assertion
testFoldStmtEmission = do
  let mode = ModeName "M"
  diag <- case genD mode [] [] (GenName "emit") of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let emitDecl =
        GenDecl
          { gdName = GenName "emit"
          , gdMode = mode
          , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort []
          , gdCod = []
          , gdAttrs = []
          }
  let doc = mkDoctrine mode [emitDecl] M.empty
  let model = mkFoldModel [] DefaultSymbolic
  vals <- case evalDiagram doc model diag [] of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right xs -> pure xs
  vals @?=
    [ VString
        ( T.intercalate
            "\n"
            [ "(() => {"
            , "  emit();"
            , "})()"
            ]
        )
    ]

testFoldSSAAvoidsParamCollision :: Assertion
testFoldSSAAvoidsParamCollision = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  diag0 <- case genD mode [a] [a] (GenName "g") of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  inPort <- case dIn diag0 of
    [p] -> pure p
    _ -> assertFailure "expected one input" >> fail "unreachable"
  outPort <- case dOut diag0 of
    [p] -> pure p
    _ -> assertFailure "expected one output" >> fail "unreachable"
  diag1 <- case setPortLabel inPort "x" diag0 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  diag2 <- case setPortLabel outPort "x" diag1 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let gDecl =
        GenDecl
          { gdName = GenName "g"
          , gdMode = mode
          , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [a]
          , gdCod = [a]
          , gdAttrs = []
          }
  let doc = mkDoctrine mode [gDecl] (M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])])
  let model = mkFoldModel [] DefaultSymbolic
  vals <- case evalDiagram doc model diag2 [] of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right xs -> pure xs
  vals @?=
    [ VString
        ( T.intercalate
            "\n"
            [ "(x) => {"
            , "  const x_1 = g(x);"
            , "  return x_1;"
            , "}"
            ]
        )
    ]

testFoldSSAHandlesCollisionAfterSuffix :: Assertion
testFoldSSAHandlesCollisionAfterSuffix = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  diag0 <- case genD mode [a] [a, a] (GenName "split") of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  inPort <- case dIn diag0 of
    [p] -> pure p
    _ -> assertFailure "expected one input" >> fail "unreachable"
  (outA, outB) <- case dOut diag0 of
    [p1, p2] -> pure (p1, p2)
    _ -> assertFailure "expected two outputs" >> fail "unreachable"
  diag1 <- case setPortLabel inPort "x" diag0 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  diag2 <- case setPortLabel outA "x" diag1 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  diag3 <- case setPortLabel outB "x_1" diag2 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let splitDecl =
        GenDecl
          { gdName = GenName "split"
          , gdMode = mode
          , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [a]
          , gdCod = [a, a]
          , gdAttrs = []
          }
  let doc = mkDoctrine mode [splitDecl] (M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])])
  let model = mkFoldModel [] DefaultSymbolic
  vals <- case evalDiagram doc model diag3 [] of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right xs -> pure xs
  vals @?=
    [ VString
        ( T.intercalate
            "\n"
            [ "(x) => {"
            , "  const [x_1, x_1_2] = split(x);"
            , "  return [x_1, x_1_2];"
            , "}"
            ]
        )
    ]

testFoldSSAIndentsMultilineStmt :: Assertion
testFoldSSAIndentsMultilineStmt = do
  let mode = ModeName "M"
  diag <- case genD mode [] [] (GenName "emit") of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let emitDecl =
        GenDecl
          { gdName = GenName "emit"
          , gdMode = mode
          , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort []
          , gdCod = []
          , gdAttrs = []
          }
  let doc = mkDoctrine mode [emitDecl] M.empty
  let emitClause = OpClause "emit" [] (MString "a();\nb();")
  let model = mkFoldModel [emitClause] DefaultSymbolic
  vals <- case evalDiagram doc model diag [] of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right xs -> pure xs
  vals @?=
    [ VString
        ( T.intercalate
            "\n"
            [ "(() => {"
            , "  a();"
            , "  b();"
            , "})()"
            ]
        )
    ]
