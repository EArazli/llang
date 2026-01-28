{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.STLC
  ( builtinSurface
  , elabSTLC
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)

import Strat.Poly.Surface (PolySurfaceDef(..), PolySurfaceKind(..))
import Strat.Poly.Doctrine (Doctrine)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Surface.CoreTerm (elabCoreTerm)
import Strat.Kernel.Syntax (Term(..), TermNode(..), Sort(..), SortName(..), OpName(..))
import Strat.Poly.Diagram (Diagram)


-- built-in surface marker

builtinSurface :: PolySurfaceDef
builtinSurface = PolySurfaceDef
  { psName = "STLCSurface"
  , psDoctrine = ""
  , psMode = ModeName ""
  , psKind = SurfaceSTLC
  }

-- Parser

data Ty
  = TyBool
  | TyUnit
  | TyProd Ty Ty
  | TyArr Ty Ty
  deriving (Eq, Show)

data Tm
  = TmVar Text
  | TmLam Text Ty Tm
  | TmApp Tm Tm
  | TmPair Tm Tm
  | TmFst Tm
  | TmSnd Tm
  | TmTrue
  | TmFalse
  deriving (Eq, Show)

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

identRaw :: Parser Text
identRaw = lexeme $ do
  c <- letterChar <|> char '_'
  rest <- many (alphaNumChar <|> char '_' <|> char '\'')
  pure (T.pack (c:rest))

ident :: Parser Text
ident = do
  name <- identRaw
  if name `elem` reserved
    then fail "reserved identifier"
    else pure name

reserved :: [Text]
reserved = ["lam", "true", "false", "fst", "snd"]

parseTerm :: Text -> Either Text Tm
parseTerm input =
  case runParser (sc *> termExpr <* eof) "<stlc>" input of
    Left err -> Left (T.pack (errorBundlePretty err))
    Right tm -> Right tm

termExpr :: Parser Tm
termExpr = lamExpr <|> appExpr

lamExpr :: Parser Tm
lamExpr = do
  _ <- symbol "lam"
  name <- ident
  _ <- symbol ":"
  ty <- tyExpr
  _ <- symbol "."
  body <- termExpr
  pure (TmLam name ty body)

appExpr :: Parser Tm
appExpr = do
  atoms <- some termAtom
  pure (foldl1 TmApp atoms)

termAtom :: Parser Tm
termAtom =
  choice
    [ try pairExpr
    , parens termExpr
    , TmTrue <$ symbol "true"
    , TmFalse <$ symbol "false"
    , TmFst <$> (symbol "fst" *> termAtom)
    , TmSnd <$> (symbol "snd" *> termAtom)
    , TmVar <$> ident
    ]

pairExpr :: Parser Tm
pairExpr = parens $ do
  t1 <- termExpr
  _ <- symbol ","
  t2 <- termExpr
  pure (TmPair t1 t2)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

tyExpr :: Parser Ty
tyExpr = makeExprParser tyAtom tyOps
  where
    tyOps =
      [ [ InfixL (TyProd <$ symbol "*") ]
      , [ InfixR (TyArr <$ symbol "->") ]
      ]

tyAtom :: Parser Ty
tyAtom =
  choice
    [ TyBool <$ symbol "Bool"
    , TyUnit <$ symbol "Unit"
    , parens tyExpr
    ]

-- Elaboration

elabSTLC :: Doctrine -> ModeName -> Text -> Either Text Diagram
elabSTLC doc mode src = do
  tm <- parseTerm src
  (_, core) <- elabTerm [] tm
  elabCoreTerm doc mode core

elabTerm :: [(Text, Ty)] -> Tm -> Either Text (Ty, Term)
elabTerm ctx tm =
  case tm of
    TmVar name -> do
      (idx, ty) <- lookupVar ctx name
      core <- projTerm (map snd ctx) idx
      pure (ty, core)
    TmTrue -> do
      let objCtx = ctxObjTerm (map snd ctx)
      let core = compTerm objCtx unitObj boolObj (tTerm) (terminalTerm objCtx)
      pure (TyBool, core)
    TmFalse -> do
      let objCtx = ctxObjTerm (map snd ctx)
      let core = compTerm objCtx unitObj boolObj (fTerm) (terminalTerm objCtx)
      pure (TyBool, core)
    TmLam name ty body -> do
      (bodyTy, bodyCore) <- elabTerm (ctx <> [(name, ty)]) body
      let objCtx = ctxObjTerm (map snd ctx)
      let core = curryTerm (tyObjTerm ty) (tyObjTerm bodyTy) objCtx bodyCore
      pure (TyArr ty bodyTy, core)
    TmApp f x -> do
      (fTy, fCore) <- elabTerm ctx f
      (xTy, xCore) <- elabTerm ctx x
      case fTy of
        TyArr a b ->
          if a /= xTy
            then Left "stlc: argument type mismatch"
            else do
              let objCtx = ctxObjTerm (map snd ctx)
              let objA = tyObjTerm a
              let objB = tyObjTerm b
              let expAB = expObj objA objB
              let pairCore = pairTerm expAB objA objCtx fCore xCore
              let core = compTerm objCtx (prodObj expAB objA) objB (evalTerm objA objB) pairCore
              pure (b, core)
        _ -> Left "stlc: expected function in application"
    TmPair a b -> do
      (ta, ca) <- elabTerm ctx a
      (tb, cb) <- elabTerm ctx b
      let objCtx = ctxObjTerm (map snd ctx)
      let core = pairTerm (tyObjTerm ta) (tyObjTerm tb) objCtx ca cb
      pure (TyProd ta tb, core)
    TmFst p -> do
      (tp, cp) <- elabTerm ctx p
      case tp of
        TyProd a b -> do
          let objCtx = ctxObjTerm (map snd ctx)
          let objA = tyObjTerm a
          let objB = tyObjTerm b
          let core = compTerm objCtx (prodObj objA objB) objA (exlTerm objA objB) cp
          pure (a, core)
        _ -> Left "stlc: expected product in fst"
    TmSnd p -> do
      (tp, cp) <- elabTerm ctx p
      case tp of
        TyProd a b -> do
          let objCtx = ctxObjTerm (map snd ctx)
          let objA = tyObjTerm a
          let objB = tyObjTerm b
          let core = compTerm objCtx (prodObj objA objB) objB (exrTerm objA objB) cp
          pure (b, core)
        _ -> Left "stlc: expected product in snd"

lookupVar :: [(Text, Ty)] -> Text -> Either Text (Int, Ty)
lookupVar ctx name = go 0 (reverse ctx)
  where
    go _ [] = Left "stlc: unknown variable"
    go idx ((n, ty):rest)
      | n == name = Right (idx, ty)
      | otherwise = go (idx + 1) rest

projTerm :: [Ty] -> Int -> Either Text Term
projTerm ctx idx = do
  (_, term) <- go ctx idx
  pure term
  where
    go [] _ = Left "stlc: projection from empty context"
    go tys i = do
      let (initTys, lastTy) = (init tys, last tys)
      let ctxObj = ctxObjTerm tys
      let ctxObj' = ctxObjTerm initTys
      let lastObj = tyObjTerm lastTy
      if i == 0
        then pure (lastTy, exrTerm ctxObj' lastObj)
        else do
          (tgtTy, proj') <- go initTys (i - 1)
          let tgtObj = tyObjTerm tgtTy
          let exl = exlTerm ctxObj' lastObj
          pure (tgtTy, compTerm ctxObj ctxObj' tgtObj proj' exl)

-- Core term constructors

objSort :: Sort
objSort = Sort (SortName "Obj") []

homSort :: Term -> Term -> Sort
homSort a b = Sort (SortName "Hom") [a, b]

opTerm :: Sort -> Text -> [Term] -> Term
opTerm sort name args = Term sort (TOp (OpName name) args)

objTerm :: Text -> [Term] -> Term
objTerm name args = opTerm objSort name args

unitObj :: Term
unitObj = objTerm "Unit" []

boolObj :: Term
boolObj = objTerm "Bool" []

prodObj :: Term -> Term -> Term
prodObj a b = objTerm "prod" [a, b]

expObj :: Term -> Term -> Term
expObj a b = objTerm "exp" [a, b]

tyObjTerm :: Ty -> Term
tyObjTerm ty =
  case ty of
    TyBool -> boolObj
    TyUnit -> unitObj
    TyProd a b -> prodObj (tyObjTerm a) (tyObjTerm b)
    TyArr a b -> expObj (tyObjTerm a) (tyObjTerm b)

ctxObjTerm :: [Ty] -> Term
ctxObjTerm tys = foldl step unitObj tys
  where
    step acc ty = prodObj acc (tyObjTerm ty)

compTerm :: Term -> Term -> Term -> Term -> Term -> Term
compTerm a b c f g = opTerm (homSort a c) "comp" [a, b, c, f, g]

pairTerm :: Term -> Term -> Term -> Term -> Term -> Term
pairTerm a b c f g = opTerm (homSort c (prodObj a b)) "pair" [a, b, c, f, g]

exlTerm :: Term -> Term -> Term
exlTerm a b = opTerm (homSort (prodObj a b) a) "exl" [a, b]

exrTerm :: Term -> Term -> Term
exrTerm a b = opTerm (homSort (prodObj a b) b) "exr" [a, b]

curryTerm :: Term -> Term -> Term -> Term -> Term
curryTerm a b c f = opTerm (homSort c (expObj a b)) "curry" [a, b, c, f]

evalTerm :: Term -> Term -> Term
evalTerm a b = opTerm (homSort (prodObj (expObj a b) a) b) "eval" [a, b]

terminalTerm :: Term -> Term
terminalTerm a = opTerm (homSort a unitObj) "terminal" [a]

tTerm :: Term
tTerm = opTerm (homSort unitObj boolObj) "T" []

fTerm :: Term
fTerm = opTerm (homSort unitObj boolObj) "F" []
