{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Weakening
  ( isCtxExtension
  , weakenTermToCtxEither
  , weakenTermToCtxMaybe
  ) where

import Strat.Kernel.Syntax
import Data.Text (Text)

isCtxExtension :: Term -> Term -> Bool
isCtxExtension ctxOld ctxNew
  | ctxNew == ctxOld = True
  | otherwise =
      case termNode ctxNew of
        TOp (OpName "extend") (prev:_) -> isCtxExtension ctxOld prev
        _ -> False

weakenTermToCtxEither :: Term -> Term -> Either Text Term
weakenTermToCtxEither term ctxNew =
  case termSort term of
    Sort (SortName "Ctx") _ -> Right term
    Sort s (ctxOld:idxOld) -> do
      if not (isCtxExtension ctxOld ctxNew)
        then Left "context mismatch for weakening"
        else do
          idxOld' <- mapM (`weakenTermToCtxEither` ctxNew) idxOld
          node' <-
            case termNode term of
              TVar v -> Right (TVar v)
              TOp op args -> do
                args' <-
                  case args of
                    [] -> Right []
                    (_:rest) -> do
                      rest' <- mapM (`weakenTermToCtxEither` ctxNew) rest
                      Right (ctxNew : rest')
                Right (TOp op args')
          let sort' = Sort s (ctxNew : idxOld')
          Right Term { termSort = sort', termNode = node' }
    _ -> Right term

weakenTermToCtxMaybe :: Term -> Term -> Maybe Term
weakenTermToCtxMaybe term ctxNew =
  case weakenTermToCtxEither term ctxNew of
    Left _ -> Nothing
    Right t -> Just t
