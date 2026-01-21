{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Weakening
  ( isCtxExtension
  , weakenTermToCtxEither
  , weakenTermToCtxMaybe
  ) where

import Strat.Kernel.Syntax
import Data.Text (Text)
import qualified Data.Text as T

splitQName :: Text -> (Maybe Text, Text)
splitQName t =
  case T.splitOn "." t of
    [] -> (Nothing, t)
    [b] -> (Nothing, b)
    parts ->
      let b = last parts
          ns = T.intercalate "." (init parts)
      in (Just ns, b)

qualify :: Maybe Text -> Text -> Text
qualify Nothing b = b
qualify (Just ns) b = ns <> "." <> b

ctxExtendOpName :: Term -> Maybe OpName
ctxExtendOpName ctx =
  case termSort ctx of
    Sort (SortName sn) _ ->
      let (mNs, base) = splitQName sn
      in if base == "Ctx"
           then Just (OpName (qualify mNs "extend"))
           else Nothing

isCtxExtension :: Term -> Term -> Bool
isCtxExtension ctxOld ctxNew
  | ctxNew == ctxOld = True
  | termSort ctxNew /= termSort ctxOld = False
  | otherwise =
      case ctxExtendOpName ctxNew of
        Nothing -> False
        Just ext ->
          case termNode ctxNew of
            TOp op (prev:_) | op == ext -> isCtxExtension ctxOld prev
            _ -> False

weakenTermToCtxEither :: Term -> Term -> Either Text Term
weakenTermToCtxEither term ctxNew =
  case termSort term of
    Sort s (ctxOld:idxOld) -> do
      let ctxSortWanted = termSort ctxNew
      if termSort ctxOld /= ctxSortWanted
        then Left "context sort mismatch for weakening"
        else
          if not (isCtxExtension ctxOld ctxNew)
            then Left "context mismatch for weakening"
            else do
              idxOld' <- mapM (`weakenTermToCtxEither` ctxNew) idxOld
              node' <-
                case termNode term of
                  TVar v -> Right (TVar v)
                  TOp op args ->
                    case args of
                      [] -> Left "context-indexed op without explicit context argument"
                      (a0:rest) ->
                        if termSort a0 /= ctxSortWanted
                          then Left "context argument has wrong sort during weakening"
                          else
                            if a0 /= ctxOld
                              then Left "context argument mismatch during weakening"
                              else do
                                rest' <- mapM (`weakenTermToCtxEither` ctxNew) rest
                                Right (TOp op (ctxNew : rest'))
              let sort' = Sort s (ctxNew : idxOld')
              Right Term { termSort = sort', termNode = node' }
    _ -> Right term

weakenTermToCtxMaybe :: Term -> Term -> Maybe Term
weakenTermToCtxMaybe term ctxNew =
  case weakenTermToCtxEither term ctxNew of
    Left _ -> Nothing
    Right t -> Just t
