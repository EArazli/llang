module Strat.Syntax.CombTerm
  ( CombTerm(..)
  ) where

import Data.Text (Text)
import Strat.Surface
import Strat.Kernel.Term (mkOp)
import Strat.Kernel.Presentation (presSig)

data CombTerm
  = CVar Text
  | COp Text [CombTerm]
  deriving (Eq, Show)

instance SurfaceLang CombTerm where
  elaborate inst tm =
    case tm of
      CVar name ->
        case diResolveVar inst name of
          Nothing -> Left (UnknownVar name)
          Just t -> Right t
      COp name args -> do
        op <-
          case diResolveOp inst name of
            Nothing -> Left (UnknownOp name)
            Just o -> Right o
        args' <- mapM (elaborate inst) args
        case mkOp (presSig (diPresentation inst)) op args' of
          Left err -> Left (ElabTypeError err)
          Right t -> Right t
