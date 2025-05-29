{-# OPTIONS_GHC -Wno-orphans #-}

module TypeSearch.Error
  ( Error (..),
    toDiagnostic,
  )
where

import Data.List (intercalate)
import Error.Diagnose
import Text.Printf

--------------------------------------------------------------------------------

data Error
  = ParseError Position [String]
  deriving stock (Show)

toDiagnostic :: [(FilePath, String)] -> Error -> Diagnostic String
toDiagnostic srcs = \case
  ParseError pos exps ->
    errDiag
      (Just pos)
      do "Parse error on input"
      if null exps
        then "While parsing this term"
        else printf "Expected one of: %s" (intercalate ", " exps)
  where
    errDiag mpos msg markerMsg =
      addReport (foldl (uncurry . addFile) def srcs) $
        err Nothing msg (maybe [] (\pos -> [(pos, This markerMsg)]) mpos) []
