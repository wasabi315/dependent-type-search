module TypeSearch.Common
  ( -- * Utils
    down,
    choose,
    par,
    punctuate,
    enclose,

    -- * Names
    Index (..),
    Meta (..),
    freshMeta,
    Name,
    TopName (..),
    freshen,
  )
where

import Control.Applicative
import Data.Function
import Data.Hashable
import Data.List (intersperse)
import Data.List.NonEmpty qualified as NE
import Data.Text qualified as T
import Data.Unique

--------------------------------------------------------------------------------
-- Utils

-- | @[x, x - 1, ..., y]@
down :: (Enum a, Num a) => a -> a -> [a]
down x y = [x, x - 1 .. y]

choose :: (Alternative m, Foldable t) => t a -> m a
choose = foldr ((<|>) . pure) empty

par :: Int -> Int -> ShowS -> ShowS
par p q = showParen (p > q)

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)

enclose :: ShowS -> ShowS -> ShowS -> ShowS
enclose open close x = open . x . close

--------------------------------------------------------------------------------
-- Names

-- | De Bruijn indices
newtype Index = Index Int
  deriving newtype (Num, Eq, Ord, Show, Hashable, Enum)

-- | Meta variables
newtype Meta = Meta Unique
  deriving newtype (Eq, Ord, Hashable)

instance Show Meta where
  showsPrec _ (Meta u) = showString "$M" . shows (hashUnique u)

freshMeta :: IO Meta
freshMeta = Meta <$> newUnique

-- | Raw variable names
type Name = T.Text

-- | Top-level names
data TopName
  = Unqual Name
  | Qual (NE.NonEmpty Name) Name
  deriving stock (Eq)

instance Show TopName where
  showsPrec _ = \case
    Unqual n -> showString (T.unpack n)
    Qual (m NE.:| ns) n ->
      (m : ns ++ [n])
        & map (showString . T.unpack)
        & punctuate (showChar '.')

freshen :: [Name] -> Name -> Name
freshen ns = \case
  "_" -> "_"
  n
    | n `elem` ns -> freshen ns (T.snoc n '\'')
    | otherwise -> n
