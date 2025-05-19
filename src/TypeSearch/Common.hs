module TypeSearch.Common
  ( -- * Utils
    down,
    choose,

    -- * Names
    Index (..),
    Meta (..),
    freshMeta,
    Name,
    TopName,
    freshen,
  )
where

import Control.Applicative
import Data.Hashable
import Data.Unique

--------------------------------------------------------------------------------
-- Utils

-- | @[x, x - 1, ..., y]@
down :: (Enum a, Num a) => a -> a -> [a]
down x y = [x, x - 1 .. y]

choose :: (Alternative m, Foldable t) => t a -> m a
choose = foldr ((<|>) . pure) empty

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
type Name = String

-- | Top-level names
type TopName = String

freshen :: [Name] -> Name -> Name
freshen ns = \case
  "_" -> "_"
  n
    | n `elem` ns -> freshen ns (n ++ "'")
    | otherwise -> n
