module TypeSearch.Common
  ( -- * Utils
    down,
    choose,
    applyN,
    par,
    punctuate,
    enclose,

    -- * Names
    Index (..),
    Meta (..),
    freshMeta,
    Name (..),
    ModuleName (..),
    QName (..),
    freshen,

    -- * Position
    Located (..),
    HasPosition (..),
    value,
    mergePosition,
  )
where

import Control.Applicative
import Data.Hashable
import Data.List (intersperse)
import Data.String
import Data.Text qualified as T
import Data.Unique
import Error.Diagnose

--------------------------------------------------------------------------------
-- Utils

-- | @[x, x - 1, ..., y]@
down :: (Enum a, Num a) => a -> a -> [a]
down x y = [x, x - 1 .. y]

choose :: (Alternative f, Foldable t) => t a -> f a
choose = foldr ((<|>) . pure) empty

applyN :: Int -> (a -> a) -> a -> a
applyN n _ _ | n < 0 = error "applyN: negative argument"
applyN 0 _ x = x
applyN n f x = f (applyN (n - 1) f x)

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

-- | Names
newtype Name = Name T.Text
  deriving newtype (Eq, Ord, Hashable, IsString)

instance Show Name where
  showsPrec _ (Name n) = showString (T.unpack n)

-- | Module names
newtype ModuleName = ModuleName T.Text
  deriving newtype (Eq, Ord, Hashable, IsString)

instance Show ModuleName where
  showsPrec _ (ModuleName n) = showString (T.unpack n)

-- | Qualified names
data QName
  = Unqual Name
  | Qual ModuleName Name
  deriving stock (Eq)

instance IsString QName where
  fromString = Unqual . Name . T.pack

instance Show QName where
  showsPrec _ = \case
    Unqual n -> shows n
    Qual m n -> shows m . showChar '.' . shows n

freshen :: [Name] -> Name -> Name
freshen ns = \case
  "_" -> "_"
  n@(Name n')
    | n `elem` ns -> freshen ns (Name $ T.snoc n' '\'')
    | otherwise -> n

--------------------------------------------------------------------------------

data Located a = a :@ Position
  deriving stock (Functor, Foldable, Traversable, Show)

class HasPosition a where
  position :: a -> Position

instance HasPosition (Located a) where
  position (_ :@ p) = p

instance HasPosition Position where
  position = id

value :: Located a -> a
value (a :@ _) = a

mergePosition :: (HasPosition a, HasPosition b) => a -> b -> Position
mergePosition (position -> Position s _ f) (position -> Position _ e _) = Position s e f
