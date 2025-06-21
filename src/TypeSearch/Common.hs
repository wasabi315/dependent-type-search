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
    SourcePos (..),
  )
where

import Control.Applicative
import Data.Hashable
import Data.List (intersperse)
import Data.String
import Data.Text qualified as T
import Data.Unique
import GHC.Generics (Generic)
import Text.Megaparsec

--------------------------------------------------------------------------------
-- Utils

-- | @[x, x - 1, ..., y]@
down :: (Enum a, Num a) => a -> a -> [a]
down x y = [x, x - 1 .. y]
{-# INLINE down #-}

choose :: (Alternative f, Foldable t) => t a -> f a
choose = foldr ((<|>) . pure) empty
{-# INLINE choose #-}

applyN :: Int -> (a -> a) -> a -> a
applyN n _ _ | n < 0 = error "applyN: negative argument"
applyN 0 _ x = x
applyN n f x = f (applyN (n - 1) f x)
{-# INLINE applyN #-}

par :: Int -> Int -> ShowS -> ShowS
par p q = showParen (p > q)
{-# INLINE par #-}

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)
{-# INLINE punctuate #-}

enclose :: ShowS -> ShowS -> ShowS -> ShowS
enclose open close x = open . x . close
{-# INLINE enclose #-}

--------------------------------------------------------------------------------
-- Names

-- | De Bruijn indices
newtype Index = Index Int
  deriving newtype (Num, Eq, Ord, Show, Hashable, Enum)

-- | Metavariables
data Meta
  = Src Name
  | Inst Name [Name] -- generated during instantiation
  | Gen Unique -- generated during unification
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (Hashable)

instance Show Meta where
  showsPrec _ = \case
    Src n -> shows n
    Inst n _ -> showString "?I$" . shows n
    Gen u -> showString "?G$" . shows (hashUnique u)

-- | Generate a fresh metavariable.
freshMeta :: IO Meta
freshMeta = Gen <$> newUnique

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
freshen ns n@(Name n')
  | n `elem` ns = freshen ns (Name $ T.snoc n' '\'')
  | otherwise = n
