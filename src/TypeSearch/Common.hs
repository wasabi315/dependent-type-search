module TypeSearch.Common
  ( -- * Utils
    impossible,
    down,
    choose,
    applyN,
    foldMapA,
    (//),
    DontPrint (..),

    -- * Names
    Index (..),
    Level (..),
    MetaVar (..),
    Name (..),
    ModuleName (..),
    QName (..),
    PQName (..),
    freshen,

    -- * Position
    SourcePos (..),

    -- * Re-exports
    module Data.Coerce,
    module Flat,
  )
where

import Control.Applicative
import Data.Coerce
import Data.Hashable
import Data.Monoid
import Data.String
import Data.Text qualified as T
import Flat
import GHC.Stack
import Text.Megaparsec

--------------------------------------------------------------------------------
-- Utils

impossible :: (HasCallStack) => a
impossible = error "impossible"

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

infix 2 //

-- strict pair construction
(//) :: a -> b -> (a, b)
a // b = (a, b)

foldMapA :: (Alternative f, Foldable t) => (a -> f b) -> t a -> f b
foldMapA f = getAlt . foldMap (Alt . f)

newtype DontPrint a = DontPrint a

instance Show (DontPrint a) where
  showsPrec _ _ = id

--------------------------------------------------------------------------------
-- Names

-- | De Bruijn indices
newtype Index = Index Int
  deriving newtype (Num, Eq, Ord, Show, Hashable, Enum, Flat)

-- | De Bruijn levels
newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show, Hashable, Flat)

-- | Metavariables
newtype MetaVar = GenMetaVar Int
  deriving newtype (Num, Eq, Ord, Hashable, Enum, Flat)

instance Show MetaVar where
  showsPrec _ (GenMetaVar m) = showString "?G%" . shows m

-- | Names
newtype Name = Name T.Text
  deriving newtype (Eq, Ord, Hashable, IsString, Flat)

instance Show Name where
  showsPrec _ (Name n) = showString (T.unpack n)

-- | Module names
newtype ModuleName = ModuleName T.Text
  deriving newtype (Eq, Ord, Hashable, IsString, Flat)

instance Show ModuleName where
  showsPrec _ (ModuleName n) = showString (T.unpack n)

-- | Qualified names
data QName = QName
  { moduleName :: ModuleName,
    name :: Name
  }
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (Hashable, Flat)

instance Show QName where
  showsPrec _ x = shows x.moduleName . showChar '.' . shows x.name

-- | Possibly qualified names
data PQName
  = Unqual Name
  | Qual ModuleName Name
  deriving stock (Eq)

instance IsString PQName where
  fromString = Unqual . Name . fromString

instance Show PQName where
  showsPrec _ = \case
    Unqual n -> shows n
    Qual m n -> shows m . showChar '.' . shows n

freshen :: [Name] -> Name -> Name
freshen ns n
  | n `elem` ns = go 0
  | otherwise = n
  where
    go (i :: Int)
      | n' `notElem` ns = n'
      | otherwise = go (i + 1)
      where
        n' = Name $ coerce n <> T.pack (map subscript (show i))

subscript :: Char -> Char
subscript = \case
  '0' -> '₀'
  '1' -> '₁'
  '2' -> '₂'
  '3' -> '₃'
  '4' -> '₄'
  '5' -> '₅'
  '6' -> '₆'
  '7' -> '₇'
  '8' -> '₈'
  '9' -> '₉'
  c -> c
