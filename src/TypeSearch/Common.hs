module TypeSearch.Common
  ( -- * Utils
    down,
    choose,
    applyN,
    foldMapA,
    (//),

    -- * Names
    Index (..),
    GenMetaVar (..),
    MetaVar (..),
    Name (..),
    ModuleName (..),
    freshen,

    -- * Position
    SourcePos (..),
  )
where

import Data.Monoid
import Control.Applicative
import Data.Coerce
import Data.Hashable
import Data.String
import Data.Text qualified as T
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

infix 2 //

-- strict pair construction
(//) :: a -> b -> (a, b)
a // b = (a, b)

foldMapA :: (Alternative f, Foldable t) => (a -> f b) -> t a -> f b
foldMapA f = getAlt . foldMap (Alt . f)

--------------------------------------------------------------------------------
-- Names

-- | De Bruijn indices
newtype Index = Index Int
  deriving newtype (Num, Eq, Ord, Show, Hashable, Enum)

-- | Generated metavariables
newtype GenMetaVar = GenMetaVar Int
  deriving newtype (Num, Eq, Ord, Show, Hashable, Enum)

-- | Metavariables
data MetaVar
  = Src Name
  | Gen GenMetaVar -- generated during unification
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (Hashable)

instance Show MetaVar where
  showsPrec _ = \case
    Src n -> shows n
    Gen (GenMetaVar u) -> showString "?G$" . shows u

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
