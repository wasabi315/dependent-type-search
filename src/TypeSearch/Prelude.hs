module TypeSearch.Prelude
  ( -- * Re-exports
    module Prelude,
    module Control.Applicative,
    module Control.Exception,
    module Control.Monad,
    module Control.Monad.Except,
    module Control.Monad.IO.Class,
    module Control.Monad.Reader,
    module Control.Monad.State.Strict,
    module Data.Bifoldable,
    module Data.Bifoldable1,
    module Data.Bifunctor,
    module Data.Bitraversable,
    module Data.Coerce,
    module Data.Either,
    module Data.Foldable,
    module Data.Foldable1,
    module Data.Functor,
    module Data.Functor.Compose,
    module Data.Functor.Identity,
    module Data.Maybe,
    module Data.Monoid,
    module Data.Semigroup,
    module Data.String,
    module Data.Traversable,
    module Data.Void,
    module Witherable,
    Generic,
    Generically,
    Typeable,
    Hashable,
    FromJSON,
    ToJSON,
    Flat,
    HasCallStack,
    elemIndex,
    partition,
    sort,
    sortOn,

    -- * Utils
    impossible,
    down,
    choose,
    foldMapA,
    applyN,
    (//),
    timed,
    (??:),
    (??%),
  )
where

import Control.Applicative
import Control.Exception (Exception (..))
import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Aeson (FromJSON, ToJSON)
import Data.Bifoldable
import Data.Bifoldable1
import Data.Bifunctor
import Data.Bitraversable
import Data.Coerce
import Data.Either
import Data.Foldable hiding (foldl1, foldr1, maximum, maximumBy, minimum, minimumBy)
import Data.Foldable1
import Data.Functor
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Hashable
import Data.List (elemIndex, partition, sort, sortOn)
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing, listToMaybe, maybe, maybeToList)
import Data.Monoid hiding (First (..), Last (..))
import Data.Semigroup
import Data.String
import Data.Time.Clock
import Data.Traversable
import Data.Typeable (Typeable)
import Data.Void
import Flat (Flat)
import GHC.Generics (Generic, Generically)
import GHC.Stack
import Witherable
import Prelude hiding (curry, filter, foldl1, foldr1, head, last, maximum, minimum, unzip)

--------------------------------------------------------------------------------

impossible :: (HasCallStack) => a
impossible = error "impossible"

-- | @[x, pred x, ..., y]@
down :: (Enum a) => a -> a -> [a]
down x y = [x, pred x .. y]
{-# INLINE down #-}

foldMapA :: (Alternative f, Foldable t) => (a -> f b) -> t a -> f b
foldMapA f = foldr ((<|>) . f) empty
{-# INLINE foldMapA #-}

choose :: (Alternative f, Foldable t) => t a -> f a
choose = foldr ((<|>) . pure) empty
{-# INLINE choose #-}

applyN :: Int -> (a -> a) -> a -> a
applyN n f = case n of
  _ | n < 0 -> error "applyN: negative argument"
  0 -> id
  n -> f . applyN (n - 1) f

infix 2 //

-- | strict pair construction
(//) :: a -> b -> (a, b)
a // b = (a, b)

timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1 <- getCurrentTime
  res <- a
  t2 <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)

infixr 0 ??:, ??%

(??:) :: (MonadError e m) => Maybe a -> e -> m a
(??:) x_ e = maybe (throwError e) pure x_

(??%) :: (MonadError e' m) => Either e a -> (e -> e') -> m a
(??%) x f = case x of
  Left e -> throwError (f e)
  Right y -> pure y
