module Aegle.Prelude
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
    module Data.Containers.ListUtils,
    module Data.Either,
    module Data.Foldable,
    module Data.Foldable1,
    module Data.Function,
    module Data.Functor,
    module Data.Functor.Compose,
    module Data.Functor.Contravariant,
    module Data.Functor.Identity,
    module Data.Maybe,
    module Data.Monoid,
    module Data.Ord,
    module Data.Semigroup,
    module Data.String,
    module Data.Traversable,
    module Data.Void,
    module GHC.Records,
    module Lens.Micro.Platform,
    module Witherable,
    (***),
    (&&&),
    Generic,
    Generically (..),
    Typeable,
    NFData,
    ($!!),
    Hashable,
    HasCallStack,
    elemIndex,
    intersperse,
    partition,
    sort,
    sortOn,
    (!?),
    readMaybe,
    Profunctor (..),
    (:!),
    (:?),
    (!),
    pattern Arg,
    pattern ArgF,
    arg,
    argDef,
    argF,
    defaults,

    -- * Utils
    impossible,
    implies,
    down,
    choose,
    foldMapA,
    applyN,
    (//),
    timed,
    timedPure,
    (??:),
    (??%),
    (?:),
    (?%),
    orThrow,
    trace,
    traceFalse,
    type (⊢) (..),
  )
where

import Control.Applicative
import Control.Arrow ((&&&), (***))
import Control.DeepSeq
import Control.Exception (Exception (..), throwIO)
import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bifoldable
import Data.Bifoldable1
import Data.Bifunctor
import Data.Bitraversable
import Data.Coerce
import Data.Containers.ListUtils
import Data.Either
import Data.Foldable hiding (foldl1, foldr1, maximum, maximumBy, minimum, minimumBy)
import Data.Foldable1
import Data.Function
import Data.Functor
import Data.Functor.Compose
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Generics.Labels ()
import Data.Hashable
import Data.List (elemIndex, intersperse, partition, sort, sortOn, (!?))
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing, listToMaybe, maybe, maybeToList)
import Data.Monoid hiding (First (..), Last (..))
import Data.Ord
import Data.Profunctor
import Data.Semigroup hiding (Arg (..))
import Data.String
import Data.Time.Clock
import Data.Traversable
import Data.Typeable (Typeable)
import Data.Void
import GHC.Generics
import GHC.Records
import GHC.Stack
import Lens.Micro.Platform
import Named
import Text.Read
import Witherable
import Prelude hiding (curry, filter, foldl1, foldr1, head, last, maximum, minimum, unzip)

#ifdef DEBUG
import Debug.Trace qualified
#endif

--------------------------------------------------------------------------------

impossible :: (HasCallStack) => String -> a
impossible msg = error $ "impossible: " ++ msg

infixr 1 `implies`

implies :: Bool -> Bool -> Bool
implies p q = not p || q

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

timed :: (MonadIO m) => m a -> m (a, NominalDiffTime)
timed a = do
  t1 <- liftIO getCurrentTime
  res <- a
  t2 <- liftIO getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# INLINE timed #-}

timedPure :: (MonadIO m) => a -> m (a, NominalDiffTime)
timedPure ~a = do
  t1 <- liftIO getCurrentTime
  let res = a
  t2 <- liftIO getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# NOINLINE timedPure #-}

infix 0 ??:, ??%

(??:) :: (MonadError e m) => Maybe a -> e -> m a
(??:) x e = maybe (throwError e) pure x

(??%) :: (MonadError e' m) => Either e a -> (e -> e') -> m a
(??%) x f = either (throwError . f) pure x

(?:) :: (MonadError e m) => m (Maybe a) -> e -> m a
(?:) m e = m >>= (??: e)

(?%) :: (MonadError e' m) => m (Either e a) -> (e -> e') -> m a
(?%) m e = m >>= (??% e)

orThrow :: (Exception a) => IO (Either a b) -> IO b
orThrow m = either throwIO pure =<< m

data a ⊢ b = a :⊢ b

#ifdef DEBUG

trace :: String -> a -> a
trace = Debug.Trace.trace

#else

trace :: String -> a -> a
trace ~_ x = x

#endif

traceFalse :: String -> Bool
traceFalse ~s = trace s False
