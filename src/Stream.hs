module Stream
  ( Stream (..),
    streamToMaybe,
    streamToList,
    maybeToStream,
    listToStream,
  )
where

import Control.Applicative
import Control.Monad

--------------------------------------------------------------------------------

-- | Immature streams. Strict in elements.
data Stream a
  = Nil
  | Cons a ~(Stream a)
  | Later ~(Stream a)
  deriving stock (Show, Functor, Foldable, Traversable)

union :: Stream a -> Stream a -> Stream a
xs `union` ~ys = case xs of
  Nil -> ys
  Cons x xs -> Cons x (xs `union` ys)
  xs@(Later xs') -> case ys of
    Nil -> xs
    Cons y ys -> Cons y (ys `union` xs)
    Later ys -> Later (xs' `union` ys)

instance Semigroup (Stream a) where
  (<>) = union
  {-# INLINE (<>) #-}

instance Monoid (Stream a) where
  mempty = Nil
  {-# INLINE mempty #-}

instance Applicative Stream where
  pure x = Cons x Nil
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Alternative Stream where
  empty = Nil
  {-# INLINE empty #-}
  (<|>) = union
  {-# INLINE (<|>) #-}

instance Monad Stream where
  m >>= k = go m
    where
      go = \case
        Nil -> Nil
        Cons x xs -> k x <|> go xs
        Later xs -> Later (go xs)
  {-# INLINE (>>=) #-}

instance MonadPlus Stream

streamToMaybe :: Stream a -> Maybe a
streamToMaybe = \case
  Nil -> Nothing
  Cons x _ -> Just x
  Later xs -> streamToMaybe xs

streamToList :: Stream a -> [a]
streamToList = \case
  Nil -> []
  Cons x xs -> x : streamToList xs
  Later xs -> streamToList xs

maybeToStream :: Maybe a -> Stream a
maybeToStream = \case
  Nothing -> Nil
  Just x -> Cons x Nil

listToStream :: [a] -> Stream a
listToStream = \case
  [] -> Nil
  x : xs -> Cons x (listToStream xs)
