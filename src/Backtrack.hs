{-# LANGUAGE NoStrict #-}

module Backtrack
  ( Backtrack,
    nil,
    cons,
    postpone,
    head,
    take,
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans
import Prelude hiding (head, take)

--------------------------------------------------------------------------------

newtype Backtrack m a = Backtrack (m (Step m a))
  deriving stock (Functor)

data Step m a
  = Nil
  | Cons a (Backtrack m a)
  | Postpone (Backtrack m a)
  deriving stock (Functor)

deriving stock instance (Show (m (Step m a))) => Show (Backtrack m a)

deriving stock instance (Show (m (Step m a)), Show a) => Show (Step m a)

unBacktrack :: Backtrack m a -> m (Step m a)
unBacktrack (Backtrack m) = m
{-# INLINE unBacktrack #-}

nil :: (Applicative m) => Backtrack m a
nil = Backtrack $ pure Nil
{-# INLINE nil #-}

cons :: (Applicative m) => a -> Backtrack m a -> Backtrack m a
cons x m = Backtrack $ pure $ Cons x m
{-# INLINE cons #-}

postpone :: (Applicative m) => Backtrack m a -> Backtrack m a
postpone m = Backtrack $ pure $ Postpone m
{-# INLINE postpone #-}

instance (Monad m) => Applicative (Backtrack m) where
  pure x = cons x nil
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

race :: (Monad m) => Backtrack m a -> Backtrack m a -> Backtrack m a
Backtrack m1 `race` Backtrack m2 = Backtrack do
  m1 >>= \case
    Nil -> m2
    Cons x m1' -> pure $ Cons x (m1' `race` Backtrack m2)
    Postpone m1' -> do
      m2 >>= \case
        Nil -> pure $ Postpone m1'
        Cons x m2' -> pure $ Cons x (postpone m1' `race` m2')
        Postpone m2' -> pure $ Postpone (m1' `race` m2')

instance (Monad m) => Alternative (Backtrack m) where
  empty = nil
  {-# INLINE empty #-}
  (<|>) = race
  {-# INLINE (<|>) #-}

instance (Monad m) => Monad (Backtrack m) where
  m >>= k = go m
    where
      go (Backtrack m1) = Backtrack do
        m1 >>= \case
          Nil -> pure Nil
          Cons x m2 -> unBacktrack $ k x <|> go m2
          Postpone m2 -> pure $ Postpone (go m2)
  {-# INLINE (>>=) #-}

instance (Monad m) => MonadPlus (Backtrack m)

instance MonadTrans Backtrack where
  lift m = Backtrack $ (`Cons` nil) <$> m
  {-# INLINE lift #-}

instance (MonadIO m) => MonadIO (Backtrack m) where
  liftIO m = Backtrack $ (`Cons` nil) <$> liftIO m
  {-# INLINE liftIO #-}

head :: (Monad m) => Backtrack m a -> m (Maybe a)
head (Backtrack m) =
  m >>= \case
    Nil -> pure Nothing
    Cons x _ -> pure $ Just x
    Postpone m' -> head m'
{-# INLINE head #-}

take :: (Monad m) => Int -> Backtrack m a -> m [a]
take n (Backtrack m) =
  m >>= \case
    Nil -> pure []
    Cons x m' -> (x :) <$> take (n - 1) m'
    Postpone m' -> take n m'
