module Data.Set.NonEmpty.Extra
  ( pattern Singleton,
  )
where

import Control.Arrow ((&&&))
import Data.Set.NonEmpty

pattern Singleton :: a -> NESet a
pattern Singleton x <- (size &&& findMin -> (1, x))
  where
    Singleton x = singleton x
