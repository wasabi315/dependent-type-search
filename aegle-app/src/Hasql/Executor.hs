module Hasql.Executor
  ( Executor (..),
  )
where

import Hasql.Connection
import Hasql.Pool
import Hasql.Session
import Prelude

--------------------------------------------------------------------------------

class Executor a where
  type Error a
  execute :: a -> Session b -> IO (Either (Error a) b)

instance Executor Connection where
  type Error Connection = SessionError
  execute = flip run

instance Executor Pool where
  type Error Pool = UsageError
  execute = use
