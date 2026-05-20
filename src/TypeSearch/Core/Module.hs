module TypeSearch.Core.Module
  ( Definition (..),
    Reexport (..),
    Module (..),
  )
where

import TypeSearch.Core.Name
import TypeSearch.Core.Term
import TypeSearch.Prelude

--------------------------------------------------------------------------------

data Definition = Definition
  { name :: QName,
    sig :: Type,
    body :: Maybe Term
  }
  deriving stock (Show, Generic)

data Reexport = Reexport
  { canonicalName :: QName,
    exportAs :: QName
  }
  deriving stock (Show, Generic)

data Module = Module
  { definitions :: [Definition],
    reexports :: [Reexport]
  }
  deriving stock (Show, Generic)
