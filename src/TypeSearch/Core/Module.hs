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

data Reexport = Reexport
  { canonicalName :: QName,
    exportAs :: QName
  }

data Module = Module
  { moduleName :: ModuleName,
    definitions :: [Definition],
    reexports :: [Reexport]
  }
