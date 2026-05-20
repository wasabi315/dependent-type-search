module TypeSearch.Core.Module
  ( Definition (..),
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

newtype Module = Module
  { definitions :: [Definition]
  }
