module TypeSearch.Raw
  ( -- * Possibly qualified names
    PQName (..),

    -- * Modules
    Module (..),
    Decl (..),

    -- * Raw terms
    Raw (..),
    unRPos,
  )
where

import TypeSearch.Common

--------------------------------------------------------------------------------

data Module = Module
  { name :: ModuleName,
    imports :: [ModuleName],
    decls :: [Decl]
  }
  deriving stock (Show)

data Decl
  = DLet (Maybe SourcePos) PQName Raw Raw
  | DAxiom (Maybe SourcePos) PQName Raw
  deriving stock (Show)

-- | Raw terms
data Raw
  = RVar PQName
  | RU
  | RPi Name Raw Raw
  | RLam Name Raw
  | RApp Raw Raw
  | RSigma Name Raw Raw
  | RPair Raw Raw
  | RProj1 Raw
  | RProj2 Raw
  | RPos Raw SourcePos
  deriving stock (Show)

unRPos :: Raw -> Raw
unRPos = \case
  RPos t _ -> unRPos t
  t -> t
