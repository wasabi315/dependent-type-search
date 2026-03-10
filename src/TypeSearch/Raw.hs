module TypeSearch.Raw
  ( -- * Possibly qualified names
    PQName (..),

    -- * Modules
    Module (..),
    Decl (..),

    -- * Raw terms
    Raw (..),
    unRPos,
    rawSize,
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

rawSize :: Raw -> Int
rawSize = \case
  RVar _ -> 1
  RU -> 1
  RPi _ a b -> 1 + rawSize a + rawSize b
  RLam _ b -> 1 + rawSize b
  RApp f x -> 1 + rawSize f + rawSize x
  RSigma _ a b -> 1 + rawSize a + rawSize b
  RPair a b -> 1 + rawSize a + rawSize b
  RProj1 x -> 1 + rawSize x
  RProj2 x -> 1 + rawSize x
  RPos t _ -> rawSize t
