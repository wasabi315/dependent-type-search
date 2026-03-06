module TypeSearch.Raw
  ( -- * Possibly qualified names
    QName (..),

    -- * Modules
    Module (..),
    Decl (..),

    -- * Raw terms
    Raw (..),
    unRPos,
    rawSize,
  )
where

import Data.String
import TypeSearch.Common

--------------------------------------------------------------------------------

-- | Qualified names
data QName
  = Unqual Name
  | Qual ModuleName Name
  deriving stock (Eq)

instance IsString QName where
  fromString = Unqual . Name . fromString

instance Show QName where
  showsPrec _ = \case
    Unqual n -> shows n
    Qual m n -> shows m . showChar '.' . shows n

data Module = Module
  { name :: ModuleName,
    imports :: [ModuleName],
    decls :: [Decl]
  }
  deriving stock (Show)

data Decl
  = DLet (Maybe SourcePos) QName Raw Raw
  | DAxiom (Maybe SourcePos) QName Raw
  deriving stock (Show)

-- | Raw terms
data Raw
  = RVar QName
  | RMeta MetaVar
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
  RMeta _ -> 1
  RU -> 1
  RPi _ a b -> 1 + rawSize a + rawSize b
  RLam _ b -> 1 + rawSize b
  RApp f x -> 1 + rawSize f + rawSize x
  RSigma _ a b -> 1 + rawSize a + rawSize b
  RPair a b -> 1 + rawSize a + rawSize b
  RProj1 x -> 1 + rawSize x
  RProj2 x -> 1 + rawSize x
  RPos t _ -> rawSize t
