module TypeSearch.Raw
  ( -- * Possibly qualified names
    QName (..),

    -- * Modules
    Module (..),
    Decl (..),

    -- * Raw terms
    Raw (..),
    unRPos,
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

data Decl = DLet SourcePos Name Raw Raw
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
  | RFst Raw
  | RSnd Raw
  | RPos Raw SourcePos
  deriving stock (Show)

unRPos :: Raw -> Raw
unRPos = \case
  RPos t _ -> unRPos t
  t -> t
