module TypeSearch.Raw
  ( -- * Modules
    Module (..),
    Decl (..),

    -- * Raw terms
    Raw (..),
    rnatLit,
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

data Decl = DLet SourcePos Name Raw Raw
  deriving stock (Show)

-- | Raw terms
data Raw
  = RVar QName
  | RMetaApp Meta [Raw]
  | RType
  | RPi Name Raw Raw
  | RArr Raw Raw -- non-dependent pi
  | RAbs Name Raw
  | RApp Raw Raw
  | RSigma Name Raw Raw
  | RProd Raw Raw -- non-dependent sigma
  | RPair Raw Raw
  | RFst Raw
  | RSnd Raw
  | RUnit
  | RTT
  | RNat
  | RZero
  | RSuc
  | RNatElim
  | REq
  | RRefl
  | REqElim
  | RPos Raw SourcePos
  deriving stock (Show)

rnatLit :: Int -> Raw
rnatLit = \case
  0 -> RZero
  n -> RSuc `RApp` rnatLit (n - 1)

unRPos :: Raw -> Raw
unRPos = \case
  RPos t _ -> unRPos t
  t -> t
