module TypeSearch.Raw
  ( -- * Modules
    Module (..),
    Decl (..),

    -- * Raw terms
    Raw (..),
    pattern (:->),
    pattern (:*),
    rnatLit,
    unRLoc,
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
  = DLet Name Raw Raw
  | DLoc (Located Decl)
  deriving stock (Show)

-- | Raw terms
data Raw
  = RVar QName
  | RMetaApp Meta [Raw]
  | RType
  | RPi Name Raw Raw
  | RAbs Name Raw
  | RApp Raw Raw
  | RSigma Name Raw Raw
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
  | RLoc (Located Raw)
  deriving stock (Show)

pattern (:->) :: Raw -> Raw -> Raw
pattern t :-> u = RPi "_" t u

pattern (:*) :: Raw -> Raw -> Raw
pattern t :* u = RSigma "_" t u

rnatLit :: Int -> Raw
rnatLit = \case
  0 -> RZero
  n -> RSuc `RApp` rnatLit (n - 1)

unRLoc :: Raw -> Raw
unRLoc = \case
  RLoc (t :@ _) -> unRLoc t
  t -> t
