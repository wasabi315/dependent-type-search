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
    metaVarSet,
  )
where

import Data.HashSet qualified as HS
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

metaVarSet :: Raw -> HS.HashSet Meta
metaVarSet = \case
  RVar _ -> HS.empty
  RMetaApp m ts -> HS.insert m (foldr (HS.union . metaVarSet) HS.empty ts)
  RType -> HS.empty
  RPi _ a b -> HS.union (metaVarSet a) (metaVarSet b)
  RAbs _ t -> metaVarSet t
  RApp a b -> HS.union (metaVarSet a) (metaVarSet b)
  RSigma _ a b -> HS.union (metaVarSet a) (metaVarSet b)
  RPair a b -> HS.union (metaVarSet a) (metaVarSet b)
  RFst t -> metaVarSet t
  RSnd t -> metaVarSet t
  RUnit -> HS.empty
  RTT -> HS.empty
  RNat -> HS.empty
  RZero -> HS.empty
  RSuc -> HS.empty
  RNatElim -> HS.empty
  RLoc (t :@ _) -> metaVarSet t
