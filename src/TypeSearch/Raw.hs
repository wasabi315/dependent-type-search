module TypeSearch.Raw
  ( -- * Raw terms
    Raw (..),
    pattern (:->),
    pattern (:*),
    metaVarSet,
  )
where

import Data.HashSet qualified as HS
import TypeSearch.Common

-- | Raw terms
data Raw
  = RVar Name
  | RMetaApp Meta [Raw]
  | RTop TopName
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
  deriving stock (Show)

pattern (:->) :: Raw -> Raw -> Raw
pattern t :-> u = RPi "_" t u

pattern (:*) :: Raw -> Raw -> Raw
pattern t :* u = RSigma "_" t u

metaVarSet :: Raw -> HS.HashSet Meta
metaVarSet = \case
  RVar _ -> HS.empty
  RMetaApp m ts -> HS.insert m (foldr (HS.union . metaVarSet) HS.empty ts)
  RTop _ -> HS.empty
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
