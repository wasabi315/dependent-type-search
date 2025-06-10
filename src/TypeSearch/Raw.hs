module TypeSearch.Raw
  ( -- * Modules
    Module (..),
    Decl (..),

    -- * Raw terms
    Raw (..),
    rnatLit,
    unRPos,
    freeVarSet,
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

data Decl = DLet SourcePos Name Raw Raw
  deriving stock (Show)

-- | Raw terms
data Raw
  = RVar QName
  | RGenVar Name
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

freeVarSet :: Raw -> HS.HashSet Name
freeVarSet = \case
  RVar (Qual _ n) -> HS.singleton n
  RVar (Unqual n) -> HS.singleton n
  RGenVar _ -> HS.empty
  RMetaApp _ ts -> foldMap freeVarSet ts
  RType -> HS.empty
  RPi x t1 t2 -> freeVarSet t1 <> HS.delete x (freeVarSet t2)
  RArr t1 t2 -> freeVarSet t1 <> freeVarSet t2
  RAbs x t -> HS.delete x (freeVarSet t)
  RApp t1 t2 -> freeVarSet t1 <> freeVarSet t2
  RSigma x t1 t2 -> freeVarSet t1 <> HS.delete x (freeVarSet t2)
  RProd t1 t2 -> freeVarSet t1 <> freeVarSet t2
  RPair t1 t2 -> freeVarSet t1 <> freeVarSet t2
  RFst t -> freeVarSet t
  RSnd t -> freeVarSet t
  RUnit -> HS.empty
  RTT -> HS.empty
  RNat -> HS.empty
  RZero -> HS.empty
  RSuc -> HS.empty
  RNatElim -> HS.empty
  REq -> HS.empty
  RRefl -> HS.empty
  REqElim -> HS.empty
  RPos t _ -> freeVarSet t
