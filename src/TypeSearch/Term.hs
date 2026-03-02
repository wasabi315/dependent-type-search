module TypeSearch.Term where

import Data.HashMap.Strict qualified as HM
import Data.Hashable
import GHC.Generics
import TypeSearch.Common

--------------------------------------------------------------------------------

data QName = QName
  { moduleName :: ModuleName,
    name :: Name
  }
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (Hashable)

instance Show QName where
  showsPrec _ x = shows x.moduleName . showChar '.' . shows x.name

-- | Terms
data Term
  = Var Index -- x
  | Meta MetaVar -- ?m
  | Top {-# UNPACK #-} QName (DontPrint (Maybe Value)) -- M.f, Nothing for axioms
  | U -- U
  | Pi Name Term Term -- (x : A) → B
  | Lam Name Term -- λ x → t
  | App Term Term -- t1 t2
  | AppPruning Term Pruning
  | Sigma Name Term Term -- (x : A) × B
  | Pair Term Term -- (t1, t2)
  | Fst Term -- t.1
  | Snd Term -- t.2
  deriving stock (Show)

--------------------------------------------------------------------------------
-- Values

-- | De Bruijn levels
newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show, Hashable)

-- | Values
data Value
  = VRigid Level Spine
  | VFlex MetaVar Spine
  | VTop {-# UNPACK #-} QName (Maybe Value) Spine (Maybe Value) -- Nothing for axioms
  | VU
  | VPi Name Value (Value -> Value)
  | VLam Name (Value -> Value)
  | VSigma Name Value (Value -> Value)
  | VPair Value Value

data Spine
  = SNil
  | SApp Spine Value
  | SFst Spine
  | SSnd Spine

pattern VVar :: Level -> Value
pattern VVar x = VRigid x SNil

pattern VMeta :: MetaVar -> Value
pattern VMeta m = VFlex m SNil

data Quant = Quant Name Value (Value -> Value)

-- | Environment keyed by De Bruijn indices
type Env = [Value]

-- | Environment keyed by top-level names
type TopEnv = HM.HashMap QName (Maybe Value)

-- | Meta-context
data MetaCtx = MetaCtx
  { nextMeta :: GenMetaVar,
    metaCtx :: HM.HashMap MetaVar MetaEntry
  }

data MetaEntry
  = Unsolved ~Value
  | Solved Value ~Value

emptyMetaCtx :: MetaCtx
emptyMetaCtx = MetaCtx 0 mempty

type Pruning = [Bool]

newtype RevPruning = RevPruning Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning . reverse

--------------------------------------------------------------------------------
-- Isomorphisms

data Iso
  = --  -------
    --   A ~ A
    Refl
  | --   A ~ B
    --  -------
    --   B ~ A
    Sym Iso
  | --   A ~ B    B ~ C
    --  ----------------
    --       A ~ C
    Trans Iso Iso
  | --  ----------------------------------------------------------------
    --   (x : (y : A) * B[y]) * C[x] ~ (y : A) * (x : B[y]) * C[(x, y)]
    Assoc
  | --  ---------------
    --   A * B ~ B * A
    Comm
  | -- ---------------------------------------------
    --  (x : A) * (y : B) * C ~ (y : B) * (x : A) * C
    --
    -- derivable from comm and assoc
    SigmaSwap
  | --  -------------------------------------------------------------------
    --   (x : (y : A) * B[y]) -> C[x] ~ (y : A) -> (x : B[y]) -> C[(x, y)]
    Curry
  | -- ---------------------------------------------
    --  (x : A) (y : B) -> C ~ (y : B) (x : A) -> C
    --
    -- derivable from comm and curry
    PiSwap
  | --                     i : A ~ A'
    --  ---------------------------------------------------
    --   (x : A) -> B[x] ~ (x : A') -> B[transportInv i x]
    PiCongL Iso
  | --             B[x] ~ B'[x]
    --  ------------------------------------
    --   (x : A) -> B[x] ~ (x : A) -> B'[x]
    PiCongR Iso
  | --                     i : A ~ A'
    --  -------------------------------------------------
    --   (x : A) * B[x] ~ (x : A') * B[transportInv i x]
    SigmaCongL Iso
  | --           B[x] ~ B'[x]
    --  ----------------------------------
    --   (x : A) * B[x] ~ (x : A) * B'[x]
    SigmaCongR Iso
  deriving stock (Show)

instance Semigroup Iso where
  Refl <> j = j
  i <> Refl = i
  i <> j = Trans i j

instance Monoid Iso where
  mempty = Refl

sym :: Iso -> Iso
sym = \case
  Refl -> Refl
  Sym i -> i
  i -> Sym i

piCongL :: Iso -> Iso
piCongL = \case
  Refl -> Refl
  i -> PiCongL i

piCongR :: Iso -> Iso
piCongR = \case
  Refl -> Refl
  i -> PiCongR i

sigmaCongL :: Iso -> Iso
sigmaCongL = \case
  Refl -> Refl
  i -> SigmaCongL i

sigmaCongR :: Iso -> Iso
sigmaCongR = \case
  Refl -> Refl
  i -> SigmaCongR i
