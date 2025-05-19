module TypeSearch.Evaluation
  ( -- * Values
    Level (..),
    RawEnv,
    Env,
    Value (..),
    pattern VVar,
    pattern VMetaApp,
    Elim (..),
    Spine,
    pattern SNil,
    pattern SApp,
    pattern SFst,
    pattern SSnd,
    pattern SApp',
    pattern SFst',
    pattern SSnd',
    Head (..),
    headSpine,

    -- * Evaluation
    evaluateRaw,
    evaluate,
    vapp,
    vfst,
    vsnd,
    vappSpine,
    vmetaApp,

    -- * Quotation
    quote,

    -- * Forcing
    force,
    deepForce,
  )
where

import Data.Foldable
import Data.HashMap.Strict qualified as HM
import Data.Sequence qualified as Seq
import TypeSearch.Common
import TypeSearch.Raw
import TypeSearch.Term

--------------------------------------------------------------------------------

-- | De Bruijn levels
newtype Level = Level Int
  deriving newtype (Num, Eq, Ord, Show, Enum)

-- | Environment keyed by raw variable names
type RawEnv = HM.HashMap Name Value

-- | Environments keyed by De Bruijn indices
type Env = [Value]

-- | Values support efficient β-reduction and substitution.
data Value
  = VRigid Level Spine
  | VFlex Meta Int [Value] Spine -- metavariables are parametarised in SOAS
  | VTop TopName Spine
  | VType
  | VPi Name Value (Value -> Value)
  | VAbs Name (Value -> Value)
  | VSigma Name Value (Value -> Value)
  | VPair Value Value
  | VUnit
  | VTT
  | VStuck Value Spine -- failed to eliminate

pattern VVar :: Level -> Value
pattern VVar l = VRigid l SNil

pattern VMetaApp :: Meta -> [Value] -> Value
pattern VMetaApp m vs <- VFlex m _ vs SNil
  where
    VMetaApp m vs = VFlex m (length vs) vs SNil

data Elim
  = EApp Value
  | EFst
  | ESnd

type Spine = Seq.Seq Elim

{-# COMPLETE SNil, SApp, SFst, SSnd #-}

{-# COMPLETE SNil, SApp', SFst', SSnd' #-}

pattern SNil :: Spine
pattern SNil = Seq.Empty

pattern SApp :: Spine -> Value -> Spine
pattern SApp sp v = sp Seq.:|> EApp v

pattern SFst :: Spine -> Spine
pattern SFst sp = sp Seq.:|> EFst

pattern SSnd :: Spine -> Spine
pattern SSnd sp = sp Seq.:|> ESnd

pattern SApp' :: Value -> Spine -> Spine
pattern SApp' v sp = EApp v Seq.:<| sp

pattern SFst' :: Spine -> Spine
pattern SFst' sp = EFst Seq.:<| sp

pattern SSnd' :: Spine -> Spine
pattern SSnd' sp = ESnd Seq.:<| sp

data Head
  = HRigid Level
  | HFlex Meta Int [Value]
  | HTop TopName
  | HType
  | HPi Name Value (Value -> Value)
  | HAbs Name (Value -> Value)
  | HSigma Name Value (Value -> Value)
  | HPair Value Value
  | HUnit
  | HTT
  | HStuck Value

headSpine :: Value -> (Head, Spine)
headSpine = \case
  VRigid l sp -> (HRigid l, sp)
  VFlex m ar vs sp -> (HFlex m ar vs, sp)
  VTop n sp -> (HTop n, sp)
  VType -> (HType, SNil)
  VPi x a b -> (HPi x a b, SNil)
  VAbs x f -> (HAbs x f, SNil)
  VSigma x a b -> (HSigma x a b, SNil)
  VPair a b -> (HPair a b, SNil)
  VUnit -> (HUnit, SNil)
  VTT -> (HTT, SNil)
  VStuck v sp -> (HStuck v, sp)

evaluateRaw :: HM.HashMap Name Value -> Raw -> Value
evaluateRaw env = \case
  RVar n -> env HM.! n
  RMetaApp m ts -> VMetaApp m $ map (evaluateRaw env) ts
  RTop n -> VTop n SNil
  RType -> VType
  RPi x a b -> VPi x (evaluateRaw env a) \v -> evaluateRaw (HM.insert x v env) b
  RAbs x t -> VAbs x \v -> evaluateRaw (HM.insert x v env) t
  RApp t u -> vapp (evaluateRaw env t) (evaluateRaw env u)
  RSigma x a b -> VSigma x (evaluateRaw env a) \v -> evaluateRaw (HM.insert x v env) b
  RPair a b -> VPair (evaluateRaw env a) (evaluateRaw env b)
  RFst t -> vfst $ evaluateRaw env t
  RSnd t -> vsnd $ evaluateRaw env t
  RUnit -> VUnit
  RTT -> VTT

-- | Convert a term into a value.
evaluate :: Env -> Term -> Value
evaluate env = \case
  Var (Index i) -> env !! i
  MetaApp m ts -> VMetaApp m $ map (evaluate env) ts
  Top n -> VTop n SNil
  Type -> VType
  Pi x a b -> VPi x (evaluate env a) \v -> evaluate (v : env) b
  Abs x t -> VAbs x \v -> evaluate (v : env) t
  App t u -> vapp (evaluate env t) (evaluate env u)
  Sigma x a b -> VSigma x (evaluate env a) \v -> evaluate (v : env) b
  Pair t u -> VPair (evaluate env t) (evaluate env u)
  Fst t -> vfst $ evaluate env t
  Snd t -> vsnd $ evaluate env t
  Unit -> VUnit
  TT -> VTT

-- | Application in "the value world".
vapp :: Value -> Value -> Value
vapp vt vu = case vt of
  VAbs _ f -> f vu
  VRigid l sp -> VRigid l (SApp sp vu)
  VFlex m ar vs sp -> VFlex m ar vs (SApp sp vu)
  VTop n sp -> VTop n (SApp sp vu)
  VStuck v sp -> VStuck v (SApp sp vu)
  _ -> VStuck vt (SApp SNil vu)

-- | Projections in "the value world".
vfst, vsnd :: Value -> Value
vfst = \case
  VPair v _ -> v
  VRigid l sp -> VRigid l (SFst sp)
  VFlex m ar vs sp -> VFlex m ar vs (SFst sp)
  VTop n sp -> VTop n (SFst sp)
  VStuck v sp -> VStuck v (SFst sp)
  v -> VStuck v (SFst SNil)
vsnd = \case
  VPair _ v -> v
  VRigid l sp -> VRigid l (SSnd sp)
  VFlex m ar vs sp -> VFlex m ar vs (SSnd sp)
  VTop n sp -> VTop n (SSnd sp)
  VStuck v sp -> VStuck v (SSnd sp)
  v -> VStuck v (SSnd SNil)

-- | Apply an elimination to a value.
vappElim :: Value -> Elim -> Value
vappElim v = \case
  EApp u -> vapp v u
  EFst -> vfst v
  ESnd -> vsnd v

-- | Apply a value to a spine.
vappSpine :: Value -> Spine -> Value
vappSpine v sp = foldl' vappElim v sp

-- | Apply a meta-abstraction to arguments.
vmetaApp :: MetaAbs -> [Value] -> Value
vmetaApp (MetaAbs _arity body) args = evaluate (reverse args) body

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index (l - x - 1)

-- | Convert back a value into a term.
quote :: Level -> Value -> Term
quote lvl = \case
  VRigid x sp -> quoteSpine lvl (Var $ levelToIndex lvl x) sp
  VFlex m _ vs sp -> quoteSpine lvl (MetaApp m $ map (quote lvl) vs) sp
  VTop n sp -> quoteSpine lvl (Top n) sp
  VType -> Type
  VPi x va vb -> Pi x (quote lvl va) (quote (lvl + 1) $ vb (VVar lvl))
  VAbs x v -> Abs x $ quote (lvl + 1) $ v (VVar lvl)
  VSigma x va vb -> Sigma x (quote lvl va) (quote (lvl + 1) $ vb (VVar lvl))
  VPair vt vu -> Pair (quote lvl vt) (quote lvl vu)
  VUnit -> Unit
  VTT -> TT
  VStuck v sp -> quoteSpine lvl (quote lvl v) sp

quoteElim :: Level -> Term -> Elim -> Term
quoteElim lvl t = \case
  EApp u -> App t (quote lvl u)
  EFst -> Fst t
  ESnd -> Snd t

-- | Convert a spine into a term.
quoteSpine :: Level -> Term -> Spine -> Term
quoteSpine lvl hd sp = foldl' (quoteElim lvl) hd sp

-- | Force metavariables
force :: MetaSubst -> Value -> Value
force subst = go
  where
    go = \case
      VFlex m _ vs sp
        | Just mabs <- HM.lookup m subst -> go $ vappSpine (vmetaApp mabs vs) sp
      v -> v

deepForce :: MetaSubst -> Value -> Value
deepForce subst = go
  where
    go v = case force subst v of
      VFlex m ar vs sp -> VFlex m ar vs (goSpine sp)
      VRigid l sp -> VRigid l (goSpine sp)
      VTop n sp -> VTop n (goSpine sp)
      VType -> VType
      VPi x a b -> VPi x (go a) (go . b)
      VAbs x f -> VAbs x (go . f)
      VSigma x a b -> VSigma x (go a) (go . b)
      VPair a b -> VPair (go a) (go b)
      VUnit -> VUnit
      VTT -> VTT
      VStuck u sp -> VStuck (go u) (goSpine sp)

    goSpine = fmap goElim

    goElim = \case
      EApp v -> EApp (go v)
      EFst -> EFst
      ESnd -> ESnd
