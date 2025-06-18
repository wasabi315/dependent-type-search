module TypeSearch.Evaluation
  ( -- * Values
    Level (..),
    RawEnv,
    Env,
    TopEnv,
    Value (..),
    pattern VVar,
    pattern VMetaApp,
    Elim (..),
    Spine,
    pattern SNil,
    pattern SApp,
    pattern SFst,
    pattern SSnd,
    pattern SNatElim,
    pattern SEqElim,
    pattern SApp',
    pattern SFst',
    pattern SSnd',
    pattern SNatElim',
    pattern SEqElim',
    spine,

    -- * Evaluation
    evaluateRaw,
    evaluate,
    vapp,
    vfst,
    vsnd,
    vnatElim,
    vappSpine,
    vmetaApp,

    -- * Quotation
    levelToIndex,
    quote,

    -- * Forcing
    force,
    deepForce,

    -- * Errors
    EvalError (..),
  )
where

import Control.Exception (Exception (..), throw)
import Data.Foldable
import Data.HashMap.Lazy qualified as HM
import Data.Hashable
import Data.Sequence qualified as Seq
import TypeSearch.Common
import TypeSearch.Raw
import TypeSearch.Term

--------------------------------------------------------------------------------
-- Values

-- | De Bruijn levels
newtype Level = Level Int
  deriving newtype (Num, Eq, Ord, Show, Enum, Hashable)

-- | Environment keyed by raw variable names
type RawEnv = HM.HashMap Name Value

-- | Environments keyed by De Bruijn indices
type Env = [Value]

-- | Environment keyed by top-level names
type TopEnv = HM.HashMap Name (HM.HashMap ModuleName Value)

-- | Values support efficient β-reduction and substitution.
data Value
  = VRigid Level Spine
  | -- metavariables are parametarised in SOAS
    -- TODO: make strict in the arguments
    VFlex Meta Int [Value] Spine
  | VTop Name Spine [(ModuleName, Value)]
  | VType
  | VPi Name Value (Value -> Value)
  | VArr Value Value
  | VAbs Name (Value -> Value)
  | VSigma Name Value (Value -> Value)
  | VProd Value Value
  | VPair Value Value
  | VUnit
  | VTT
  | VNat
  | VZero
  | VSuc Value
  | VEq Value Value Value
  | VRefl Value Value
  | VStuck Value Spine

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
  | ENatElim Value Value Value
  | EEqElim Value Value Value Value Value

type Spine = Seq.Seq Elim

{-# COMPLETE SNil, SApp, SFst, SSnd, SNatElim, SEqElim #-}

{-# COMPLETE SNil, SApp', SFst', SSnd', SNatElim', SEqElim' #-}

pattern SNil :: Spine
pattern SNil = Seq.Empty

pattern SApp :: Spine -> Value -> Spine
pattern SApp sp v = sp Seq.:|> EApp v

pattern SFst :: Spine -> Spine
pattern SFst sp = sp Seq.:|> EFst

pattern SSnd :: Spine -> Spine
pattern SSnd sp = sp Seq.:|> ESnd

pattern SNatElim :: Value -> Value -> Value -> Spine -> Spine
pattern SNatElim p s z sp = sp Seq.:|> ENatElim p s z

pattern SEqElim :: Value -> Value -> Value -> Value -> Value -> Spine -> Spine
pattern SEqElim a x p r y sp = sp Seq.:|> EEqElim a x p r y

pattern SApp' :: Value -> Spine -> Spine
pattern SApp' v sp = EApp v Seq.:<| sp

pattern SFst' :: Spine -> Spine
pattern SFst' sp = EFst Seq.:<| sp

pattern SSnd' :: Spine -> Spine
pattern SSnd' sp = ESnd Seq.:<| sp

pattern SNatElim' :: Value -> Value -> Value -> Spine -> Spine
pattern SNatElim' p s z sp = ENatElim p s z Seq.:<| sp

pattern SEqElim' :: Value -> Value -> Value -> Value -> Value -> Spine -> Spine
pattern SEqElim' a x p r y sp = EEqElim a x p r y Seq.:<| sp

spine :: Value -> Spine
spine = \case
  VRigid _ sp -> sp
  VFlex _ _ _ sp -> sp
  VTop _ sp _ -> sp
  VType -> SNil
  VPi {} -> SNil
  VArr {} -> SNil
  VAbs {} -> SNil
  VSigma {} -> SNil
  VProd {} -> SNil
  VPair {} -> SNil
  VUnit -> SNil
  VTT -> SNil
  VNat -> SNil
  VZero -> SNil
  VSuc {} -> SNil
  VEq {} -> SNil
  VRefl {} -> SNil
  VStuck _ sp -> sp

data EvalError
  = VarNotFound QName
  | ArityMismatch
  deriving stock (Show)

instance Exception EvalError where
  displayException = \case
    VarNotFound n -> "Variable not found: " ++ show n
    ArityMismatch -> "Arity mismatch"

--------------------------------------------------------------------------------
-- Evaluation

lookupWithQName :: TopEnv -> RawEnv -> QName -> Value
lookupWithQName topEnv env = \case
  m@(Unqual n) -> case HM.lookup n env of
    Just v -> v
    Nothing -> case HM.lookup n topEnv of
      Just vs -> VTop n SNil (HM.toList vs)
      Nothing -> throw $ VarNotFound m
  m@(Qual q n) -> case HM.lookup n topEnv >>= HM.lookup q of
    Just v -> VTop n SNil [(q, v)]
    Nothing -> throw $ VarNotFound m

lookupPossibleModules :: TopEnv -> [ModuleName] -> Name -> Value
lookupPossibleModules topEnv ms n = case HM.lookup n topEnv of
  Nothing -> case ms of
    [] -> throw $ VarNotFound (Unqual n)
    (m : _) -> throw $ VarNotFound (Qual m n)
  Just vs -> VTop n SNil (map (\m -> (m, vs HM.! m)) ms)

evaluateRaw :: TopEnv -> RawEnv -> Raw -> Value
evaluateRaw topEnv env = \case
  RVar n -> lookupWithQName topEnv env n
  RMetaApp m ts -> VMetaApp m $ map (evaluateRaw topEnv env) ts
  RType -> VType
  RPi x a b -> VPi x (evaluateRaw topEnv env a) \ ~v -> evaluateRaw topEnv (HM.insert x v env) b
  RArr a b -> VArr (evaluateRaw topEnv env a) (evaluateRaw topEnv env b)
  RAbs x t -> VAbs x \v -> evaluateRaw topEnv (HM.insert x v env) t
  RApp t u -> vapp (evaluateRaw topEnv env t) (evaluateRaw topEnv env u)
  RSigma x a b -> VSigma x (evaluateRaw topEnv env a) \ ~v -> evaluateRaw topEnv (HM.insert x v env) b
  RProd a b -> VProd (evaluateRaw topEnv env a) (evaluateRaw topEnv env b)
  RPair a b -> VPair (evaluateRaw topEnv env a) (evaluateRaw topEnv env b)
  RFst t -> vfst $ evaluateRaw topEnv env t
  RSnd t -> vsnd $ evaluateRaw topEnv env t
  RUnit -> VUnit
  RTT -> VTT
  RNat -> VNat
  RZero -> VZero
  RSuc -> VAbs "n" VSuc
  RNatElim -> VAbs "p" \p -> VAbs "s" \s -> VAbs "z" \z -> VAbs "n" \n -> vnatElim p s z n
  REq -> VAbs "A" \a -> VAbs "x" \x -> VAbs "y" \y -> VEq a x y
  RRefl -> VAbs "A" \a -> VAbs "x" \x -> VRefl a x
  REqElim -> VAbs "A" \a -> VAbs "x" \x -> VAbs "p" \p -> VAbs "r" \r -> VAbs "y" \y -> VAbs "eq" \eq -> veqElim a x p r y eq
  RPos t _ -> evaluateRaw topEnv env t

-- | Convert a term into a value.
evaluate :: TopEnv -> Env -> Term -> Value
evaluate topEnv env = \case
  Var (Index i) -> env !! i
  MetaApp m ts -> VMetaApp m $ map (evaluate topEnv env) ts
  Top ms n -> lookupPossibleModules topEnv ms n
  Type -> VType
  Pi x a b -> VPi x (evaluate topEnv env a) \ ~v -> evaluate topEnv (v : env) b
  Arr a b -> VArr (evaluate topEnv env a) (evaluate topEnv env b)
  Abs x t -> VAbs x \v -> evaluate topEnv (v : env) t
  App t u -> vapp (evaluate topEnv env t) (evaluate topEnv env u)
  Sigma x a b -> VSigma x (evaluate topEnv env a) \ ~v -> evaluate topEnv (v : env) b
  Prod a b -> VProd (evaluate topEnv env a) (evaluate topEnv env b)
  Pair t u -> VPair (evaluate topEnv env t) (evaluate topEnv env u)
  Fst t -> vfst $ evaluate topEnv env t
  Snd t -> vsnd $ evaluate topEnv env t
  Unit -> VUnit
  TT -> VTT
  Nat -> VNat
  Zero -> VZero
  Suc -> VAbs "n" VSuc
  NatElim -> VAbs "p" \p -> VAbs "s" \s -> VAbs "z" \z -> VAbs "n" \n -> vnatElim p s z n
  Eq -> VAbs "A" \a -> VAbs "x" \x -> VAbs "y" \y -> VEq a x y
  Refl -> VAbs "A" \a -> VAbs "x" \x -> VRefl a x
  EqElim -> VAbs "A" \a -> VAbs "x" \x -> VAbs "p" \p -> VAbs "r" \r -> VAbs "y" \y -> VAbs "eq" \eq -> veqElim a x p r y eq

-- | Application in "the value world".
vapp :: Value -> Value -> Value
vapp vt vu = case vt of
  VAbs _ f -> f vu
  VRigid l sp -> VRigid l (SApp sp vu)
  VFlex m ar vs sp -> VFlex m ar vs (SApp sp vu)
  VTop n sp vs -> VTop n (SApp sp vu) (fmap (`vapp` vu) <$> vs)
  _ -> VStuck vt (SApp SNil vu)

-- | Projections in "the value world".
vfst, vsnd :: Value -> Value
vfst = \case
  VPair v _ -> v
  VRigid l sp -> VRigid l (SFst sp)
  VFlex m ar vs sp -> VFlex m ar vs (SFst sp)
  VTop n sp vs -> VTop n (SFst sp) (fmap vfst <$> vs)
  v -> VStuck v (SFst SNil)
vsnd = \case
  VPair _ v -> v
  VRigid l sp -> VRigid l (SSnd sp)
  VFlex m ar vs sp -> VFlex m ar vs (SSnd sp)
  VTop n sp vs -> VTop n (SSnd sp) (fmap vsnd <$> vs)
  v -> VStuck v (SSnd SNil)

vnatElim :: Value -> Value -> Value -> Value -> Value
vnatElim p s z = \case
  VZero -> z
  VSuc n -> (s `vapp` n) `vapp` vnatElim p s z n
  VRigid l sp -> VRigid l (SNatElim p s z sp)
  VFlex m ar vs sp -> VFlex m ar vs (SNatElim p s z sp)
  VTop n sp vs -> VTop n (SNatElim p s z sp) (fmap (vnatElim p s z) <$> vs)
  v -> VStuck v (SNatElim p s z SNil)

veqElim :: Value -> Value -> Value -> Value -> Value -> Value -> Value
veqElim a x p r y = \case
  VRefl {} -> r
  VRigid l sp -> VRigid l (SEqElim a x p r y sp)
  VFlex m ar vs sp -> VFlex m ar vs (SEqElim a x p r y sp)
  VTop n sp vs -> VTop n (SEqElim a x p r y sp) (fmap (veqElim a x p r y) <$> vs)
  v -> VStuck v (SEqElim a x p r y SNil)

-- | Apply an elimination to a value.
vappElim :: Value -> Elim -> Value
vappElim v = \case
  EApp u -> vapp v u
  EFst -> vfst v
  ESnd -> vsnd v
  ENatElim p s z -> vnatElim p s z v
  EEqElim a x p r y -> veqElim a x p r y v

-- | Apply a value to a spine.
vappSpine :: Value -> Spine -> Value
vappSpine v sp = foldl' vappElim v sp

-- | Apply a meta-abstraction to arguments.
vmetaApp :: TopEnv -> MetaAbs -> [Value] -> Value
vmetaApp topEnv (MetaAbs arity body) args
  | length args /= arity = throw ArityMismatch
  | otherwise = evaluate topEnv (reverse args) body

--------------------------------------------------------------------------------
-- Quotation

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index (l - x - 1)

-- | Convert back a value into a term.
quote :: Level -> Value -> Term
quote lvl = \case
  VRigid x sp -> quoteSpine lvl (Var $ levelToIndex lvl x) sp
  VFlex m _ vs sp -> quoteSpine lvl (MetaApp m $ map (quote lvl) vs) sp
  VTop n sp vs -> quoteSpine lvl (Top (fst <$> vs) n) sp
  VType -> Type
  VPi x va vb -> Pi x (quote lvl va) (quote (lvl + 1) $ vb (VVar lvl))
  VArr va vb -> Arr (quote lvl va) (quote lvl vb)
  VAbs x v -> Abs x $ quote (lvl + 1) $ v (VVar lvl)
  VSigma x va vb -> Sigma x (quote lvl va) (quote (lvl + 1) $ vb (VVar lvl))
  VProd va vb -> Prod (quote lvl va) (quote lvl vb)
  VPair vt vu -> Pair (quote lvl vt) (quote lvl vu)
  VUnit -> Unit
  VTT -> TT
  VNat -> Nat
  VZero -> Zero
  VSuc n -> Suc `App` quote lvl n
  VEq a x y -> Eq `App` quote lvl a `App` quote lvl x `App` quote lvl y
  VRefl a x -> Refl `App` quote lvl a `App` quote lvl x
  VStuck v sp -> quoteSpine lvl (quote lvl v) sp

quoteElim :: Level -> Term -> Elim -> Term
quoteElim lvl t = \case
  EApp u -> App t (quote lvl u)
  EFst -> Fst t
  ESnd -> Snd t
  ENatElim p s z -> NatElim `App` quote lvl p `App` quote lvl s `App` quote lvl z `App` t
  EEqElim a x p r y -> EqElim `App` quote lvl a `App` quote lvl x `App` quote lvl p `App` quote lvl r `App` quote lvl y `App` t

-- | Convert a spine into a term.
quoteSpine :: Level -> Term -> Spine -> Term
quoteSpine lvl hd sp = foldl' (quoteElim lvl) hd sp

--------------------------------------------------------------------------------
-- Forcing

-- | Force metavariables
force :: TopEnv -> MetaSubst -> Value -> Value
force topEnv subst = go
  where
    go = \case
      VFlex m _ vs sp
        | Just mabs <- HM.lookup m subst -> go $ vappSpine (vmetaApp topEnv mabs vs) sp
      v -> v

deepForce :: TopEnv -> MetaSubst -> Value -> Value
deepForce topEnv subst = go
  where
    go v = case force topEnv subst v of
      VFlex m ar vs sp -> VFlex m ar vs (goSpine sp)
      VRigid l sp -> VRigid l (goSpine sp)
      VTop n sp vs -> VTop n (goSpine sp) (fmap go <$> vs)
      VType -> VType
      VPi x a b -> VPi x (go a) \ ~u -> go (b u)
      VArr a b -> VArr (go a) (go b)
      VAbs x f -> VAbs x \u -> go (f u)
      VSigma x a b -> VSigma x (go a) \ ~u -> go (b u)
      VProd a b -> VProd (go a) (go b)
      VPair a b -> VPair (go a) (go b)
      VUnit -> VUnit
      VTT -> VTT
      VNat -> VNat
      VZero -> VZero
      VSuc n -> VSuc (go n)
      VEq a x y -> VEq (go a) (go x) (go y)
      VRefl a x -> VRefl (go a) (go x)
      VStuck u sp -> VStuck (go u) (goSpine sp)

    goSpine = fmap goElim

    goElim = \case
      EApp v -> EApp (go v)
      EFst -> EFst
      ESnd -> ESnd
      ENatElim p s z -> ENatElim (go p) (go s) (go z)
      EEqElim a x p r y -> EEqElim (go a) (go x) (go p) (go r) (go y)
