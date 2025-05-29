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

    -- * Top-level environment
    modulesEnv,
  )
where

import Data.Foldable
import Data.HashMap.Lazy qualified as HM
import Data.Sequence qualified as Seq
import TypeSearch.Common
import TypeSearch.Raw
import TypeSearch.Term

--------------------------------------------------------------------------------
-- Values

-- | De Bruijn levels
newtype Level = Level Int
  deriving newtype (Num, Eq, Ord, Show, Enum)

-- | Environment keyed by raw variable names
type RawEnv = HM.HashMap Name Value

-- | Environments keyed by De Bruijn indices
type Env = [Value]

-- | Environment keyed by top-level names
type TopEnv = HM.HashMap Name (HM.HashMap ModuleName Value)

-- | Values support efficient β-reduction and substitution.
data Value
  = VRigid Level Spine
  | VFlex Meta Int [Value] Spine -- metavariables are parametarised in SOAS
  | VTop [ModuleName] Name Spine [Value]
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
  | HTop [ModuleName] Name [Value]
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
  VTop ms n sp vs -> (HTop ms n vs, sp)
  VType -> (HType, SNil)
  VPi x a b -> (HPi x a b, SNil)
  VAbs x f -> (HAbs x f, SNil)
  VSigma x a b -> (HSigma x a b, SNil)
  VPair a b -> (HPair a b, SNil)
  VUnit -> (HUnit, SNil)
  VTT -> (HTT, SNil)
  VStuck v sp -> (HStuck v, sp)

--------------------------------------------------------------------------------
-- Evaluation

lookupWithQName :: TopEnv -> RawEnv -> QName -> Value
lookupWithQName topEnv env = \case
  Unqual n -> case HM.lookup n env of
    Just v -> v
    Nothing -> case HM.lookup n topEnv of
      Just vs -> VTop (HM.keys vs) n SNil (HM.elems vs)
      Nothing -> error $ "Variable not found: " ++ show n
  m@(Qual q n) -> case HM.lookup n topEnv >>= HM.lookup q of
    Just v -> VTop [q] n SNil [v]
    Nothing -> error $ "Variable not found: " ++ show m

lookupPossibleModules :: TopEnv -> [ModuleName] -> Name -> Value
lookupPossibleModules topEnv ms n = case HM.lookup n topEnv of
  Nothing -> error $ "Variable not found: " ++ show n
  Just vs -> VTop ms n SNil (map (vs HM.!) ms)

evaluateRaw :: TopEnv -> RawEnv -> Raw -> Value
evaluateRaw topEnv env = \case
  RVar n -> lookupWithQName topEnv env n
  RMetaApp m ts -> VMetaApp m $ map (evaluateRaw topEnv env) ts
  RType -> VType
  RPi x a b -> VPi x (evaluateRaw topEnv env a) \v -> evaluateRaw topEnv (HM.insert x v env) b
  RAbs x t -> VAbs x \v -> evaluateRaw topEnv (HM.insert x v env) t
  RApp t u -> vapp (evaluateRaw topEnv env t) (evaluateRaw topEnv env u)
  RSigma x a b -> VSigma x (evaluateRaw topEnv env a) \v -> evaluateRaw topEnv (HM.insert x v env) b
  RPair a b -> VPair (evaluateRaw topEnv env a) (evaluateRaw topEnv env b)
  RFst t -> vfst $ evaluateRaw topEnv env t
  RSnd t -> vsnd $ evaluateRaw topEnv env t
  RUnit -> VUnit
  RTT -> VTT
  RLoc (t :@ _) -> evaluateRaw topEnv env t

-- | Convert a term into a value.
evaluate :: TopEnv -> Env -> Term -> Value
evaluate topEnv env = \case
  Var (Index i) -> env !! i
  MetaApp m ts -> VMetaApp m $ map (evaluate topEnv env) ts
  Top ms n -> lookupPossibleModules topEnv ms n
  Type -> VType
  Pi x a b -> VPi x (evaluate topEnv env a) \v -> evaluate topEnv (v : env) b
  Abs x t -> VAbs x \v -> evaluate topEnv (v : env) t
  App t u -> vapp (evaluate topEnv env t) (evaluate topEnv env u)
  Sigma x a b -> VSigma x (evaluate topEnv env a) \v -> evaluate topEnv (v : env) b
  Pair t u -> VPair (evaluate topEnv env t) (evaluate topEnv env u)
  Fst t -> vfst $ evaluate topEnv env t
  Snd t -> vsnd $ evaluate topEnv env t
  Unit -> VUnit
  TT -> VTT

-- | Application in "the value world".
vapp :: Value -> Value -> Value
vapp vt vu = case vt of
  VAbs _ f -> f vu
  VRigid l sp -> VRigid l (SApp sp vu)
  VFlex m ar vs sp -> VFlex m ar vs (SApp sp vu)
  VTop ms n sp vs -> VTop ms n (SApp sp vu) (map (`vapp` vu) vs)
  VStuck v sp -> VStuck v (SApp sp vu)
  _ -> VStuck vt (SApp SNil vu)

-- | Projections in "the value world".
vfst, vsnd :: Value -> Value
vfst = \case
  VPair v _ -> v
  VRigid l sp -> VRigid l (SFst sp)
  VFlex m ar vs sp -> VFlex m ar vs (SFst sp)
  VTop ms n sp vs -> VTop ms n (SFst sp) (map vfst vs)
  VStuck v sp -> VStuck v (SFst sp)
  v -> VStuck v (SFst SNil)
vsnd = \case
  VPair _ v -> v
  VRigid l sp -> VRigid l (SSnd sp)
  VFlex m ar vs sp -> VFlex m ar vs (SSnd sp)
  VTop ms n sp vs -> VTop ms n (SSnd sp) (map vsnd vs)
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
vmetaApp :: TopEnv -> MetaAbs -> [Value] -> Value
vmetaApp topEnv (MetaAbs _arity body) args = evaluate topEnv (reverse args) body

--------------------------------------------------------------------------------
-- Quotation

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index (l - x - 1)

-- | Convert back a value into a term.
quote :: Level -> Value -> Term
quote lvl = \case
  VRigid x sp -> quoteSpine lvl (Var $ levelToIndex lvl x) sp
  VFlex m _ vs sp -> quoteSpine lvl (MetaApp m $ map (quote lvl) vs) sp
  VTop ms n sp _ -> quoteSpine lvl (Top ms n) sp
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
      VTop ms n sp vs -> VTop ms n (goSpine sp) (map go vs)
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

--------------------------------------------------------------------------------
-- Create top-level environment from modules

-- | Create a top-level environment from modules.
modulesEnv :: HM.HashMap ModuleName Module -> TopEnv
modulesEnv mods = go HM.empty (HM.keys mods)
  where
    go topEnv = \case
      [] -> topEnv
      m : todos ->
        let mod' = mods HM.! m
            deps = mod'.imports
         in if any (`elem` todos) deps
              then go topEnv (todos ++ [m])
              else go (goModule topEnv mod') todos

    goModule topEnv (Module m _ decls) = foldl' (goDecl m) topEnv decls

    goDecl m topEnv = \case
      DLoc (d :@ _) -> goDecl m topEnv d
      DLet x _ t ->
        HM.insertWith
          (<>)
          x
          (HM.singleton m (evaluateRaw topEnv HM.empty t))
          topEnv
