module TypeSearch.Evaluation where

import Data.HashMap.Strict qualified as HM
import Data.Hashable
import TypeSearch.Common
import TypeSearch.Term

--------------------------------------------------------------------------------
-- Values

-- | De Bruijn levels
newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show, Hashable)

data Value
  = VRigid Level Spine
  | VFlex MetaVar Spine
  | VTop {-# UNPACK #-} QName Spine (Maybe Value)
  | VU
  | VPi Name Value (Value -> Value)
  | VLam Name (Value -> Value)
  | VSigma Name Value (Value -> Value)
  | VPair Value Value
  | VStuck Value Spine

data Spine
  = SNil
  | SApp Spine Value
  | SFst Spine
  | SSnd Spine

pattern VVar :: Level -> Value
pattern VVar x = VRigid x SNil

pattern VMeta :: MetaVar -> Value
pattern VMeta m = VFlex m SNil

-- | Environment keyed by De Bruijn indices
type Env = [Value]

-- | Environment keyed by top-level names
type TopEnv = HM.HashMap QName (Maybe Value)

-- | Meta-context
data MetaCtx = MetaCtx
  { nextMeta :: GenMetaVar,
    metaEnv :: HM.HashMap MetaVar MetaEntry
  }

data MetaEntry = Unsolved | Solved Value

--------------------------------------------------------------------------------
-- Evaluation

eval :: TopEnv -> Env -> MetaCtx -> Term -> Value
eval tenv env mctx = \case
  Var (Index x) -> env !! x
  Meta m -> vMeta mctx m
  Top x -> vTop tenv x
  U -> VU
  Pi x a b -> VPi x (eval tenv env mctx a) (evalBind tenv env mctx b)
  Lam x t -> VLam x (evalBind' tenv env mctx t)
  App t u -> eval tenv env mctx t $$ eval tenv env mctx u
  Sigma x a b -> VSigma x (eval tenv env mctx a) (evalBind tenv env mctx b)
  Pair t u -> VPair (eval tenv env mctx t) (eval tenv env mctx u)
  Fst t -> vFst (eval tenv env mctx t)
  Snd t -> vSnd (eval tenv env mctx t)

evalBind :: TopEnv -> Env -> MetaCtx -> Term -> (Value -> Value)
evalBind tenv env mctx t ~u = eval tenv (u : env) mctx t

evalBind' :: TopEnv -> Env -> MetaCtx -> Term -> (Value -> Value)
evalBind' tenv env mctx t u = eval tenv (u : env) mctx t

vTop :: TopEnv -> QName -> Value
vTop tenv x = VTop x SNil (tenv HM.! x)

vMeta :: MetaCtx -> MetaVar -> Value
vMeta mctx x = case mctx.metaEnv HM.! x of
  Unsolved -> VMeta x
  Solved v -> v

($$) :: Value -> Value -> Value
VLam _ t $$ u = t u
VRigid x sp $$ u = VRigid x (SApp sp u)
VFlex m sp $$ u = VFlex m (SApp sp u)
VTop x sp t $$ u = VTop x (SApp sp u) (fmap ($$ u) t)
VStuck t sp $$ u = VStuck t (SApp sp u)
t $$ u = VStuck t (SApp SNil u)

vFst :: Value -> Value
vFst = \case
  VPair t _ -> t
  VRigid x sp -> VRigid x (SFst sp)
  VFlex m sp -> VFlex m (SFst sp)
  VTop x sp t -> VTop x (SFst sp) (vFst <$> t)
  VStuck t sp -> VStuck t (SFst sp)
  t -> VStuck t (SFst SNil)

vSnd :: Value -> Value
vSnd = \case
  VPair _ t -> t
  VRigid x sp -> VRigid x (SSnd sp)
  VFlex m sp -> VFlex m (SSnd sp)
  VTop x sp t -> VTop x (SSnd sp) (vSnd <$> t)
  VStuck t sp -> VStuck t (SSnd sp)
  t -> VStuck t (SSnd SNil)

vAppSpine :: Value -> Spine -> Value
vAppSpine t = \case
  SNil -> t
  SApp sp u -> vAppSpine t sp $$ u
  SFst sp -> vFst $ vAppSpine t sp
  SSnd sp -> vSnd $ vAppSpine t sp

--------------------------------------------------------------------------------
-- Quotation

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index (l - x - 1)

quote :: Level -> Value -> Term
quote l = \case
  VRigid x sp -> quoteSpine l (Var (levelToIndex l x)) sp
  VFlex m sp -> quoteSpine l (Meta m) sp
  VTop x sp _ -> quoteSpine l (Top x) sp
  VU -> U
  VPi x a b -> Pi x (quote l a) (quoteBind l b)
  VLam x t -> Lam x (quoteBind l t)
  VSigma x a b -> Sigma x (quote l a) (quoteBind l b)
  VPair t u -> Pair (quote l t) (quote l u)
  VStuck t sp -> quoteSpine l (quote l t) sp

quoteBind :: Level -> (Value -> Value) -> Term
quoteBind l b = quote (l + 1) (b $ VVar l)

quoteSpine :: Level -> Term -> Spine -> Term
quoteSpine l h = \case
  SNil -> h
  SApp sp u -> quoteSpine l h sp `App` quote l u
  SFst sp -> Fst $ quoteSpine l h sp
  SSnd sp -> Snd $ quoteSpine l h sp

--------------------------------------------------------------------------------
-- Transport

-- transport along an isomorphism
transport :: Iso -> Value -> Value
transport i v = case i of
  Refl -> v
  Sym i -> transportInv i v
  Trans i j -> transport j (transport i v)
  Assoc -> vFst (vFst v) `VPair` (vSnd (vFst v) `VPair` vSnd v)
  Comm -> vSnd v `VPair` vFst v
  SigmaSwap -> vFst (vSnd v) `VPair` (vFst v `VPair` vSnd (vSnd v))
  Curry -> VLam "x" \x -> VLam "y" \y -> v $$ VPair x y
  PiSwap -> VLam "y" \y -> VLam "x" \x -> v $$ x $$ y
  PiCongL i -> VLam "x" \x -> v $$ transportInv i x
  PiCongR i -> VLam "x" \x -> transport i (v $$ x)
  SigmaCongL i -> transport i (vFst v) `VPair` vSnd v
  SigmaCongR i -> vFst v `VPair` transport i (vSnd v)

-- transport back
transportInv :: Iso -> Value -> Value
transportInv i v = case i of
  Refl -> v
  Sym i -> transport i v
  Trans i j -> transportInv i (transportInv j v)
  Assoc -> (vFst v `VPair` vFst (vSnd v)) `VPair` vSnd (vSnd v)
  Comm -> vSnd v `VPair` vFst v
  SigmaSwap -> vFst (vSnd v) `VPair` (vFst v `VPair` vSnd (vSnd v))
  Curry -> VLam "p" \p -> v $$ vFst p $$ vSnd p
  PiSwap -> VLam "x" \x -> VLam "y" \y -> v $$ y $$ x
  PiCongL i -> VLam "x" \x -> v $$ transport i x
  PiCongR i -> VLam "x" \x -> transportInv i (v $$ x)
  SigmaCongL i -> transportInv i (vFst v) `VPair` vSnd v
  SigmaCongR i -> vFst v `VPair` transportInv i (vSnd v)
