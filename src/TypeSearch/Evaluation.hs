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
    metaCtx :: HM.HashMap MetaVar MetaEntry
  }

data MetaEntry = Unsolved | Solved Value

--------------------------------------------------------------------------------
-- Evaluation

eval :: MetaCtx -> TopEnv -> Env -> Term -> Value
eval mctx tenv env = \case
  Var (Index x) -> env !! x
  Meta m -> vMeta mctx m
  Top x -> vTop tenv x
  U -> VU
  Pi x a b -> VPi x (eval mctx tenv env a) (evalBind mctx tenv env b)
  Lam x t -> VLam x (evalBind' mctx tenv env t)
  App t u -> eval mctx tenv env t $$ eval mctx tenv env u
  Sigma x a b -> VSigma x (eval mctx tenv env a) (evalBind mctx tenv env b)
  Pair t u -> VPair (eval mctx tenv env t) (eval mctx tenv env u)
  Fst t -> vFst (eval mctx tenv env t)
  Snd t -> vSnd (eval mctx tenv env t)

evalBind :: MetaCtx -> TopEnv -> Env -> Term -> (Value -> Value)
evalBind mctx tenv env t ~u = eval mctx tenv (u : env) t

evalBind' :: MetaCtx -> TopEnv -> Env -> Term -> (Value -> Value)
evalBind' mctx tenv env t u = eval mctx tenv (u : env) t

vTop :: TopEnv -> QName -> Value
vTop tenv x = VTop x SNil (tenv HM.! x)

vMeta :: MetaCtx -> MetaVar -> Value
vMeta mctx x = case mctx.metaCtx HM.! x of
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

force :: MetaCtx -> Value -> Value
force mctx = \case
  VFlex m sp
    | Solved v <- mctx.metaCtx HM.! m -> force mctx (vAppSpine v sp)
  v -> v

--------------------------------------------------------------------------------
-- Quotation

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index (l - x - 1)

quote :: MetaCtx -> Level -> Value -> Term
quote mctx l t = case force mctx t of
  VRigid x sp -> quoteSpine mctx l (Var (levelToIndex l x)) sp
  VFlex m sp -> quoteSpine mctx l (Meta m) sp
  VTop x sp _ -> quoteSpine mctx l (Top x) sp
  VU -> U
  VPi x a b -> Pi x (quote mctx l a) (quoteBind mctx l b)
  VLam x t -> Lam x (quoteBind mctx l t)
  VSigma x a b -> Sigma x (quote mctx l a) (quoteBind mctx l b)
  VPair t u -> Pair (quote mctx l t) (quote mctx l u)
  VStuck t sp -> quoteSpine mctx l (quote mctx l t) sp

quoteBind :: MetaCtx -> Level -> (Value -> Value) -> Term
quoteBind mctx l b = quote mctx (l + 1) (b $ VVar l)

quoteSpine :: MetaCtx -> Level -> Term -> Spine -> Term
quoteSpine mctx l h = \case
  SNil -> h
  SApp sp u -> quoteSpine mctx l h sp `App` quote mctx l u
  SFst sp -> Fst $ quoteSpine mctx l h sp
  SSnd sp -> Snd $ quoteSpine mctx l h sp

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
