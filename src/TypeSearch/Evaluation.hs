module TypeSearch.Evaluation where

import Data.Foldable
import Data.HashMap.Lazy qualified as HML
import TypeSearch.Common
import TypeSearch.Pretty
import TypeSearch.Term

infixr 6 -->

infixr 7 ***

--------------------------------------------------------------------------------

(-->) :: Value -> Value -> Value
a --> b = VPi "_" a \ ~_ -> b

(***) :: Value -> Value -> Value
a *** b = VSigma "_" a \ ~_ -> b

exMetaCtx :: MetaCtx
exMetaCtx =
  MetaCtx 5 $
    HML.fromList
      [ (0, Unsolved VU),
        (1, Unsolved VU),
        (2, Unsolved VU),
        (3, Unsolved VU),
        (4, Unsolved ((vlist $$ vgamma) --> VU))
      ]

valpha :: Value
valpha = VMeta 0

vbeta :: Value
vbeta = VMeta 1

vgamma :: Value
vgamma = VMeta 2

veps :: Value
veps = VMeta 3

vdelta :: Value
vdelta = VMeta 4

vlist :: Value
vlist = VTop (QName "Agda.Builtin.List" "List") SNil Nothing

tFoldr0 :: Term
tFoldr0 =
  quote exMetaCtx 0 $
    VPi "A" VU \a -> VPi "B" VU \b ->
      (a --> b --> b) --> b --> (vlist $$ a) --> b

tFoldr1 :: Term
tFoldr1 =
  quote exMetaCtx 0 $
    (valpha --> vbeta --> vbeta) --> vbeta --> (vlist $$ valpha) --> vbeta

tFoldr2 :: Term
tFoldr2 =
  quote exMetaCtx 0 $
    (vlist $$ vgamma) --> (veps *** vgamma --> veps) --> veps --> veps

tFoldr3 :: Term
tFoldr3 =
  quote exMetaCtx 0 $
    VPi "xs" (vlist $$ vgamma) \xs -> ((vdelta $$ xs) *** (vdelta $$ xs) --> (vdelta $$ xs)) *** (vdelta $$ xs) --> (vdelta $$ xs)

-- printResults :: (Foldable t) => t (Iso, MetaCtx) -> IO ()
-- printResults res = for_ res \(i, mctx) -> do
--   putStrLn "----------"
--   putStrLn $ "iso: " ++ prettyIso 0 i ""
--   putStrLn "subst: "
--   for_ (HML.toList mctx.metaCtx) \(v, t) -> case (v, t) of
--     (Src _, Solved sol ty) -> putStrLn $ "  " ++ show v ++ " : " ++ prettyTerm0 Unqualify (quote mctx 0 ty) "" ++ " = " ++ prettyTerm0 Unqualify (quote mctx 0 sol) ""
--     _ -> pure ()

--------------------------------------------------------------------------------
-- Values

-- | Values
data Value
  = VRigid Level Spine
  | VFlex MetaVar Spine
  | VTop {-# UNPACK #-} QName Spine (Maybe Value) -- Nothing for axioms
  | VU
  | VPi Name VType (Value -> VType)
  | VLam Name (Value -> Value)
  | VSigma Name VType (Value -> VType)
  | VPair Value Value
  | VBrave Value Spine

type VType = Value

data Spine
  = SNil
  | SApp Spine Value
  | SProj1 Spine
  | SProj2 Spine

pattern VVar :: Level -> Value
pattern VVar x = VRigid x SNil

pattern VMeta :: MetaVar -> Value
pattern VMeta m = VFlex m SNil

data Quant = Quant Name Value (Value -> Value)

-- | Environment keyed by De Bruijn indices
type Env = [Value]

-- | Environment keyed by top-level names
type TopEnv = HML.HashMap QName Value

-- | Meta-context
data MetaCtx = MetaCtx
  { nextMeta :: MetaVar,
    metaCtx :: HML.HashMap MetaVar MetaEntry
  }

data MetaEntry
  = Unsolved ~Value
  | Solved Value ~Value

emptyMetaCtx :: MetaCtx
emptyMetaCtx = MetaCtx 0 mempty

--------------------------------------------------------------------------------
-- Evaluation

eval :: MetaCtx -> TopEnv -> Env -> Term -> Value
eval mctx tenv env = \case
  Var (Index x) -> env !! x
  Meta m -> vMeta mctx m
  Top x -> VTop x SNil (HML.lookup x tenv)
  U -> VU
  Pi x a b -> VPi x (eval mctx tenv env a) (evalBind mctx tenv env b)
  Lam x t -> VLam x (evalBind' mctx tenv env t)
  App t u -> eval mctx tenv env t $$ eval mctx tenv env u
  Sigma x a b -> VSigma x (eval mctx tenv env a) (evalBind mctx tenv env b)
  Pair t u -> VPair (eval mctx tenv env t) (eval mctx tenv env u)
  Proj1 t -> vProj1 (eval mctx tenv env t)
  Proj2 t -> vProj2 (eval mctx tenv env t)
  AppPruning t pr -> vAppPruning env (eval mctx tenv env t) pr

evalBind :: MetaCtx -> TopEnv -> Env -> Term -> (Value -> Value)
evalBind mctx tenv env t ~u = eval mctx tenv (u : env) t

evalBind' :: MetaCtx -> TopEnv -> Env -> Term -> (Value -> Value)
evalBind' mctx tenv env t u = eval mctx tenv (u : env) t

vMeta :: MetaCtx -> MetaVar -> Value
vMeta mctx x = case mctx.metaCtx HML.! x of
  Unsolved {} -> VMeta x
  Solved v _ -> v

vAppPruning :: Env -> Value -> Pruning -> Value
vAppPruning env ~v pr = case (env, pr) of
  ([], []) -> v
  (t : env, True : pr) -> vAppPruning env v pr $$ t
  (_ : env, False : pr) -> vAppPruning env v pr
  _ -> impossible

($$) :: Value -> Value -> Value
t $$ u = case t of
  VLam _ t -> t u
  VRigid x sp -> VRigid x (SApp sp u)
  VFlex m sp -> VFlex m (SApp sp u)
  VTop x sp t -> VTop x (SApp sp u) (fmap ($$ u) t)
  VBrave b sp -> VBrave b (SApp sp u)
  t -> VBrave t (SApp SNil u)

vProj1 :: Value -> Value
vProj1 = \case
  VPair t _ -> t
  VRigid x sp -> VRigid x (SProj1 sp)
  VFlex m sp -> VFlex m (SProj1 sp)
  VTop x sp t -> VTop x (SProj1 sp) (vProj1 <$> t)
  VBrave b sp -> VBrave b (SProj1 sp)
  t -> VBrave t (SProj1 SNil)

vProj2 :: Value -> Value
vProj2 = \case
  VPair _ t -> t
  VRigid x sp -> VRigid x (SProj2 sp)
  VFlex m sp -> VFlex m (SProj2 sp)
  VTop x sp t -> VTop x (SProj2 sp) (vProj2 <$> t)
  VBrave b sp -> VBrave b (SProj2 sp)
  t -> VBrave t (SProj2 SNil)

vAppSpine :: Value -> Spine -> Value
vAppSpine t = \case
  SNil -> t
  SApp sp u -> vAppSpine t sp $$ u
  SProj1 sp -> vProj1 $ vAppSpine t sp
  SProj2 sp -> vProj2 $ vAppSpine t sp

force :: MetaCtx -> Value -> Value
force mctx = \case
  VFlex m sp
    | Solved t _ <- mctx.metaCtx HML.! m -> force mctx (vAppSpine t sp)
  t -> t

forceAll :: MetaCtx -> Value -> Value
forceAll mctx = \case
  VFlex m sp
    | Solved t _ <- mctx.metaCtx HML.! m -> forceAll mctx (vAppSpine t sp)
  VTop _ _ (Just t) -> forceAll mctx t
  t -> t

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
  VBrave t sp -> quoteSpine mctx l (quote mctx l t) sp

quoteBind :: MetaCtx -> Level -> (Value -> Value) -> Term
quoteBind mctx l b = quote mctx (l + 1) (b $ VVar l)

quoteSpine :: MetaCtx -> Level -> Term -> Spine -> Term
quoteSpine mctx l h = \case
  SNil -> h
  SApp sp u -> quoteSpine mctx l h sp `App` quote mctx l u
  SProj1 sp -> Proj1 $ quoteSpine mctx l h sp
  SProj2 sp -> Proj2 $ quoteSpine mctx l h sp

--------------------------------------------------------------------------------
-- Transport

-- transport along an isomorphism
transport :: Iso -> Value -> Value
transport i v = case i of
  Refl -> v
  Sym i -> transportInv i v
  Trans i j -> transport j (transport i v)
  Assoc -> vProj1 (vProj1 v) `VPair` (vProj2 (vProj1 v) `VPair` vProj2 v)
  Comm -> vProj2 v `VPair` vProj1 v
  SigmaSwap -> vProj1 (vProj2 v) `VPair` (vProj1 v `VPair` vProj2 (vProj2 v))
  Curry -> VLam "x" \x -> VLam "y" \y -> v $$ VPair x y
  PiSwap -> VLam "y" \y -> VLam "x" \x -> v $$ x $$ y
  PiCongL i -> VLam "x" \x -> v $$ transportInv i x
  PiCongR i -> VLam "x" \x -> transport i (v $$ x)
  SigmaCongL i -> transport i (vProj1 v) `VPair` vProj2 v
  SigmaCongR i -> vProj1 v `VPair` transport i (vProj2 v)

-- transport back
transportInv :: Iso -> Value -> Value
transportInv i v = case i of
  Refl -> v
  Sym i -> transport i v
  Trans i j -> transportInv i (transportInv j v)
  Assoc -> (vProj1 v `VPair` vProj1 (vProj2 v)) `VPair` vProj2 (vProj2 v)
  Comm -> vProj2 v `VPair` vProj1 v
  SigmaSwap -> vProj1 (vProj2 v) `VPair` (vProj1 v `VPair` vProj2 (vProj2 v))
  Curry -> VLam "p" \p -> v $$ vProj1 p $$ vProj2 p
  PiSwap -> VLam "x" \x -> VLam "y" \y -> v $$ y $$ x
  PiCongL i -> VLam "x" \x -> v $$ transport i x
  PiCongR i -> VLam "x" \x -> transportInv i (v $$ x)
  SigmaCongL i -> transportInv i (vProj1 v) `VPair` vProj2 v
  SigmaCongR i -> vProj1 v `VPair` transportInv i (vProj2 v)
