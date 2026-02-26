module TypeSearch.Evaluation where

import Data.Coerce
import Data.HashMap.Strict qualified as HM
import TypeSearch.Common
import TypeSearch.Term

infixr 6 -->

infixr 7 ***

(-->) :: Value -> Value -> Value
a --> b = VPi "_" a \_ -> b

(***) :: Value -> Value -> Value
a *** b = VSigma "_" a \_ -> b

tequality :: Term
tequality =
  Top
    (QName "Agda.Builtin.Equality" "_≡_")
    (DontPrint Nothing)

vequality :: Value
vequality =
  VTop
    (QName "Agda.Builtin.Equality" "_≡_")
    Nothing
    SNil
    Nothing

tnat :: Term
tnat =
  Top
    (QName "Agda.Builtin.Nat" "Nat")
    (DontPrint Nothing)

vnat :: Value
vnat =
  VTop
    (QName "Agda.Builtin.Nat" "Nat")
    Nothing
    SNil
    Nothing

tidentityR :: Term
tidentityR =
  Top
    (QName "Algebra.Definitions" "Commutative")
    ( DontPrint $
        Just $
          VLam "A" \a ->
            VLam "op" \op ->
              VPi "x" a \x -> VPi "y" a \y ->
                vequality $$ a $$ (op $$ x $$ y) $$ (op $$ y $$ x)
    )

tadd :: Term
tadd =
  Top
    (QName "Agda.Builtin.Nat" "_+_")
    (DontPrint Nothing)

vadd :: Value
vadd =
  VTop
    (QName "Agda.Builtin.Nat" "_+_")
    Nothing
    SNil
    Nothing

tAddIdR1 :: Term
tAddIdR1 = tidentityR `App` tnat `App` tadd

tAddIdR2 :: Term
tAddIdR2 = quote emptyMetaCtx 0 $
  VPi "m" vnat \m -> VPi "n" vnat \n ->
    vequality $$ vnat $$ (vadd $$ m $$ n) $$ (vadd $$ n $$ m)

exMetaCtx :: MetaCtx
exMetaCtx = MetaCtx 0 (HM.fromList [("α", Unsolved), ("β", Unsolved), ("γ", Unsolved)])

valpha :: Value
valpha = VMeta "α"

vbeta :: Value
vbeta = VMeta "β"

vgamma :: Value
vgamma = VMeta "γ"

tAddIdR3 :: Term
tAddIdR3 = quote exMetaCtx 0 $
  VPi "m" vnat \m -> VPi "n" valpha \n ->
    vequality $$ valpha $$ (vadd $$ m $$ n) $$ (vadd $$ n $$ m)

tAddIdR4 :: Term
tAddIdR4 = quote exMetaCtx 0 $
  VPi "m" vbeta \m -> VPi "n" vbeta \n ->
    vequality $$ vbeta $$ (vgamma $$ m $$ n) $$ (vgamma $$ n $$ m)

vlist :: Value
vlist = VTop (QName "Agda.Builtin.List" "List") Nothing SNil Nothing

tFoldr1 :: Term
tFoldr1 =
  quote exMetaCtx 0 $
    (valpha --> vbeta --> vbeta) --> vbeta --> (vlist $$ valpha) --> vbeta

tFoldr2 :: Term
tFoldr2 =
  quote exMetaCtx 0 $
    (vgamma --> vgamma --> vgamma) --> vgamma --> (vlist $$ vgamma) --> vgamma

tFoldr3 :: Term
tFoldr3 =
  quote exMetaCtx 0 $
    (vgamma *** vgamma --> vgamma) --> vgamma --> (vlist $$ vgamma) --> vgamma

--------------------------------------------------------------------------------
-- Evaluation

eval :: MetaCtx -> Env -> Term -> Value
eval mctx env = \case
  Var (Index x) -> env !! x
  Meta m -> vMeta mctx m
  Top x v -> VTop x (coerce v) SNil (coerce v)
  U -> VU
  Pi x a b -> VPi x (eval mctx env a) (evalBind mctx env b)
  Lam x t -> VLam x (evalBind' mctx env t)
  App t u -> eval mctx env t $$ eval mctx env u
  Sigma x a b -> VSigma x (eval mctx env a) (evalBind mctx env b)
  Pair t u -> VPair (eval mctx env t) (eval mctx env u)
  Fst t -> vFst (eval mctx env t)
  Snd t -> vSnd (eval mctx env t)

evalBind :: MetaCtx -> Env -> Term -> (Value -> Value)
evalBind mctx env t ~u = eval mctx (u : env) t

evalBind' :: MetaCtx -> Env -> Term -> (Value -> Value)
evalBind' mctx env t u = eval mctx (u : env) t

vMeta :: MetaCtx -> MetaVar -> Value
vMeta mctx x = case mctx.metaCtx HM.! x of
  Unsolved -> VMeta x
  Solved v -> v

($$) :: Value -> Value -> Value
t $$ u = case t of
  VLam _ t -> t u
  VRigid x sp -> VRigid x (SApp sp u)
  VFlex m sp -> VFlex m (SApp sp u)
  VTop x f sp t -> VTop x f (SApp sp u) (fmap ($$ u) t)
  _ -> error "($$): not a function"

vFst :: Value -> Value
vFst = \case
  VPair t _ -> t
  VRigid x sp -> VRigid x (SFst sp)
  VFlex m sp -> VFlex m (SFst sp)
  VTop x f sp t -> VTop x f (SFst sp) (vFst <$> t)
  _ -> error "vFst: not a pair"

vSnd :: Value -> Value
vSnd = \case
  VPair _ t -> t
  VRigid x sp -> VRigid x (SSnd sp)
  VFlex m sp -> VFlex m (SSnd sp)
  VTop x f sp t -> VTop x f (SSnd sp) (vSnd <$> t)
  _ -> error "vSnd: not a pair"

vAppSpine :: Value -> Spine -> Value
vAppSpine t = \case
  SNil -> t
  SApp sp u -> vAppSpine t sp $$ u
  SFst sp -> vFst $ vAppSpine t sp
  SSnd sp -> vSnd $ vAppSpine t sp

force :: MetaCtx -> Value -> Value
force mctx = \case
  VFlex m sp
    | Solved t <- mctx.metaCtx HM.! m -> force mctx (vAppSpine t sp)
  t -> t

--------------------------------------------------------------------------------
-- Quotation

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index (l - x - 1)

quote :: MetaCtx -> Level -> Value -> Term
quote mctx l t = case force mctx t of
  VRigid x sp -> quoteSpine mctx l (Var (levelToIndex l x)) sp
  VFlex m sp -> quoteSpine mctx l (Meta m) sp
  VTop x f sp _ -> quoteSpine mctx l (Top x (coerce f)) sp
  VU -> U
  VPi x a b -> Pi x (quote mctx l a) (quoteBind mctx l b)
  VLam x t -> Lam x (quoteBind mctx l t)
  VSigma x a b -> Sigma x (quote mctx l a) (quoteBind mctx l b)
  VPair t u -> Pair (quote mctx l t) (quote mctx l u)

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
