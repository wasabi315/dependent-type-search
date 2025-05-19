module TypeSearch.UnificationModulo
  ( -- * Unification
    unifyRaw,
    unifiable,
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Heap
import Control.Monad.Trans
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.Maybe
import Data.Monus.Dist
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Raw
import TypeSearch.Term
import Witherable

--------------------------------------------------------------------------------
-- Untyped version of the rewrite system STR^{Coq} presented in the paper by Delahaye (2000).
-- TODO: Is this rewrite system confluent?

-- | Σ associativity and currying
normalise1 :: Value -> Value
normalise1 = \case
  -- (x : (y : A) * B[y]) * C[x] ~> (x : A) * (y : B[x]) * C[(x, y)]
  VSigma x (VSigma y va vb) vc ->
    normalise1 $ VSigma x va \v -> VSigma y (vb v) \u -> vc (VPair v u)
  -- (x : (y : A) * B[y]) -> C[x] ~> (x : A) -> (y : B[x]) -> C[(x, y)]
  VPi x (VSigma y va vb) vc ->
    normalise1 $ VPi x va \v -> VPi y (vb v) \u -> vc (VPair v u)
  VSigma x va vb ->
    -- DO NOT RECURSE ON va
    VSigma x va \v -> normalise1 $ vb v
  VPi x va vb ->
    -- DO NOT RECURSE ON va
    VPi x va \v -> normalise1 $ vb v
  -- DO NOT RECURSE
  v -> v

-- | Unit elimination
normalise2 :: Level -> Value -> Value
normalise2 lvl = \case
  -- (x : Unit) * B[x] ~> B[tt]
  VSigma _ VUnit vb -> normalise2 lvl $ vb VTT
  -- (x : Unit) -> B[x] ~> B[tt]
  VPi _ VUnit vb -> normalise2 lvl $ vb VTT
  -- (x : A) * Unit ~> A
  VSigma x va vb -> case normalise2 (lvl + 1) (vb $ VVar lvl) of
    VUnit -> normalise2 lvl va
    -- DO NOT RECURSE ON va
    _ -> VSigma x va \v -> normalise2 (lvl + 1) (vb v)
  -- (x : A) -> Unit ~> Unit
  VPi x va vb -> case normalise2 (lvl + 1) (vb $ VVar lvl) of
    VUnit -> VUnit
    -- DO NOT RECURSE ON va
    _ -> VPi x va \v -> normalise2 (lvl + 1) (vb v)
  -- DO NOT RECURSE
  v -> v

-- | Π distribution over Σ
normalise3 :: Level -> Value -> Value
normalise3 lvl = \case
  -- (x : A) -> (y : B[x]) * C[x, y] ~> (y : (x : A) -> B[x]) * ((x : A) -> C[x, y x])
  VPi x va vb -> case normalise3 (lvl + 1) (vb $ VVar lvl) of
    VSigma y _ _ ->
      let vb1 v = case normalise3 (lvl + 1) (vb v) of
            -- This pattern match should always succeed because
            -- no rewrite rule eliminates Σs in @normalise3@.
            -- Such rewrites are already done in @normalise1@ and @normalise2@.
            ~(VSigma _ u _) -> u
          vb2 f v = case normalise3 (lvl + 1) (vb v) of
            ~(VSigma _ _ u) -> u (vapp f v)
       in normalise3 lvl $ VSigma y (VPi x va vb1) \f -> VPi x va (vb2 f)
    -- DO NOT RECURSE ON va
    _ -> VPi x va \v -> normalise3 (lvl + 1) (vb v)
  -- DO NOT RECURSE ON va
  VSigma x va vb -> VSigma x va \v -> normalise3 (lvl + 1) (vb v)
  -- DO NOT RECURSE
  v -> v

-- | Normalise a type into an isomorphic type.
normalise :: Level -> Value -> Value
normalise lvl t = normalise3 lvl $ normalise2 lvl $ normalise1 t

--------------------------------------------------------------------------------
-- Pre-unification algorithm modulo βη-equivalence and type isomorphisms related to Π and Σ:
--   - (x : (y : A) * B[y]) * C[x]     ~ (x : A) * (y : B[x]) * C[(x, y)]
--   - (x : (y : A) * B[y]) -> C[x]    ~ (x : A) -> (y : B[x]) -> C[(x, y)]
--   - (x : A) * B                     ~ (x : B) * A
--   - (x : A) -> (y : B[x]) * C[x, y] ~ (y : (x : A) -> B[x]) * ((x : A) -> C[x, y x])
--   - (x : A) * Unit                  ~ A
--   - (x : Unit) * A[x]               ~ A[tt]
--   - (x : A) -> Unit                 ~ Unit
--   - (x : Unit) -> A[x]              ~ A[tt]
-- Constraints are solved from left to right (static unification).

-- | Constraints: ∀ x0, ..., x{n - 1}. t1 ≟ t2
data Constraint = Constraint
  { level :: Level, -- n
    moduloIso :: Bool, -- modulo type isomorphisms?
    lhs, rhs :: Value -- t1, t2
  }

forceConstraint :: MetaSubst -> Constraint -> Constraint
forceConstraint subst (Constraint lvl moduloIso lhs rhs) =
  Constraint lvl moduloIso (force subst lhs) (force subst rhs)

-- | Monad for unification.
-- @HeapT@ is like list transformer with priority.
-- @IO@ is for generating fresh metavariables.
type UnifyM = HeapT Dist IO

-- | Pre-unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
-- TODO: modulo permutations of Σ components
-- NOTE: Permutating Σ components would unblock reduction!
--       Take this into account?
--   e.g.)   (x : (y : (z : Type) * z) -> y.1)) * Type
--         ~ (x : Type) * (y : (z : Type) * z) -> y.1)
--         ~ (x : Type) * ((z : Type) * (y : z) -> z)
unify :: MetaSubst -> [Constraint] -> UnifyM (MetaSubst, [Constraint])
unify subst = \case
  [] -> pure (subst, [])
  (forceConstraint subst -> todo@(Constraint lvl moduloIso lhs rhs)) : todos' -> do
    let norm = if moduloIso then normalise else const id
    case (norm lvl lhs, norm lvl rhs) of
      (VStuck {}, _) -> empty
      (_, VStuck {}) -> empty
      -- rigid-rigid
      (VRigid x sp, VRigid x' sp')
        | x == x' -> unifySpine subst todos' lvl sp sp'
      (VTop n sp, VTop n' sp')
        -- TODO: unfold definitions
        | n == n' -> unifySpine subst todos' lvl sp sp'
      (VType, VType) ->
        unify subst todos'
      (VPi _ a b, VPi _ a' b') -> do
        let todo' = Constraint lvl False a a'
            todo'' = Constraint (lvl + 1) moduloIso (b $ VVar lvl) (b' $ VVar lvl)
        unify subst (todo' : todo'' : todos')
      (VAbs _ f, VAbs _ f') -> do
        let todo' = Constraint (lvl + 1) False (f $ VVar lvl) (f' $ VVar lvl)
        unify subst (todo' : todos')
      -- η-expansion
      (VAbs _ f, v) -> do
        let todo' = Constraint (lvl + 1) False (f $ VVar lvl) (vapp v $ VVar lvl)
        unify subst (todo' : todos')
      (v, VAbs _ f) -> do
        let todo' = Constraint (lvl + 1) False (vapp v $ VVar lvl) (f $ VVar lvl)
        unify subst (todo' : todos')
      (VSigma _ a b, VSigma _ a' b') -> do
        let todo' = Constraint lvl False a a'
            todo'' = Constraint (lvl + 1) moduloIso (b $ VVar lvl) (b' $ VVar lvl)
        unify subst (todo' : todo'' : todos')
      (VPair t u, VPair t' u') -> do
        let todo' = Constraint lvl False t t'
            todo'' = Constraint lvl False u u'
        unify subst (todo' : todo'' : todos')
      -- η-expansion
      (VPair t u, v) -> do
        let todo' = Constraint lvl False t (vfst v)
            todo'' = Constraint lvl False u (vsnd v)
        unify subst (todo' : todo'' : todos')
      (v, VPair t u) -> do
        let todo' = Constraint lvl False (vfst v) t
            todo'' = Constraint lvl False (vsnd v) u
        unify subst (todo' : todo'' : todos')
      (VTT, VTT) ->
        unify subst todos'
      (VUnit, VUnit) ->
        unify subst todos'
      (VFlex m ar vs sp, VFlex m' ar' vs' sp')
        | m == m' -> do
            guard (ar == ar')
            unifyMetaAppSpine subst todos' lvl vs sp vs' sp'
      -- Guessing metavariables
      -- TODO: modulo Iso
      (VFlex m arity vs (SApp' v sp), u) -> do
        m' <- lift freshMeta
        let paramsInScope = Var 0 : map Var (down (Index arity) 1)
            -- m[x0, ..., xn] ↦ λx. m'[x, x0, ..., xn]
            mabs = MetaAbs arity $ Abs "x" $ MetaApp m' paramsInScope
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl False (VFlex m' (arity + 1) (v : vs) sp) u
        unify subst' (todo' : todos')
      (t, VFlex m arity vs (SApp' v sp)) -> do
        m' <- lift freshMeta
        let paramsInScope = Var 0 : map Var (down (Index arity) 1)
            -- m[x0, ..., xn] ↦ λx. m'[x, x0, ..., xn]
            mabs = MetaAbs arity $ Abs "x" $ MetaApp m' paramsInScope
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl False t (VFlex m' (arity + 1) (v : vs) sp)
        unify subst' (todo' : todos')
      (VFlex m arity vs (SFst' sp), u) -> do
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let params = map Var $ down (Index arity - 1) 0
            -- m[x0, ..., xn] ↦ (m1[x0, ..., xn], m2[x0, ..., xn])
            mabs = MetaAbs arity $ Pair (MetaApp m1 params) (MetaApp m2 params)
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl False (VFlex m1 arity vs sp) u
        unify subst' (todo' : todos')
      (t, VFlex m arity vs (SFst' sp)) -> do
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let params = map Var $ down (Index arity - 1) 0
            -- m[x0, ..., xn] ↦ (m1[x0, ..., xn], m2[x0, ..., xn])
            mabs = MetaAbs arity $ Pair (MetaApp m1 params) (MetaApp m2 params)
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl False t (VFlex m1 arity vs sp)
        unify subst' (todo' : todos')
      (VFlex m arity vs (SSnd' sp), u) -> do
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let params = map Var $ down (Index arity - 1) 0
            -- m[x0, ..., xn] ↦ (m1[x0, ..., xn], m2[x0, ..., xn])
            mabs = MetaAbs arity $ Pair (MetaApp m1 params) (MetaApp m2 params)
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl False (VFlex m2 arity vs sp) u
        unify subst' (todo' : todos')
      (t, VFlex m arity vs (SSnd' sp)) -> do
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let params = map Var $ down (Index arity - 1) 0
            -- m[x0, ..., xn] ↦ (m1[x0, ..., xn], m2[x0, ..., xn])
            mabs = MetaAbs arity $ Pair (MetaApp m1 params) (MetaApp m2 params)
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl False t (VFlex m2 arity vs sp)
        unify subst' (todo' : todos')
      -- flex-flex
      (VFlex _ _ _ SNil, VFlex _ _ _ SNil) -> pure (subst, todo : todos')
      -- flex-rigid
      (VFlex m arity vs SNil, v) -> tryFlexRigid subst todos' lvl moduloIso m arity vs v
      (v, VFlex m arity vs SNil) -> tryFlexRigid subst todos' lvl moduloIso m arity vs v
      _ -> empty

-- | Decompose a pair of spines into constraints.
unifySpine ::
  MetaSubst ->
  [Constraint] ->
  Level ->
  Spine ->
  Spine ->
  UnifyM (MetaSubst, [Constraint])
unifySpine subst todos lvl lhs rhs = case (lhs, rhs) of
  (SNil, SNil) ->
    unify subst todos
  (SApp sp v, SApp sp' v') ->
    unifySpine subst (Constraint lvl False v v' : todos) lvl sp sp'
  (SFst sp, SFst sp') ->
    unifySpine subst todos lvl sp sp'
  (SSnd sp, SSnd sp') ->
    unifySpine subst todos lvl sp sp'
  _ -> empty

-- | Decompose pairs of meta-application arguments and spines into constraints.
unifyMetaAppSpine ::
  MetaSubst ->
  [Constraint] ->
  Level ->
  [Value] ->
  Spine ->
  [Value] ->
  Spine ->
  UnifyM (MetaSubst, [Constraint])
unifyMetaAppSpine subst todos lvl lhsVs lhsSp rhsVs rhsSp = case (lhsSp, rhsSp) of
  (SNil, SNil) ->
    unifyMetaApp subst todos lvl (reverse lhsVs) (reverse rhsVs)
  (SApp sp v, SApp sp' v') ->
    unifyMetaAppSpine subst (Constraint lvl False v v' : todos) lvl lhsVs sp rhsVs sp'
  (SFst sp, SFst sp') ->
    unifyMetaAppSpine subst todos lvl lhsVs sp rhsVs sp'
  (SSnd sp, SSnd sp') ->
    unifyMetaAppSpine subst todos lvl lhsVs sp rhsVs sp'
  _ -> empty

unifyMetaApp ::
  MetaSubst ->
  [Constraint] ->
  Level ->
  [Value] ->
  [Value] ->
  UnifyM (MetaSubst, [Constraint])
unifyMetaApp subst todos lvl lhs rhs = case (lhs, rhs) of
  ([], []) ->
    unify subst todos
  (v : vs, v' : vs') ->
    unifyMetaApp subst (Constraint lvl False v v' : todos) lvl vs vs'
  _ -> empty

-- | Go through candidate solutions for ∀ x0, ..., x{lvl - 1}. m[args] ≟ t
tryFlexRigid ::
  MetaSubst ->
  [Constraint] ->
  Level ->
  Bool ->
  Meta ->
  Int ->
  [Value] ->
  Value ->
  UnifyM (MetaSubst, [Constraint])
tryFlexRigid subst todos lvl moduloIso m arity args t = do
  (body, val) <- generate tSpine
  let mabs = MetaAbs arity body
      subst' = HM.insert m mabs subst
      todo' = Constraint lvl moduloIso val t
  unify subst' (todo' : todos)
  where
    params = map Var $ down (Index arity - 1) 0
    paramsInScope = Var 0 : map Var (down (Index arity) 1)

    (tHead, tSpine) = headSpine t

    -- Huet-style projection bindings generalised for SOAS
    generate = \case
      SNil -> imitation <|> projection
      SApp sp _ -> do
        m' <- lift freshMeta
        let arg = MetaApp m' params
            varg = VMetaApp m' args
        (body, val) <- generate sp <|> projection
        pure (App body arg, vapp val varg)
      SFst sp -> do
        (body, val) <- generate sp <|> projection
        pure (Fst body, vfst val)
      SSnd sp -> do
        (body, val) <- generate sp <|> projection
        pure (Snd body, vsnd val)

    projection = do
      i <- choose [0 .. arity - 1]
      let tm = Var (Index i)
          val = args !! (arity - i - 1)
      pure (tm, val)

    imitation = case tHead of
      HStuck {} -> error "unreachable"
      HFlex {} -> error "unreachable"
      HRigid {} -> empty
      -- m[x0, ..., xn] ↦ f
      HTop f -> pure (Top f, VTop f SNil)
      -- m[x0, ..., xn] ↦ Type
      HType -> pure (Type, VType)
      -- m[x0, ..., xn] ↦ (x : m1[x0, ..., xn]) -> m2[x, x0, ..., xn]
      HPi n _ _ -> do
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let u = Pi n (MetaApp m1 params) (MetaApp m2 paramsInScope)
            v = VPi n (VMetaApp m1 args) \x -> VMetaApp m2 (x : args)
        pure (u, v)
      -- m[x0, ..., xn] ↦ λx. m'[x, x0, ..., xn]
      HAbs n _ -> do
        m' <- lift freshMeta
        let u = Abs n $ MetaApp m' paramsInScope
            v = VAbs n \x -> VMetaApp m' (x : args)
        pure (u, v)
      -- m[x0, ..., xn] ↦ (x : m1[x0, ..., xn]) * m2[x, x0, ..., xn]
      HSigma n _ _ -> do
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let u = Sigma n (MetaApp m1 params) (MetaApp m2 paramsInScope)
            v = VSigma n (VMetaApp m1 args) \x -> VMetaApp m2 (x : args)
        pure (u, v)
      -- m[x0, ..., xn] ↦ (x : m1[x0, ..., xn]) * m2[x, x0, ..., xn]
      HPair {} -> do
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let u = Pair (MetaApp m1 params) (MetaApp m2 params)
            v = VPair (VMetaApp m1 args) (VMetaApp m2 args)
        pure (u, v)
      -- m[x0, ..., xn] ↦ Unit
      HUnit -> pure (Unit, VUnit)
      -- m[x0, ..., xn] ↦ tt
      HTT -> pure (TT, VTT)

-- | Pre-unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
unifyRaw' :: Raw -> Raw -> UnifyM (MetaSubst, [Constraint])
unifyRaw' t t' =
  unify HM.empty [Constraint 0 True (evaluateRaw HM.empty t) (evaluateRaw HM.empty t')]

deepForceMetaAbs :: MetaSubst -> MetaAbs -> MetaAbs
deepForceMetaAbs subst mabs = mabs {body = body'}
  where
    vbody =
      deepForce subst $
        vmetaApp mabs [VVar l | l <- [0 .. Level mabs.arity - 1]]
    body' = quote (Level mabs.arity) vbody

deepForceMetaSubst :: HS.HashSet Meta -> MetaSubst -> MetaSubst
deepForceMetaSubst mvars subst = flip imapMaybe subst \m mabs ->
  if m `HS.member` mvars
    then Just $ deepForceMetaAbs subst mabs
    else Nothing

unifyRaw :: Raw -> Raw -> IO (Maybe MetaSubst)
unifyRaw t t' =
  fmap (deepForceMetaSubst (metaVarSet t <> metaVarSet t') . fst . snd)
    <$> bestT (unifyRaw' t t')

unifiable :: Raw -> Raw -> IO Bool
unifiable t t' = isJust <$> bestT (unifyRaw' t t')
