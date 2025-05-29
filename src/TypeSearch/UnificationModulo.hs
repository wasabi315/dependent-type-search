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
import Control.Monad.Writer
import Data.HashMap.Lazy qualified as HM
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
    convMode :: ConvMode,
    moduloIso :: Bool, -- modulo type isomorphisms?
    lhs, rhs :: Value -- t1, t2
  }

forceConstraint :: TopEnv -> MetaSubst -> Constraint -> Constraint
forceConstraint topEnv subst constraint =
  constraint
    { lhs = force topEnv subst constraint.lhs,
      rhs = force topEnv subst constraint.rhs
    }

-- | Monad for unification.
-- @HeapT@ is like list transformer with priority.
-- @IO@ is for generating fresh metavariables.
type UnifyM = HeapT Dist IO

data ConvMode
  = Rigid
  | Flex
  | Full

expectNotFlex :: ConvMode -> UnifyM ()
expectNotFlex cm = case cm of
  Flex -> empty
  _ -> pure ()

-- | Pre-unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
-- TODO: modulo permutations of Σ components
-- NOTE: Permutating Σ components would unblock reduction!
--       Take this into account?
--   e.g.)   (x : (y : (z : Type) * z) -> y.1)) * Type
--         ~ (x : Type) * (y : (z : Type) * z) -> y.1)
--         ~ (x : Type) * ((z : Type) * (y : z) -> z)
unify :: TopEnv -> MetaSubst -> [Constraint] -> UnifyM (MetaSubst, [Constraint])
unify topEnv subst = \case
  [] -> pure (subst, [])
  (forceConstraint topEnv subst -> todo@(Constraint lvl cm moduloIso lhs rhs)) : todos' -> do
    let norm = if moduloIso then normalise else const id
    case (norm lvl lhs, norm lvl rhs) of
      (VStuck {}, _) -> empty
      (_, VStuck {}) -> empty
      -- rigid-rigid
      (VRigid x sp, VRigid x' sp')
        | x == x' -> unifySpine cm topEnv subst todos' lvl sp sp'
      (VType, VType) ->
        unify topEnv subst todos'
      (VPi _ a b, VPi _ a' b') -> do
        let todo' = Constraint lvl cm False a a'
            todo'' = Constraint (lvl + 1) cm moduloIso (b $ VVar lvl) (b' $ VVar lvl)
        unify topEnv subst (todo' : todo'' : todos')
      (VAbs _ f, VAbs _ f') -> do
        let todo' = Constraint (lvl + 1) cm False (f $ VVar lvl) (f' $ VVar lvl)
        unify topEnv subst (todo' : todos')
      -- η-expansion
      (VAbs _ f, t') -> do
        let todo' = Constraint (lvl + 1) cm False (f $ VVar lvl) (vapp t' $ VVar lvl)
        unify topEnv subst (todo' : todos')
      (t, VAbs _ f) -> do
        let todo' = Constraint (lvl + 1) cm False (vapp t $ VVar lvl) (f $ VVar lvl)
        unify topEnv subst (todo' : todos')
      (VSigma _ a b, VSigma _ a' b') -> do
        let todo' = Constraint lvl cm False a a'
            todo'' = Constraint (lvl + 1) cm moduloIso (b $ VVar lvl) (b' $ VVar lvl)
        unify topEnv subst (todo' : todo'' : todos')
      (VPair t u, VPair t' u') -> do
        let todo' = Constraint lvl cm False t t'
            todo'' = Constraint lvl cm False u u'
        unify topEnv subst (todo' : todo'' : todos')
      -- η-expansion
      (VPair t u, v) -> do
        let todo' = Constraint lvl cm False t (vfst v)
            todo'' = Constraint lvl cm False u (vsnd v)
        unify topEnv subst (todo' : todo'' : todos')
      (v, VPair t u) -> do
        let todo' = Constraint lvl cm False (vfst v) t
            todo'' = Constraint lvl cm False (vsnd v) u
        unify topEnv subst (todo' : todo'' : todos')
      (VTT, VTT) ->
        unify topEnv subst todos'
      (VUnit, VUnit) ->
        unify topEnv subst todos'
      (VFlex m ar vs sp, VFlex m' ar' vs' sp')
        | m == m' -> do
            guard (ar == ar')
            unifyMetaAppSpine cm topEnv subst todos' lvl vs sp vs' sp'
      -- Guessing metavariables
      -- TODO: modulo Iso
      (VFlex m arity ts (SApp' v sp), t') -> do
        expectNotFlex cm
        m' <- lift freshMeta
        let paramsInScope = Var 0 : map Var (down (Index arity) 1)
            -- m[x0, ..., xn] ↦ λx. m'[x, x0, ..., xn]
            mabs = MetaAbs arity $ Abs "x" $ MetaApp m' paramsInScope
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl cm False (VFlex m' (arity + 1) (v : ts) sp) t'
        unify topEnv subst' (todo' : todos')
      (t, VFlex m arity ts' (SApp' v sp)) -> do
        expectNotFlex cm
        m' <- lift freshMeta
        let paramsInScope = Var 0 : map Var (down (Index arity) 1)
            -- m[x0, ..., xn] ↦ λx. m'[x, x0, ..., xn]
            mabs = MetaAbs arity $ Abs "x" $ MetaApp m' paramsInScope
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl cm False t (VFlex m' (arity + 1) (v : ts') sp)
        unify topEnv subst' (todo' : todos')
      (VFlex m arity ts (SFst' sp), t') -> do
        expectNotFlex cm
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let params = map Var $ down (Index arity - 1) 0
            -- m[x0, ..., xn] ↦ (m1[x0, ..., xn], m2[x0, ..., xn])
            mabs = MetaAbs arity $ Pair (MetaApp m1 params) (MetaApp m2 params)
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl cm False (VFlex m1 arity ts sp) t'
        unify topEnv subst' (todo' : todos')
      (t, VFlex m arity ts' (SFst' sp)) -> do
        expectNotFlex cm
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let params = map Var $ down (Index arity - 1) 0
            -- m[x0, ..., xn] ↦ (m1[x0, ..., xn], m2[x0, ..., xn])
            mabs = MetaAbs arity $ Pair (MetaApp m1 params) (MetaApp m2 params)
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl cm False t (VFlex m1 arity ts' sp)
        unify topEnv subst' (todo' : todos')
      (VFlex m arity ts (SSnd' sp), t') -> do
        expectNotFlex cm
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let params = map Var $ down (Index arity - 1) 0
            -- m[x0, ..., xn] ↦ (m1[x0, ..., xn], m2[x0, ..., xn])
            mabs = MetaAbs arity $ Pair (MetaApp m1 params) (MetaApp m2 params)
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl cm False (VFlex m2 arity ts sp) t'
        unify topEnv subst' (todo' : todos')
      (t, VFlex m arity ts' (SSnd' sp)) -> do
        expectNotFlex cm
        m1 <- lift freshMeta
        m2 <- lift freshMeta
        let params = map Var $ down (Index arity - 1) 0
            -- m[x0, ..., xn] ↦ (m1[x0, ..., xn], m2[x0, ..., xn])
            mabs = MetaAbs arity $ Pair (MetaApp m1 params) (MetaApp m2 params)
            subst' = HM.insert m mabs subst
            todo' = Constraint lvl cm False t (VFlex m2 arity ts' sp)
        unify topEnv subst' (todo' : todos')
      -- flex-flex
      (VFlex _ _ _ SNil, VFlex _ _ _ SNil) -> pure (subst, todo : todos')
      -- flex-rigid
      (VFlex m arity ts SNil, t') -> do
        expectNotFlex cm
        tryFlexRigid cm topEnv subst todos' lvl moduloIso m arity ts t'
      (t, VFlex m arity ts' SNil) -> do
        expectNotFlex cm
        tryFlexRigid cm topEnv subst todos' lvl moduloIso m arity ts' t
      -- definition unfolding
      -- TODO: track which definition we have unfolded
      (VTop _ n sp ts, VTop _ n' sp' ts') -> case cm of
        Rigid
          | n == n' ->
              unifySpine Flex topEnv subst todos' lvl sp sp'
                <|> do
                  tell 1
                  v <- choose ts
                  v' <- choose ts'
                  let todo' = Constraint lvl Full False v v'
                  unify topEnv subst (todo' : todos')
        Flex
          | n == n' -> unifySpine Flex topEnv subst todos' lvl sp sp'
          | otherwise -> empty
        _ -> do
          tell 1
          t <- choose ts
          t' <- choose ts'
          let todo' = Constraint lvl cm False t t'
          unify topEnv subst (todo' : todos')
      (VTop _ _ _ ts, t') -> case cm of
        Flex -> empty
        _ -> do
          tell 1
          t <- choose ts
          let todo' = Constraint lvl cm False t t'
          unify topEnv subst (todo' : todos')
      (t, VTop _ _ _ ts) -> case cm of
        Flex -> empty
        _ -> do
          tell 1
          t' <- choose ts
          let todo' = Constraint lvl cm False t t'
          unify topEnv subst (todo' : todos')
      _ -> empty

-- | Decompose a pair of spines into constraints.
unifySpine ::
  ConvMode ->
  TopEnv ->
  MetaSubst ->
  [Constraint] ->
  Level ->
  Spine ->
  Spine ->
  UnifyM (MetaSubst, [Constraint])
unifySpine cm topEnv subst todos lvl lhs rhs = case (lhs, rhs) of
  (SNil, SNil) ->
    unify topEnv subst todos
  (SApp sp v, SApp sp' v') ->
    unifySpine cm topEnv subst (Constraint lvl cm False v v' : todos) lvl sp sp'
  (SFst sp, SFst sp') ->
    unifySpine cm topEnv subst todos lvl sp sp'
  (SSnd sp, SSnd sp') ->
    unifySpine cm topEnv subst todos lvl sp sp'
  _ -> empty

-- | Decompose pairs of meta-application arguments and spines into constraints.
unifyMetaAppSpine ::
  ConvMode ->
  TopEnv ->
  MetaSubst ->
  [Constraint] ->
  Level ->
  [Value] ->
  Spine ->
  [Value] ->
  Spine ->
  UnifyM (MetaSubst, [Constraint])
unifyMetaAppSpine cm topEnv subst todos lvl lhsVs lhsSp rhsVs rhsSp = case (lhsSp, rhsSp) of
  (SNil, SNil) ->
    unifyMetaApp cm topEnv subst todos lvl (reverse lhsVs) (reverse rhsVs)
  (SApp sp v, SApp sp' v') ->
    unifyMetaAppSpine cm topEnv subst (Constraint lvl cm False v v' : todos) lvl lhsVs sp rhsVs sp'
  (SFst sp, SFst sp') ->
    unifyMetaAppSpine cm topEnv subst todos lvl lhsVs sp rhsVs sp'
  (SSnd sp, SSnd sp') ->
    unifyMetaAppSpine cm topEnv subst todos lvl lhsVs sp rhsVs sp'
  _ -> empty

unifyMetaApp ::
  ConvMode ->
  TopEnv ->
  MetaSubst ->
  [Constraint] ->
  Level ->
  [Value] ->
  [Value] ->
  UnifyM (MetaSubst, [Constraint])
unifyMetaApp cm topEnv subst todos lvl lhs rhs = case (lhs, rhs) of
  ([], []) ->
    unify topEnv subst todos
  (v : vs, v' : vs') ->
    unifyMetaApp cm topEnv subst (Constraint lvl cm False v v' : todos) lvl vs vs'
  _ -> empty

-- | Go through candidate solutions for ∀ x0, ..., x{lvl - 1}. m[args] ≟ t
tryFlexRigid ::
  ConvMode ->
  TopEnv ->
  MetaSubst ->
  [Constraint] ->
  Level ->
  Bool ->
  Meta ->
  Int ->
  [Value] ->
  Value ->
  UnifyM (MetaSubst, [Constraint])
tryFlexRigid cm topEnv subst todos lvl moduloIso m arity args t = do
  (body, val) <- generate tSpine
  let mabs = MetaAbs arity body
      subst' = HM.insert m mabs subst
      todo' = Constraint lvl cm moduloIso val t
  unify topEnv subst' (todo' : todos)
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
      HTop ms f vs -> pure (Top ms f, VTop ms f SNil vs)
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
unifyRaw' :: TopEnv -> Raw -> Raw -> UnifyM (MetaSubst, [Constraint])
unifyRaw' topEnv t t' =
  unify topEnv HM.empty [Constraint 0 Rigid True (evaluateRaw topEnv HM.empty t) (evaluateRaw topEnv HM.empty t')]

deepForceMetaAbs :: TopEnv -> MetaSubst -> MetaAbs -> MetaAbs
deepForceMetaAbs topEnv subst mabs = mabs {body = body'}
  where
    vbody =
      deepForce topEnv subst $
        vmetaApp topEnv mabs [VVar l | l <- [0 .. Level mabs.arity - 1]]
    body' = quote (Level mabs.arity) vbody

deepForceMetaSubst :: TopEnv -> HS.HashSet Meta -> MetaSubst -> MetaSubst
deepForceMetaSubst topEnv mvars subst = flip imapMaybe subst \m mabs ->
  if m `HS.member` mvars
    then Just $ deepForceMetaAbs topEnv subst mabs
    else Nothing

unifyRaw :: TopEnv -> Raw -> Raw -> IO (Maybe MetaSubst)
unifyRaw topEnv t t' =
  fmap (deepForceMetaSubst topEnv (metaVarSet t <> metaVarSet t') . fst . snd)
    <$> bestT (unifyRaw' topEnv t t')

unifiable :: TopEnv -> Raw -> Raw -> IO Bool
unifiable topEnv t t' = isJust <$> bestT (unifyRaw' topEnv t t')
