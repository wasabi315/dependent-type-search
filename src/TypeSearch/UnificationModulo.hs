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
import Data.List (subsequences)
import Data.Maybe
import Data.Monus.Dist
import Data.Text qualified as T
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Pretty
import TypeSearch.Raw
import TypeSearch.Term
import Witherable

--------------------------------------------------------------------------------
-- Untyped version of the rewrite system STR^{Coq} presented in the paper by Delahaye (2000).
-- TODO: Is this rewrite system confluent?

-- | Σ associativity and currying
normalise1 :: TopEnv -> MetaSubst -> Value -> Value
normalise1 topEnv subst t = case force topEnv subst t of
  -- (x : (y : A) * B[y]) * C[x] ~> (x : A) * (y : B[x]) * C[(x, y)]
  VSigma x (force topEnv subst -> VSigma y va vb) vc ->
    normalise1 topEnv subst $ VSigma x va \ ~v -> VSigma y (vb v) \ ~u -> vc (VPair v u)
  -- (x : (y : A) * B[y]) -> C[x] ~> (x : A) -> (y : B[x]) -> C[(x, y)]
  VPi x (force topEnv subst -> VSigma y va vb) vc ->
    normalise1 topEnv subst $ VPi x va \ ~v -> VPi y (vb v) \ ~u -> vc (VPair v u)
  VSigma x va vb ->
    -- DO NOT RECURSE ON va
    VSigma x va \ ~v -> normalise1 topEnv subst $ vb v
  VPi x va vb ->
    -- DO NOT RECURSE ON va
    VPi x va \ ~v -> normalise1 topEnv subst $ vb v
  -- DO NOT RECURSE
  v -> v

-- | Unit elimination
normalise2 :: TopEnv -> MetaSubst -> Level -> Value -> Value
normalise2 topEnv subst lvl t = case force topEnv subst t of
  -- (x : Unit) * B[x] ~> B[tt]
  VSigma _ VUnit vb -> normalise2 topEnv subst lvl $ vb VTT
  -- (x : Unit) -> B[x] ~> B[tt]
  VPi _ VUnit vb -> normalise2 topEnv subst lvl $ vb VTT
  -- (x : A) * Unit ~> A
  VSigma x va vb -> case normalise2 topEnv subst (lvl + 1) (vb $ VVar lvl) of
    VUnit -> normalise2 topEnv subst lvl va
    -- DO NOT RECURSE ON va
    _ -> VSigma x va \ ~v -> normalise2 topEnv subst (lvl + 1) (vb v)
  -- (x : A) -> Unit ~> Unit
  VPi x va vb -> case normalise2 topEnv subst (lvl + 1) (vb $ VVar lvl) of
    VUnit -> VUnit
    -- DO NOT RECURSE ON va
    _ -> VPi x va \ ~v -> normalise2 topEnv subst (lvl + 1) (vb v)
  -- DO NOT RECURSE
  v -> v

-- | Π distribution over Σ
normalise3 :: TopEnv -> MetaSubst -> Level -> Value -> Value
normalise3 topEnv subst lvl t = case force topEnv subst t of
  -- (x : A) -> (y : B[x]) * C[x, y] ~> (y : (x : A) -> B[x]) * ((x : A) -> C[x, y x])
  VPi x va vb -> case normalise3 topEnv subst (lvl + 1) (vb $ VVar lvl) of
    VSigma y _ _ ->
      let vb1 ~v = case normalise3 topEnv subst (lvl + 1) (vb v) of
            -- This pattern match should always succeed because
            -- no rewrite rule eliminates Σs in @normalise3@.
            -- Such rewrites are already done in @normalise1@ and @normalise2@.
            ~(VSigma _ u _) -> u
          vb2 ~f ~v = case normalise3 topEnv subst (lvl + 2) (vb v) of
            ~(VSigma _ _ u) -> u (vapp f v)
       in normalise3 topEnv subst lvl $ VSigma y (VPi x va vb1) \ ~f -> VPi x va (vb2 f)
    -- DO NOT RECURSE ON va
    _ -> VPi x va \ ~v -> normalise3 topEnv subst (lvl + 1) (vb v)
  -- DO NOT RECURSE ON va
  VSigma x va vb -> VSigma x va \ ~v -> normalise3 topEnv subst (lvl + 1) (vb v)
  -- DO NOT RECURSE
  v -> v

-- | Normalise a type into an isomorphic type.
normalise :: TopEnv -> MetaSubst -> Level -> Value -> Value
normalise topEnv subst lvl t =
  normalise3 topEnv subst lvl $
    normalise2 topEnv subst lvl $
      normalise1 topEnv subst t

--------------------------------------------------------------------------------
-- Unification procedure modulo βη-equivalence and type isomorphisms related to Π and Σ:
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
  if constraint.moduloIso
    then
      constraint
        { lhs = normalise topEnv subst constraint.level constraint.lhs,
          rhs = normalise topEnv subst constraint.level constraint.rhs
        }
    else
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
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Functions for creating bindings

data ImitationKind
  = ITop [ModuleName] Name
  | IType
  | IPi Name
  | IAbs Name
  | ISigma Name
  | IPair
  | IUnit
  | ITT
  | INat
  | IZero
  | ISuc
  | IEq
  | IRefl

imitation :: ImitationKind -> Int -> UnifyM MetaAbs
imitation kind arity =
  MetaAbs arity <$> imitationHelper kind params params'
  where
    -- [x0, ..., xn]
    params = map Var $ down (Index arity - 1) 0
    -- x. [x0, ..., xn, x]
    params' = map Var $ down (Index arity) 0

imitationHelper :: ImitationKind -> [Term] -> [Term] -> UnifyM Term
imitationHelper kind params params' = lift case kind of
  -- M[x0, ..., xn] ↦ n
  ITop ms n -> pure $ Top ms n
  -- M[x0, ..., xn] ↦ Type
  IType -> pure Type
  -- M[x0, ..., xn] ↦ (x : M1[x0, ..., xn]) -> M2[x0, ..., xn, x]
  IPi x -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Pi x (MetaApp m1 params) (MetaApp m2 params')
  -- M[x0, ..., xn] ↦ λx. M'[x0, ..., xn, x]
  IAbs x -> do
    m' <- freshMeta
    pure $ Abs x (MetaApp m' params')
  -- M[x0, ..., xn] ↦ Σ x : M1[x0, ..., xn]. M2[x0, ..., xn, x]
  ISigma x -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Sigma x (MetaApp m1 params) (MetaApp m2 params')
  -- M[x0, ..., xn] ↦ (M1[x0, ..., xn], M2[x0, ..., xn])
  IPair -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Pair (MetaApp m1 params) (MetaApp m2 params')
  -- M[x0, ..., xn] ↦ Unit
  IUnit -> pure Unit
  -- M[x0, ..., xn] ↦ tt
  ITT -> pure TT
  -- M[x0, ..., xn] ↦ Nat
  INat -> pure Nat
  -- M[x0, ..., xn] ↦ zero
  IZero -> pure Zero
  -- M[x0, ..., xn] ↦ suc M'[x0, ..., xn]
  ISuc -> do
    m' <- freshMeta
    pure $ Suc `App` MetaApp m' params
  -- M[x0, ..., xn] ↦ Eq M1[x0, ..., xn] M2[x0, ..., xn] M3[x0, ..., xn]
  IEq -> do
    m1 <- freshMeta
    m2 <- freshMeta
    m3 <- freshMeta
    pure $ Eq `App` MetaApp m1 params `App` MetaApp m2 params `App` MetaApp m3 params
  -- M[x0, ..., xn] ↦ Refl M1[x0, ..., xn] M2[x0, ..., xn]
  IRefl -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Refl `App` MetaApp m1 params `App` MetaApp m2 params

jpProjectionHelper :: Int -> UnifyM Term
jpProjectionHelper arity = Var <$> choose [0 .. Index arity - 1]

huetProjection :: Value -> Int -> UnifyM MetaAbs
huetProjection t arity =
  MetaAbs arity <$> huetProjectionHelper t arity params params'
  where
    params = map Var $ down (Index arity - 1) 0
    params' = map Var $ down (Index arity) 0

huetProjectionHelper :: Value -> Int -> [Term] -> [Term] -> UnifyM Term
huetProjectionHelper t arity params params' = go $ spine t
  where
    kind = case t of
      VRigid {} -> empty
      VFlex {} -> empty
      VTop n _ ts -> pure $ ITop (fst <$> ts) n
      VType -> pure IType
      VPi x _ _ -> pure $ IPi x
      VAbs x _ -> pure $ IAbs x
      VSigma x _ _ -> pure $ ISigma x
      VPair {} -> pure IPair
      VUnit -> pure IUnit
      VTT -> pure ITT
      VNat -> pure INat
      VZero -> pure IZero
      VSuc {} -> pure ISuc
      VEq {} -> pure IEq
      VRefl {} -> pure IRefl
      VStuck {} -> empty

    go sp =
      ( case sp of
          SNil -> kind >>= \k -> imitationHelper k params params'
          SApp sp' _ -> do
            m <- lift freshMeta
            let u = MetaApp m params
            flip App u <$> go sp'
          SFst sp' -> Fst <$> go sp'
          SSnd sp' -> Snd <$> go sp'
          SNatElim _ _ _ sp' -> do
            m1 <- lift freshMeta
            m2 <- lift freshMeta
            m3 <- lift freshMeta
            let p = MetaApp m1 params
                s = MetaApp m2 params
                z = MetaApp m3 params
            (\n -> NatElim `App` p `App` s `App` z `App` n) <$> go sp'
          SEqElim _ _ _ _ _ sp' -> do
            m1 <- lift freshMeta
            m2 <- lift freshMeta
            m3 <- lift freshMeta
            m4 <- lift freshMeta
            m5 <- lift freshMeta
            let a = MetaApp m1 params
                x = MetaApp m2 params
                p = MetaApp m3 params
                r = MetaApp m4 params
                y = MetaApp m5 params
            (\eq -> EqElim `App` a `App` x `App` p `App` r `App` y `App` eq) <$> go sp'
      )
        <|> jpProjectionHelper arity

identification :: Int -> Int -> UnifyM (MetaAbs, MetaAbs)
identification arity arity' = lift do
  i <- freshMeta
  ms <- replicateM arity freshMeta
  ms' <- replicateM arity' freshMeta
  let params = map Var $ down (Index arity - 1) 0
      params' = map Var $ down (Index arity' - 1) 0
      mabs = MetaAbs arity $ MetaApp i $ params ++ map (`MetaApp` params) ms'
      mabs' = MetaAbs arity' $ MetaApp i $ map (`MetaApp` params') ms ++ params'
  pure (mabs, mabs')

elimination :: Int -> UnifyM MetaAbs
elimination arity = do
  e <- lift freshMeta
  let params = map Var $ down (Index arity - 1) 0
  subParams <- choose $ subsequences params
  let mabs = MetaAbs arity $ MetaApp e subParams
  pure mabs

--------------------------------------------------------------------------------

data PartialRenaming = PRen
  { dom :: Level,
    cod :: Level,
    ren :: HM.HashMap Level Level
  }

liftPRen :: PartialRenaming -> PartialRenaming
liftPRen (PRen dom cod ren) = PRen (dom + 1) (cod + 1) (HM.insert cod dom ren)

invert :: TopEnv -> MetaSubst -> Level -> [Value] -> UnifyM PartialRenaming
invert topEnv subst lvl args = do
  let go dom ren = \case
        [] -> pure (dom, ren)
        t : ts -> case force topEnv subst t of
          VVar l
            | not (HM.member l ren) -> go (dom + 1) (HM.insert l dom ren) ts
          _ -> empty
  (dom, ren) <- go 0 HM.empty args
  pure $ PRen dom lvl ren

rename :: TopEnv -> MetaSubst -> Meta -> PartialRenaming -> Value -> UnifyM Term
rename topEnv metaSubst m = go
  where
    go :: PartialRenaming -> Value -> UnifyM Term
    go pren t = case force topEnv metaSubst t of
      VFlex m' _ ts sp
        | m == m' -> empty -- occurs check
        | otherwise -> do
            ts' <- traverse (go pren) ts
            goSpine pren (MetaApp m' ts') sp
      VRigid l sp -> case HM.lookup l pren.ren of
        Nothing -> empty
        Just l' -> goSpine pren (Var $ levelToIndex pren.dom l') sp
      VTop n sp ts -> goSpine pren (Top (map fst ts) n) sp
      VType -> pure Type
      VPi x a b -> Pi x <$> go pren a <*> go (liftPRen pren) (b $ VVar pren.cod)
      VAbs x f -> Abs x <$> go (liftPRen pren) (f $ VVar pren.cod)
      VSigma x a b -> Sigma x <$> go pren a <*> go (liftPRen pren) (b $ VVar pren.cod)
      VPair u v -> Pair <$> go pren u <*> go pren v
      VUnit -> pure Unit
      VTT -> pure TT
      VNat -> pure Nat
      VZero -> pure Zero
      VSuc u -> (Suc `App`) <$> go pren u
      VEq a x y -> do
        a' <- go pren a
        x' <- go pren x
        y' <- go pren y
        pure $ Eq `App` a' `App` x' `App` y'
      VRefl a x -> do
        a' <- go pren a
        x' <- go pren x
        pure $ Refl `App` a' `App` x'
      VStuck {} -> empty

    goSpine :: PartialRenaming -> Term -> Spine -> UnifyM Term
    goSpine pren = foldM (goElim pren)

    goElim :: PartialRenaming -> Term -> Elim -> UnifyM Term
    goElim pren t = \case
      EApp u -> App t <$> go pren u
      EFst -> pure $ Fst t
      ESnd -> pure $ Snd t
      ENatElim p s z -> do
        p' <- go pren p
        s' <- go pren s
        z' <- go pren z
        pure $ NatElim `App` p' `App` s' `App` z' `App` t
      EEqElim a x p r y -> do
        a' <- go pren a
        x' <- go pren x
        p' <- go pren p
        r' <- go pren r
        y' <- go pren y
        pure $ EqElim `App` a' `App` x' `App` p' `App` r' `App` y' `App` t

--------------------------------------------------------------------------------

solve :: TopEnv -> MetaSubst -> Constraint -> UnifyM MetaSubst
solve topEnv subst (Constraint lvl _ _ lhs rhs) = do
  case (lhs, rhs) of
    (VFlex m ar ts SNil, t') -> helper m ar ts t'
    (t, VFlex m ar ts' SNil) -> helper m ar ts' t
    _ -> empty
  where
    helper m ar ts t = do
      pren <- invert topEnv subst lvl ts
      body <- rename topEnv subst m pren t
      let mabs = MetaAbs ar body
          subst' = HM.insert m mabs subst
      pure subst'

-- | Decompose a constraint into a set of smaller constraints.
decompose :: Constraint -> [Constraint] -> UnifyM [Constraint]
decompose (Constraint lvl cm iso lhs rhs) todos = case (lhs, rhs) of
  (VStuck {}, _) -> empty
  (_, VStuck {}) -> empty
  (VRigid x sp, VRigid x' sp')
    | x == x' -> decomposeSpine cm lvl sp sp' todos
    | otherwise -> empty
  (VRigid x (SApp sp t), VFlex m' ar' ts' (SApp sp' t')) -> do
    let todo' = Constraint lvl cm False (VRigid x sp) (VFlex m' ar' ts' sp')
        todo'' = Constraint lvl cm False t t'
    pure (todo' : todo'' : todos)
  (VRigid x (SFst sp), VFlex m' ar' ts' (SFst sp')) -> do
    let todo' = Constraint lvl cm False (VRigid x sp) (VFlex m' ar' ts' sp')
    pure (todo' : todos)
  (VRigid x (SSnd sp), VFlex m' ar' ts' (SSnd sp')) -> do
    let todo' = Constraint lvl cm False (VRigid x sp) (VFlex m' ar' ts' sp')
    pure (todo' : todos)
  (VFlex m ar ts (SApp sp t), VRigid x' (SApp sp' t')) -> do
    let todo' = Constraint lvl cm False (VFlex m ar ts sp) (VRigid x' sp')
        todo'' = Constraint lvl cm False t t'
    pure (todo' : todo'' : todos)
  (VFlex m ar ts (SFst sp), VRigid x' (SFst sp')) -> do
    let todo' = Constraint lvl cm False (VFlex m ar ts sp) (VRigid x' sp')
    pure (todo' : todos)
  (VFlex m ar ts (SSnd sp), VRigid x' (SSnd sp')) -> do
    let todo' = Constraint lvl cm False (VFlex m ar ts sp) (VRigid x' sp')
    pure (todo' : todos)
  (VFlex m ar ts (SApp sp t), VFlex m' ar' ts' (SApp sp' t')) -> do
    let todo' = Constraint lvl cm False (VFlex m ar ts sp) (VFlex m' ar' ts' sp')
        todo'' = Constraint lvl cm False t t'
    pure (todo' : todo'' : todos)
  (VFlex m ar ts (SFst sp), VFlex m' ar' ts' (SFst sp')) -> do
    let todo' = Constraint lvl cm False (VFlex m ar ts sp) (VFlex m' ar' ts' sp')
    pure (todo' : todos)
  (VFlex m ar ts (SSnd sp), VFlex m' ar' ts' (SSnd sp')) -> do
    let todo' = Constraint lvl cm False (VFlex m ar ts sp) (VFlex m' ar' ts' sp')
    pure (todo' : todos)
  (VFlex m _ ts SNil, VFlex m' _ ts' SNil)
    | m == m' -> decomposeMetaArgs cm lvl (reverse ts) (reverse ts') todos
  (VType, VType) -> pure todos
  (VPi _ a b, VPi _ a' b') -> do
    let todo' = Constraint lvl cm False a a'
        todo'' = Constraint (lvl + 1) cm iso (b $ VVar lvl) (b' $ VVar lvl)
    pure (todo' : todo'' : todos)
  (VAbs _ f, VAbs _ f') -> do
    let todo' = Constraint (lvl + 1) cm False (f $ VVar lvl) (f' $ VVar lvl)
    pure (todo' : todos)
  -- η-expansion
  (VAbs _ f, t') -> do
    let todo' = Constraint (lvl + 1) cm False (f $ VVar lvl) (vapp t' $ VVar lvl)
    pure (todo' : todos)
  (t, VAbs _ f) -> do
    let todo' = Constraint (lvl + 1) cm False (vapp t $ VVar lvl) (f $ VVar lvl)
    pure (todo' : todos)
  (VSigma _ a b, VSigma _ a' b') -> do
    let todo' = Constraint lvl cm False a a'
        todo'' = Constraint (lvl + 1) cm iso (b $ VVar lvl) (b' $ VVar lvl)
    pure (todo' : todo'' : todos)
  (VPair t u, VPair t' u') -> do
    let todo' = Constraint lvl cm False t t'
        todo'' = Constraint lvl cm False u u'
    pure (todo' : todo'' : todos)
  -- η-expansion
  (VPair t u, t') -> do
    let todo' = Constraint lvl cm False t (vfst t')
        todo'' = Constraint lvl cm False u (vsnd t')
    pure (todo' : todo'' : todos)
  (t, VPair t' u') -> do
    let todo' = Constraint lvl cm False (vfst t) t'
        todo'' = Constraint lvl cm False (vsnd t) u'
    pure (todo' : todo'' : todos)
  (VUnit, VUnit) -> pure todos
  (VTT, VTT) -> pure todos
  (VNat, VNat) -> pure todos
  (VZero, VZero) -> pure todos
  (VSuc t, VSuc t') -> do
    let todo' = Constraint lvl cm False t t'
    pure (todo' : todos)
  (VEq a t u, VEq a' t' u') -> do
    let todo' = Constraint lvl cm False a a'
        todo'' = Constraint lvl cm False t t'
        todo''' = Constraint lvl cm False u u'
    pure (todo' : todo'' : todo''' : todos)
  (VRefl a t, VRefl a' t') -> do
    let todo' = Constraint lvl cm False a a'
        todo'' = Constraint lvl cm False t t'
    pure (todo' : todo'' : todos)
  _ -> empty

-- | Decompose a pair of spines into constraints.
decomposeSpine ::
  ConvMode ->
  Level ->
  Spine ->
  Spine ->
  [Constraint] ->
  UnifyM [Constraint]
decomposeSpine cm lvl lhs rhs todos = case (lhs, rhs) of
  (SNil, SNil) -> pure todos
  (SApp sp v, SApp sp' v') -> do
    let todo' = Constraint lvl cm False v v'
    decomposeSpine cm lvl sp sp' (todo' : todos)
  (SFst sp, SFst sp') -> decomposeSpine cm lvl sp sp' todos
  (SSnd sp, SSnd sp') -> decomposeSpine cm lvl sp sp' todos
  (SNatElim p s z sp, SNatElim p' s' z' sp') -> do
    let todo1 = Constraint lvl cm False p p'
        todo2 = Constraint lvl cm False s s'
        todo3 = Constraint lvl cm False z z'
    decomposeSpine cm lvl sp sp' (todo1 : todo2 : todo3 : todos)
  (SEqElim a x p r y sp, SEqElim a' x' p' r' y' sp') -> do
    let todo1 = Constraint lvl cm False a a'
        todo2 = Constraint lvl cm False x x'
        todo3 = Constraint lvl cm False p p'
        todo4 = Constraint lvl cm False r r'
        todo5 = Constraint lvl cm False y y'
    decomposeSpine cm lvl sp sp' (todo1 : todo2 : todo3 : todo4 : todo5 : todos)
  _ -> empty

-- | Decompose a pair of argument lists applied to metavariables into constraints.
decomposeMetaArgs ::
  ConvMode ->
  Level ->
  [Value] ->
  [Value] ->
  [Constraint] ->
  UnifyM [Constraint]
decomposeMetaArgs cm lvl lhs rhs todos = case (lhs, rhs) of
  ([], []) -> pure todos
  (v : vs, v' : vs') ->
    decomposeMetaArgs cm lvl vs vs' (Constraint lvl cm False v v' : todos)
  _ -> empty

-- | Guess a metavariable from how they are eliminated.
guessMeta :: Constraint -> MetaSubst -> [Constraint] -> UnifyM (MetaSubst, [Constraint])
guessMeta todo@(Constraint _ _ _ lhs rhs) subst todos = do
  tell 1
  (m, mabs) <- helper lhs <|> helper rhs
  let subst' = HM.insert m mabs subst
  pure (subst', todo : todos)
  where
    helper = \case
      VFlex m arity _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") arity
      VFlex m arity _ (SFst' {}) -> (m,) <$> imitation IPair arity
      VFlex m arity _ (SSnd' {}) -> (m,) <$> imitation IPair arity
      VFlex m arity _ (SNatElim' {}) -> (m,) <$> (imitation IZero arity <|> imitation ISuc arity)
      VFlex m arity _ (SEqElim' {}) -> (m,) <$> imitation IRefl arity
      _ -> empty

-- | Like @guessMeta@, but for type isomorphisms.
-- Π and Σ types act as "eliminators" when considering type isomorphisms!
guessMetaIso :: TopEnv -> Constraint -> MetaSubst -> [Constraint] -> UnifyM (MetaSubst, [Constraint])
guessMetaIso topEnv todo@(Constraint lvl _ iso lhs rhs) subst todos = do
  guard iso
  tell 1
  (m, mabs) <- helper lhs <|> helper rhs
  let subst' = HM.insert m mabs subst
  pure (subst', todo : todos)
  where
    helper = \case
      -- Σ x : M[t0, ..., tn]. B[x]
      VSigma _ (force topEnv subst -> VFlex m ar _ _) _ ->
        -- M[x0, ..., xn] ↦ Unit or
        -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
        (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
      -- (x : M[t0, ..., tn]) → B[x]
      VPi _ (force topEnv subst -> VFlex m ar _ _) _ ->
        -- M[x0, ..., xn] ↦ Unit or
        -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
        (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
      -- Σ x : A. M[t0, ..., tn]
      VSigma _ _ b
        | VFlex m ar _ _ <- force topEnv subst (b $ VVar lvl) ->
            -- M[x0, ..., xn] ↦ Unit
            (m,) <$> imitation IUnit ar
      -- (x0 : A0) ... (xn : An) → M[t0, ..., tn]
      VPi _ _ b
        | VFlex m ar _ _ <- go lvl b ->
            -- M[x0, ..., xn] ↦ Unit or
            -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
            (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
      _ -> empty

    go x f = case force topEnv subst (f $ VVar x) of
      VPi _ _ f' -> go (x + 1) f'
      t -> t

-- | Go through candidate solutions for flex-rigid constraints
flexRigid :: Constraint -> MetaSubst -> [Constraint] -> UnifyM (MetaSubst, [Constraint])
flexRigid todo@(Constraint _ _ _ lhs rhs) subst todos = do
  tell 1
  case (lhs, rhs) of
    (VFlex {}, VFlex {}) -> empty
    (VFlex m ar _ SNil, t') -> do
      mabs <- huetProjection t' ar
      let subst' = HM.insert m mabs subst
      pure (subst', todo : todos)
    (t, VFlex m' ar' _ SNil) -> do
      mabs <- huetProjection t ar'
      let subst' = HM.insert m' mabs subst
      pure (subst', todo : todos)
    _ -> empty

-- | Go through candidate solutions for flex-flex constraints
-- Iteration binding is not supported yet.
flexFlex :: Constraint -> MetaSubst -> [Constraint] -> UnifyM (MetaSubst, [Constraint])
flexFlex todo@(Constraint _ _ _ lhs rhs) subst todos = do
  tell 2
  case (lhs, rhs) of
    (VFlex m ar _ SNil, VFlex m' ar' _ SNil)
      | m == m' -> do
          guard (ar == ar')
          mabs <- elimination ar
          let subst' = HM.insert m mabs subst
          pure (subst', todo : todos)
      | otherwise -> do
          (mabs, mabs') <- identification ar ar'
          let subst' = HM.insert m mabs $ HM.insert m' mabs' subst
          pure (subst', todo : todos)
    _ -> empty

type ChosenDefs = HM.HashMap Name ModuleName

-- | Lazily unfold definitions.
unfold :: Constraint -> [Constraint] -> ChosenDefs -> UnifyM ([Constraint], ChosenDefs)
unfold (Constraint lvl cm iso lhs rhs) todos chosenDefs = do
  case (cm, lhs, rhs) of
    (Rigid, VTop n sp ts, VTop n' sp' ts')
      | n == n' ->
          (,chosenDefs) <$> decomposeSpine Flex lvl sp sp' todos
            <|> do
              tell 1
              -- assume modName = modName'
              ((modName, t), (_modName', t')) <- choose (zip ts ts')
              let chosenDefs' = HM.insert n modName chosenDefs
                  todo' = Constraint lvl Full iso t t'
              pure (todo' : todos, chosenDefs')
      | otherwise -> do
          tell 2
          (modName, t) <- choose ts
          (modName', t') <- choose ts'
          let chosenDefs' = HM.insert n modName $ HM.insert n' modName' chosenDefs
              todo' = Constraint lvl Rigid iso t t'
          pure (todo' : todos, chosenDefs')
    (Flex, VTop n sp _, VTop n' sp' _)
      | n == n' -> (,chosenDefs) <$> decomposeSpine Flex lvl sp sp' todos
      | otherwise -> empty
    (Full, VTop n _ ts, VTop n' _ ts')
      | n == n' -> do
          tell 1
          -- assume modName = modName'
          ((modName, t), (_modName', t')) <- choose (zip ts ts')
          let chosenDefs' = HM.insert n modName chosenDefs
              todo' = Constraint lvl Full iso t t'
          pure (todo' : todos, chosenDefs')
      | otherwise -> do
          tell 2
          (modName, t) <- choose ts
          (modName', t') <- choose ts'
          let chosenDefs' = HM.insert n modName $ HM.insert n' modName' chosenDefs
              todo' = Constraint lvl Rigid iso t t'
          pure (todo' : todos, chosenDefs')
    (Flex, VTop {}, _) -> empty
    (_, VTop n _ ts, t') -> do
      tell 1
      (modName, t) <- choose ts
      let todo' = Constraint lvl cm iso t t'
          chosenDefs' = HM.insert n modName chosenDefs
      pure (todo' : todos, chosenDefs')
    (Flex, _, VTop {}) -> empty
    (_, t, VTop n _ ts) -> do
      tell 1
      (modName, t') <- choose ts
      let todo' = Constraint lvl cm iso t t'
          chosenDefs' = HM.insert n modName chosenDefs
      pure (todo' : todos, chosenDefs')
    _ -> empty

printConstraint :: Constraint -> IO ()
printConstraint (Constraint lvl _ iso lhs rhs) = do
  let lhs' = quote lvl lhs
      rhs' = quote lvl rhs
      vars = map (\i -> Name $ "x" <> T.pack (show i)) [0 .. lvl - 1]
  putStrLn "--------------------------------------------------"
  putStrLn $
    concat
      [ if lvl > 0 then "∀ " ++ unwords (map show vars) ++ ". " else "",
        prettyTerm (reverse vars) 0 lhs' "",
        if iso then " ≅ " else " ≡ ",
        prettyTerm (reverse vars) 0 rhs' ""
      ]

-- | Unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
-- TODO: modulo permutations of Σ components
-- NOTE: Permutating Σ components would unblock reduction!
--       Take this into account?
--   e.g.)   (x : (y : (z : Type) * z) -> y.1)) * Type
--         ~ (x : Type) * (y : (z : Type) * z) -> y.1)
--         ~ (x : Type) * ((z : Type) * (y : z) -> z)
unify :: TopEnv -> ChosenDefs -> MetaSubst -> [Constraint] -> UnifyM (MetaSubst, [Constraint])
unify topEnv chosenDefs subst = \case
  [] -> pure (subst, [])
  (forceConstraint topEnv subst -> todo) : todos -> do
    -- lift $ printConstraint todo
    (subst', todos', chosenDefs') <-
      asum
        [ do
            subst' <- solve topEnv subst todo
            pure (subst', todos, chosenDefs),
          (subst,,chosenDefs) <$> decompose todo todos,
          do
            (subst', todos') <- guessMeta todo subst todos
            pure (subst', todos', chosenDefs),
          do
            (subst', todos') <- guessMetaIso topEnv todo subst todos
            pure (subst', todos', chosenDefs),
          do
            (subst', todos') <- flexRigid todo subst todos
            pure (subst', todos', chosenDefs),
          do
            (subst', todos') <- flexFlex todo subst todos
            pure (subst', todos', chosenDefs),
          do
            (todos', chosenDefs') <- unfold todo todos chosenDefs
            pure (subst, todos', chosenDefs')
        ]
    unify topEnv chosenDefs' subst' todos'

-- | Unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
unifyRaw' :: TopEnv -> Raw -> Raw -> UnifyM (MetaSubst, [Constraint])
unifyRaw' topEnv t t' = do
  let initTodo =
        Constraint 0 Rigid True (evaluateRaw topEnv HM.empty t) (evaluateRaw topEnv HM.empty t')
  unify topEnv HM.empty HM.empty [initTodo]

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
