module TypeSearch.UnificationModulo
  ( Modulo (..),

    -- * Normalisation
    normalise,
    normaliseRaw,

    -- * Unification (+ instantiation)
    unifyValue,
    unifyTerm,
    unifyRaw,
    unifyValueInst,
    unifyTermInst,
    unifyRawInst,
  )
where

import Control.Applicative
import Control.Exception (Exception, throwIO, try)
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Reader
import Data.HashMap.Lazy qualified as HM
import Data.HashSet qualified as HS
import Data.Text qualified as T
import System.IO
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Pretty
import TypeSearch.Raw
import TypeSearch.Term

--------------------------------------------------------------------------------
-- Normalisation into isomorphic types

-- | Σ associativity and currying.
normalise1 :: TopEnv -> MetaSubst -> Value -> Value
normalise1 topEnv subst = go
  where
    go t = case force topEnv subst t of
      VSigma x va vb -> goSigma x va (go . vb)
      VProd va vb -> goProd va (go vb)
      VPi x va vb -> goPi x va (go . vb)
      VArr va vb -> goArr va (go vb)
      v -> v

    goSigma x va vb = case force topEnv subst va of
      -- (x : (y : A) * B[y]) * C[x] ~> (x : A) * (y : B[x]) * C[(x, y)]
      VSigma y va' vb' -> goSigma x va' \ ~v -> goSigma y (vb' v) \ ~u -> vb (VPair v u)
      -- (x : A * B) * C[x] ~> (x : A) * (y : B) * C[(x, y)]
      VProd va' vb' -> goSigma x va' \ ~v -> goSigma "x" vb' \ ~u -> vb (VPair v u)
      -- DO NOT RECURSE on va'
      va' -> VSigma x va' vb

    goProd va vb = case force topEnv subst va of
      -- ((x : A) * B[x]) * C ~> (x : A) * B[x] * C
      VSigma y va' vb' -> goSigma y va' \ ~v -> goProd (vb' v) vb
      -- (A * B) * C ~> A * (B * C)
      VProd va' vb' -> goProd va' (goProd vb' vb)
      va' -> VProd (go va') vb

    goPi x va vb = case force topEnv subst va of
      -- (x : (y : A) * B[y]) -> C[x] ~> (x : A) (y : B[x]) -> C[(x, y)]
      VSigma y va' vb' -> goPi x va' \ ~v -> goPi y (vb' v) \ ~u -> vb (VPair v u)
      -- (x : A * B) -> C[x] ~> (x : A) (y : B) -> C[(x, y)]
      VProd va' vb' -> goPi x va' \ ~v -> goPi "x" vb' \ ~u -> vb (VPair v u)
      -- DO NOT RECURSE on va'
      va' -> VPi x va' vb

    goArr va vb = case force topEnv subst va of
      -- ((y : A) * B[y]) -> C ~> (y : A) -> B[y] -> C
      VSigma y va' vb' -> goPi y va' \ ~v -> goArr (vb' v) vb
      -- (A * B) -> C ~> A -> B -> C
      VProd va' vb' -> goArr va' (goArr vb' vb)
      va' -> VArr (go va') vb

-- | Unit elimination. Potentially unblocks normalise1.
normalise2 :: TopEnv -> MetaSubst -> Level -> Value -> Value
normalise2 topEnv subst = go
  where
    go lvl t = case force topEnv subst t of
      VSigma x va vb -> goSigma lvl x va (go (lvl + 1) . vb)
      VProd va vb -> goProd (go lvl va) (go lvl vb)
      VPi x va vb -> goPi x va (go (lvl + 1) . vb)
      VArr va vb -> goArr (go lvl va) (go lvl vb)
      v -> v

    goSigma lvl x va vb = case (force topEnv subst va, vb (VVar lvl)) of
      -- (x : Unit) * B[x] ~> B[tt]
      (VUnit, _) -> vb VTT
      -- (x : A) * Unit ~> A. Unblocks normalise1 on A.
      (va', VUnit) -> normalise topEnv subst lvl va'
      -- DO NOT RECURSE on va'
      (va', _) -> VSigma x va' vb

    goProd va vb = case (va, vb) of
      -- Unit * B ~> B
      (VUnit, vb') -> vb'
      -- A * Unit ~> A
      (va', VUnit) -> va'
      (va', vb') -> VProd va' vb'

    goPi x va vb = case force topEnv subst va of
      -- (x : Unit) -> B[x] ~> B[tt]
      VUnit -> vb VTT
      -- DO NOT RECURSE on va'
      va' -> VPi x va' vb

    goArr va vb = case va of
      -- Unit -> B ~> B
      VUnit -> vb
      va' -> VArr va' vb

-- | Normalise a value into an isomorphic one.
normalise :: TopEnv -> MetaSubst -> Level -> Value -> Value
normalise topEnv subst lvl t =
  normalise2 topEnv subst lvl $
    normalise1 topEnv subst t

-- | Normalise a raw term into an isomorphic one.
normaliseRaw :: Raw -> Term
normaliseRaw t =
  quote 0 $ normalise mempty mempty 0 $ evaluateRaw mempty mempty t

--------------------------------------------------------------------------------
-- Projections

data ImitationKind
  = ITop [ModuleName] Name
  | IType
  | IPi Name
  | IArr
  | IAbs Name
  | ISigma Name
  | IProd
  | IPair
  | IUnit
  | ITT
  | INat
  | IZero
  | ISuc
  | IEq
  | IRefl

-- | Create a meta abstraction of a given arity that imitates a particular rigid value.
imitation :: ImitationKind -> Int -> UnifyM MetaAbs
imitation kind arity =
  MetaAbs arity <$> imitation' kind params params'
  where
    -- [x0, ..., xn]
    params = map Var $ down (Index arity - 1) 0
    -- x. [x0, ..., xn, x]
    params' = map Var $ down (Index arity) 0

imitation' :: ImitationKind -> [Term] -> [Term] -> UnifyM Term
imitation' kind params params' = liftIO case kind of
  -- M[x0, ..., xn] ↦ n
  ITop ms n -> pure $ Top ms n
  -- M[x0, ..., xn] ↦ Type
  IType -> pure Type
  -- M[x0, ..., xn] ↦ (x : M1[x0, ..., xn]) -> M2[x0, ..., xn, x]
  IPi x -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Pi x (MetaApp m1 params) (MetaApp m2 params')
  -- M[x0, ..., xn] ↦ M1[x0, ..., xn] -> M2[x0, ..., xn]
  IArr -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Arr (MetaApp m1 params) (MetaApp m2 params)
  -- M[x0, ..., xn] ↦ λx. M'[x0, ..., xn, x]
  IAbs x -> do
    m' <- freshMeta
    pure $ Abs x (MetaApp m' params')
  -- M[x0, ..., xn] ↦ Σ x : M1[x0, ..., xn]. M2[x0, ..., xn, x]
  ISigma x -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Sigma x (MetaApp m1 params) (MetaApp m2 params')
  -- M[x0, ..., xn] ↦ M1[x0, ..., xn] * M2[x0, ..., xn]
  IProd -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Prod (MetaApp m1 params) (MetaApp m2 params)
  -- M[x0, ..., xn] ↦ (M1[x0, ..., xn], M2[x0, ..., xn])
  IPair -> do
    m1 <- freshMeta
    m2 <- freshMeta
    pure $ Pair (MetaApp m1 params) (MetaApp m2 params)
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

jpProjection' :: Int -> UnifyM Term
jpProjection' arity = Var <$> choose [0 .. Index arity - 1]

-- | Generate Huet-style projections for a given value.
huetProjection :: Value -> Int -> UnifyM MetaAbs
huetProjection t arity =
  MetaAbs arity <$> huetProjection' t arity params params'
  where
    params = map Var $ down (Index arity - 1) 0
    params' = map Var $ down (Index arity) 0

huetProjection' :: Value -> Int -> [Term] -> [Term] -> UnifyM Term
huetProjection' t arity params params' = go $ spine t
  where
    kind = case t of
      VRigid {} -> empty
      VFlex {} -> empty
      VTop n _ ts -> pure $ ITop (fst <$> ts) n
      VType -> pure IType
      VPi x _ _ -> pure $ IPi x
      VArr {} -> pure IArr
      VAbs x _ -> pure $ IAbs x
      VSigma x _ _ -> pure $ ISigma x
      VProd {} -> pure IProd
      VPair {} -> pure IPair
      VUnit -> pure IUnit
      VTT -> pure ITT
      VNat -> pure INat
      VZero -> pure IZero
      VSuc {} -> pure ISuc
      VEq {} -> pure IEq
      VRefl {} -> pure IRefl
      VStuck {} -> empty

    go sp = do
      ( case sp of
          SNil -> kind >>= \k -> imitation' k params params'
          SApp sp' _ -> do
            m <- liftIO freshMeta
            let u = MetaApp m params
            flip App u <$> go sp'
          SFst sp' -> Fst <$> go sp'
          SSnd sp' -> Snd <$> go sp'
          SNatElim _ _ _ sp' -> do
            m1 <- liftIO freshMeta
            m2 <- liftIO freshMeta
            m3 <- liftIO freshMeta
            let p = MetaApp m1 params
                s = MetaApp m2 params
                z = MetaApp m3 params
            n <- go sp'
            pure $ NatElim `App` p `App` s `App` z `App` n
          SEqElim _ _ _ _ _ sp' -> do
            m1 <- liftIO freshMeta
            m2 <- liftIO freshMeta
            m3 <- liftIO freshMeta
            m4 <- liftIO freshMeta
            m5 <- liftIO freshMeta
            let a = MetaApp m1 params
                x = MetaApp m2 params
                p = MetaApp m3 params
                r = MetaApp m4 params
                y = MetaApp m5 params
            eq <- go sp'
            pure $ EqElim `App` a `App` x `App` p `App` r `App` y `App` eq
        )
        <|> jpProjection' arity

--------------------------------------------------------------------------------
-- Solving constraints in solved form
-- Adopted from elaboration-zoo

data PartialRenaming = PRen
  { dom :: Level,
    cod :: Level,
    ren :: HM.HashMap Level Level
  }

liftPRen :: PartialRenaming -> PartialRenaming
liftPRen (PRen dom cod ren) = PRen (dom + 1) (cod + 1) (HM.insert cod dom ren)

invert :: TopEnv -> MetaSubst -> Level -> [Value] -> Maybe PartialRenaming
invert topEnv subst lvl args = do
  (dom, ren) <- go 0 HM.empty args
  pure $ PRen dom lvl ren
  where
    go dom ren = \case
      [] -> pure (dom, ren)
      t : ts -> case force topEnv subst t of
        VVar l
          | not (HM.member l ren) -> go (dom + 1) (HM.insert l dom ren) ts
        _ -> empty

rename :: TopEnv -> MetaSubst -> Meta -> PartialRenaming -> Value -> Maybe Term
rename topEnv metaSubst m = go
  where
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
      VPi x a b -> Pi x <$> go pren a <*> goScope pren b
      VArr a b -> Arr <$> go pren a <*> go pren b
      VAbs x f -> Abs x <$> goScope pren f
      VSigma x a b -> Sigma x <$> go pren a <*> goScope pren b
      VProd a b -> Prod <$> go pren a <*> go pren b
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
      VStuck {} -> Nothing

    goScope pren f = go (liftPRen pren) (f $ VVar pren.cod)

    goSpine pren = foldM (goElim pren)

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

solve :: TopEnv -> MetaSubst -> Level -> Meta -> Int -> [Value] -> Value -> Maybe MetaAbs
solve topEnv subst lvl m ar ts t = do
  pren <- invert topEnv subst lvl ts
  body <- rename topEnv subst m pren t
  let mabs = MetaAbs ar body
  pure mabs

--------------------------------------------------------------------------------
-- Swapping domains of pi types and components of sigma types

-- | Compute the free variable set of a value.
freeVarSet :: TopEnv -> MetaSubst -> Level -> Value -> HS.HashSet Level
freeVarSet topEnv subst = go
  where
    go lvl t = case force topEnv subst t of
      VRigid l sp -> HS.insert l (goSpine lvl sp)
      VFlex _ _ ts sp -> foldMap (go lvl) ts <> goSpine lvl sp
      VTop _ sp _ -> goSpine lvl sp
      VType -> HS.empty
      VPi _ a b -> go lvl a <> goScope lvl b
      VArr a b -> go lvl a <> go lvl b
      VAbs _ b -> goScope lvl b
      VSigma _ a b -> go lvl a <> goScope lvl b
      VProd a b -> go lvl a <> go lvl b
      VPair a b -> go lvl a <> go lvl b
      VUnit -> HS.empty
      VTT -> HS.empty
      VNat -> HS.empty
      VZero -> HS.empty
      VSuc u -> go lvl u
      VEq a u v -> go lvl a <> go lvl u <> go lvl v
      VRefl a u -> go lvl a <> go lvl u
      VStuck {} -> HS.empty

    goScope lvl f = HS.delete lvl $ go (lvl + 1) (f $ VVar lvl)

    goSpine lvl = foldMap (goElim lvl)

    goElim lvl = \case
      EApp t -> go lvl t
      EFst -> HS.empty
      ESnd -> HS.empty
      ENatElim p s z -> go lvl p <> go lvl s <> go lvl z
      EEqElim a x p r y -> go lvl a <> go lvl x <> go lvl p <> go lvl r <> go lvl y

isPi :: Value -> Bool
isPi = \case
  VPi {} -> True
  VArr {} -> True
  _ -> False

-- | From a pi type, generate the same type but with single domain is hoisted to the top respecting dependencies.
-- Example 1:
--   * Input:   (A B : Type) -> A -> B -> A
--   * Output: [(B A : Type) -> A -> B -> A]
-- Example 2:
--   * Input:    (A -> B -> B) -> B -> List A -> B  (where A and B are free)
--   * Output: [ B -> (A -> B -> B) -> List A -> B,
--               List A -> (A -> B -> B) -> B -> B ]
possibleDomainHoists :: TopEnv -> MetaSubst -> Level -> Value -> [Value]
possibleDomainHoists topEnv subst lvl t = do
  guard $ isPi t
  go HS.empty 0 lvl t
  where
    go lvls i lvl' u = case force topEnv subst u of
      VPi x a b
        | hoistable a ->
            VPi x a (\ ~v -> deletePi i v t)
              : go (HS.insert lvl' lvls) (i + 1) (lvl' + 1) (b $ VVar lvl')
        | otherwise ->
            go (HS.insert lvl' lvls) (i + 1) (lvl' + 1) (b $ VVar lvl')
      VArr a b
        | hoistable a ->
            VArr a (deleteArr i t)
              : go lvls (i + 1) lvl' b
        | otherwise ->
            go lvls (i + 1) lvl' b
      _ -> []
      where
        hoistable a =
          HS.null lvls
            || HS.null (HS.intersection (freeVarSet topEnv subst lvl' a) lvls)

    deleteArr i u = case (i, force topEnv subst u) of
      (0 :: Int, VArr _ b) -> b
      (0, _) -> error "deleteArr: not an arrow"
      (_, VPi x a b) -> VPi x a (deleteArr (i - 1) . b)
      (_, VArr a b) -> VArr a (deleteArr (i - 1) b)
      _ -> error "deleteArr: not an arrow"

    deletePi i u v = case (i, force topEnv subst v) of
      (0 :: Int, VPi _ _ b) -> b u
      (0, _) -> error "deletePi: not a pi"
      (_, VPi x a b) -> VPi x a (deletePi (i - 1) u . b)
      (_, VArr a b) -> VArr a (deletePi (i - 1) u b)
      _ -> error "deletePi: not a pi"

isSigma :: Value -> Bool
isSigma = \case
  VSigma {} -> True
  VProd {} -> True
  _ -> False

-- | Like @possibleDomainHoists@, generate sigma types with single component is hoisted to the top respecting dependencies.
possibleComponentHoists :: TopEnv -> MetaSubst -> Level -> Value -> [Value]
possibleComponentHoists topEnv subst lvl t = do
  guard $ isSigma t
  go HS.empty 0 lvl t
  where
    go lvls i lvl' u = case force topEnv subst u of
      VSigma x a b
        | hoistable a ->
            VSigma x a (\ ~v -> deleteSigma i v t)
              : go (HS.insert lvl' lvls) (i + 1) (lvl' + 1) (b $ VVar lvl')
        | otherwise ->
            go (HS.insert lvl' lvls) (i + 1) (lvl' + 1) (b $ VVar lvl')
      VProd a b
        | hoistable a ->
            VProd a (deleteProd i t)
              : go lvls (i + 1) lvl' b
        | otherwise ->
            go lvls (i + 1) lvl' b
      a
        | hoistable a -> [VProd a (deleteProd i t)]
        | otherwise -> []
      where
        hoistable a =
          HS.null lvls
            || HS.null (HS.intersection (freeVarSet topEnv subst lvl' a) lvls)

    deleteProd i u = case (i, force topEnv subst u) of
      (0 :: Int, VProd _ b) -> b
      (0, _) -> error "deleteProd: not a prod"
      (1, VProd a b) -> case force topEnv subst b of
        b'@VProd {} -> VProd a (deleteProd (i - 1) b')
        _ -> a
      (_, VSigma x a b) -> VSigma x a (deleteProd (i - 1) . b)
      (_, VProd a b) -> VProd a (deleteProd (i - 1) b)
      _ -> error "deleteProd: not a prod"

    deleteSigma i u v = case (i, force topEnv subst v) of
      (0 :: Int, VSigma _ _ b) -> b u
      (0, _) -> error "deleteSigma: not a sigma"
      (_, VSigma x a b) -> VSigma x a (deleteSigma (i - 1) u . b)
      (_, VProd a b) -> VProd a (deleteSigma (i - 1) u b)
      _ -> error "deleteSigma: not a sigma"

--------------------------------------------------------------------------------
-- Unification procedure modulo βη-equivalence and type isomorphisms related to Π and Σ:
--   - (x : (y : A) * B[y]) * C[x]  ~ (x : A) * (y : B[x]) * C[(x, y)]
--   - (x : (y : A) * B[y]) -> C[x] ~ (x : A) -> (y : B[x]) -> C[(x, y)]
--   - (x : A) * B                  ~ (x : B) * A
--   - (x : A) (y : B) -> C[x, y]   ~ (y : B) (x : A) -> C[x, y]
--   - (x : A) * Unit               ~ A
--   - (x : Unit) * A[x]            ~ A[tt]
--   - (x : Unit) -> A[x]           ~ A[tt]
-- Constraints are solved from left to right (static unification).

unifyLog :: (Handle -> IO ()) -> UnifyM ()
unifyLog f = when True do
  h <- ask
  liftIO $ f h

-- | Constraints: ∀ x0, ..., x{n - 1}. t1 ≟ t2
data Constraint = Constraint
  { level :: Level, -- n
    convMode :: ConvMode,
    modulo :: Modulo,
    lhs, rhs :: Value -- t1, t2
  }

data Modulo = DefEq | Iso
  deriving stock (Eq, Show)

-- | Monad for unification.
-- @HeapT@ is like list transformer with priority.
-- @IO@ is for generating fresh metavariables.
type UnifyM = ReaderT Handle (LogicT IO)

-- | Used for controlling definition unfolding.
data ConvMode
  = Rigid
  | Flex
  | Full
  deriving stock (Eq, Show)

data SharedCtx = SharedCtx
  { topEnv :: TopEnv,
    metaSubst :: MetaSubst,
    chosenDefs :: ChosenDefs,
    numGuessMetaIso :: Int
  }

-- | For consistently unfolding definitions.
-- Multiple modules possibly export definitions with the same name.
-- In order to avoid unfolding definitions from different modules during unification, we need to keep track of which module has chosen a definition for a given name.
type ChosenDefs = HM.HashMap Name ModuleName

-- | Force a constraint. If the constraint is to be solved up to type isomorphisms, terms are normalised.
forceConstraint :: SharedCtx -> Constraint -> Constraint
forceConstraint ctx constraint =
  if constraint.modulo == Iso
    then
      constraint
        { lhs = normalise ctx.topEnv ctx.metaSubst constraint.level constraint.lhs,
          rhs = normalise ctx.topEnv ctx.metaSubst constraint.level constraint.rhs
        }
    else
      constraint
        { lhs = force ctx.topEnv ctx.metaSubst constraint.lhs,
          rhs = force ctx.topEnv ctx.metaSubst constraint.rhs
        }

force' :: SharedCtx -> Value -> Value
force' ctx = force ctx.topEnv ctx.metaSubst

addMetaSubst :: Meta -> MetaAbs -> SharedCtx -> SharedCtx
addMetaSubst m mabs ctx = ctx {metaSubst = HM.insert m mabs ctx.metaSubst}

addChosenDef :: Name -> ModuleName -> SharedCtx -> SharedCtx
addChosenDef name m ctx = ctx {chosenDefs = HM.insert name m ctx.chosenDefs}

incrNumGuessMetaIso :: SharedCtx -> SharedCtx
incrNumGuessMetaIso ctx = ctx {numGuessMetaIso = ctx.numGuessMetaIso + 1}

-- | Decompose a constraint into a set of smaller constraints.
decompose :: SharedCtx -> Constraint -> [Constraint] -> UnifyM [Constraint]
decompose ctx (Constraint lvl cm iso lhs rhs) todos = do
  case (lhs, rhs) of
    (VRigid x sp, VRigid x' sp')
      | x == x' -> decomposeSpine cm lvl sp sp' todos
      | otherwise -> empty
    (VRigid x (SApp sp t), VFlex m' ar' ts' (SApp sp' t')) -> do
      let todo1 = Constraint lvl cm DefEq (VRigid x sp) (VFlex m' ar' ts' sp')
          todo2 = Constraint lvl cm DefEq t t'
      pure (todo1 : todo2 : todos)
    (VRigid x (SFst sp), VFlex m' ar' ts' (SFst sp')) -> do
      let todo1 = Constraint lvl cm DefEq (VRigid x sp) (VFlex m' ar' ts' sp')
      pure (todo1 : todos)
    (VRigid x (SSnd sp), VFlex m' ar' ts' (SSnd sp')) -> do
      let todo1 = Constraint lvl cm DefEq (VRigid x sp) (VFlex m' ar' ts' sp')
      pure (todo1 : todos)
    -- FIXME: avoid recomputation
    (VRigid x (SApp sp t), VTop n (SApp sp' t') _) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (VRigid x sp) (vappSpine def sp')
          todo2 = Constraint lvl cm DefEq t t'
      pure (todo1 : todo2 : todos)
    (VRigid x (SFst sp), VTop n (SFst sp') _) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (VRigid x sp) (vappSpine def sp')
      pure (todo1 : todos)
    (VRigid x (SSnd sp), VTop n (SSnd sp') _) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (VRigid x sp) (vappSpine def sp')
      pure (todo1 : todos)
    (VFlex m ar ts (SApp sp t), VRigid x' (SApp sp' t')) -> do
      let todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (VRigid x' sp')
          todo2 = Constraint lvl cm DefEq t t'
      pure (todo1 : todo2 : todos)
    (VFlex m ar ts (SFst sp), VRigid x' (SFst sp')) -> do
      let todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (VRigid x' sp')
      pure (todo1 : todos)
    (VFlex m ar ts (SSnd sp), VRigid x' (SSnd sp')) -> do
      let todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (VRigid x' sp')
      pure (todo1 : todos)
    (VFlex m ar ts (SApp sp t), VFlex m' ar' ts' (SApp sp' t')) -> do
      let todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (VFlex m' ar' ts' sp')
          todo2 = Constraint lvl cm DefEq t t'
      pure (todo1 : todo2 : todos)
    (VFlex m ar ts (SFst sp), VFlex m' ar' ts' (SFst sp')) -> do
      let todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (VFlex m' ar' ts' sp')
      pure (todo1 : todos)
    (VFlex m ar ts (SSnd sp), VFlex m' ar' ts' (SSnd sp')) -> do
      let todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (VFlex m' ar' ts' sp')
      pure (todo1 : todos)
    (VFlex m _ ts SNil, VFlex m' _ ts' SNil)
      | m == m' -> decomposeMetaArgs cm lvl (reverse ts) (reverse ts') todos
    (VFlex m ar ts (SApp sp t), VTop n (SApp sp' t') _) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (vappSpine def sp')
          todo2 = Constraint lvl cm DefEq t t'
      pure (todo1 : todo2 : todos)
    (VFlex m ar ts (SFst sp), VTop n (SFst sp') _) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (vappSpine def sp')
      pure (todo1 : todos)
    (VFlex m ar ts (SSnd sp), VTop n (SSnd sp') _) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (VFlex m ar ts sp) (vappSpine def sp')
      pure (todo1 : todos)
    (VTop n (SApp sp t) _, VRigid x' (SApp sp' t')) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (vappSpine def sp) (VRigid x' sp')
          todo2 = Constraint lvl cm DefEq t t'
      pure (todo1 : todo2 : todos)
    (VTop n (SFst sp) _, VRigid x' (SFst sp')) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (vappSpine def sp) (VRigid x' sp')
      pure (todo1 : todos)
    (VTop n (SSnd sp) _, VRigid x' (SSnd sp')) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (vappSpine def sp) (VRigid x' sp')
      pure (todo1 : todos)
    (VTop n (SApp sp t) _, VFlex m' ar' ts' (SApp sp' t')) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (vappSpine def sp) (VFlex m' ar' ts' sp')
          todo2 = Constraint lvl cm DefEq t t'
      pure (todo1 : todo2 : todos)
    (VTop n (SFst sp) _, VFlex m' ar' ts' (SFst sp')) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (vappSpine def sp) (VFlex m' ar' ts' sp')
      pure (todo1 : todos)
    (VTop n (SSnd sp) _, VFlex m' ar' ts' (SSnd sp')) -> do
      let def = evaluateRaw ctx.topEnv mempty (RVar (Unqual n))
          todo1 = Constraint lvl cm DefEq (vappSpine def sp) (VFlex m' ar' ts' sp')
      pure (todo1 : todos)
    (VType, VType) -> pure todos
    (VPi _ a b, VPi _ a' b') -> do
      let todo1 = Constraint lvl cm DefEq a a'
          todo2 = Constraint (lvl + 1) cm iso (b $ VVar lvl) (b' $ VVar lvl)
      pure (todo1 : todo2 : todos)
    (VPi _ a b, VArr a' b') -> do
      let todo1 = Constraint lvl cm iso a a'
          todo2 = Constraint (lvl + 1) cm iso (b $ VVar lvl) b'
      pure (todo1 : todo2 : todos)
    (VArr a b, VPi _ a' b') -> do
      let todo1 = Constraint lvl cm iso a a'
          todo2 = Constraint (lvl + 1) cm iso b (b' $ VVar lvl)
      pure (todo1 : todo2 : todos)
    (VArr a b, VArr a' b') -> do
      let todo1 = Constraint lvl cm iso a a'
          todo2 = Constraint lvl cm iso b b'
      pure (todo1 : todo2 : todos)
    (VAbs _ f, VAbs _ f') -> do
      let todo1 = Constraint (lvl + 1) cm DefEq (f $ VVar lvl) (f' $ VVar lvl)
      pure (todo1 : todos)
    -- η-expansion
    (VAbs _ f, t') -> do
      let todo1 = Constraint (lvl + 1) cm DefEq (f $ VVar lvl) (vapp t' $ VVar lvl)
      pure (todo1 : todos)
    (t, VAbs _ f) -> do
      let todo1 = Constraint (lvl + 1) cm DefEq (vapp t $ VVar lvl) (f $ VVar lvl)
      pure (todo1 : todos)
    (VSigma _ a b, VSigma _ a' b') -> do
      let todo1 = Constraint lvl cm DefEq a a'
          todo2 = Constraint (lvl + 1) cm iso (b $ VVar lvl) (b' $ VVar lvl)
      pure (todo1 : todo2 : todos)
    (VSigma _ a b, VProd a' b') -> do
      let todo1 = Constraint lvl cm iso a a'
          todo2 = Constraint (lvl + 1) cm iso (b $ VVar lvl) b'
      pure (todo1 : todo2 : todos)
    (VProd a b, VSigma _ a' b') -> do
      let todo1 = Constraint lvl cm iso a a'
          todo2 = Constraint (lvl + 1) cm iso b (b' $ VVar lvl)
      pure (todo1 : todo2 : todos)
    (VProd a b, VProd a' b') -> do
      let todo1 = Constraint lvl cm iso a a'
          todo2 = Constraint lvl cm iso b b'
      pure (todo1 : todo2 : todos)
    (VPair t u, VPair t' u') -> do
      let todo1 = Constraint lvl cm DefEq t t'
          todo2 = Constraint lvl cm DefEq u u'
      pure (todo1 : todo2 : todos)
    -- η-expansion
    (VPair t u, t') -> do
      let todo1 = Constraint lvl cm DefEq t (vfst t')
          todo2 = Constraint lvl cm DefEq u (vsnd t')
      pure (todo1 : todo2 : todos)
    (t, VPair t' u') -> do
      let todo1 = Constraint lvl cm DefEq (vfst t) t'
          todo2 = Constraint lvl cm DefEq (vsnd t) u'
      pure (todo1 : todo2 : todos)
    (VUnit, VUnit) -> pure todos
    (VTT, VTT) -> pure todos
    (VNat, VNat) -> pure todos
    (VZero, VZero) -> pure todos
    (VSuc t, VSuc t') -> do
      let todo1 = Constraint lvl cm DefEq t t'
      pure (todo1 : todos)
    (VEq a t u, VEq a' t' u') -> do
      let todo1 = Constraint lvl cm DefEq a a'
          todo2 = Constraint lvl cm DefEq t t'
          todo3 = Constraint lvl cm DefEq u u'
      pure (todo1 : todo2 : todo3 : todos)
    (VRefl a t, VRefl a' t') -> do
      let todo1 = Constraint lvl cm DefEq a a'
          todo2 = Constraint lvl cm DefEq t t'
      pure (todo1 : todo2 : todos)
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
    let todo1 = Constraint lvl cm DefEq v v'
    decomposeSpine cm lvl sp sp' (todo1 : todos)
  (SFst sp, SFst sp') -> decomposeSpine cm lvl sp sp' todos
  (SSnd sp, SSnd sp') -> decomposeSpine cm lvl sp sp' todos
  (SNatElim p s z sp, SNatElim p' s' z' sp') -> do
    let todo1 = Constraint lvl cm DefEq p p'
        todo2 = Constraint lvl cm DefEq s s'
        todo3 = Constraint lvl cm DefEq z z'
    decomposeSpine cm lvl sp sp' (todo1 : todo2 : todo3 : todos)
  (SEqElim a x p r y sp, SEqElim a' x' p' r' y' sp') -> do
    let todo1 = Constraint lvl cm DefEq a a'
        todo2 = Constraint lvl cm DefEq x x'
        todo3 = Constraint lvl cm DefEq p p'
        todo4 = Constraint lvl cm DefEq r r'
        todo5 = Constraint lvl cm DefEq y y'
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
    decomposeMetaArgs cm lvl vs vs' (Constraint lvl cm DefEq v v' : todos)
  _ -> empty

-- | Like @decompose@, but function domains, sigma components, or equality sides are permuted.
decomposeIso :: SharedCtx -> Constraint -> [Constraint] -> UnifyM [Constraint]
decomposeIso ctx (Constraint lvl cm iso lhs rhs) todos = do
  guard (iso == Iso)
  case (lhs, rhs) of
    -- Hoist one of the domains respecting dependencies
    (isPi -> True, isPi -> True) -> do
      lhs' <- choose $ tail $ possibleDomainHoists ctx.topEnv ctx.metaSubst lvl lhs
      let todo1 = Constraint lvl cm iso lhs' rhs
      decompose ctx todo1 todos
    -- Hoist one of the components respecting dependencies
    (isSigma -> True, isSigma -> True) -> do
      lhs' <- choose $ tail $ possibleComponentHoists ctx.topEnv ctx.metaSubst lvl lhs
      let todo1 = Constraint lvl cm iso lhs' rhs
      decompose ctx todo1 todos
    -- swap the sides of the equality
    (VEq a t u, VEq {}) -> do
      let todo1 = Constraint lvl cm iso (VEq a u t) rhs
      decompose ctx todo1 todos
    _ -> empty

-- | Guess a metavariable from how they are eliminated.
guessMeta :: SharedCtx -> Constraint -> [Constraint] -> UnifyM (SharedCtx, [Constraint])
guessMeta ctx todo@(Constraint _ _ _ lhs rhs) todos = do
  (m, mabs) <- guessMeta' lhs <|> guessMeta' rhs
  let ctx' = addMetaSubst m mabs ctx
  pure (ctx', todo : todos)
  where
    guessMeta' = \case
      VFlex m arity _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") arity
      VFlex m arity _ (SFst' {}) -> (m,) <$> imitation IPair arity
      VFlex m arity _ (SSnd' {}) -> (m,) <$> imitation IPair arity
      _ -> empty

data TooManyGuessMetaIso = TooManyGuessMetaIso
  deriving stock (Show)

instance Exception TooManyGuessMetaIso

-- | Like @guessMeta@, but for type isomorphisms.
-- Π and Σ types act as "eliminators" when considering type isomorphisms!
guessMetaIso :: SharedCtx -> Constraint -> [Constraint] -> UnifyM (SharedCtx, [Constraint])
guessMetaIso ctx todo@(Constraint lvl _ iso lhs rhs) todos = do
  guard $ iso == Iso
  when (ctx.numGuessMetaIso >= 3) do
    liftIO $ throwIO TooManyGuessMetaIso
  (m, mabs) <- guessMetaIso' lhs <|> guessMetaIso' rhs
  let ctx' = incrNumGuessMetaIso $ addMetaSubst m mabs ctx
  pure (ctx', todo : todos)
  where
    guessMetaIso' = \case
      VSigma _ a b ->
        asum
          [ -- Σ x : M[t0, ..., tn]. B[x]
            case force' ctx a of
              -- M[x0, ..., xn] ↦ Unit or
              -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
              VFlex m ar _ _ -> (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
              _ -> empty,
            -- Σ x : A. M[t0, ..., tn]
            case force' ctx (b $ VVar lvl) of
              -- M[x0, ..., xn] ↦ Unit or
              -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
              VFlex m ar _ _ -> (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
              _ -> empty
          ]
      VProd a b ->
        asum
          [ -- M[t0, ..., tn] * B
            case force' ctx a of
              -- M[x0, ..., xn] ↦ Unit or
              -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
              VFlex m ar _ _ -> (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
              _ -> empty,
            -- A * M[t0, ..., tn]
            case force' ctx b of
              -- M[x0, ..., xn] ↦ Unit or
              -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
              VFlex m ar _ _ -> (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
              _ -> empty
          ]
      VPi _ a b ->
        asum
          [ -- (x : M[t0, ..., tn]) → B[x]
            case force' ctx a of
              -- M[x0, ..., xn] ↦ Unit or
              -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
              VFlex m ar _ _ -> (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
              _ -> empty,
            -- (x : A) -> M[t0, ..., tn]
            case force' ctx (b $ VVar lvl) of
              -- M[x0, ..., xn] ↦ (y : M1[x0, ..., xn]). M2[x0, ..., xn, y]
              VFlex m ar _ _ -> (m,) <$> imitation (IPi "x") ar
              _ -> empty
          ]
      VArr a b ->
        asum
          [ -- M[t0, ..., tn] → B
            case force' ctx a of
              -- M[x0, ..., xn] ↦ Unit or
              -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
              VFlex m ar _ _ -> (m,) <$> (imitation IUnit ar <|> imitation (ISigma "x") ar)
              _ -> empty,
            -- A → M[t0, ..., tn]
            case force' ctx b of
              -- M[x0, ..., xn] ↦ (y : M1[x0, ..., xn]). M2[x0, ..., xn, y]
              VFlex m ar _ _ -> (m,) <$> imitation (IPi "x") ar
              _ -> empty
          ]
      _ -> empty

-- | Go through candidate solutions for flex-rigid constraints
flexRigid :: SharedCtx -> Constraint -> [Constraint] -> UnifyM (SharedCtx, [Constraint])
flexRigid ctx todo@(Constraint _ _ _ lhs rhs) todos = do
  case (lhs, rhs) of
    (VFlex {}, VFlex {}) -> empty
    (VFlex m ar _ SNil, t') -> do
      mabs <- huetProjection t' ar
      let ctx' = addMetaSubst m mabs ctx
      pure (ctx', todo : todos)
    (t, VFlex m' ar' _ SNil) -> do
      mabs <- huetProjection t ar'
      let ctx' = addMetaSubst m' mabs ctx
      pure (ctx', todo : todos)
    _ -> empty

-- | Lazily unfold definitions.
unfold :: SharedCtx -> Constraint -> [Constraint] -> UnifyM (SharedCtx, [Constraint])
unfold ctx (Constraint lvl cm iso lhs rhs) todos = do
  case (cm, lhs, rhs) of
    (Rigid, VTop n sp ts, VTop n' sp' ts')
      | n == n' ->
          (ctx,) <$> decomposeSpine Flex lvl sp sp' todos
            <|> do
              -- unifyLog \h -> hPutStrLn h $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
              -- assume modName = modName'
              ((modName, t), (_modName', t')) <- choose (zip ts ts')
              let ctx' = addChosenDef n modName ctx
                  todo1 = Constraint lvl Full iso t t'
              pure (ctx', todo1 : todos)
      | otherwise -> do
          -- unifyLog \h -> hPutStrLn h $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
          (modName, t) <- choose ts
          -- unifyLog \h -> hPutStrLn h $ "unfold: " ++ show n' ++ " (" ++ show (length ts') ++ " alternatives)"
          (modName', t') <- choose ts'
          let ctx' = addChosenDef n modName $ addChosenDef n' modName' ctx
              todo1 = Constraint lvl Rigid iso t t'
          pure (ctx', todo1 : todos)
    (Flex, VTop n sp _, VTop n' sp' _)
      | n == n' -> (ctx,) <$> decomposeSpine Flex lvl sp sp' todos
      | otherwise -> empty
    (Full, VTop n _ ts, VTop n' _ ts')
      | n == n' -> do
          -- assume modName = modName'
          -- unifyLog \h -> hPutStrLn h $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
          ((modName, t), (_modName', t')) <- choose (zip ts ts')
          let ctx' = addChosenDef n modName ctx
              todo1 = Constraint lvl Full iso t t'
          pure (ctx', todo1 : todos)
      | otherwise -> do
          -- unifyLog \h -> hPutStrLn h $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
          (modName, t) <- choose ts
          -- unifyLog \h -> hPutStrLn h $ "unfold: " ++ show n' ++ " (" ++ show (length ts') ++ " alternatives)"
          (modName', t') <- choose ts'
          let ctx' = addChosenDef n modName $ addChosenDef n' modName' ctx
              todo1 = Constraint lvl Rigid iso t t'
          pure (ctx', todo1 : todos)
    (Flex, VTop {}, _) -> empty
    (_, VTop n _ ts, t') -> do
      -- unifyLog \h -> hPutStrLn h $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
      (modName, t) <- choose ts
      let todo1 = Constraint lvl cm iso t t'
          ctx' = addChosenDef n modName ctx
      pure (ctx', todo1 : todos)
    (Flex, _, VTop {}) -> empty
    (_, t, VTop n _ ts) -> do
      -- unifyLog \h -> hPutStrLn h $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
      (modName, t') <- choose ts
      let todo1 = Constraint lvl cm iso t t'
          ctx' = addChosenDef n modName ctx
      pure (ctx', todo1 : todos)
    _ -> empty

data ChooseResult
  = Done [Constraint]
  | Solved Meta MetaAbs [Constraint]
  | Next Constraint [Constraint]
  | Stuck

chooseConstraint :: SharedCtx -> [Constraint] -> ChooseResult
chooseConstraint ctx = go [] []
  where
    go fr ff = \case
      [] -> case fr of
        [] -> Done ff
        todo : todos -> Next todo (todos ++ ff)
      (forceConstraint ctx -> todo) : todos ->
        case todo of
          Constraint _ _ _ (VStuck {}) _ -> Stuck
          Constraint _ _ _ _ (VStuck {}) -> Stuck
          Constraint lvl _ _ (VFlex m ar ts SNil) t'
            | Just mabs <- solve ctx.topEnv ctx.metaSubst lvl m ar ts t' ->
                Solved m mabs (todos ++ fr ++ ff)
          Constraint lvl _ _ t (VFlex m' ar' ts' SNil)
            | Just mabs <- solve ctx.topEnv ctx.metaSubst lvl m' ar' ts' t ->
                Solved m' mabs (todos ++ fr ++ ff)
          Constraint _ _ _ (VFlex m _ _ SNil) (VFlex m' _ _ SNil)
            | m == m' -> Next todo (todos ++ fr ++ ff)
            | otherwise -> go fr (todo : ff) todos
          Constraint _ _ _ (VFlex _ _ _ SNil) _ -> go (todo : fr) ff todos
          Constraint _ _ _ _ (VFlex _ _ _ SNil) -> go (todo : fr) ff todos
          _ -> Next todo (todos ++ fr ++ ff)

-- | Unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
unify :: SharedCtx -> [Constraint] -> UnifyM (MetaSubst, [Constraint])
unify ctx todos = do
  unifyLog \h -> do
    -- threadDelay 500000
    hPutStrLn h "--------------------------------------------------"
    hPutStrLn h $ prettyMetaSubst ctx.metaSubst ""
    mapM_ (\todo' -> hPutStrLn h $ prettyConstraint todo' "") todos
  case chooseConstraint ctx todos of
    Stuck -> empty
    Done ff -> pure (ctx.metaSubst, ff)
    Solved m mabs todos' -> unify (addMetaSubst m mabs ctx) todos'
    Next todo todos' ->
      do
        do
          asum
            [ (ctx,) <$> decompose ctx todo todos',
              (ctx,) <$> decomposeIso ctx todo todos',
              guessMeta ctx todo todos',
              unfold ctx todo todos',
              flexRigid ctx todo todos'
            ]
          >>= uncurry unify
        <|> catchEmpty @TooManyGuessMetaIso (guessMetaIso ctx todo todos' >>= uncurry unify)

catchEmpty :: forall e a. (Exception e) => UnifyM a -> UnifyM a
catchEmpty m = ReaderT \h -> LogicT \cons nil ->
  try @e (runLogicT (runReaderT m h) cons nil) >>= either (const nil) pure

prettyConstraint :: Constraint -> ShowS
prettyConstraint (Constraint lvl _ iso lhs rhs) =
  ( if lvl > 0
      then
        showString "∀ "
          . punctuate (showString " ") (map shows $ reverse vars)
          . showString ". "
      else id
  )
    . prettyTerm vars 0 lhs'
    . showString eq
    . prettyTerm vars 0 rhs'
  where
    lhs' = quote lvl lhs
    rhs' = quote lvl rhs
    vars = map (\i -> Name $ "x" <> T.pack (show i)) $ down (lvl - 1) 0
    eq = case iso of
      DefEq -> " ≡ "
      Iso -> " ≅ "

--------------------------------------------------------------------------------
-- Zonking (unfold all metavariables in terms)

zonkMetaAbs :: Modulo -> TopEnv -> MetaSubst -> MetaAbs -> MetaAbs
zonkMetaAbs modulo topEnv subst mabs = mabs {body = body'}
  where
    vbody =
      (if modulo == Iso then normalise topEnv subst 0 else id) $
        deepForce topEnv subst $
          vmetaApp topEnv mabs [VVar l | l <- [0 .. Level mabs.arity - 1]]
    body' = quote (Level mabs.arity) vbody

zonkMetaSubst :: Modulo -> TopEnv -> MetaSubst -> MetaSubst
zonkMetaSubst modulo topEnv subst = fmap (zonkMetaAbs modulo topEnv subst) subst

--------------------------------------------------------------------------------
-- Instantiation

-- | Instantiate the second argument inside the top-level pis of the first argument.
-- Example:
--    instantiateInPisOf ((A : Type) -> A -> A -> A) ((A B : Type) -> A -> B -> A)
--  = (A : Type) -> ?M1[A] -> ?M2[A] -> ?M1[A]
--        where M1 and M2 are fresh metavariables generated for A and B respectively.
instantiateInPisOf :: Value -> Value -> UnifyM Value
instantiateInPisOf t u = do
  let lvl = numTopPis t
  u' <- instantiateTopPis lvl u
  pure $ go u' t
  where
    go v = \case
      VPi x a b -> VPi x a (go v . b)
      VArr _ b -> go v b
      _ -> v

-- | Count the number of top-level pis.
numTopPis :: Value -> Level
numTopPis = go 0
  where
    go lvl = \case
      VPi _ _ b -> go (lvl + 1) (b (VVar lvl))
      VArr _ b -> go lvl b
      _ -> lvl

-- | Instantiate top-level pis. Unfold definitions.
instantiateTopPis :: Level -> Value -> UnifyM Value
instantiateTopPis lvl = go
  where
    go = \case
      VTop _ _ ts -> do
        (_, t) <- choose ts
        go t
      t -> go' t

    go' = \case
      t@(VPi x _ b) -> do
        m <- liftIO $ freshMetaSrc x
        go (b $ VMetaApp m args) <|> pure t
      VArr a b -> VArr a <$> go' b
      t -> pure t

    args = map VVar [0 .. lvl - 1]

--------------------------------------------------------------------------------
-- Entry points

unifyValue' :: Modulo -> TopEnv -> Value -> Value -> UnifyM (MetaSubst, [Constraint])
unifyValue' modulo topEnv v v' = do
  let initCtx = SharedCtx topEnv HM.empty HM.empty 0
      initTodo = Constraint 0 Rigid modulo v v'
  unify initCtx [initTodo]

-- | Unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
unifyValue :: Modulo -> TopEnv -> Value -> Value -> IO (Maybe MetaSubst)
unifyValue modulo topEnv v v' = do
  xs <- withFile "/dev/null" AppendMode \h -> do
    observeManyT 1 $ runReaderT (unifyValue' modulo topEnv v v') h
  case xs of
    [] -> pure Nothing
    (subst, _) : _ -> pure (Just (zonkMetaSubst modulo topEnv subst))

-- | Unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
unifyTerm :: Modulo -> TopEnv -> Term -> Term -> IO (Maybe MetaSubst)
unifyTerm modulo topEnv t t' =
  unifyValue modulo topEnv (evaluate topEnv [] t) (evaluate topEnv [] t')

-- | Unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
unifyRaw :: Modulo -> TopEnv -> Raw -> Raw -> IO (Maybe MetaSubst)
unifyRaw modulo topEnv t t' =
  unifyValue modulo topEnv (evaluateRaw topEnv HM.empty t) (evaluateRaw topEnv HM.empty t')

unifyValueInst' :: Modulo -> TopEnv -> Value -> Value -> UnifyM (MetaSubst, [Constraint])
unifyValueInst' modulo topEnv v v' = do
  w <- instantiateInPisOf v' v
  unifyValue' modulo topEnv w v'

-- | Unification modulo βη-equivalence and type isomorphisms related to Π and Σ.
-- The left hand side is instantiated.
unifyValueInst :: Modulo -> TopEnv -> Value -> Value -> IO (Maybe MetaSubst)
unifyValueInst modulo topEnv v v' = do
  xs <- withFile "/dev/null" AppendMode \h -> do
    observeManyT 1 $ runReaderT (unifyValueInst' modulo topEnv v v') h
  case xs of
    [] -> pure Nothing
    (subst, _) : _ -> pure (Just (zonkMetaSubst modulo topEnv subst))

unifyTermInst :: Modulo -> TopEnv -> Term -> Term -> IO (Maybe MetaSubst)
unifyTermInst modulo topEnv t t' =
  unifyValueInst modulo topEnv (evaluate topEnv [] t) (evaluate topEnv [] t')

unifyRawInst :: Modulo -> TopEnv -> Raw -> Raw -> IO (Maybe MetaSubst)
unifyRawInst modulo topEnv t t' =
  unifyValueInst modulo topEnv (evaluateRaw topEnv HM.empty t) (evaluateRaw topEnv HM.empty t')
