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

import Backtrack
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bits
import Data.Coerce
import Data.HashMap.Lazy qualified as HM
import Data.IntSet qualified as IS
-- import Data.Text qualified as T
-- import System.IO
import TypeSearch.Common
import TypeSearch.Evaluation
-- import TypeSearch.Pretty
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
  deriving stock (Show)

-- | Create a meta abstraction of a given arity that imitates a particular rigid value.
imitation :: (MonadIO m) => ImitationKind -> Int -> m MetaAbs
imitation kind arity =
  MetaAbs arity <$> imitation' kind params params'
  where
    -- [x0, ..., xn]
    params = map Var $ down (Index arity - 1) 0
    -- x. [x0, ..., xn, x]
    params' = map Var $ down (Index arity) 0

imitation' :: (MonadIO m) => ImitationKind -> [Term] -> [Term] -> m Term
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

jpProjection' :: (Alternative m) => Int -> m Term
jpProjection' arity = Var <$> choose [0 .. Index arity - 1]

-- | Generate Huet-style projections for a given value.
huetProjection :: (MonadIO m, MonadPostpone m) => Value -> Int -> m MetaAbs
huetProjection t arity =
  MetaAbs arity <$> huetProjection' t arity params params'
  where
    params = map Var $ down (Index arity - 1) 0
    params' = map Var $ down (Index arity) 0

hasNoElimRule :: Term -> Bool
hasNoElimRule = \case
  Type -> True
  Pi {} -> True
  Arr {} -> True
  Sigma {} -> True
  Prod {} -> True
  Unit -> True
  Nat -> True
  Eq {} -> True
  _ -> False

huetProjection' :: (MonadIO m, MonadPostpone m) => Value -> Int -> [Term] -> [Term] -> m Term
huetProjection' t arity params params' = hd >>= go
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

    hd = (kind >>= \k -> imitation' k params params') <|> jpProjection' arity

    go u =
      pure u <|> postpone do
        guard (not $ hasNoElimRule u)
        elim <-
          asum
            [ do
                m <- liftIO freshMeta
                let v = MetaApp m params
                pure (`App` v),
              pure Fst,
              pure Snd
            ]
        u' <- go u
        pure $ elim u'

-- | Elimination bindings.
elimination :: (MonadIO m) => Int -> (Int -> Bool) -> m MetaAbs
elimination arity elim = do
  m <- liftIO freshMeta
  let params = [Var (Index (arity - i - 1)) | i <- [0 .. arity - 1], not (elim i)]
  pure $ MetaAbs arity $ MetaApp m params

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

data PruneInfo = PruneInfo
  { arity :: Int,
    paramsToPrune :: Int
  }
  deriving stock (Show)

instance Semigroup PruneInfo where
  PruneInfo ar ps <> PruneInfo _ ps' = PruneInfo ar (ps .|. ps')

newtype Prune = Prune (HM.HashMap Meta PruneInfo)
  deriving stock (Show)

instance Semigroup Prune where
  Prune ps <> Prune ps' = Prune (HM.unionWith (<>) ps ps')

instance Monoid Prune where
  mempty = Prune mempty

-- | Try to eliminate some of the arguments of parametrised metavariables in a given value in order to prune dependencies to the given set of free variables.
tryPrune :: TopEnv -> MetaSubst -> IS.IntSet -> Level -> Value -> IO (Maybe (Value, MetaSubst))
tryPrune topEnv subst wantPrunes = \lvl t -> case execStateT (go lvl t) mempty of
  Nothing -> pure Nothing
  Just (Prune prune) -> do
    subst' <-
      foldM
        ( \acc (m, PruneInfo ar is) -> do
            mabs <- elimination ar (testBit is)
            pure $! HM.insert m mabs acc
        )
        subst
        (HM.toList prune)
    let t' = deepForce topEnv subst' t
    pure (Just (t', subst'))
  where
    go lvl t = case force topEnv subst t of
      VRigid (Level l) sp
        | IS.member l wantPrunes -> empty
        | otherwise -> goSpine lvl sp
      VFlex m ar ts sp -> goSpine lvl sp >> goArgs m ar lvl ts
      VTop _ sp _ -> goSpine lvl sp
      VType -> pure ()
      VPi _ a b -> go lvl a >> goScope lvl b
      VArr a b -> go lvl a >> go lvl b
      VAbs _ b -> goScope lvl b
      VSigma _ a b -> go lvl a >> goScope lvl b
      VProd a b -> go lvl a >> go lvl b
      VPair a b -> go lvl a >> go lvl b
      VUnit -> pure ()
      VTT -> pure ()
      VNat -> pure ()
      VZero -> pure ()
      VSuc u -> go lvl u
      VEq a u v -> go lvl a >> go lvl u >> go lvl v
      VRefl a u -> go lvl a >> go lvl u
      VStuck {} -> empty

    goArgs m ar lvl ts = mapM_ (goArg m ar lvl) $ zip [0 ..] ts

    goArg m ar lvl (i :: Int, t)
      | isFree topEnv subst wantPrunes lvl t = do
          modify' (<> Prune (HM.singleton m (PruneInfo ar (bit i))))
      | otherwise = pure ()

    goScope lvl f = go (lvl + 1) (f $ VVar lvl)

    goSpine lvl = mapM_ (goElim lvl)

    goElim lvl = \case
      EApp u -> go lvl u
      EFst -> pure ()
      ESnd -> pure ()
      ENatElim p s z -> go lvl p >> go lvl s >> go lvl z
      EEqElim a x p r y -> go lvl a >> go lvl x >> go lvl p >> go lvl r >> go lvl y

-- | Check if some of the variables in the set is free in the value.
isFree :: TopEnv -> MetaSubst -> IS.IntSet -> Level -> Value -> Bool
isFree topEnv subst fv = go
  where
    go lvl t = case force topEnv subst t of
      VRigid (Level l) sp -> IS.member l fv || goSpine lvl sp
      VFlex _ _ ts sp -> any (go lvl) ts || goSpine lvl sp
      VTop _ sp _ -> goSpine lvl sp
      VType -> False
      VPi _ a b -> go lvl a || goScope lvl b
      VArr a b -> go lvl a || go lvl b
      VAbs _ b -> goScope lvl b
      VSigma _ a b -> go lvl a || goScope lvl b
      VProd a b -> go lvl a || go lvl b
      VPair a b -> go lvl a || go lvl b
      VUnit -> False
      VTT -> False
      VNat -> False
      VZero -> False
      VSuc u -> go lvl u
      VEq a u v -> go lvl a || go lvl u || go lvl v
      VRefl a u -> go lvl a || go lvl u
      VStuck {} -> False

    goScope lvl f = go (lvl + 1) (f $ VVar lvl)

    goSpine lvl = any (goElim lvl)

    goElim lvl = \case
      EApp t -> go lvl t
      EFst -> False
      ESnd -> False
      ENatElim p s z -> go lvl p || go lvl s || go lvl z
      EEqElim a x p r y -> go lvl a || go lvl x || go lvl p || go lvl r || go lvl y

isPi :: Value -> Bool
isPi = \case
  VPi {} -> True
  VArr {} -> True
  _ -> False

-- | From a pi type, generate the same type but with single domain is hoisted to the top respecting dependencies.
-- When the domain trying to be hoisted is a parametrised metavariable, we try to eliminate some of the parameters to prune dependencies that block the hoisting.
-- Example 1:
--   * Input:   (A B : Type) -> A -> B -> A
--   * Output: [(B A : Type) -> A -> B -> A]
-- Example 2:
--   * Input:    (A -> B -> B) -> B -> List A -> B  (where A and B are free)
--   * Output: [ B -> (A -> B -> B) -> List A -> B,
--               List A -> (A -> B -> B) -> B -> B ]
-- Example 3:
--   * Input:    (A : Type) -> ?M[A] -> Type
--   * Output: [?N[] -> (A : Type) -> Type] where ?M[x] := ?N[] (?N is fresh)
possibleDomainHoists :: (MonadIO m, MonadPlus m) => TopEnv -> MetaSubst -> Level -> Value -> m (Value, MetaSubst)
possibleDomainHoists topEnv subst lvl t = case t of
  VPi _ _ b -> go (IS.singleton (coerce lvl)) (1 :: Int) (lvl + 1) (b $ VVar lvl)
  VArr _ b -> go IS.empty 1 lvl b
  _ -> empty
  where
    go lvls i lvl' u = case force topEnv subst u of
      VPi x a b ->
        ( do
            (a', subst') <- choose =<< liftIO (tryPrune topEnv subst lvls lvl' a)
            pure (VPi x a' (\ ~v -> deletePi i v t), subst')
        )
          <|> go (IS.insert (coerce lvl') lvls) (i + 1) (lvl' + 1) (b $ VVar lvl')
      VArr a b ->
        ( do
            (a', subst') <- choose =<< liftIO (tryPrune topEnv subst lvls lvl' a)
            pure (VArr a' (deleteArr i t), subst')
        )
          <|> go lvls (i + 1) lvl' b
      _ -> empty

    deleteArr i u = case (i, force topEnv subst u) of
      (0, VArr _ b) -> b
      (0, _) -> error "deleteArr: not an arrow"
      (_, VPi x a b) -> VPi x a (deleteArr (i - 1) . b)
      (_, VArr a b) -> VArr a (deleteArr (i - 1) b)
      _ -> error "deleteArr: not an arrow"

    deletePi i u v = case (i, force topEnv subst v) of
      (0, VPi _ _ b) -> b u
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
possibleComponentHoists :: (MonadIO m, MonadPlus m) => TopEnv -> MetaSubst -> Level -> Value -> m (Value, MetaSubst)
possibleComponentHoists topEnv subst lvl t = case t of
  VSigma _ _ b -> go (IS.singleton (coerce lvl)) (1 :: Int) (lvl + 1) (b $ VVar lvl)
  VProd _ b -> go IS.empty 1 lvl b
  _ -> empty
  where
    go lvls i lvl' u = case force topEnv subst u of
      VSigma x a b ->
        ( do
            (a', subst') <- choose =<< liftIO (tryPrune topEnv subst lvls lvl' a)
            pure (VSigma x a' (\ ~v -> deleteSigma i v t), subst')
        )
          <|> go (IS.insert (coerce lvl') lvls) (i + 1) (lvl' + 1) (b $ VVar lvl')
      VProd a b ->
        ( do
            (a', subst') <- choose =<< liftIO (tryPrune topEnv subst lvls lvl' a)
            pure (VProd a' (deleteProd i t), subst')
        )
          <|> go lvls (i + 1) lvl' b
      a -> do
        (a', subst') <- choose =<< liftIO (tryPrune topEnv subst lvls lvl' a)
        pure (VProd a' (deleteProd i t), subst')

    deleteProd i u = case (i, force topEnv subst u) of
      (0, VProd _ b) -> b
      (0, _) -> error "deleteProd: not a prod"
      (1, VProd a b) -> case force topEnv subst b of
        b'@VProd {} -> VProd a (deleteProd (i - 1) b')
        _ -> a
      (_, VSigma x a b) -> VSigma x a (deleteProd (i - 1) . b)
      (_, VProd a b) -> VProd a (deleteProd (i - 1) b)
      _ -> error "deleteProd: not a prod"

    deleteSigma i u v = case (i, force topEnv subst v) of
      (0, VSigma _ _ b) -> b u
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
type UnifyM = Backtrack IO

-- type UnifyM = ReaderT (String -> IO ()) (Backtrack IO)

-- unifyLog :: ((String -> IO ()) -> IO ()) -> UnifyM ()
-- unifyLog f = ask >>= liftIO . (f $)

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
      let bx = b $ VVar lvl
          b'x = b' $ VVar lvl
          free = any (isFree ctx.topEnv ctx.metaSubst (IS.singleton (coerce lvl)) lvl) [bx, b'x]
          todo1 = Constraint lvl cm (if free then DefEq else Iso) a a'
          todo2 = Constraint (lvl + 1) cm iso bx b'x
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
      let bx = b $ VVar lvl
          b'x = b' $ VVar lvl
          free = any (isFree ctx.topEnv ctx.metaSubst (IS.singleton (coerce lvl)) lvl) [bx, b'x]
          todo1 = Constraint lvl cm (if free then DefEq else Iso) a a'
          todo2 = Constraint (lvl + 1) cm iso bx b'x
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
decomposeIso :: SharedCtx -> Constraint -> [Constraint] -> UnifyM (SharedCtx, [Constraint])
decomposeIso ctx (Constraint lvl cm iso lhs rhs) todos = do
  guard (iso == Iso)
  case (lhs, rhs) of
    -- Hoist one of the domains respecting dependencies
    (isPi -> True, isPi -> True) -> do
      (lhs', subst') <- possibleDomainHoists ctx.topEnv ctx.metaSubst lvl lhs
      let ctx' = ctx {metaSubst = subst'}
          todo1 = Constraint lvl cm iso lhs' rhs
      (ctx',) <$> decompose ctx' todo1 todos
    -- Hoist one of the components respecting dependencies
    (isSigma -> True, isSigma -> True) -> do
      (lhs', subst') <- possibleComponentHoists ctx.topEnv ctx.metaSubst lvl lhs
      let ctx' = ctx {metaSubst = subst'}
          todo1 = Constraint lvl cm iso lhs' rhs
      (ctx',) <$> decompose ctx' todo1 todos
    -- swap the sides of the equality
    (VEq a t u, VEq {}) -> do
      let todo1 = Constraint lvl cm iso (VEq a u t) rhs
      (ctx,) <$> decompose ctx todo1 todos
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

isMeta :: Value -> Bool
isMeta = \case
  VFlex {} -> True
  _ -> False

-- | Like @guessMeta@, but for type isomorphisms.
-- Π and Σ types act as "eliminators" when considering type isomorphisms!
guessMetaIso :: SharedCtx -> Constraint -> [Constraint] -> UnifyM (SharedCtx, [Constraint])
guessMetaIso ctx todo@(Constraint lvl _ iso lhs rhs) todos = do
  guard $ iso == Iso
  (m, mabs) <- guessMetaIso' lhs rhs <|> guessMetaIso' rhs lhs
  let ctx' = incrNumGuessMetaIso $ addMetaSubst m mabs ctx
  pure (ctx', todo : todos)
  where
    guessMetaIso' subj other = case subj of
      VSigma _ a b ->
        asum
          [ case force' ctx a of
              -- Σ x : M[t0, ..., tn]. B[x]
              VFlex m ar _ SNil ->
                asum
                  [ -- M[x0, ..., xn] ↦ Unit
                    (m,) <$> imitation IUnit ar,
                    -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
                    do
                      guard $ isSigma other || isMeta other
                      postpone $ (m,) <$> imitation (ISigma "x") ar
                  ]
              VFlex m ar _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") ar
              VFlex m ar _ (SFst' {}) -> (m,) <$> imitation IPair ar
              VFlex m ar _ (SSnd' {}) -> (m,) <$> imitation IPair ar
              _ -> empty,
            case force' ctx (b $ VVar lvl) of
              -- Σ x : A. M[t0, ..., tn]
              VFlex m ar _ SNil ->
                asum
                  [ -- M[x0, ..., xn] ↦ Unit
                    (m,) <$> imitation IUnit ar,
                    -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
                    do
                      guard $ isSigma other || isMeta other
                      postpone $ (m,) <$> imitation (ISigma "x") ar
                  ]
              VFlex m ar _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") ar
              VFlex m ar _ (SFst' {}) -> (m,) <$> imitation IPair ar
              VFlex m ar _ (SSnd' {}) -> (m,) <$> imitation IPair ar
              _ -> empty
          ]
      VProd a b ->
        asum
          [ case force' ctx a of
              -- M[t0, ..., tn] * B
              VFlex m ar _ SNil ->
                asum
                  [ -- M[x0, ..., xn] ↦ Unit
                    (m,) <$> imitation IUnit ar,
                    -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
                    do
                      guard $ isSigma other || isMeta other
                      postpone $ (m,) <$> imitation (ISigma "x") ar
                  ]
              VFlex m ar _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") ar
              VFlex m ar _ (SFst' {}) -> (m,) <$> imitation IPair ar
              VFlex m ar _ (SSnd' {}) -> (m,) <$> imitation IPair ar
              _ -> empty,
            case force' ctx b of
              -- A * M[t0, ..., tn]
              VFlex m ar _ SNil ->
                asum
                  [ -- M[x0, ..., xn] ↦ Unit
                    (m,) <$> imitation IUnit ar,
                    -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
                    do
                      guard $ isSigma other || isMeta other
                      postpone $ (m,) <$> imitation (ISigma "x") ar
                  ]
              VFlex m ar _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") ar
              VFlex m ar _ (SFst' {}) -> (m,) <$> imitation IPair ar
              VFlex m ar _ (SSnd' {}) -> (m,) <$> imitation IPair ar
              _ -> empty
          ]
      VPi _ a b ->
        asum
          [ case force' ctx a of
              -- (x : M[t0, ..., tn]) → B[x]
              VFlex m ar _ SNil ->
                asum
                  [ -- M[x0, ..., xn] ↦ Unit
                    (m,) <$> imitation IUnit ar,
                    -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
                    do
                      guard $ isPi other || isMeta other
                      postpone $ (m,) <$> imitation (ISigma "x") ar
                  ]
              VFlex m ar _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") ar
              VFlex m ar _ (SFst' {}) -> (m,) <$> imitation IPair ar
              VFlex m ar _ (SSnd' {}) -> (m,) <$> imitation IPair ar
              _ -> empty,
            case force' ctx (b $ VVar lvl) of
              -- (x : A) -> M[t0, ..., tn]
              VFlex m ar _ SNil ->
                -- M[x0, ..., xn] ↦ (y : M1[x0, ..., xn]). M2[x0, ..., xn, y]
                do
                  guard $ isPi other || isMeta other
                  postpone $ (m,) <$> imitation (IPi "x") ar
              _ -> empty
          ]
      VArr a b ->
        asum
          [ -- M[t0, ..., tn] → B
            case force' ctx a of
              VFlex m ar _ SNil ->
                asum
                  [ -- M[x0, ..., xn] ↦ Unit
                    (m,) <$> imitation IUnit ar,
                    -- M[x0, ..., xn] ↦ Σ y : M1[x0, ..., xn]. M2[x0, ..., xn, y]
                    do
                      guard $ isPi other || isMeta other
                      postpone $ (m,) <$> imitation (ISigma "x") ar
                  ]
              VFlex m ar _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") ar
              VFlex m ar _ (SFst' {}) -> (m,) <$> imitation IPair ar
              VFlex m ar _ (SSnd' {}) -> (m,) <$> imitation IPair ar
              _ -> empty,
            -- A → M[t0, ..., tn]
            case force' ctx b of
              VFlex m ar _ SNil ->
                -- M[x0, ..., xn] ↦ (y : M1[x0, ..., xn]). M2[x0, ..., xn, y]
                do
                  guard $ isPi other || isMeta other
                  postpone $ (m,) <$> imitation (IPi "x") ar
              VFlex m ar _ (SApp' {}) -> (m,) <$> imitation (IAbs "x") ar
              VFlex m ar _ (SFst' {}) -> (m,) <$> imitation IPair ar
              VFlex m ar _ (SSnd' {}) -> (m,) <$> imitation IPair ar
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
              -- unifyLog \f -> f $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
              -- assume modName = modName'
              ((modName, t), (_modName', t')) <- choose (zip ts ts')
              let ctx' = addChosenDef n modName ctx
                  todo1 = Constraint lvl Full iso t t'
              pure (ctx', todo1 : todos)
      | otherwise -> do
          -- unifyLog \f -> f $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
          (modName, t) <- choose ts
          -- unifyLog \f -> f $ "unfold: " ++ show n' ++ " (" ++ show (length ts') ++ " alternatives)"
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
          -- unifyLog \f -> f $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
          ((modName, t), (_modName', t')) <- choose (zip ts ts')
          let ctx' = addChosenDef n modName ctx
              todo1 = Constraint lvl Full iso t t'
          pure (ctx', todo1 : todos)
      | otherwise -> do
          -- unifyLog \f -> f $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
          (modName, t) <- choose ts
          -- unifyLog \f -> f $ "unfold: " ++ show n' ++ " (" ++ show (length ts') ++ " alternatives)"
          (modName', t') <- choose ts'
          let ctx' = addChosenDef n modName $ addChosenDef n' modName' ctx
              todo1 = Constraint lvl Rigid iso t t'
          pure (ctx', todo1 : todos)
    (Flex, VTop {}, _) -> empty
    (_, VTop n _ ts, t') -> do
      -- unifyLog \f -> f $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
      (modName, t) <- choose ts
      let todo1 = Constraint lvl cm iso t t'
          ctx' = addChosenDef n modName ctx
      pure (ctx', todo1 : todos)
    (Flex, _, VTop {}) -> empty
    (_, t, VTop n _ ts) -> do
      -- unifyLog \f -> f $ "unfold: " ++ show n ++ " (" ++ show (length ts) ++ " alternatives)"
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
  -- unifyLog \f -> do
  --   f "--------------------------------------------------"
  --   f $ prettyMetaSubst ctx.metaSubst ""
  --   mapM_ (\todo' -> f $ prettyConstraint todo' "") todos
  case chooseConstraint ctx todos of
    Stuck -> empty
    Done ff -> pure (ctx.metaSubst, ff)
    Solved m mabs todos' -> unify (addMetaSubst m mabs ctx) todos'
    Next todo todos' -> do
      (ctx', todos'') <-
        asum
          [ (ctx,) <$> decompose ctx todo todos',
            decomposeIso ctx todo todos',
            guessMeta ctx todo todos',
            unfold ctx todo todos',
            guard (ctx.numGuessMetaIso < 5) >> guessMetaIso ctx todo todos',
            flexRigid ctx todo todos'
          ]
      unify ctx' todos''

-- prettyConstraint :: Constraint -> ShowS
-- prettyConstraint (Constraint lvl _ iso lhs rhs) =
--   ( if lvl > 0
--       then
--         showString "∀ "
--           . punctuate (showString " ") (map shows $ reverse vars)
--           . showString ". "
--       else id
--   )
--     . prettyTerm vars 0 lhs'
--     . showString eq
--     . prettyTerm vars 0 rhs'
--   where
--     lhs' = quote lvl lhs
--     rhs' = quote lvl rhs
--     vars = map (\i -> Name $ "x" <> T.pack (show i)) $ down (lvl - 1) 0
--     eq = case iso of
--       DefEq -> " ≡ "
--       Iso -> " ≅ "

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
  let names = topPiNames t
  u' <- instantiateTopPis names u
  pure $ go u' t
  where
    go v = \case
      VPi x a b -> VPi x a (go v . b)
      VArr _ b -> go v b
      _ -> v

-- | Collect the variable names bound by top-level pis.
topPiNames :: Value -> [Name]
topPiNames = go [] 0
  where
    go acc lvl = \case
      VPi x _ b -> go (x : acc) (lvl + 1) (b (VVar lvl))
      VArr _ b -> go acc lvl b
      _ -> acc

-- | Instantiate top-level pis. Unfold definitions.
instantiateTopPis :: [Name] -> Value -> UnifyM Value
instantiateTopPis names = go
  where
    go = \case
      VTop _ _ ts -> do
        (_, t) <- choose ts
        go t
      t -> go' t

    go' = \case
      t@(VPi x _ b) -> do
        let m = Inst x names
        go (b $ VMetaApp m args) <|> pure t
      VArr a b -> VArr a <$> go' b
      t -> pure t

    lvl = Level $ length names
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
  -- xs <- withFile "unify.log" AppendMode \h -> do
  --   Backtrack.head $ runReaderT (unifyValue' modulo topEnv v v') (hPutStrLn h)
  xs <- Backtrack.head $ unifyValue' modulo topEnv v v'
  case xs of
    Nothing -> pure Nothing
    Just (subst, _) -> pure (Just (zonkMetaSubst modulo topEnv subst))

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
  -- xs <- withFile "unify.log" AppendMode \h -> do
  --   Backtrack.head $ runReaderT (unifyValueInst' modulo topEnv v v') (hPutStrLn h)
  xs <- Backtrack.head $ unifyValueInst' modulo topEnv v v'
  case xs of
    Nothing -> pure Nothing
    Just (subst, _) -> pure (Just (zonkMetaSubst modulo topEnv subst))

unifyTermInst :: Modulo -> TopEnv -> Term -> Term -> IO (Maybe MetaSubst)
unifyTermInst modulo topEnv t t' =
  unifyValueInst modulo topEnv (evaluate topEnv [] t) (evaluate topEnv [] t')

unifyRawInst :: Modulo -> TopEnv -> Raw -> Raw -> IO (Maybe MetaSubst)
unifyRawInst modulo topEnv t t' =
  unifyValueInst modulo topEnv (evaluateRaw topEnv HM.empty t) (evaluateRaw topEnv HM.empty t')
