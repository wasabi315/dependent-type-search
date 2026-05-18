module TypeSearch.Unification where

import Data.HashMap.Strict qualified as HM
import Data.ImmatureStream qualified as ImS
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import TypeSearch.Core.Evaluation
import TypeSearch.Core.Isomorphism
import TypeSearch.Core.Name
import TypeSearch.Core.Term hiding (rename)
import TypeSearch.Prelude

--------------------------------------------------------------------------------

-- | Partial renaming from @Γ@ to @Δ@.
data PartialRenaming = PRen
  { -- | optional occurs check.
    occ :: Maybe MetaVar,
    -- | size of @Γ@.
    dom :: Level,
    -- | size of @Δ@.
    cod :: Level,
    -- | mapping from @Δ@ vars to @Γ@ vars.
    ren :: IM.IntMap Level
  }

emptyPRen :: PartialRenaming
emptyPRen = PRen Nothing 0 0 mempty

-- | @(σ : PRen Γ Δ) → PRen (Γ, x : A[σ]) (Δ, x : A)@.
liftPren :: PartialRenaming -> PartialRenaming
liftPren (PRen occ dom cod ren) =
  PRen occ (dom + 1) (cod + 1) (IM.insert (coerce cod) dom ren)

-- | @PRen Γ Δ → PRen Γ (Δ, x : A)@.
skipPren :: PartialRenaming -> PartialRenaming
skipPren (PRen occ dom cod ren) = PRen occ dom (cod + 1) ren

skipPrenN :: Level -> PartialRenaming -> PartialRenaming
skipPrenN n (PRen occ dom cod ren) = PRen occ dom (cod + n) ren

-- | @(Γ : Cxt) → (spine : Sub Γ Δ) → PRen Δ Γ@.
--   Optionally returns a pruning of nonlinear spine entries, if there's any.
invert :: MetaCtx -> Level -> Spine -> Maybe (PartialRenaming, Maybe Pruning)
invert mctx gamma sp = do
  let go = \case
        SNil -> pure (0, mempty, mempty, [])
        SApp sp (force mctx -> VVar (Level x)) -> do
          (dom, ren, nlvars, fsp) <- go sp
          case IM.member x ren || IS.member x nlvars of
            True -> pure (dom + 1, IM.delete x ren, IS.insert x nlvars, Level x : fsp)
            False -> pure (dom + 1, IM.insert x dom ren, nlvars, Level x : fsp)
        SApp {} -> Nothing
        SProj1 {} -> Nothing
        SProj2 {} -> Nothing

  (dom, ren, nlvars, fsp) <- go sp

  let mask = map \(Level x) -> IS.notMember x nlvars

  pure (PRen Nothing dom gamma ren, mask fsp <$ guard (not $ IS.null nlvars))

type P = StateT MetaCtx Maybe

newMeta :: MetaCtx -> Value -> (MetaVar, MetaCtx)
newMeta mctx ~mty = do
  let m' = mctx.nextMeta
      mctx' =
        mctx
          { nextMeta = mctx.nextMeta + 1,
            metaCtx = HM.insert m' (Unsolved mty) mctx.metaCtx
          }
  (m', mctx')

newMetaP :: Value -> P MetaVar
newMetaP ~mty = state (`newMeta` mty)

forceP :: Value -> P Value
forceP t = gets (`force` t)

evalP :: TopEnv -> Env -> Term -> P Value
evalP tenv env t = gets \mctx -> eval mctx tenv env t

lookupUnsolved :: MetaVar -> P Value
lookupUnsolved m = gets \mctx -> case mctx.metaCtx HM.! m of
  Unsolved a -> a
  Solved {} -> error "lookupUnsolved"

writeMeta :: MetaVar -> Value -> Value -> P ()
writeMeta m t ~a = modify' \mctx ->
  mctx {metaCtx = HM.insert m (Solved t a) mctx.metaCtx}

-- | Remove some arguments from a closed iterated Pi type.
pruneType :: TopEnv -> RevPruning -> Value -> P Term
pruneType tenv (RevPruning pr) a =
  go pr (PRen Nothing 0 0 mempty) a
  where
    go pr pren a = do
      a <- forceP a
      case (pr, a) of
        ([], a) -> renameP tenv pren a
        (True : pr, VPi x a b) ->
          Pi x
            <$> renameP tenv pren a
            <*> go pr (liftPren pren) (b $ VVar pren.cod)
        (False : pr, VPi _ _ b) ->
          go pr (skipPren pren) (b $ VVar pren.cod)
        _ -> empty

-- | Prune arguments from a meta, return new meta + pruned type.
pruneMeta :: TopEnv -> Pruning -> MetaVar -> P MetaVar
pruneMeta tenv pr m = do
  mty <- lookupUnsolved m
  prunedty <- evalP tenv [] =<< pruneType tenv (revPruning pr) mty
  m' <- newMetaP prunedty
  solution <- evalP tenv [] =<< lams (Level $ length pr) mty (AppPruning (Meta m') pr)
  writeMeta m solution mty
  pure m'

data SpinePruneStatus
  = -- | Valid spine which is a renaming
    OKRenaming
  | -- | Valid spine but not a renaming (has a non-var entry)
    OKNonRenaming
  | -- | A spine which is a renaming and has out-of-scope var entries
    NeedsPruning

-- | Prune illegal var occurrences from a meta + spine.
--   Returns: renamed + pruned term.
pruneVFlex :: TopEnv -> PartialRenaming -> MetaVar -> Spine -> P Term
pruneVFlex tenv pren m sp = do
  (sp :: [Maybe Term], status :: SpinePruneStatus) <- do
    let go = \case
          SNil -> pure ([], OKRenaming)
          SApp sp t -> do
            (sp, status) <- go sp
            forceP t >>= \case
              VVar x -> case (IM.lookup (coerce x) pren.ren, status) of
                (Just x, _) -> pure (Just (Var (levelToIndex pren.dom x)) : sp, status)
                (Nothing, OKNonRenaming) -> empty
                (Nothing, _) -> pure (Nothing : sp, NeedsPruning)
              t -> case status of
                NeedsPruning -> empty
                _ -> do
                  t <- renameP tenv pren t
                  pure (Just t : sp, OKNonRenaming)
          _ -> empty
    go sp

  m' <- case status of
    OKRenaming -> pure m
    OKNonRenaming -> pure m
    NeedsPruning -> pruneMeta tenv (isJust <$> sp) m

  let t = foldr (\mu t -> maybe t (App t) mu) (Meta m') sp
  pure t

rename :: MetaCtx -> TopEnv -> PartialRenaming -> Value -> Maybe (Term, MetaCtx)
rename mctx tenv pren t = flip runStateT mctx $ renameP tenv pren t

renameP :: TopEnv -> PartialRenaming -> Value -> P Term
renameP tenv pren t =
  forceP t >>= \case
    VFlex m' sp -> case pren.occ of
      Just m | m == m' -> empty -- occurs check
      _ -> pruneVFlex tenv pren m' sp
    VRigid (Level x) sp -> case IM.lookup x pren.ren of
      Nothing -> empty -- scope error ("escaping variable" error)
      Just x' -> renameSpine tenv pren (Var $ levelToIndex pren.dom x') sp
    VTop x sp Nothing -> renameSpine tenv pren (Top x) sp
    VTop _ _ (Just t) -> renameP tenv pren t
    VU -> pure U
    VPi x a b ->
      Pi x
        <$> renameP tenv pren a
        <*> renameP tenv (liftPren pren) (b $ VVar pren.cod)
    VLam x t ->
      Lam x <$> renameP tenv (liftPren pren) (t $ VVar pren.cod)
    VSigma x a b ->
      Sigma x
        <$> renameP tenv pren a
        <*> renameP tenv (liftPren pren) (b $ VVar pren.cod)
    VPair t u ->
      Pair <$> renameP tenv pren t <*> renameP tenv pren u
    VBrave {} -> empty

renameSpine :: TopEnv -> PartialRenaming -> Term -> Spine -> P Term
renameSpine tenv pren t = \case
  SNil -> pure t
  SApp sp u -> App <$> renameSpine tenv pren t sp <*> renameP tenv pren u
  SProj1 sp -> Proj1 <$> renameSpine tenv pren t sp
  SProj2 sp -> Proj2 <$> renameSpine tenv pren t sp

-- | Wrap a term in Level number of lambdas. We get the domain info from the Value
--   argument.
lams :: Level -> Value -> Term -> P Term
lams l a t = join $ gets \mctx -> do
  let go _ (l' :: Level) | l' == l = pure t
      go a l' = case force mctx a of
        VPi "_" _ b ->
          Lam (fromString $ "x" ++ show l')
            <$> go (b $ VVar l') (l' + 1)
        VPi x _ b ->
          Lam x <$> go (b $ VVar l') (l' + 1)
        _ -> empty
  go a (0 :: Level)

-- | Solve @Γ ⊢ m spine =? rhs@.
solve :: MetaCtx -> TopEnv -> Level -> MetaVar -> Spine -> Value -> Maybe MetaCtx
solve mctx tenv gamma m sp rhs = do
  pren <- invert mctx gamma sp
  solveWithPren mctx tenv m pren rhs

-- | Solve m given the result of inversion on a spine.
solveWithPren ::
  MetaCtx -> TopEnv -> MetaVar -> (PartialRenaming, Maybe Pruning) -> Value -> Maybe MetaCtx
solveWithPren mctx tenv m (pren, pruneNonLinear) rhs = flip execStateT mctx do
  mty <- lookupUnsolved m
  -- if the spine was non-linear, we check that the non-linear arguments
  -- can be pruned from the meta type (i.e. that the pruned solution will
  -- be well-typed)
  case pruneNonLinear of
    Nothing -> pure ()
    Just pr -> void $ pruneType tenv (revPruning pr) mty
  rhs <- renameP tenv (pren {occ = Just m}) rhs
  solution <- evalP tenv [] =<< lams pren.dom mty rhs
  writeMeta m solution mty

spineLength :: Spine -> Int
spineLength = \case
  SNil -> 0
  SApp sp _ -> 1 + spineLength sp
  SProj1 sp -> spineLength sp
  SProj2 sp -> spineLength sp

-- | Solve @Γ ⊢ m spine =? m' spine'@.
flexFlex :: MetaCtx -> TopEnv -> Level -> MetaVar -> Spine -> MetaVar -> Spine -> Maybe MetaCtx
flexFlex mctx tenv gamma m sp m' sp' = do
  let -- It may be that only one of the two spines is invertible
      go m sp m' sp' = case invert mctx gamma sp of
        Nothing -> solve mctx tenv gamma m' sp' (VFlex m sp)
        Just pren -> solveWithPren mctx tenv m pren (VFlex m' sp')
  -- usually, a longer spine indicates that the meta is in an inner scope. If we solve
  -- inner metas with outer metas, that means that we have to do less pruning.
  if spineLength sp < spineLength sp'
    then go m' sp' m sp
    else go m sp m' sp'

--------------------------------------------------------------------------------

data ConvState
  = Rigid
  | Flex
  | Full
  deriving stock (Show, Eq, Ord)

forceCS :: MetaCtx -> ConvState -> Value -> Value
forceCS mctx cs v = case cs of
  Full -> forceAll mctx v
  _ -> force mctx v

unify0 :: MetaCtx -> TopEnv -> Term -> Term -> Maybe MetaCtx
unify0 mctx tenv t t' = do
  let v = eval mctx tenv [] t
      v' = eval mctx tenv [] t'
  unify mctx tenv Rigid 0 v v'

unify :: MetaCtx -> TopEnv -> ConvState -> Level -> Value -> Value -> Maybe MetaCtx
unify mctx tenv cs l t t' = case (forceCS mctx cs t, forceCS mctx cs t') of
  (VBrave {}, _) -> Nothing
  (_, VBrave {}) -> Nothing
  (VPi _ a b, VPi _ a' b') -> do
    mctx <- unify mctx tenv cs l a a'
    unify mctx tenv cs (l + 1) (b $ VVar l) (b' $ VVar l)
  (VU, VU) -> pure mctx
  (VLam _ t, VLam _ t') ->
    unify mctx tenv cs (l + 1) (t $ VVar l) (t' $ VVar l)
  (t, VLam _ t') ->
    unify mctx tenv cs (l + 1) (t $$ VVar l) (t' $ VVar l)
  (VLam _ t, t') ->
    unify mctx tenv cs (l + 1) (t $ VVar l) (t' $$ VVar l)
  (VSigma _ a b, VSigma _ a' b') -> do
    mctx <- unify mctx tenv cs l a a'
    unify mctx tenv cs (l + 1) (b $ VVar l) (b' $ VVar l)
  (VPair t u, VPair t' u') -> do
    mctx <- unify mctx tenv cs l t t'
    unify mctx tenv cs l u u'
  (VPair t u, t') -> do
    mctx <- unify mctx tenv cs l t (vProj1 t')
    unify mctx tenv cs l u (vProj2 t')
  (t, VPair t' u') -> do
    mctx <- unify mctx tenv cs l (vProj1 t) t'
    unify mctx tenv cs l (vProj2 t) u'
  (VRigid x sp, VRigid x' sp')
    | x == x' -> unifySpine mctx tenv cs l sp sp'
  (VFlex m sp, VFlex m' sp')
    | m == m' -> unifySpine mctx tenv cs l sp sp'
    | otherwise -> do
        guard $ cs /= Flex
        flexFlex mctx tenv l m sp m' sp'
  (VTop x sp Nothing, VTop x' sp' Nothing)
    | x == x' -> unifySpine mctx tenv cs l sp sp'
  (VTop x sp (Just t), VTop x' sp' (Just t')) -> case cs of
    Rigid
      | x == x' ->
          unifySpine mctx tenv Flex l sp sp'
            <|> unify mctx tenv Full l t t'
      | otherwise -> unify mctx tenv Rigid l t t'
    Flex
      | x == x' -> unifySpine mctx tenv Flex l sp sp'
      | otherwise -> Nothing
    Full -> impossible
  (VFlex m sp, t') -> do
    guard $ cs /= Flex
    solve mctx tenv l m sp t'
  (t, VFlex m' sp') -> do
    guard $ cs /= Flex
    solve mctx tenv l m' sp' t
  (VTop _ _ (Just t), t') -> case cs of
    Rigid -> unify mctx tenv cs l t t'
    Flex -> Nothing
    Full -> impossible
  (t, VTop _ _ (Just t')) -> case cs of
    Rigid -> unify mctx tenv cs l t t'
    Flex -> Nothing
    Full -> impossible
  _ -> Nothing

unifySpine :: MetaCtx -> TopEnv -> ConvState -> Level -> Spine -> Spine -> Maybe MetaCtx
unifySpine mctx tenv cs l = \cases
  SNil SNil -> pure mctx
  (SApp sp t) (SApp sp' t') -> do
    mctx <- unifySpine mctx tenv cs l sp sp'
    unify mctx tenv cs l t t'
  (SProj1 sp) (SProj1 sp') -> unifySpine mctx tenv cs l sp sp'
  (SProj2 sp) (SProj2 sp') -> unifySpine mctx tenv cs l sp sp'
  _ _ -> Nothing

--------------------------------------------------------------------------------

data Ctx = Ctx
  { topEnv :: TopEnv,
    level :: Level,
    env :: Env,
    idRen :: PartialRenaming,
    convState :: ConvState
  }

initCtx :: TopEnv -> Ctx
initCtx tenv = Ctx tenv 0 empty emptyPRen Rigid

bind :: Ctx -> Ctx
bind (Ctx tenv l env idRen cs) =
  Ctx tenv (l + 1) (VVar l : env) (liftPren idRen) cs

--------------------------------------------------------------------------------
-- Rewriting types

-- | Curry until the first domain becomes non-sigma.
curryCS :: MetaCtx -> ConvState -> Quant -> (Quant, Iso)
curryCS mctx cs = go Refl
  where
    go i (Quant x a b) = case forceCS mctx cs a of
      VSigma y a1 a2 ->
        go (i <> Curry) $ Quant y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> (Quant x a b, i)

-- | Right-nest until the first projection becomes non-sigma.
assocCS :: MetaCtx -> ConvState -> Quant -> (Quant, Iso)
assocCS mctx cs = go Refl
  where
    go i (Quant x a b) = case forceCS mctx cs a of
      VSigma y a1 a2 ->
        go (i <> Assoc) $ Quant y a1 \ ~u -> VSigma x (a2 u) \ ~v -> b (VPair u v)
      a -> (Quant x a b, i)

-- | Pick up a domain without breaking dependencies.
pickUpDomain :: MetaCtx -> Ctx -> Quant -> [(Quant, Iso, MetaCtx)]
pickUpDomain mctx (Ctx tenv l env idRen cs) (Quant x a b) = (Quant x a b, Refl, mctx) : go l b
  where
    go l' c = case forceCS mctx cs $ c (VVar l') of
      VPi y c1 c2 ->
        ( do
            let i = l' - l
            -- Strengthen c1. This may involve pruning.
            (c1, mctx) <- maybeToList $ rename mctx tenv (skipPrenN (i + 1) idRen) c1
            let c1' = eval mctx tenv env c1
                rest ~vc1 = VPi x a (instPiAt i vc1 . b)
                s = swaps i
            pure (Quant y c1' rest, s, mctx)
        )
          ++ go (l' + 1) c2
      _ -> []

    instPiAt i ~v t = case (i, forceCS mctx cs t) of
      (0, VPi _ _ b) -> b v
      (i, VPi x a b) -> VPi x a (instPiAt (i - 1) v . b)
      _ -> impossible

    swaps = \case
      0 -> PiSwap
      n -> piCongR (swaps (n - 1)) <> PiSwap

-- | Pick up a projection without breaking dependencies.
pickUpProjection :: MetaCtx -> Ctx -> Quant -> [(Quant, Iso, MetaCtx)]
pickUpProjection mctx (Ctx tenv l env idRen cs) (Quant x a b) = (Quant x a b, Refl, mctx) : go l b
  where
    go l' c = case forceCS mctx cs $ c (VVar l') of
      VSigma y c1 c2 ->
        ( do
            let i = l' - l
            -- Strengthen c1. This may involve pruning.
            (c1, mctx) <- maybeToList $ rename mctx tenv (skipPrenN (i + 1) idRen) c1
            let c1' = eval mctx tenv env c1
                rest ~vc1 = VSigma x a (instSigmaAt i vc1 . b)
                s = swaps SigmaSwap i
            pure (Quant y c1' rest, s, mctx)
        )
          ++ go (l' + 1) c2
      c -> do
        let i = l' - l
        (c, mctx) <- maybeToList $ rename mctx tenv (skipPrenN (i + 1) idRen) c
        let c' = eval mctx tenv env c
            rest ~_ = dropLastProj (l + 1) (VSigma x a b)
            s = swaps Comm i
        pure (Quant "_" c' rest, s, mctx)

    instSigmaAt i ~v t = case (i, forceCS mctx cs t) of
      (0, VSigma _ _ b) -> b v
      (i, VSigma x a b) -> VSigma x a (instSigmaAt (i - 1) v . b)
      _ -> impossible

    dropLastProj l t = case forceCS mctx cs t of
      VSigma x a b -> case b (VVar l) of
        VSigma {} -> VSigma x a (dropLastProj (l + 1) . b)
        _ -> a
      _ -> impossible

    swaps i = \case
      0 -> i
      n -> sigmaCongR (swaps i (n - 1)) <> SigmaSwap

-- | Pick a **non-sigma** projection without breaking dependencies.
-- This works even in the presence of arbitrarily nested sigmas in the type.
assocSwap :: MetaCtx -> Ctx -> Quant -> [(Quant, Iso, MetaCtx)]
assocSwap mctx ctx q = do
  -- Pick one projection first.
  (q, i, mctx) <- pickUpProjection mctx ctx q
  case q of
    -- When the selected projection is a sigma type, we invoke
    -- assocSwap recursively to make the first projection of the sigma non-sigma!
    Quant x (VSigma y a b) c -> do
      (Quant y a b, j, mctx) <- assocSwap mctx ctx (Quant y a b)
      let -- Then associate to make the first projection non-sigma.
          -- Note the transport along j!
          q = Quant y a \ ~u -> VSigma x (b u) \ ~v -> c (transportInv j (VPair u v))
          k = i <> sigmaCongL j <> Assoc
      pure (q, k, mctx)
    q -> pure (q, i, mctx)

-- | Pick a **non-sigma** domain without breaking dependencies.
-- This works even in the presence of arbitrarily nested sigmas in the type.

--   e.g) currySwap (List A → (B × A → A) × B → B) =
--          [ ( List A → (B × A → A) × B → B , Refl                    ),
--            ( (B × A → B) → B → List A → B , ΠSwap · Curry           ),
--            ( B → (B × A → B) → List A → B , ΠSwap · ΠL Comm · Curry )
--          ]
currySwap :: MetaCtx -> Ctx -> Quant -> [(Quant, Iso, MetaCtx)]
currySwap mctx ctx q = do
  (q, i, mctx) <- pickUpDomain mctx ctx q
  case q of
    Quant x (VSigma y a b) c -> do
      (Quant y a b, j, mctx) <- assocSwap mctx ctx (Quant y a b)
      let q = Quant y a \ ~u -> VPi x (b u) \ ~v -> c (transportInv j (VPair u v))
          k = i <> piCongL j <> Curry
      pure (q, k, mctx)
    q -> pure (q, i, mctx)

--------------------------------------------------------------------------------
-- Unification modulo type isomorphism

unifyIso0 :: MetaCtx -> TopEnv -> Term -> Term -> [(Iso, MetaCtx)]
unifyIso0 mctx tenv t t' = do
  let v = eval mctx tenv [] t
      v' = eval mctx tenv [] t'
  (i, i', mctx) <- unifyIso mctx (initCtx tenv) v v'
  let j = i <> sym i'
  pure (j, mctx)

unifyIso :: MetaCtx -> Ctx -> Value -> Value -> [(Iso, Iso, MetaCtx)]
unifyIso mctx ctx t u = case (forceCS mctx ctx.convState t, forceCS mctx ctx.convState u) of
  (VBrave {}, _) -> []
  (_, VBrave {}) -> []
  (VPi x a b, VPi x' a' b') -> case ctx.convState of
    Rigid ->
      unifyPi mctx (ctx {convState = Flex}) (Quant x a b) (Quant x' a' b')
        <|> unifyPi mctx (ctx {convState = Full}) (Quant x a b) (Quant x' a' b')
    _ -> unifyPi mctx ctx (Quant x a b) (Quant x' a' b')
  (VSigma x a b, VSigma x' a' b') -> case ctx.convState of
    Rigid ->
      unifySigma mctx (ctx {convState = Flex}) (Quant x a b) (Quant x' a' b')
        <|> unifySigma mctx (ctx {convState = Full}) (Quant x a b) (Quant x' a' b')
    _ -> unifySigma mctx ctx (Quant x a b) (Quant x' a' b')
  (VTop x sp Nothing, VTop x' sp' Nothing)
    | x == x' -> unifySpineRefl mctx ctx sp sp'
  (VTop x sp (Just t), VTop x' sp' (Just t')) -> case ctx.convState of
    Rigid
      | x == x' ->
          unifySpineRefl mctx (ctx {convState = Flex}) sp sp'
            <|> unifyIso mctx (ctx {convState = Full}) t t'
      | otherwise -> unifyIso mctx ctx t t'
    Flex
      | x == x' -> unifySpineRefl mctx ctx sp sp'
      | otherwise -> []
    Full -> impossible
  (VTop _ _ (Just t), t') -> case ctx.convState of
    Rigid -> unifyIso mctx ctx t t'
    Flex -> []
    _ -> impossible
  (t, VTop _ _ (Just t')) -> case ctx.convState of
    Rigid -> unifyIso mctx ctx t t'
    Flex -> []
    _ -> impossible
  (t, u) -> do
    mctx <- maybeToList $ unify mctx ctx.topEnv ctx.convState ctx.level t u
    pure (Refl, Refl, mctx)

unifySpineRefl :: MetaCtx -> Ctx -> Spine -> Spine -> [(Iso, Iso, MetaCtx)]
unifySpineRefl mctx ctx sp sp' = do
  mctx <- maybeToList $ unifySpine mctx ctx.topEnv ctx.convState ctx.level sp sp'
  pure (Refl, Refl, mctx)

unifyPi :: MetaCtx -> Ctx -> Quant -> Quant -> [(Iso, Iso, MetaCtx)]
unifyPi mctx ctx q q' = do
  let (Quant _ a b, i) = curryCS mctx ctx.convState q
  flip foldMapA (currySwap mctx ctx q') \(Quant _ a' b', i', mctx) -> do
    (ia, ia', mctx) <- unifyIso mctx ctx a a'
    let v = transportInv ia (VVar ctx.level)
        v' = transportInv ia' (VVar ctx.level)
    (ib, ib', mctx) <- unifyIso mctx (bind ctx) (b v) (b' v')
    let j = i <> piCongL ia <> piCongR ib
        j' = i' <> piCongL ia' <> piCongR ib'
    pure (j, j', mctx)

unifySigma :: MetaCtx -> Ctx -> Quant -> Quant -> [(Iso, Iso, MetaCtx)]
unifySigma mctx ctx q q' = do
  let (Quant _ a b, i) = assocCS mctx ctx.convState q
  flip foldMapA (assocSwap mctx ctx q') \(Quant _ a' b', i', mctx) -> do
    (ia, ia', mctx) <- unifyIso mctx ctx a a'
    let v = transportInv ia (VVar ctx.level)
        v' = transportInv ia' (VVar ctx.level)
    (ib, ib', mctx) <- unifyIso mctx (bind ctx) (b v) (b' v')
    let j = i <> sigmaCongL ia <> sigmaCongR ib
        j' = i' <> sigmaCongL ia' <> sigmaCongR ib'
    pure (j, j', mctx)

--------------------------------------------------------------------------------

data Locals
  = Here
  | Bind Locals Name ~Term

closeTy :: Locals -> Term -> Term
closeTy = \cases
  Here b -> b
  (Bind locs x a) b -> closeTy locs (Pi x a b)

closeTm :: Locals -> Term -> Term
closeTm = \cases
  Here t -> t
  (Bind locs x _) b -> closeTm locs (Lam x b)

check :: QName -> (Ctx, Locals) -> Value -> Value -> ImS.Stream (Iso, Term)
check h (ctx, locs) query item =
  ( do
      (item, inst, mctx) <- possibleInstantiation emptyMetaCtx (ctx, locs) item (VTop h SNil Nothing)
      (i, i', mctx) <- ImS.maybeToStream $ listToMaybe $ unifyIso mctx ctx query item
      guard $ allMetaSolved mctx
      let j = i <> sym i'
          ~sol = closeTm locs $ quote mctx ctx.level $ transportInv j inst
      pure (j, sol)
  )
    <|> ImS.Later case forceAll emptyMetaCtx query of
      VPi "_" _ _ -> empty
      VPi x a b -> do
        check h (bind ctx, Bind locs x (quote emptyMetaCtx ctx.level a)) (b $ VVar ctx.level) item
      _ -> empty

freshMeta :: MetaCtx -> Ctx -> Locals -> Value -> (Term, MetaCtx)
freshMeta mctx ctx locs a = do
  let ~closed = eval mctx ctx.topEnv [] $ closeTy locs (quote mctx ctx.level a)
      (m, mctx') = newMeta mctx closed
  (AppPruning (Meta m) (replicate (coerce ctx.level) True), mctx')

possibleInstantiation :: MetaCtx -> (Ctx, Locals) -> Value -> Value -> ImS.Stream (Value, Value, MetaCtx)
possibleInstantiation mctx (ctx, locs) a ~inst =
  pure (a, inst, mctx)
    <|> ImS.Later case forceAll mctx a of
      VPi "_" _ _ -> empty
      VPi _ a b -> do
        (m, mctx) <- pure $ freshMeta mctx ctx locs a
        let mv = eval mctx ctx.topEnv ctx.env m
        possibleInstantiation mctx (ctx, locs) (b mv) (inst $$ mv)
      _ -> empty
