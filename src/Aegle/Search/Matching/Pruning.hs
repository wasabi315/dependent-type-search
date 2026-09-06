module Aegle.Search.Matching.Pruning
  ( PartialRenaming (..),
    emptyPRen,
    idPRen,
    liftPRen,
    skipPRen,
    skipPRenN,
    rename,
    solveWithPren,
  )
where

import Aegle.Core.Evaluation
import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Prelude
import Data.IntMap.Strict qualified as IM
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Partial renaming and pruning

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
  deriving stock (Generic)

emptyPRen :: PartialRenaming
emptyPRen =
  PRen
    { occ = Nothing,
      dom = 0,
      cod = 0,
      ren = mempty
    }

idPRen :: Level -> PartialRenaming
idPRen l =
  PRen
    { occ = Nothing,
      dom = l,
      cod = l,
      ren = IM.fromDistinctAscList $ map (coerce &&& id) [0 .. l - 1]
    }

-- | @(σ : PRen Γ Δ) → PRen (Γ, x : A[σ]) (Δ, x : A)@.
liftPRen :: PartialRenaming -> PartialRenaming
liftPRen PRen {..} =
  PRen
    { dom = dom + 1,
      cod = cod + 1,
      ren = IM.insert (coerce cod) dom ren,
      ..
    }
{-# INLINE liftPRen #-}

-- | @PRen Γ Δ → PRen Γ (Δ, x : A)@.
skipPRen :: PartialRenaming -> PartialRenaming
skipPRen PRen {..} = PRen {cod = cod + 1, ..}
{-# INLINE skipPRen #-}

skipPRenN :: Level -> PartialRenaming -> PartialRenaming
skipPRenN n PRen {..} = PRen {cod = cod + n, ..}
{-# INLINE skipPRenN #-}

-- Monad for pruning
type Prune = StateT MetaCtx Maybe

newMetaP :: Value -> Prune MetaVar
newMetaP ~mty = state $ flip newMeta mty
{-# INLINE newMetaP #-}

forceP :: Value -> Prune Value
forceP t = gets $ flip force t
{-# INLINE forceP #-}

evalP :: TopEnv -> Env -> Term -> Prune Value
evalP tenv env t = gets \mctx -> eval tenv mctx env t
{-# INLINE evalP #-}

lookupUnsolvedP :: MetaVar -> Prune Value
lookupUnsolvedP m = gets $ flip lookupUnsolved m
{-# INLINE lookupUnsolvedP #-}

writeMetaP :: MetaVar -> Value -> Value -> Prune ()
writeMetaP m t ~a = modify' \mctx -> writeMeta mctx m t a
{-# INLINE writeMetaP #-}

-- | Remove some arguments from a closed iterated Pi type.
pruneType :: TopEnv -> RevPruning -> VType -> Prune Term
pruneType tenv (RevPruning pr) a = go pr emptyPRen a
  where
    go pr pren a = do
      a <- forceP a
      case (pr, a) of
        ([], a) -> renameP tenv pren a
        (True : pr, VPi x a b) ->
          Pi x
            <$> renameP tenv pren a
            <*> go pr (liftPRen pren) (b $ VVar pren.cod)
        (False : pr, VPi _ _ b) ->
          go pr (skipPRen pren) (b $ VVar pren.cod)
        _ -> empty

-- | Prune arguments from a meta, return new meta + pruned type.
pruneMeta :: TopEnv -> Pruning -> MetaVar -> Prune MetaVar
pruneMeta tenv pr m = do
  mty <- lookupUnsolvedP m
  prunedty <- evalP tenv [] =<< pruneType tenv (revPruning pr) mty
  m' <- newMetaP prunedty
  solution <- evalP tenv [] =<< lams (Level $ length pr) mty (AppPruning (Meta m') pr)
  writeMetaP m solution mty
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
pruneVFlex :: TopEnv -> PartialRenaming -> MetaVar -> Spine -> Prune Term
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

rename :: TopEnv -> MetaCtx -> PartialRenaming -> Value -> Maybe (Term, MetaCtx)
rename tenv mctx pren t = flip runStateT mctx $ renameP tenv pren t
{-# INLINE rename #-}

renameP :: TopEnv -> PartialRenaming -> Value -> Prune Term
renameP tenv pren t =
  forceP t >>= \case
    VFlex m' sp -> case pren.occ of
      Just m | m == m' -> empty -- occurs check
      _ -> pruneVFlex tenv pren m' sp
    VRigid (Level x) sp -> case IM.lookup x pren.ren of
      Nothing -> empty -- scope error ("escaping variable" error)
      Just x' -> renameSpine tenv pren (Var $ levelToIndex pren.dom x') sp
    VOpaque x sp -> renameSpine tenv pren (Opaque x) sp
    VAmb x sp _ _ -> renameSpine tenv pren (Amb x) sp
    VU -> pure U
    VPi x a b ->
      Pi x
        <$> renameP tenv pren a
        <*> renameP tenv (liftPRen pren) (b $ VVar pren.cod)
    VLam x t ->
      Lam x <$> renameP tenv (liftPRen pren) (t $ VVar pren.cod)
    VSigma x a b ->
      Sigma x
        <$> renameP tenv pren a
        <*> renameP tenv (liftPRen pren) (b $ VVar pren.cod)
    VPair t u ->
      Pair <$> renameP tenv pren t <*> renameP tenv pren u
    VBrave {} -> empty

renameSpine :: TopEnv -> PartialRenaming -> Term -> Spine -> Prune Term
renameSpine tenv pren t = \case
  SNil -> pure t
  SApp sp u -> App <$> renameSpine tenv pren t sp <*> renameP tenv pren u
  SProj1 sp -> Proj1 <$> renameSpine tenv pren t sp
  SProj2 sp -> Proj2 <$> renameSpine tenv pren t sp

-- | Wrap a term in Level number of lambdas. We get the domain info from the Value
--   argument.
lams :: Level -> Value -> Term -> Prune Term
lams l a t = StateT \mctx -> (,mctx) <$> go mctx a (0 :: Level)
  where
    go _ _ (l' :: Level) | l' == l = Just t
    go mctx a l' = case force mctx a of
      VPi "_" _ b -> do
        let x = coerce $ "x" <> T.map subscript (T.show l')
        Lam x <$> go mctx (b $ VVar l') (l' + 1)
      VPi x _ b ->
        Lam x <$> go mctx (b $ VVar l') (l' + 1)
      _ -> Nothing
{-# INLINE lams #-}

-- | Solve m given the result of inversion on a spine.
solveWithPren ::
  TopEnv -> MetaCtx -> MetaVar -> (PartialRenaming, Maybe Pruning) -> Value -> Maybe MetaCtx
solveWithPren tenv mctx m (pren, pruneNonLinear) rhs = flip execStateT mctx do
  mty <- lookupUnsolvedP m
  -- if the spine was non-linear, we check that the non-linear arguments
  -- can be pruned from the meta type (i.e. that the pruned solution will
  -- be well-typed)
  case pruneNonLinear of
    Nothing -> pure ()
    Just pr -> void $ pruneType tenv (revPruning pr) mty
  rhs <- renameP tenv (pren {occ = Just m}) rhs
  solution <- evalP tenv [] =<< lams pren.dom mty rhs
  writeMetaP m solution mty
