module TypeSearch.Unification where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Data.HashMap.Strict qualified as HM
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Maybe
import Data.String
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Term

-- This file contains an implementation of pattern unification with pruning.
-- The implementation is embarrassingly based on András Kovács's
-- elaboration-zoo/05-pruning and smalltt.

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
  Solved {} -> impossible

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
        _ -> impossible

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

renameSpine :: TopEnv -> PartialRenaming -> Term -> Spine -> P Term
renameSpine tenv pren t = \case
  SNil -> pure t
  SApp sp u -> App <$> renameSpine tenv pren t sp <*> renameP tenv pren u
  SProj1 sp -> Proj1 <$> renameSpine tenv pren t sp
  SProj2 sp -> Proj2 <$> renameSpine tenv pren t sp

-- | Wrap a term in Level number of lambdas. We get the domain info from the Value
--   argument.
lams :: Level -> Value -> Term -> P Term
lams l a t = gets \mctx -> do
  let go _ (l' :: Level) | l' == l = t
      go a l' = case force mctx a of
        VPi "_" _ b ->
          Lam (fromString $ "x" ++ show l') $
            go (b $ VVar l') (l' + 1)
        VPi x _ b ->
          Lam x $ go (b $ VVar l') (l' + 1)
        _ -> impossible
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
