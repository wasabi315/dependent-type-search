module TypeSearch.Unification where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Data.Coerce
import Data.HashMap.Strict qualified as HM
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Maybe
import Data.String
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Term

--------------------------------------------------------------------------------

data PartialRenaming = PRen
  { occ :: Maybe MetaVar,
    dom :: Level,
    cod :: Level,
    ren :: IM.IntMap Level
  }

liftPren :: PartialRenaming -> PartialRenaming
liftPren (PRen occ dom cod ren) =
  PRen occ (dom + 1) (cod + 1) (IM.insert (coerce cod) dom ren)

skipPren :: PartialRenaming -> PartialRenaming
skipPren (PRen occ dom cod ren) = PRen occ dom (cod + 1) ren

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
        SFst {} -> Nothing
        SSnd {} -> Nothing

  (dom, ren, nlvars, fsp) <- go sp

  let mask = map \(Level x) -> IS.notMember x nlvars

  pure (PRen Nothing dom gamma ren, mask fsp <$ guard (not $ IS.null nlvars))

type P = StateT MetaCtx Maybe

newMeta :: MetaCtx -> Value -> (MetaVar, MetaCtx)
newMeta mctx ~mty = do
  let m' = Gen mctx.nextMeta
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

evalP :: Env -> Term -> P Value
evalP env t = gets \mctx -> eval mctx env t

lookupUnsolved :: MetaVar -> P Value
lookupUnsolved m = gets \mctx -> case mctx.metaCtx HM.! m of
  Unsolved a -> a
  Solved {} -> impossible

solveMeta :: MetaVar -> Value -> Value -> P ()
solveMeta m t ~a = modify' \mctx ->
  mctx {metaCtx = HM.insert m (Solved t a) mctx.metaCtx}

pruneType :: RevPruning -> Value -> P Term
pruneType (RevPruning pr) a =
  go pr (PRen Nothing 0 0 mempty) a
  where
    go pr pren a = do
      a <- forceP a
      case (pr, a) of
        ([], a) -> rename pren a
        (True : pr, VPi x a b) ->
          Pi x
            <$> rename pren a
            <*> go pr (liftPren pren) (b $ VVar pren.cod)
        (False : pr, VPi _ _ b) ->
          go pr (skipPren pren) (b $ VVar pren.cod)
        _ -> impossible

pruneMeta :: Pruning -> MetaVar -> P MetaVar
pruneMeta pr m = do
  mty <- lookupUnsolved m
  prunedty <- evalP [] =<< pruneType (revPruning pr) mty
  m' <- newMetaP prunedty
  solution <- evalP [] =<< lams (Level $ length pr) mty (AppPruning (Meta m') pr)
  solveMeta m solution mty
  pure m'

data SpinePruneStatus
  = OKRenaming
  | OKNonRenaming
  | NeedsPruning

pruneVFlex :: PartialRenaming -> MetaVar -> Spine -> P Term
pruneVFlex pren m sp = do
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
                  t <- rename pren t
                  pure (Just t : sp, OKNonRenaming)
          _ -> empty
    go sp

  m' <- case status of
    OKRenaming -> pure m
    OKNonRenaming -> pure m
    NeedsPruning -> pruneMeta (isJust <$> sp) m

  let t = foldr (\mu t -> maybe t (App t) mu) (Meta m') sp
  pure t

rename :: PartialRenaming -> Value -> P Term
rename pren t =
  forceP t >>= \case
    VFlex m' sp -> case pren.occ of
      Just m | m == m' -> empty -- occurs check
      _ -> pruneVFlex pren m' sp
    VRigid (Level x) sp -> case IM.lookup x pren.ren of
      Nothing -> empty -- scope error ("escaping variable" error)
      Just x' -> renameSpine pren (Var $ levelToIndex pren.dom x') sp
    VTop x f sp _ -> renameSpine pren (Top x (coerce f)) sp
    VU -> pure U
    VPi x a b ->
      Pi x
        <$> rename pren a
        <*> rename (liftPren pren) (b $ VVar pren.cod)
    VLam x t ->
      Lam x <$> rename (liftPren pren) (t $ VVar pren.cod)
    VSigma x a b ->
      Sigma x
        <$> rename pren a
        <*> rename (liftPren pren) (b $ VVar pren.cod)
    VPair t u ->
      Pair <$> rename pren t <*> rename pren u

renameSpine :: PartialRenaming -> Term -> Spine -> P Term
renameSpine pren t = \case
  SNil -> pure t
  SApp sp u -> App <$> renameSpine pren t sp <*> rename pren u
  SFst sp -> Fst <$> renameSpine pren t sp
  SSnd sp -> Snd <$> renameSpine pren t sp

lams :: Level -> Value -> Term -> P Term
lams l a t = gets \mctx -> do
  let go _ (l' :: Level) | l' == l = t
      go a l' = case force mctx a of
        VPi "_" _ b ->
          Lam (fromString $ "x" ++ show l') $
            go (b $ VVar l') (l' + 1)
        VPi x _ b ->
          Lam x $ go (b $ VVar l') (l' + 1)
        _ -> error "impossible"
  go a (0 :: Level)

solve :: MetaCtx -> Level -> MetaVar -> Spine -> Value -> Maybe MetaCtx
solve mctx gamma m sp rhs = do
  pren <- invert mctx gamma sp
  solveWithPren mctx m pren rhs

solveWithPren ::
  MetaCtx -> MetaVar -> (PartialRenaming, Maybe Pruning) -> Value -> Maybe MetaCtx
solveWithPren mctx m (pren, pruneNonLinear) rhs = flip execStateT mctx do
  mty <- lookupUnsolved m
  case pruneNonLinear of
    Nothing -> pure ()
    Just pr -> void $ pruneType (revPruning pr) mty
  rhs <- rename (pren {occ = Just m}) rhs
  solution <- evalP [] =<< lams pren.dom mty rhs
  solveMeta m solution mty

--------------------------------------------------------------------------------

data ConvState
  = Rigid
  | Flex
  | Full
  deriving stock (Show, Eq, Ord)

unify0 :: MetaCtx -> Term -> Term -> Maybe MetaCtx
unify0 mctx t t' = do
  let v = eval mctx [] t
      v' = eval mctx [] t'
  unify mctx Rigid 0 v v'

unify :: MetaCtx -> ConvState -> Level -> Value -> Value -> Maybe MetaCtx
unify mctx cs l t t' = case (force mctx t, force mctx t') of
  (VPi _ a b, VPi _ a' b') -> do
    mctx <- unify mctx cs l a a'
    unify mctx cs (l + 1) (b $ VVar l) (b' $ VVar l)
  (VU, VU) -> pure mctx
  (VLam _ t, VLam _ t') ->
    unify mctx cs (l + 1) (t $ VVar l) (t' $ VVar l)
  (t, VLam _ t') ->
    unify mctx cs (l + 1) (t $$ VVar l) (t' $ VVar l)
  (VLam _ t, t') ->
    unify mctx cs (l + 1) (t $ VVar l) (t' $$ VVar l)
  (VSigma _ a b, VSigma _ a' b') -> do
    mctx <- unify mctx cs l a a'
    unify mctx cs (l + 1) (b $ VVar l) (b' $ VVar l)
  (VPair t u, VPair t' u') -> do
    mctx <- unify mctx cs l t t'
    unify mctx cs l u u'
  (VPair t u, t') -> do
    mctx <- unify mctx cs l t (vFst t')
    unify mctx cs l u (vSnd t')
  (t, VPair t' u') -> do
    mctx <- unify mctx cs l (vFst t) t'
    unify mctx cs l (vSnd t) u'
  (VRigid x sp, VRigid x' sp')
    | x == x' -> unifySpine mctx cs l sp sp'
  (VFlex m sp, VFlex m' sp')
    | m == m' -> unifySpine mctx cs l sp sp'
    | otherwise -> do
        guard $ cs /= Flex
        flexFlex mctx l m sp m' sp'
  (t@(VTop x _ sp ft), t'@(VTop x' _ sp' ft')) -> case cs of
    Rigid
      | x == x' ->
          unifySpine mctx Flex l sp sp'
            <|> unify mctx Full l (unfold t) (unfold t')
      | otherwise -> unify mctx Rigid l (unfold t) (unfold t')
    Flex
      | x == x' -> unifySpine mctx Flex l sp sp'
      | otherwise -> Nothing
    Full
      | x == x' && isNothing ft && isNothing ft' ->
          unifySpine mctx Full l sp sp'
      | otherwise -> unify mctx Full l (unfold t) (unfold t')
  (VFlex m sp, t') -> do
    guard $ cs /= Flex
    solve mctx l m sp t'
  (t, VFlex m' sp') -> do
    guard $ cs /= Flex
    solve mctx l m' sp' t
  (VTop _ _ _ t, t') -> case cs of
    Flex -> Nothing
    _
      | Just t <- t -> unify mctx cs l t t'
      | otherwise -> Nothing
  (t, VTop _ _ _ t') -> case cs of
    Flex -> Nothing
    _
      | Just t' <- t' -> unify mctx cs l t t'
      | otherwise -> Nothing
  _ -> Nothing

unifySpine :: MetaCtx -> ConvState -> Level -> Spine -> Spine -> Maybe MetaCtx
unifySpine mctx cs l = \cases
  SNil SNil -> pure mctx
  (SApp sp t) (SApp sp' t') -> do
    mctx <- unifySpine mctx cs l sp sp'
    unify mctx cs l t t'
  (SFst sp) (SFst sp') -> unifySpine mctx cs l sp sp'
  (SSnd sp) (SSnd sp') -> unifySpine mctx cs l sp sp'
  _ _ -> Nothing

unfold :: Value -> Value
unfold = \case
  VTop _ _ _ (Just t) -> t
  t -> t

spineLength :: Spine -> Int
spineLength = \case
  SNil -> 0
  SApp sp _ -> 1 + spineLength sp
  SFst sp -> spineLength sp
  SSnd sp -> spineLength sp

flexFlex :: MetaCtx -> Level -> MetaVar -> Spine -> MetaVar -> Spine -> Maybe MetaCtx
flexFlex mctx gamma m sp m' sp' = do
  let go m sp m' sp' = case invert mctx gamma sp of
        Nothing -> solve mctx gamma m' sp' (VFlex m sp)
        Just pren -> solveWithPren mctx m pren (VFlex m' sp')
  if spineLength sp < spineLength sp'
    then go m' sp' m sp
    else go m sp m' sp'
