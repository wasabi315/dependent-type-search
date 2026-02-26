module TypeSearch.Unification where

import Control.Applicative
import Control.Monad
import Data.Coerce
import Data.HashMap.Strict qualified as HM
import Data.IntMap.Strict qualified as IM
import Data.Maybe
import Data.String
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Term

{-

This file contains an implementation of untyped pattern unification.
The algorithm is the same as the one in András Kovács's elaboration-zoo/03-holes
except that we don't use global mutable metacontext.

-}

--------------------------------------------------------------------------------

data PartialRenaming = PRen
  { dom :: Level,
    cod :: Level,
    ren :: IM.IntMap Level
  }

lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (coerce cod) dom ren)

invert :: MetaCtx -> Level -> Spine -> Maybe PartialRenaming
invert mctx gamma sp = do
  let go = \case
        SNil -> pure (0, mempty)
        SApp sp t -> do
          (dom, ren) <- go sp
          case force mctx t of
            VVar (Level x)
              | IM.notMember x ren ->
                  pure (dom + 1, IM.insert x dom ren)
            _ -> Nothing
        SFst _ -> Nothing
        SSnd _ -> Nothing
  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

rename :: MetaCtx -> MetaVar -> PartialRenaming -> Value -> Maybe Term
rename mctx m pren v = go pren v
  where
    go pren t = case force mctx t of
      VFlex m' sp
        | m == m' -> Nothing -- occurs check
        | otherwise -> goSpine pren (Meta m') sp
      VRigid (Level x) sp -> case IM.lookup x pren.ren of
        Nothing -> Nothing -- scope error ("escaping variable" error)
        Just x' -> goSpine pren (Var $ levelToIndex pren.dom x') sp
      VTop x f sp _ -> goSpine pren (Top x (coerce f)) sp
      VU -> pure U
      VPi x a b -> Pi x <$> go pren a <*> go (lift pren) (b $ VVar pren.cod)
      VLam x t -> Lam x <$> go (lift pren) (t $ VVar pren.cod)
      VSigma x a b -> Sigma x <$> go pren a <*> go (lift pren) (b $ VVar pren.cod)
      VPair t u -> Pair <$> go pren t <*> go pren u

    goSpine pren t = \case
      SNil -> pure t
      SApp sp u -> App <$> goSpine pren t sp <*> go pren u
      SFst sp -> Fst <$> goSpine pren t sp
      SSnd sp -> Snd <$> goSpine pren t sp

lams :: Level -> Term -> Term
lams l = go 0
  where
    go x t
      | x == l = t
      | otherwise = Lam (fromString $ "x" ++ show (x + 1)) $ go (x + 1) t

solve :: MetaCtx -> Level -> MetaVar -> Spine -> Value -> Maybe MetaCtx
solve mctx gamma m sp rhs = do
  pren <- invert mctx gamma sp
  rhs <- rename mctx m pren rhs
  let solution = eval mctx [] $ lams pren.dom rhs
      mctx' = mctx {metaCtx = HM.insert m (Solved solution) mctx.metaCtx}
  Just mctx'

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

unfold :: Value -> Value
unfold = \case
  VTop _ _ _ (Just t) -> t
  t -> t

unifySpine :: MetaCtx -> ConvState -> Level -> Spine -> Spine -> Maybe MetaCtx
unifySpine mctx cs l = \cases
  SNil SNil -> pure mctx
  (SApp sp t) (SApp sp' t') -> do
    mctx <- unifySpine mctx cs l sp sp'
    unify mctx cs l t t'
  (SFst sp) (SFst sp') -> unifySpine mctx cs l sp sp'
  (SSnd sp) (SSnd sp') -> unifySpine mctx cs l sp sp'
  _ _ -> Nothing
