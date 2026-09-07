module Aegle.Search.Matching
  ( match0,
    match,
  )
where

import Aegle.Core.Name
import Aegle.Prelude
import Aegle.Search.Evaluation
import Aegle.Search.Matching.Pruning
import Aegle.Search.Term
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Set qualified as S

--------------------------------------------------------------------------------
-- Solving flex/rigid

-- Flex/rigid

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

-- | Solve @Γ ⊢ m spine =? rhs@.
solve :: MetaCtx -> Level -> MetaVar -> Spine -> Value -> Maybe MetaCtx
solve mctx gamma m sp rhs = do
  pren <- invert mctx gamma sp
  solveWithPren mctx m pren rhs

--------------------------------------------------------------------------------

match0 :: MetaCtx -> "pat" :! Term -> "term" :! Term -> [MetaCtx]
match0 mctx (Arg p) (Arg t) = do
  let vp = eval mctx [] p
      vt = eval mctx [] t
  match mctx 0 ! #pat vp ! #term vt

match :: MetaCtx -> Level -> "pat" :! Value -> "term" :! Value -> [MetaCtx]
match mctx l (Arg p) (Arg t) = case (force mctx p, force mctx t) of
  (_, VNe (HFlex _) _) -> error "match: metavariable in term"
  (VBrave {}, _) -> []
  (_, VBrave {}) -> []
  (VPi _ pa pb, VPi _ a b) -> do
    mctx <- match mctx l ! #pat pa ! #term a
    match mctx (l + 1) ! #pat (pb $ VVar l) ! #term (b $ VVar l)
  (VU, VU) -> pure mctx
  (VLam _ pt, VLam _ t) ->
    match mctx (l + 1) ! #pat (pt $ VVar l) ! #term (t $ VVar l)
  (p, VLam _ pt) ->
    match mctx (l + 1) ! #pat (p $$ VVar l) ! #term (pt $ VVar l)
  (VLam _ pt, t) ->
    match mctx (l + 1) ! #pat (pt $ VVar l) ! #term (t $$ VVar l)
  (VSigma _ pa pb, VSigma _ a b) -> do
    mctx <- match mctx l ! #pat pa ! #term a
    match mctx (l + 1) ! #pat (pb $ VVar l) ! #term (b $ VVar l)
  (VPair pt pu, VPair t u) -> do
    mctx <- match mctx l ! #pat pt ! #term t
    match mctx l ! #pat pu ! #term u
  (VPair pt pu, t) -> do
    mctx <- match mctx l ! #pat pt ! #term (vProj1 t)
    match mctx l ! #pat pu ! #term (vProj2 t)
  (pt, VPair t u) -> do
    mctx <- match mctx l ! #pat (vProj1 pt) ! #term t
    match mctx l ! #pat (vProj2 pt) ! #term u
  (VNe ph@(HRigid {}; HOpaque {}) psp, VNe h sp)
    | ph == h -> matchSpine mctx l ! #pat psp ! #term sp
  (VNe (HFlex m) psp, t) -> maybeToList $ solve mctx l m psp t
  (VNe (HAmb px) psp, VNe (HOpaque x) sp)
    | Unresolved pxs [] <- lookupResol mctx px,
      x `S.member` pxs -> do
        let mctx' = resolveOpaque mctx px x
        matchSpine mctx' l ! #pat psp ! #term sp
  -- we don't take intersection of possible name sets currently
  (VNe (HAmb px) psp, VNe (HAmb x) sp)
    | px == x,
      Unresolved _ [] <- lookupResol mctx px ->
        matchSpine mctx l ! #pat psp ! #term sp
  (VNe (HAmb px) psp, t)
    | Unresolved pxs pts@(_ : _) <- lookupResol mctx px -> do
        (p, mctx) <- chooseAmb mctx px psp pxs pts
        match mctx l ! #pat p ! #term t
  (VNe (HOpaque px) psp, VNe (HAmb x) sp)
    | Unresolved xs [] <- lookupResol mctx x,
      px `S.member` xs -> do
        let mctx' = resolveOpaque mctx x px
        matchSpine mctx' l ! #pat psp ! #term sp
  (p, VNe (HAmb x) sp)
    | Unresolved xs ts@(_ : _) <- lookupResol mctx x -> do
        (t, mctx) <- chooseAmb mctx x sp xs ts
        match mctx l ! #pat p ! #term t
  _ -> []

matchSpine :: MetaCtx -> Level -> "pat" :! Spine -> "term" :! Spine -> [MetaCtx]
matchSpine mctx l (Arg psp) (Arg sp) = case (psp, sp) of
  (SNil, SNil) -> pure mctx
  (SApp psp p, SApp sp t) -> do
    mctx <- matchSpine mctx l ! #pat psp ! #term sp
    match mctx l ! #pat p ! #term t
  (SProj1 psp, SProj1 sp) -> matchSpine mctx l ! #pat psp ! #term sp
  (SProj2 psp, SProj2 sp) -> matchSpine mctx l ! #pat psp ! #term sp
  _ -> []
