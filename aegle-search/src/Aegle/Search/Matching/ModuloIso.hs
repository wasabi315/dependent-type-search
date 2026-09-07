module Aegle.Search.Matching.ModuloIso
  ( matchIso0,
    matchIso,
    assocSwap,
    currySwap,
  )
where

import Aegle.Core.Isomorphism (Iso (..), piCongL, piCongR, sigmaCongL, sigmaCongR, sym)
import Aegle.Core.Name
import Aegle.Prelude
import Aegle.Search.Evaluation
import Aegle.Search.Isomorphism
import Aegle.Search.Matching
import Aegle.Search.Matching.Pruning
import Aegle.Search.Term

--------------------------------------------------------------------------------
-- Rewriting types

-- | Pick up a domain without breaking dependencies.
-- Assuming the given pi contains no metas.
pickUpDomain :: MetaCtx -> Level -> VQuant -> [(VQuant, Iso, MetaCtx)]
pickUpDomain mctx lvl (VQuant x a b) = (VQuant x a b, Refl, mctx) : go lvl b
  where
    idr = idPRen lvl
    ide = idEnv lvl

    go l c = case force mctx $ c (VVar l) of
      VPi y c1 c2 ->
        concat
          [ do
              let i = l - lvl
              -- Strengthen c1.
              -- TODO: we don't need pruning here
              (c1, mctx) <- maybeToList $ rename mctx (skipPRenN (i + 1) idr) c1
              let c1' = eval mctx ide c1
                  rest ~vc1 = VPi x a (instPiAt i vc1 . b)
                  s = swaps i
              pure (VQuant y c1' rest, s, mctx),
            go (l + 1) c2
          ]
      -- TODO: consider case where head is VAmb
      _ -> []

    instPiAt i ~v t = case (i, force mctx t) of
      (0, VPi _ _ b) -> b v
      (i, VPi x a b) -> VPi x a (instPiAt (i - 1) v . b)
      _ -> impossible "pickUpDomain.instPiAt"

    swaps = \case
      0 -> PiSwap
      n -> piCongR (swaps (n - 1)) <> PiSwap

-- | Pick up a projection without breaking dependencies.
-- Assuming the given sigma contains no metas.
pickUpProjection :: MetaCtx -> Level -> VQuant -> [(VQuant, Iso, MetaCtx)]
pickUpProjection mctx lvl (VQuant x a b) = (VQuant x a b, Refl, mctx) : go lvl b
  where
    idr = idPRen lvl
    ide = idEnv lvl

    go l c = case force mctx $ c (VVar l) of
      VSigma y c1 c2 ->
        concat
          [ do
              let i = l - lvl
              -- Strengthen c1.
              -- TODO: we don't need pruning here
              (c1, mctx) <- maybeToList $ rename mctx (skipPRenN (i + 1) idr) c1
              let c1' = eval mctx ide c1
                  rest ~vc1 = VSigma x a (instSigmaAt i vc1 . b)
                  s = swaps SigmaSwap i
              pure (VQuant y c1' rest, s, mctx),
            go (l + 1) c2
          ]
      -- TODO: consider case where head is VAmb
      c -> do
        let i = l - lvl
        (c, mctx) <- maybeToList $ rename mctx (skipPRenN (i + 1) idr) c
        let c' = eval mctx ide c
            rest ~_ = dropLastProj (l + 1) (VSigma x a b)
            s = swaps Comm i
        pure (VQuant "_" c' rest, s, mctx)

    instSigmaAt i ~v t = case (i, force mctx t) of
      (0, VSigma _ _ b) -> b v
      (i, VSigma x a b) -> VSigma x a (instSigmaAt (i - 1) v . b)
      _ -> impossible "pickUpProjection.instSigmaAt"

    dropLastProj l t = case force mctx t of
      VSigma x a b -> case b (VVar l) of
        VSigma {} -> VSigma x a (dropLastProj (l + 1) . b)
        _ -> a
      _ -> impossible "pickUpProjection.dropLastProj"

    swaps i = \case
      0 -> i
      n -> sigmaCongR (swaps i (n - 1)) <> SigmaSwap

-- | Pick a **non-sigma** projection without breaking dependencies.
-- This works even in the presence of arbitrarily nested sigmas in the type.
assocSwap :: MetaCtx -> Level -> VQuant -> [(VQuant, Iso, MetaCtx)]
assocSwap mctx lvl q = do
  -- Pick one projection first.
  (q, i, mctx) <- pickUpProjection mctx lvl q
  case q of
    -- When the selected projection is a sigma type, we invoke
    -- assocSwap recursively to make the first projection of the sigma non-sigma!
    -- TODO: Consider case when domain is VAmb
    VQuant x (VSigma y a b) c -> do
      (VQuant y a b, j, mctx) <- assocSwap mctx lvl (VQuant y a b)
      let -- Then associate to make the first projection non-sigma.
          -- Note the transport along j!
          q = VQuant y a \ ~u -> VSigma x (b u) \ ~v -> c (transportInv j (VPair u v))
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
currySwap :: MetaCtx -> Level -> VQuant -> [(VQuant, Iso, MetaCtx)]
currySwap mctx lvl q = do
  (q, i, mctx) <- pickUpDomain mctx lvl q
  case q of
    -- TODO: consider when domain is VAmb
    VQuant x (VSigma y a b) c -> do
      (VQuant y a b, j, mctx) <- assocSwap mctx lvl (VQuant y a b)
      let q = VQuant y a \ ~u -> VPi x (b u) \ ~v -> c (transportInv j (VPair u v))
          k = i <> piCongL j <> Curry
      pure (q, k, mctx)
    q -> pure (q, i, mctx)

--------------------------------------------------------------------------------
-- Matching modulo type isomorphism

matchIso0 :: MetaCtx -> "pat" :! Term -> "term" :! Term -> [(Iso, MetaCtx)]
matchIso0 mctx (Arg p) (Arg t) = do
  let vp = eval mctx [] p
      vt = eval mctx [] t
  (i, i', mctx) <- matchIso mctx 0 ! #pat vp ! #term vt
  let j = i <> sym i'
  pure (j, mctx)

matchIso :: MetaCtx -> Level -> "pat" :! Value -> "term" :! Value -> [(Iso, Iso, MetaCtx)]
matchIso mctx lvl (Arg p) (Arg t) = case (force mctx p, force mctx t) of
  (_, VNe (HFlex _) _) -> error "matchIso: metavariable in term"
  -- TODO: consider when p is VFlex
  -- (VFlex {}, t) -> ???
  (VBrave {}, _) -> []
  (_, VBrave {}) -> []
  (VPi px pa pb, VPi x a b) ->
    matchPi mctx lvl ! #pat (VQuant px pa pb) ! #term (VQuant x a b)
  (VSigma px pa pb, VSigma x a b) ->
    matchSigma mctx lvl ! #pat (VQuant px pa pb) ! #term (VQuant x a b)
  (VNe (HAmb px) psp, t)
    | Unresolved pxs pts@(_ : _) <- lookupResol mctx px -> do
        (p, mctx) <- chooseAmb mctx px psp pxs pts
        matchIso mctx lvl ! #pat p ! #term t
  (p, VNe (HAmb x) sp)
    | Unresolved xs ts@(_ : _) <- lookupResol mctx x -> do
        (t, mctx) <- chooseAmb mctx x sp xs ts
        matchIso mctx lvl ! #pat p ! #term t
  (p, t) -> (Refl,Refl,) <$> match mctx lvl ! #pat p ! #term t

matchPi :: MetaCtx -> Level -> "pat" :! VQuant -> "term" :! VQuant -> [(Iso, Iso, MetaCtx)]
matchPi mctx lvl (Arg ppi) (Arg pi) = do
  -- TODO: consider case when pa is VAmb
  let (VQuant _ pa pb, i) = curry mctx ppi
  -- permutation on term side
  -- TODO: consider case where a is a flex term (can be a sigma, unblocks currying!)
  -- TODO: consider case where b is a flex term (can be a pi, unblocks permutation!)
  (VQuant _ a b, i', mctx) <- currySwap mctx lvl pi
  (ia, ia', mctx) <- matchIso mctx lvl ! #pat pa ! #term a
  let pv = transportInv ia (VVar lvl)
      v = transportInv ia' (VVar lvl)
  (ib, ib', mctx) <- matchIso mctx (lvl + 1) ! #pat (pb pv) ! #term (b v)
  let j = i <> piCongL ia <> piCongR ib
      j' = i' <> piCongL ia' <> piCongR ib'
  pure (j, j', mctx)

matchSigma :: MetaCtx -> Level -> "pat" :! VQuant -> "term" :! VQuant -> [(Iso, Iso, MetaCtx)]
matchSigma mctx lvl (Arg psig) (Arg sig) = do
  -- TODO: consider case when pa is VAmb
  let (VQuant _ pa pb, i) = assoc mctx psig
  -- permutation on term side
  -- TODO: consider case where a is a flex term (can be a sigma, unblocks assoc!)
  -- TODO: consider case where b is a flex term (can be a sigma, unblocks permutation!)
  (VQuant _ a b, i', mctx) <- assocSwap mctx lvl sig
  (ia, ia', mctx) <- matchIso mctx lvl ! #pat pa ! #term a
  let pv = transportInv ia (VVar lvl)
      v = transportInv ia' (VVar lvl)
  (ib, ib', mctx) <- matchIso mctx (lvl + 1) ! #pat (pb pv) ! #term (b v)
  let j = i <> sigmaCongL ia <> sigmaCongR ib
      j' = i' <> sigmaCongL ia' <> sigmaCongR ib'
  pure (j, j', mctx)
