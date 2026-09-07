module Aegle.Search.Isomorphism
  ( transport,
    transportInv,
    curry,
    assoc,
    quoteIso,
  )
where

import Aegle.Core.Isomorphism (Iso (..), piCongL, piCongR, sigmaCongL, sigmaCongR)
import Aegle.Core.Name
import Aegle.Prelude
import Aegle.Search.Evaluation
import Aegle.Search.Term

--------------------------------------------------------------------------------
-- Transport

-- transport along an isomorphism
transport :: Iso -> Value -> Value
transport i v = case i of
  Refl -> v
  Sym i -> transportInv i v
  Trans i j -> transport j (transport i v)
  Assoc -> vProj1 (vProj1 v) `VPair` (vProj2 (vProj1 v) `VPair` vProj2 v)
  Comm -> vProj2 v `VPair` vProj1 v
  SigmaSwap -> vProj1 (vProj2 v) `VPair` (vProj1 v `VPair` vProj2 (vProj2 v))
  Curry -> VLam "x" \x -> VLam "y" \y -> v $$ VPair x y
  PiSwap -> VLam "y" \y -> VLam "x" \x -> v $$ x $$ y
  PiCongL i -> VLam "x" \x -> v $$ transportInv i x
  PiCongR i -> VLam "x" \x -> transport i (v $$ x)
  SigmaCongL i -> transport i (vProj1 v) `VPair` vProj2 v
  SigmaCongR i -> vProj1 v `VPair` transport i (vProj2 v)

-- transport back
transportInv :: Iso -> Value -> Value
transportInv i v = case i of
  Refl -> v
  Sym i -> transport i v
  Trans i j -> transportInv i (transportInv j v)
  Assoc -> (vProj1 v `VPair` vProj1 (vProj2 v)) `VPair` vProj2 (vProj2 v)
  Comm -> vProj2 v `VPair` vProj1 v
  SigmaSwap -> vProj1 (vProj2 v) `VPair` (vProj1 v `VPair` vProj2 (vProj2 v))
  Curry -> VLam "p" \p -> v $$ vProj1 p $$ vProj2 p
  PiSwap -> VLam "x" \x -> VLam "y" \y -> v $$ y $$ x
  PiCongL i -> VLam "x" \x -> v $$ transport i x
  PiCongR i -> VLam "x" \x -> transportInv i (v $$ x)
  SigmaCongL i -> transportInv i (vProj1 v) `VPair` vProj2 v
  SigmaCongR i -> vProj1 v `VPair` transportInv i (vProj2 v)

--------------------------------------------------------------------------------

-- | Curry until the first domain becomes non-sigma.
curry :: MetaCtx -> VQuant -> (VQuant, Iso)
curry mctx = go Refl
  where
    go i (VQuant x a b) = case force mctx a of
      VSigma y a1 a2 ->
        go (i <> Curry) $ VQuant y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> (VQuant x a b, i)

-- | Right-nest until the first projection becomes non-sigma.
assoc :: MetaCtx -> VQuant -> (VQuant, Iso)
assoc mctx = go Refl
  where
    go i (VQuant x a b) = case force mctx a of
      VSigma y a1 a2 ->
        go (i <> Assoc) $ VQuant y a1 \ ~u -> VSigma x (a2 u) \ ~v -> b (VPair u v)
      a -> (VQuant x a b, i)

quoteIso :: MetaCtx -> Level -> Value -> (Term, Iso)
quoteIso mctx l = \case
  VPi x a b -> quoteIsoPi mctx l (VQuant x a b)
  VSigma x a b -> quoteIsoSigma mctx l (VQuant x a b)
  v -> quote mctx l v // mempty

quoteIsoPi :: MetaCtx -> Level -> VQuant -> (Term, Iso)
quoteIsoPi mctx l q = do
  let (VQuant x a b, i) = curry mctx q
      (ta, ia) = quoteIso mctx l a
      (tb, ib) = quoteIso mctx (l + 1) $ b (transportInv ia (VVar l))
  Pi x ta tb // i <> piCongL ia <> piCongR ib

quoteIsoSigma :: MetaCtx -> Level -> VQuant -> (Term, Iso)
quoteIsoSigma mctx l q = do
  let (VQuant x a b, i) = assoc mctx q
      (ta, ia) = quoteIso mctx l a
      (tb, ib) = quoteIso mctx (l + 1) $ b (transportInv ia (VVar l))
  Sigma x ta tb // i <> sigmaCongL ia <> sigmaCongR ib
