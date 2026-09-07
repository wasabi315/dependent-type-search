module Aegle.Core.Isomorphism
  ( Iso (..),
    sym,
    piCongL,
    piCongR,
    sigmaCongL,
    sigmaCongR,
    transport,
    transportInv,
    curry,
    assoc,
    quoteIso,
  )
where

import Aegle.Core.Evaluation
import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Prelude

--------------------------------------------------------------------------------
-- Isomorphisms

data Iso
  = --  -------
    --   A ~ A
    Refl
  | --   A ~ B
    --  -------
    --   B ~ A
    Sym Iso
  | --   A ~ B    B ~ C
    --  ----------------
    --       A ~ C
    Trans Iso Iso
  | --  ----------------------------------------------------------------
    --   (x : (y : A) * B[y]) * C[x] ~ (y : A) * (x : B[y]) * C[(x, y)]
    Assoc
  | --  ---------------
    --   A * B ~ B * A
    Comm
  | -- ---------------------------------------------
    --  (x : A) * (y : B) * C ~ (y : B) * (x : A) * C
    --
    -- derivable from comm and assoc
    SigmaSwap
  | --  -------------------------------------------------------------------
    --   (x : (y : A) * B[y]) -> C[x] ~ (y : A) -> (x : B[y]) -> C[(x, y)]
    Curry
  | -- ---------------------------------------------
    --  (x : A) (y : B) -> C ~ (y : B) (x : A) -> C
    --
    -- derivable from comm and curry
    PiSwap
  | --                     i : A ~ A'
    --  ---------------------------------------------------
    --   (x : A) -> B[x] ~ (x : A') -> B[transportInv i x]
    PiCongL Iso
  | --             B[x] ~ B'[x]
    --  ------------------------------------
    --   (x : A) -> B[x] ~ (x : A) -> B'[x]
    PiCongR Iso
  | --                     i : A ~ A'
    --  -------------------------------------------------
    --   (x : A) * B[x] ~ (x : A') * B[transportInv i x]
    SigmaCongL Iso
  | --           B[x] ~ B'[x]
    --  ----------------------------------
    --   (x : A) * B[x] ~ (x : A) * B'[x]
    SigmaCongR Iso
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (NFData)

instance Semigroup Iso where
  (<>) = \cases
    Refl j -> j
    i Refl -> i
    i j -> Trans i j
  {-# INLINE (<>) #-}

instance Monoid Iso where
  mempty = Refl
  {-# INLINE mempty #-}

sym :: Iso -> Iso
sym = \case
  Refl -> Refl
  Sym i -> i
  i -> Sym i
{-# INLINE sym #-}

piCongL :: Iso -> Iso
piCongL = \case
  Refl -> Refl
  i -> PiCongL i
{-# INLINE piCongL #-}

piCongR :: Iso -> Iso
piCongR = \case
  Refl -> Refl
  i -> PiCongR i
{-# INLINE piCongR #-}

sigmaCongL :: Iso -> Iso
sigmaCongL = \case
  Refl -> Refl
  i -> SigmaCongL i
{-# INLINE sigmaCongL #-}

sigmaCongR :: Iso -> Iso
sigmaCongR = \case
  Refl -> Refl
  i -> SigmaCongR i
{-# INLINE sigmaCongR #-}

--------------------------------------------------------------------------------
-- Transport

-- | transport a value @v : A@ along an isomorphism @i : A ~ B@
transport :: Iso -> Value -> Value
transport = \cases
  Refl v -> v
  (Sym i) v -> transportInv i v
  (Trans i j) v -> transport j (transport i v)
  Assoc ((u :* v) :* w) -> u :* v :* w
  Comm (u :* v) -> v :* u
  SigmaSwap (u :* v :* w) -> v :* u :* w
  Curry v -> VLam "x" \x -> VLam "y" \y -> v $$ (x :* y)
  PiSwap v -> VLam "y" \y -> VLam "x" \x -> v $$ x $$ y
  (PiCongL i) v -> VLam "x" \x -> v $$ transportInv i x
  (PiCongR i) v -> VLam "x" \x -> transport i (v $$ x)
  (SigmaCongL i) (u :* v) -> transport i u :* v
  (SigmaCongR i) (u :* v) -> u `VPair` transport i v

-- | transport back a value @v : B@ along an isomorphism @i : A ~ B@
transportInv :: Iso -> Value -> Value
transportInv = \cases
  Refl v -> v
  (Sym i) v -> transport i v
  (Trans i j) v -> transportInv i (transportInv j v)
  Assoc (u :* v :* w) -> (u :* v) :* w
  Comm (u :* v) -> v :* u
  SigmaSwap (u :* v :* w) -> v :* u :* w
  Curry v -> VLam "p" \(x :* y) -> v $$ x $$ y
  PiSwap v -> VLam "x" \x -> VLam "y" \y -> v $$ y $$ x
  (PiCongL i) v -> VLam "x" \x -> v $$ transport i x
  (PiCongR i) v -> VLam "x" \x -> transportInv i (v $$ x)
  (SigmaCongL i) (u :* v) -> transportInv i u `VPair` v
  (SigmaCongR i) (u :* v) -> u `VPair` transportInv i v

--------------------------------------------------------------------------------

-- | Curry until the first domain becomes non-sigma.
curry :: VQuant -> (VQuant, Iso)
curry = go Refl
  where
    go i (VQuant x a b) = case a of
      VSigma y a1 a2 ->
        go (i <> Curry) $ VQuant y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> (VQuant x a b, i)

-- | Right-nest until the first projection becomes non-sigma.
assoc :: VQuant -> (VQuant, Iso)
assoc = go Refl
  where
    go i (VQuant x a b) = case a of
      VSigma y a1 a2 ->
        go (i <> Assoc) $ VQuant y a1 \ ~u -> VSigma x (a2 u) \ ~v -> b (VPair u v)
      a -> (VQuant x a b, i)

quoteIso :: Level -> Value -> (Term, Iso)
quoteIso l = \case
  VPi x a b -> quoteIsoPi l (VQuant x a b)
  VSigma x a b -> quoteIsoSigma l (VQuant x a b)
  v -> quote l v // mempty

quoteIsoPi :: Level -> VQuant -> (Term, Iso)
quoteIsoPi l pi = do
  let (VQuant x a b, i) = curry pi
      (ta, ia) = quoteIso l a
      (tb, ib) = quoteIso (l + 1) $ b (transportInv ia (VVar l))
  Pi x ta tb // i <> piCongL ia <> piCongR ib

quoteIsoSigma :: Level -> VQuant -> (Term, Iso)
quoteIsoSigma l sig = do
  let (VQuant x a b, i) = assoc sig
      (ta, ia) = quoteIso l a
      (tb, ib) = quoteIso (l + 1) $ b (transportInv ia (VVar l))
  Sigma x ta tb // i <> sigmaCongL ia <> sigmaCongR ib
