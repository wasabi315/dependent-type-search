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
    normalise0,
    normalise,
  )
where

import Aegle.Core.Evaluation
import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Prelude
import Prettyprinter

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
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

instance Semigroup Iso where
  Refl <> j = j
  i <> Refl = i
  i <> j = Trans i j
  {-# INLINE (<>) #-}

instance Monoid Iso where
  mempty = Refl
  {-# INLINE mempty #-}

sym :: Iso -> Iso
sym = \case
  Refl -> Refl
  Sym i -> i
  Comm -> Comm
  SigmaSwap -> SigmaSwap
  PiSwap -> PiSwap
  i -> Sym i

piCongL :: Iso -> Iso
piCongL = \case
  Refl -> Refl
  i -> PiCongL i

piCongR :: Iso -> Iso
piCongR = \case
  Refl -> Refl
  i -> PiCongR i

sigmaCongL :: Iso -> Iso
sigmaCongL = \case
  Refl -> Refl
  i -> SigmaCongL i

sigmaCongR :: Iso -> Iso
sigmaCongR = \case
  Refl -> Refl
  i -> SigmaCongR i

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
curry :: MetaCtx -> Quant -> (Quant, Iso)
curry mctx = go Refl
  where
    go i (Quant x a b) = case force mctx a of
      VSigma y a1 a2 ->
        go (i <> Curry) $ Quant y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> (Quant x a b, i)

-- | Right-nest until the first projection becomes non-sigma.
assoc :: MetaCtx -> Quant -> (Quant, Iso)
assoc mctx = go Refl
  where
    go i (Quant x a b) = case force mctx a of
      VSigma y a1 a2 ->
        go (i <> Assoc) $ Quant y a1 \ ~u -> VSigma x (a2 u) \ ~v -> b (VPair u v)
      a -> (Quant x a b, i)

normalise0 :: MetaCtx -> Term -> (Term, Iso)
normalise0 mctx t = normalise mctx 0 (eval mctx [] t)

normalise :: MetaCtx -> Level -> Value -> (Term, Iso)
normalise mctx l = \case
  VPi x a b -> normalisePi mctx l (Quant x a b)
  VSigma x a b -> normaliseSigma mctx l (Quant x a b)
  v -> quote mctx l v // mempty

normalisePi :: MetaCtx -> Level -> Quant -> (Term, Iso)
normalisePi mctx l q = do
  let (Quant x a b, i) = curry mctx q
      (ta, ia) = normalise mctx l a
      (tb, ib) = normalise mctx (l + 1) $ b (transportInv ia (VVar l))
  Pi x ta tb // i <> piCongL ia <> piCongR ib

normaliseSigma :: MetaCtx -> Level -> Quant -> (Term, Iso)
normaliseSigma mctx l q = do
  let (Quant x a b, i) = assoc mctx q
      (ta, ia) = normalise mctx l a
      (tb, ib) = normalise mctx (l + 1) $ b (transportInv ia (VVar l))
  Sigma x ta tb // i <> sigmaCongL ia <> sigmaCongR ib

--------------------------------------------------------------------------------
-- Prettyprinting

instance Pretty Iso where
  pretty = goTrans
    where
      goTrans = \case
        Trans i j -> goTrans i <+> "·" <+> goTrans j
        i -> goCong i

      goCong = \case
        PiCongL i -> "ΠL" <+> goSym i
        PiCongR i -> "ΠR" <+> goSym i
        SigmaCongL i -> "ΣL" <+> goSym i
        SigmaCongR i -> "ΣR" <+> goSym i
        i -> goSym i

      goSym = \case
        Sym i -> goAtom i <+> "⁻¹"
        i -> goAtom i

      goAtom = \case
        Refl -> "refl"
        Assoc -> "Assoc"
        Comm -> "Comm"
        SigmaSwap -> "ΣSwap"
        Curry -> "Curry"
        PiSwap -> "ΠSwap"
        i -> parens (goTrans i)
