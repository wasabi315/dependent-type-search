module TypeSearch.UnificationModuloIso where

import Control.Applicative
import Data.Maybe
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Term
import TypeSearch.Unification
import Prelude hiding (curry)

--------------------------------------------------------------------------------
-- Rewriting types

data Quant = Quant Name Value (Value -> Value)

-- | Curry until the first domain becomes non-sigma
curry :: MetaCtx -> Quant -> (Quant, Iso)
curry mctx = go Refl
  where
    go i (Quant x a b) = case forceAll mctx a of
      VSigma y a1 a2 ->
        go (i <> Curry) $ Quant y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> (Quant x a b, i)

-- | Right-nest until the first projection becomes non-sigma
assoc :: MetaCtx -> Quant -> (Quant, Iso)
assoc mctx = go Refl
  where
    go i (Quant x a b) = case forceAll mctx a of
      VSigma y a1 a2 ->
        go (i <> Assoc) $ Quant y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> (Quant x a b, i)

-- | Pick a domain without breaking dependencies.
pickDomain :: MetaCtx -> Level -> Quant -> [(Quant, Iso, MetaCtx)]
pickDomain mctx l q = undefined

-- | Pick a projection without breaking dependencies.
pickProjection :: MetaCtx -> Level -> Quant -> [(Quant, Iso, MetaCtx)]
pickProjection mctx l q = undefined

-- | Pick a **non-sigma** projection without breaking dependencies.
-- This works even in the presence of arbitrarily nested sigmas in the type.
assocSwap :: MetaCtx -> Level -> Quant -> [(Quant, Iso, MetaCtx)]
assocSwap mctx l q = do
  -- Pick one projection first.
  (q, i, mctx) <- pickProjection mctx l q
  case q of
    -- When the selected projection is a sigma type, we invoke
    -- assocSwap recursively to make the first projection of the sigma non-sigma!
    Quant x (VSigma y a b) c -> do
      (Quant y a b, j, mctx) <- assocSwap mctx l (Quant y a b)
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
currySwap :: MetaCtx -> Level -> Quant -> [(Quant, Iso, MetaCtx)]
currySwap mctx l q = do
  (q, i, mctx) <- pickDomain mctx l q
  case q of
    Quant x (VSigma y a b) c -> do
      (Quant y a b, j, mctx) <- assocSwap mctx l (Quant y a b)
      let q = Quant y a \ ~u -> VPi x (b u) \ ~v -> c (transportInv j (VPair u v))
          k = i <> piCongL j <> Curry
      pure (q, k, mctx)
    q -> pure (q, i, mctx)

--------------------------------------------------------------------------------

unifyIso0 :: MetaCtx -> Term -> Term -> [(Iso, MetaCtx)]
unifyIso0 mctx t t' = do
  let v = eval mctx [] t
      v' = eval mctx [] t'
  (i, i', mctx) <- unifyIso mctx Rigid 0 v v'
  let j = i <> sym i'
  pure (j, mctx)

unifyIso :: MetaCtx -> ConvState -> Level -> Value -> Value -> [(Iso, Iso, MetaCtx)]
unifyIso mctx cs l t u = case (force mctx t, force mctx u) of
  (VPi x a b, VPi x' a' b') -> case cs of
    Rigid ->
      unifyPi mctx Flex l (Quant x a b) (Quant x' a' b')
        <|> unifyPiIso mctx l (Quant x a b) (Quant x' a' b')
    Flex -> unifyPi mctx Flex l (Quant x a b) (Quant x' a' b')
    Full -> unifyPiIso mctx l (Quant x a b) (Quant x' a' b')
  (VSigma x a b, VSigma x' a' b') -> case cs of
    Rigid ->
      unifySigma mctx Flex l (Quant x a b) (Quant x' a' b')
        <|> unifySigmaIso mctx l (Quant x a b) (Quant x' a' b')
    Flex -> unifySigma mctx Flex l (Quant x a b) (Quant x' a' b')
    Full -> unifySigmaIso mctx l (Quant x a b) (Quant x' a' b')
  (t@(VTop x _ sp ft), t'@(VTop x' _ sp' ft')) -> case cs of
    Rigid
      | x == x' ->
          unifySpineRefl mctx Flex l sp sp'
            <|> unifyIso mctx Full l (unfold t) (unfold t')
      | otherwise -> unifyIso mctx Rigid l (unfold t) (unfold t')
    Flex
      | x == x' -> unifySpineRefl mctx Flex l sp sp'
      | otherwise -> []
    Full
      | x == x' && isNothing ft && isNothing ft' ->
          unifySpineRefl mctx Full l sp sp'
      | otherwise -> unifyIso mctx Full l (unfold t) (unfold t')
  (VTop _ _ _ t, t') -> case cs of
    Flex -> []
    _
      | Just t <- t -> unifyIso mctx cs l t t'
      | otherwise -> []
  (t, VTop _ _ _ t') -> case cs of
    Flex -> []
    _
      | Just t' <- t' -> unifyIso mctx cs l t t'
      | otherwise -> []
  (t, u) -> do
    mctx <- maybeToList $ unify mctx cs l t u
    pure (Refl, Refl, mctx)

unifySpineRefl :: MetaCtx -> ConvState -> Level -> Spine -> Spine -> [(Iso, Iso, MetaCtx)]
unifySpineRefl mctx cs l sp sp' = do
  mctx <- maybeToList $ unifySpine mctx cs l sp sp'
  pure (Refl, Refl, mctx)

unifyPi :: MetaCtx -> ConvState -> Level -> Quant -> Quant -> [(Iso, Iso, MetaCtx)]
unifyPi mctx cs l (Quant _ a b) (Quant _ a' b') = do
  (ia, ia', mctx) <- unifyIso mctx cs l a a'
  let v = transportInv ia (VVar l)
      v' = transportInv ia' (VVar l)
  (ib, ib', mctx) <- unifyIso mctx cs l (b v) (b' v')
  let i = piCongL ia <> piCongL ib
      i' = piCongL ia' <> piCongL ib'
  pure (i, i', mctx)

unifyPiIso :: MetaCtx -> Level -> Quant -> Quant -> [(Iso, Iso, MetaCtx)]
unifyPiIso mctx l q q' = do
  let (Quant _ a b, i) = curry mctx q
  flip foldMapA (currySwap mctx l q') \(Quant _ a' b', i', mctx) -> do
    (ia, ia', mctx) <- unifyIso mctx Full l a a'
    let v = transportInv ia (VVar l)
        v' = transportInv ia' (VVar l)
    (ib, ib', mctx) <- unifyIso mctx Full (l + 1) (b v) (b' v')
    let j = i <> piCongL ia <> piCongR ib
        j' = i' <> piCongL ia' <> piCongR ib'
    pure (j, j', mctx)

unifySigma :: MetaCtx -> ConvState -> Level -> Quant -> Quant -> [(Iso, Iso, MetaCtx)]
unifySigma mctx cs l (Quant _ a b) (Quant _ a' b') = do
  (ia, ia', mctx) <- unifyIso mctx cs l a a'
  let v = transportInv ia (VVar l)
      v' = transportInv ia' (VVar l)
  (ib, ib', mctx) <- unifyIso mctx cs l (b v) (b' v')
  let i = sigmaCongL ia <> sigmaCongL ib
      i' = sigmaCongL ia' <> sigmaCongL ib'
  pure (i, i', mctx)

unifySigmaIso :: MetaCtx -> Level -> Quant -> Quant -> [(Iso, Iso, MetaCtx)]
unifySigmaIso mctx l q q' = do
  let (Quant _ a b, i) = assoc mctx q
  flip foldMapA (assocSwap mctx l q') \(Quant _ a' b', i', mctx) -> do
    (ia, ia', mctx) <- unifyIso mctx Full l a a'
    let v = transportInv ia (VVar l)
        v' = transportInv ia' (VVar l)
    (ib, ib', mctx) <- unifyIso mctx Full (l + 1) (b v) (b' v')
    let j = i <> sigmaCongL ia <> sigmaCongR ib
        j' = i' <> sigmaCongL ia' <> sigmaCongR ib'
    pure (j, j', mctx)
