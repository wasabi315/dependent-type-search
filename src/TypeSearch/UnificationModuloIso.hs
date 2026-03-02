module TypeSearch.UnificationModuloIso where

import Control.Applicative
import Control.Monad.State.Strict
import Data.Maybe
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Term
import TypeSearch.Unification
import Prelude hiding (curry)

--------------------------------------------------------------------------------

data Ctx = Ctx
  { level :: Level,
    env :: Env,
    idRen :: PartialRenaming,
    convState :: ConvState
  }

emptyCtx :: Ctx
emptyCtx = Ctx 0 [] emptyPRen Rigid

bind :: Ctx -> Ctx
bind (Ctx l env idRen cs) =
  Ctx (l + 1) (VVar l : env) (liftPren idRen) cs

--------------------------------------------------------------------------------
-- Rewriting types

-- | Curry until the first domain becomes non-sigma.
curry :: MetaCtx -> ConvState -> Quant -> (Quant, Iso)
curry mctx cs = go Refl
  where
    go i (Quant x a b) = case forceCS mctx cs a of
      VSigma y a1 a2 ->
        go (i <> Curry) $ Quant y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> (Quant x a b, i)

-- | Right-nest until the first projection becomes non-sigma.
assoc :: MetaCtx -> ConvState -> Quant -> (Quant, Iso)
assoc mctx cs = go Refl
  where
    go i (Quant x a b) = case forceCS mctx cs a of
      VSigma y a1 a2 ->
        go (i <> Assoc) $ Quant y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> (Quant x a b, i)

-- | Pick a domain without breaking dependencies.
pickDomain :: MetaCtx -> Ctx -> Quant -> [(Quant, Iso, MetaCtx)]
pickDomain mctx (Ctx l env idl cs) q@(Quant x a b) = (q, Refl, mctx) : go l b
  where
    go l' c = case forceCS mctx cs $ c (VVar l') of
      VPi y c1 c2 ->
        ( maybeToList do
            let i = l' - l
            -- Strengthen c1. This may involve pruning.
            (c1, mctx) <- flip runStateT mctx $ rename (skipPrenN (i + 1) idl) c1
            let c1' = eval mctx env c1
                rest ~vc1 = VPi x a (instPiAt i vc1 . b)
                s = swaps i
            pure (Quant y c1' rest, s, mctx)
        )
          ++ go (l' + 1) c2
      _ -> []

    instPiAt i ~v t = case (i, forceCS mctx cs t) of
      (0, VPi _ _ b) -> b v
      (i, VPi x a b) -> VPi x a (instPiAt (i - 1) v . b)
      _ -> impossible

    swaps = \case
      0 -> PiSwap
      n -> piCongR (swaps (n - 1)) <> PiSwap

-- | Pick a projection without breaking dependencies.
pickProjection :: MetaCtx -> Ctx -> Quant -> [(Quant, Iso, MetaCtx)]
pickProjection mctx (Ctx l env idl cs) q@(Quant x a b) = (q, Refl, mctx) : go l b
  where
    go l' c = case forceCS mctx cs $ c (VVar l') of
      VSigma y c1 c2 ->
        ( maybeToList do
            let i = l' - l
            -- Strengthen c1. This may involve pruning.
            (c1, mctx) <- flip runStateT mctx $ rename (skipPrenN (i + 1) idl) c1
            let c1' = eval mctx env c1
                rest ~vc1 = VSigma x a (instSigmaAt i vc1 . b)
                s = swaps SigmaSwap i
            pure (Quant y c1' rest, s, mctx)
        )
          ++ go (l' + 1) c2
      c -> maybeToList do
        let i = l' - l
        (c, mctx) <- flip runStateT mctx $ rename (skipPrenN (i + 1) idl) c
        let c' = eval mctx env c
            rest ~_ = dropLastProj l' (VSigma x a b)
            s = swaps Comm i
        Just (Quant "_" c' rest, s, mctx)

    instSigmaAt i ~v t = case (i, forceCS mctx cs t) of
      (0, VSigma _ _ b) -> b v
      (i, VSigma x a b) -> VSigma x a (instSigmaAt (i - 1) v . b)
      _ -> impossible

    dropLastProj l t = case forceCS mctx cs t of
      VSigma x a b -> case b (VVar l) of
        VSigma {} -> VSigma x a (dropLastProj (l + 1) . b)
        _ -> a
      _ -> impossible

    swaps i = \case
      0 -> i
      n -> sigmaCongR (swaps i (n - 1)) <> SigmaSwap

-- | Pick a **non-sigma** projection without breaking dependencies.
-- This works even in the presence of arbitrarily nested sigmas in the type.
assocSwap :: MetaCtx -> Ctx -> Quant -> [(Quant, Iso, MetaCtx)]
assocSwap mctx ctx q = do
  -- Pick one projection first.
  (q, i, mctx) <- pickProjection mctx ctx q
  case q of
    -- When the selected projection is a sigma type, we invoke
    -- assocSwap recursively to make the first projection of the sigma non-sigma!
    Quant x (VSigma y a b) c -> do
      (Quant y a b, j, mctx) <- assocSwap mctx ctx (Quant y a b)
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
currySwap :: MetaCtx -> Ctx -> Quant -> [(Quant, Iso, MetaCtx)]
currySwap mctx ctx q = do
  (q, i, mctx) <- pickDomain mctx ctx q
  case q of
    Quant x (VSigma y a b) c -> do
      (Quant y a b, j, mctx) <- assocSwap mctx ctx (Quant y a b)
      let q = Quant y a \ ~u -> VPi x (b u) \ ~v -> c (transportInv j (VPair u v))
          k = i <> piCongL j <> Curry
      pure (q, k, mctx)
    q -> pure (q, i, mctx)

--------------------------------------------------------------------------------

unifyIso0 :: MetaCtx -> Term -> Term -> [(Iso, MetaCtx)]
unifyIso0 mctx t t' = do
  let v = eval mctx [] t
      v' = eval mctx [] t'
  (i, i', mctx) <- unifyIso mctx emptyCtx v v'
  let j = i <> sym i'
  pure (j, mctx)

unifyIso :: MetaCtx -> Ctx -> Value -> Value -> [(Iso, Iso, MetaCtx)]
unifyIso mctx ctx t u = case (forceCS mctx ctx.convState t, forceCS mctx ctx.convState u) of
  (VPi x a b, VPi x' a' b') -> case ctx.convState of
    Rigid ->
      unifyPi mctx (ctx {convState = Flex}) (Quant x a b) (Quant x' a' b')
        <|> unifyPi mctx (ctx {convState = Full}) (Quant x a b) (Quant x' a' b')
    _ -> unifyPi mctx ctx (Quant x a b) (Quant x' a' b')
  (VSigma x a b, VSigma x' a' b') -> case ctx.convState of
    Rigid ->
      unifySigma mctx (ctx {convState = Flex}) (Quant x a b) (Quant x' a' b')
        <|> unifySigma mctx (ctx {convState = Full}) (Quant x a b) (Quant x' a' b')
    _ -> unifySigma mctx ctx (Quant x a b) (Quant x' a' b')
  (VTop x _ sp Nothing, VTop x' _ sp' Nothing)
    | x == x' -> unifySpineRefl mctx ctx sp sp'
  (VTop x _ sp (Just t), VTop x' _ sp' (Just t')) -> case ctx.convState of
    Rigid
      | x == x' ->
          unifySpineRefl mctx (ctx {convState = Flex}) sp sp'
            <|> unifyIso mctx (ctx {convState = Full}) t t'
      | otherwise -> unifyIso mctx ctx t t'
    Flex
      | x == x' -> unifySpineRefl mctx ctx sp sp'
      | otherwise -> []
    Full -> impossible
  (VTop _ _ _ (Just t), t') -> case ctx.convState of
    Rigid -> unifyIso mctx ctx t t'
    Flex -> []
    _ -> impossible
  (t, VTop _ _ _ (Just t')) -> case ctx.convState of
    Rigid -> unifyIso mctx ctx t t'
    Flex -> []
    _ -> impossible
  (t, u) -> do
    mctx <- maybeToList $ unify mctx ctx.convState ctx.level t u
    pure (Refl, Refl, mctx)

unifySpineRefl :: MetaCtx -> Ctx -> Spine -> Spine -> [(Iso, Iso, MetaCtx)]
unifySpineRefl mctx ctx sp sp' = do
  mctx <- maybeToList $ unifySpine mctx ctx.convState ctx.level sp sp'
  pure (Refl, Refl, mctx)

unifyPi :: MetaCtx -> Ctx -> Quant -> Quant -> [(Iso, Iso, MetaCtx)]
unifyPi mctx ctx q q' = do
  let (Quant _ a b, i) = curry mctx ctx.convState q
  flip foldMapA (currySwap mctx ctx q') \(Quant _ a' b', i', mctx) -> do
    (ia, ia', mctx) <- unifyIso mctx ctx a a'
    let v = transportInv ia (VVar ctx.level)
        v' = transportInv ia' (VVar ctx.level)
    (ib, ib', mctx) <- unifyIso mctx (bind ctx) (b v) (b' v')
    let j = i <> piCongL ia <> piCongR ib
        j' = i' <> piCongL ia' <> piCongR ib'
    pure (j, j', mctx)

unifySigma :: MetaCtx -> Ctx -> Quant -> Quant -> [(Iso, Iso, MetaCtx)]
unifySigma mctx ctx q q' = do
  let (Quant _ a b, i) = assoc mctx ctx.convState q
  flip foldMapA (assocSwap mctx ctx q') \(Quant _ a' b', i', mctx) -> do
    (ia, ia', mctx) <- unifyIso mctx ctx a a'
    let v = transportInv ia (VVar ctx.level)
        v' = transportInv ia' (VVar ctx.level)
    (ib, ib', mctx) <- unifyIso mctx (bind ctx) (b v) (b' v')
    let j = i <> sigmaCongL ia <> sigmaCongR ib
        j' = i' <> sigmaCongL ia' <> sigmaCongR ib'
    pure (j, j', mctx)
