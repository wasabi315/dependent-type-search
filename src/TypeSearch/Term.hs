module TypeSearch.Term where

import Control.Monad.State.Strict
import Data.List (elemIndex)
import Data.Map.Strict qualified as M
import Data.Maybe
import GHC.Generics
import TypeSearch.Common
import TypeSearch.Raw

--------------------------------------------------------------------------------

-- | Terms
data Term
  = Var Index -- x
  | Meta MetaVar -- ?m
  | Top {-# UNPACK #-} QName -- M.f
  | U -- U
  | Pi Name Type Type -- (x : A) → B
  | Lam Name Term -- λ x → t
  | App Term Term -- t1 t2
  | AppPruning Term Pruning
  | Sigma Name Type Type -- (x : A) × B
  | Pair Term Term -- (t1, t2)
  | Proj1 Term -- t.1
  | Proj2 Term -- t.2
  deriving stock (Show, Generic)
  deriving anyclass (Flat)

type Type = Term

type Pruning = [Bool]

newtype RevPruning = RevPruning Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning . reverse

--------------------------------------------------------------------------------

rawToTerm :: Raw -> Maybe Term
rawToTerm = go []
  where
    go ns = \case
      RVar (Qual m x) -> pure $ Top (QName m x)
      RVar (Unqual x) -> case x `elemIndex` ns of
        Nothing -> Nothing
        Just i -> pure $ Var (Index i)
      RU -> pure U
      RPi x a b -> Pi x <$> go ns a <*> go (x : ns) b
      RLam x t -> Lam x <$> go (x : ns) t
      RApp t u -> App <$> go ns t <*> go ns u
      RSigma x a b -> Sigma x <$> go ns a <*> go (x : ns) b
      RPair t u -> Pair <$> go ns t <*> go ns u
      RProj1 t -> Proj1 <$> go ns t
      RProj2 t -> Proj2 <$> go ns t
      RPos t _ -> go ns t

possibleResolutions :: M.Map Name [QName] -> Raw -> [Term]
possibleResolutions tbl = flip evalStateT mempty . go []
  where
    fixName qn = StateT \fixed -> do
      fixed <-
        M.alterF
          ( maybe
              (pure $ Just qn)
              \qn' -> if qn == qn' then pure (Just qn) else []
          )
          qn.name
          fixed
      pure ((), fixed)

    go ns = \case
      RVar (Unqual x)
        | Just i <- x `elemIndex` ns -> pure $ Var (Index i)
      RVar (Unqual x) -> do
        qn <- lift $ fromMaybe [] (tbl M.!? x)
        fixName qn
        pure $ Top qn
      RVar (Qual m x) -> do
        fixName (QName m x)
        pure $ Top (QName m x)
      RU -> pure U
      RPi x a b -> Pi x <$> go ns a <*> go (x : ns) b
      RLam x t -> Lam x <$> go (x : ns) t
      RApp t u -> App <$> go ns t <*> go ns u
      RSigma x a b -> Sigma x <$> go ns a <*> go (x : ns) b
      RPair t u -> Pair <$> go ns t <*> go ns u
      RProj1 t -> Proj1 <$> go ns t
      RProj2 t -> Proj2 <$> go ns t
      RPos t _ -> go ns t

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
  deriving stock (Show)

instance Semigroup Iso where
  Refl <> j = j
  i <> Refl = i
  i <> j = Trans i j

instance Monoid Iso where
  mempty = Refl

sym :: Iso -> Iso
sym = \case
  Refl -> Refl
  Sym i -> i
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
