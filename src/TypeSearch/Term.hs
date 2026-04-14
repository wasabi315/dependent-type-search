module TypeSearch.Term where

import Control.Monad.State.Strict
import Data.List (elemIndex)
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.Set qualified as S
import Database.PostgreSQL.Simple.FromField
import Database.PostgreSQL.Simple.ToField
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
  deriving (FromField, ToField) via ViaFlat Term

type Type = Term

type Pruning = [Bool]

newtype RevPruning = RevPruning Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning . reverse

--------------------------------------------------------------------------------

freeVar :: Term -> S.Set Index
freeVar = \case
  Var i -> S.singleton i
  Meta {} -> S.empty
  Top {} -> S.empty
  U -> S.empty
  Pi _ a b -> freeVar a <> freeVarBind b
  Lam _ t -> freeVarBind t
  App t u -> freeVar t <> freeVar u
  Sigma _ a b -> freeVar a <> freeVarBind b
  Pair t u -> freeVar t <> freeVar u
  Proj1 t -> freeVar t
  Proj2 t -> freeVar t
  AppPruning {} -> error "freeVar: AppPruning is not supported yet"
  where
    freeVarBind t = S.mapMonotonic (subtract 1) $ S.filter (> 0) $ freeVar t

subst :: (Index -> Term) -> Term -> Term
subst s = \case
  Var i -> s i
  t@Meta {} -> t
  t@Top {} -> t
  U -> U
  Pi x a b -> Pi x (subst s a) (substBind s b)
  Lam x t -> Lam x (substBind s t)
  App t u -> App (subst s t) (subst s u)
  Sigma x a b -> Sigma x (subst s a) (substBind s b)
  Pair t u -> Pair (subst s t) (subst s u)
  Proj1 t -> Proj1 (subst s t)
  Proj2 t -> Proj2 (subst s t)
  AppPruning {} -> error "subst: substitution on AppPruning is not supported yet"
  where
    substBind s = subst \case
      0 -> Var 0
      i -> weakenBy 1 $ s (i - 1)

rename :: (Index -> Index) -> Term -> Term
rename r = subst (Var . r)

weakenBy :: Int -> Term -> Term
weakenBy n = rename (coerce n +)

data TeleView = TeleView
  { tele :: [Type],
    cod :: Type
  }

teleView :: Type -> TeleView
teleView = go []
  where
    go tele = \case
      Pi _ a b -> go (a : tele) b
      cod -> TeleView tele cod

-- | Get the return type. Doesn't perform any reduction.
returnType :: Type -> Type
returnType = (.cod) . teleView

-- | Is the return type U? Doesn't perform any reduction.
endsInSort :: Type -> Bool
endsInSort t = case teleView t of
  TeleView _ U -> True
  _ -> False

-- | The head term. Doesn't consider projections as elimination. Doesn't perform any reduction.
headTerm :: Term -> Term
headTerm = \case
  App t _ -> headTerm t
  t -> t

termSize :: Term -> Int
termSize = \case
  Var {} -> 1
  U -> 1
  Meta {} -> 1
  Top {} -> 1
  Pi _ a b -> 1 + termSize a + termSize b
  Lam _ t -> 1 + termSize t
  App t u -> 1 + termSize t + termSize u
  AppPruning t pr -> termSize t + length (filter id pr)
  Sigma _ a b -> 1 + termSize a + termSize b
  Pair t u -> 1 + termSize t + termSize u
  Proj1 t -> 1 + termSize t
  Proj2 t -> 1 + termSize t

--------------------------------------------------------------------------------

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
