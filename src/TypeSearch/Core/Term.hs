module TypeSearch.Core.Term
  ( Term (..),
    Type,
    Pruning,
    RevPruning (..),
    revPruning,
    freeVar,
    subst,
    rename,
    weakenBy,
    TeleView (..),
    teleView,
    returnType,
    endsInSort,
    AppView (..),
    appView,
    headTerm,
    termSize,
  )
where

import Data.Set qualified as S
import Database.PostgreSQL.Simple.Extra
import Database.PostgreSQL.Simple.FromField
import Database.PostgreSQL.Simple.ToField
import TypeSearch.Core.Name
import TypeSearch.Prelude

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

data TeleView a = TeleView
  { tele :: [(Name, a)],
    cod :: a
  }

teleView :: Type -> TeleView Type
teleView = go []
  where
    go tele = \case
      Pi x a b -> go ((x, a) : tele) b
      cod -> TeleView tele cod

-- | Get the return type. Doesn't perform any reduction.
returnType :: Type -> Type
returnType = (.cod) . teleView

-- | Is the return type U? Doesn't perform any reduction.
endsInSort :: Type -> Bool
endsInSort t = case returnType t of
  U -> True
  _ -> False

data AppView a = AppView
  { head :: a,
    args :: [a]
  }

appView :: Term -> AppView Term
appView = go id
  where
    go args = \case
      App t u -> go ((u :) . args) t
      t -> AppView {head = t, args = args []}

-- | The head term. Doesn't consider projections as elimination. Doesn't perform any reduction.
headTerm :: Term -> Term
headTerm = (.head) . appView

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
