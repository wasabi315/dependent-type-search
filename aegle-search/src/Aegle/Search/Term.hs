module Aegle.Search.Term
  ( Term (..),
    Type,
    MetaVar (..),
    Pruning,
    RevPruning (..),
    revPruning,
    freeVars,
    weakenBy,
    TeleView (..),
    teleView,
    returnType,
    endsInSort,
    AppView (..),
    appView,
    headTerm,
    termSize,
    subscript,
    filterFeatureQ,
  )
where

import Aegle.Core.Name
import Aegle.Core.Term (Unqualified (..), freshen, subscript)
import Aegle.Database.Feature
import Aegle.Prelude
import Data.Set qualified as S
import Prettyprinter

--------------------------------------------------------------------------------

-- | Metavariables
newtype MetaVar = MetaVar Int
  deriving stock (Generic)
  deriving newtype (Num, Eq, Ord, Show, Hashable, Enum, NFData)

-- | Terms
data Term
  = Var Index -- x
  | Meta MetaVar -- ?m
  | Opaque {-# UNPACK #-} QName -- M.f
  | Amb PQName
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
  deriving anyclass (NFData)

type Type = Term

type Pruning = [Bool]

newtype RevPruning = RevPruning Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning . reverse

--------------------------------------------------------------------------------

freeVars :: Term -> S.Set Index
freeVars = \case
  Var i -> S.singleton i
  Meta {} -> S.empty
  Opaque {} -> S.empty
  Amb {} -> S.empty
  U -> S.empty
  Pi _ a b -> freeVars a <> freeVarBind b
  Lam _ t -> freeVarBind t
  App t u -> freeVars t <> freeVars u
  Sigma _ a b -> freeVars a <> freeVarBind b
  Pair t u -> freeVars t <> freeVars u
  Proj1 t -> freeVars t
  Proj2 t -> freeVars t
  AppPruning {} -> error "freeVar: AppPruning is not supported yet"
  where
    freeVarBind t = S.mapMonotonic (subtract 1) $ S.filter (> 0) $ freeVars t

weakenBy :: Int -> Term -> Term
weakenBy n = go 0
  where
    go d = \case
      Var i
        | i < d -> Var i
        | otherwise -> Var (i + coerce n)
      t@Meta {} -> t
      t@Opaque {} -> t
      t@Amb {} -> t
      U -> U
      Pi x a b -> Pi x (go d a) (go (d + 1) b)
      Lam x t -> Lam x (go (d + 1) t)
      App t u -> App (go d t) (go d u)
      Sigma x a b -> Sigma x (go d a) (go (d + 1) b)
      Pair t u -> Pair (go d t) (go d u)
      Proj1 t -> Proj1 (go d t)
      Proj2 t -> Proj2 (go d t)
      AppPruning {} -> error "weakenBy: weakening on AppPruning is not supported yet"

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
  Opaque {} -> 1
  Amb {} -> 1
  Pi _ a b -> 1 + termSize a + termSize b
  Lam _ t -> 1 + termSize t
  App t u -> 1 + termSize t + termSize u
  AppPruning t pr -> termSize t + length (filter id pr)
  Sigma _ a b -> 1 + termSize a + termSize b
  Pair t u -> 1 + termSize t + termSize u
  Proj1 t -> 1 + termSize t
  Proj2 t -> 1 + termSize t

--------------------------------------------------------------------------------
-- Feature

resultHeadQ :: Type -> Maybe (ResultHead PQName)
resultHeadQ t =
  case headTerm (returnType t) of
    U -> Just RHU
    Var {} -> Just RHVar
    Opaque (QName _ m x) -> Just $ RHTop (Qual m x)
    Amb x -> Just $ RHTop x
    Sigma {} -> Just RHSigma
    Proj1 {} -> Just RHProj1
    Proj2 {} -> Just RHProj2
    (Meta {}; Pi {}; Lam {}; App {}; AppPruning {}; Pair {}) -> Nothing

-- | The input type must be closed. Doesn't perform any reduction.
polymorphicQ :: Type -> Polymorphic
polymorphicQ = \case
  Pi _ a _ | endsInSort a -> Polymorphic
  Pi _ _ b -> polymorphicQ b
  _ -> Monomorphic

-- | The input type must be closed. Doesn't perform any reduction.
arityQ :: Type -> Arity
arityQ = go [] False 0
  where
    go ctx hasVar arity = \case
      Pi _ a b -> case headTerm a of
        Var (Index i)
          | endsInSort (ctx !! i) ->
              go (a : ctx) True (arity + 1) b
        _ ->
          go (a : ctx) hasVar (arity + 1) b
      a -> case headTerm a of
        Var (Index i)
          | endsInSort (ctx !! i) ->
              Arity {hasVar = True, ..}
        _ -> Arity {..}

filterFeatureQ :: Type -> Maybe (FilterFeature PQName)
filterFeatureQ typ = do
  resultHead <- resultHeadQ typ
  pure
    FilterFeature
      { resultHead,
        polymorphic = polymorphicQ typ,
        arity = arityQ typ
      }

--------------------------------------------------------------------------------
-- Prettyprinting

instance Pretty MetaVar where
  pretty (MetaVar m) = "?" <> pretty m

instance Pretty Term where
  pretty = pretty' True []

instance Pretty (Unqualified Term) where
  pretty = pretty' False [] . coerce

instance Pretty ([Name] ⊢ Term) where
  pretty (ns :⊢ t) = pretty' True ns t

instance Pretty ([Name] ⊢ Unqualified Term) where
  pretty (ns :⊢ t) = pretty' False ns (coerce t)

pretty' :: Bool -> [Name] -> Term -> Doc ann
pretty' qual = goPair
  where
    goPair ns = \case
      Pair t u -> goLam ns t <+> comma <+> goPair ns u
      t -> goLam ns t

    goLam ns = \case
      Lam (freshen ns -> n) t -> do
        let go ns = \case
              Lam (freshen ns -> n) t -> " " <> pretty n <> go (n : ns) t
              t -> "." <+> goLam ns t
        "λ" <+> pretty n <> go (n : ns) t
      t -> goPi ns t

    goPi ns = \case
      Pi "_" a b -> goSigma ns a <+> "→" <+> goPi ("_" : ns) b
      Pi (freshen ns -> n) a b -> do
        let go ns = \case
              Pi "_" a b -> " →" <+> goSigma ns a <+> "→" <+> goPi ("_" : ns) b
              Pi (freshen ns -> n) a b -> " " <> piBind n ns a <> go (n : ns) b
              b -> " →" <+> goPi ns b
        piBind n ns a <> go (n : ns) b
      t -> goSigma ns t

    goSigma ns = \case
      Sigma "_" a b -> goApp ns a <+> "×" <+> goSigma ("_" : ns) b
      Sigma (freshen ns -> n) a b -> piBind n ns a <+> "×" <+> goSigma (n : ns) b
      t -> goApp ns t

    goApp ns = \case
      App t u -> goApp ns t <+> goProj ns u
      AppPruning t pr -> do
        let go t i = \cases
              _ [] -> t
              (n : ns) (True : pr) -> go t i ns pr <+> pretty n
              (_ : ns) (False : pr) -> go t i ns pr
              [] (True : pr) -> go t (i + 1) [] pr <+> pretty @Index i
              [] (False : pr) -> go t (i + 1) [] pr
        go (goApp ns t) 0 ns pr
      t -> goProj ns t

    goProj ns = \case
      Proj1 t -> goProj ns t <> ".1"
      Proj2 t -> goProj ns t <> ".2"
      t -> goAtom ns t

    goAtom ns = \case
      Var i -> case ns !? coerce i of
        Nothing -> pretty i
        Just n -> pretty n
      Meta m -> pretty m
      Opaque x
        | qual -> pretty x
        | otherwise -> pretty x.name
      Amb (Unqual x) -> pretty x
      Amb (Qual m x)
        | qual -> pretty (Qual m x)
        | otherwise -> pretty x
      U -> "Set"
      t -> parens (goPair ns t)

    piBind n ns a = parens $ pretty n <+> colon <+> goPair ns a
