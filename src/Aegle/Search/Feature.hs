module Aegle.Search.Feature
  ( Feature (..),
    ResultHead (..),
    resultHead,
    resultHeadQ,
    ResultHeadCompat (..),
    Polymorphic (..),
    polymorphic,
    PolymorphicCompat (..),
    Arity (..),
    arity,
    ArityCompat (..),
    AllFeature (..),
    allFeature,
    AllFeatureCompat (..),
    FilterFeature (..),
    filterFeatureQ,
    FilterFeatureCompat (..),
  )
where

import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Prelude
import Data.Generics.Product.Subtype

--------------------------------------------------------------------------------

-- | Search feature with a compatibility relation.
class Feature a where
  -- | @compatible query db@ means that a definition with feature @db@ is a
  -- possible candidate for a search query with feature @query@.
  -- Expected to be a preorder.
  compatible :: "query" :! a -> "db" :! a -> Bool
  compatible = matchesCompat . toCompat
  {-# INLINE compatible #-}

  -- | Reified compatibility condition produced from a query feature.
  -- Backend code can compile this, e.g. to SQL.
  type Compat a

  toCompat :: "query" :! a -> Compat a
  matchesCompat :: Compat a -> "db" :! a -> Bool

--------------------------------------------------------------------------------
-- Result Head

data ResultHead n
  = RHU
  | RHVar
  | RHTop n
  | RHSigma
  | RHProj1
  | RHProj2
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

-- | The input type must be closed. Doesn't perform any reduction.
resultHead' :: (QName -> n) -> (PQName -> n) -> Type -> Maybe (ResultHead n)
resultHead' onOpaque onAmb t = case headTerm (returnType t) of
  U -> Just RHU
  Var {} -> Just RHVar
  Opaque x -> Just $ RHTop (onOpaque x)
  Amb x -> Just $ RHTop (onAmb x)
  Sigma {} -> Just RHSigma
  Proj1 {} -> Just RHProj1
  Proj2 {} -> Just RHProj2
  (Meta {}; Pi {}; Lam {}; App {}; AppPruning {}; Pair {}) -> Nothing

-- | The input type must be closed and well-formed. Doesn't perform any reduction.
resultHead :: Type -> ResultHead QName
resultHead = fromJust . resultHead' id (const $ impossible "resultHead")

-- | The input type must be closed.
resultHeadQ :: Type -> Maybe (ResultHead PQName)
resultHeadQ = resultHead' (const $ impossible "resultHeadQ") id

data ResultHeadCompat n
  = IsVar
  | IsVarOrU
  | IsVarOrTop n
  | IsVarOrSigma
  | IsVarOrProj1
  | IsVarOrProj2
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance (Eq n) => Feature (ResultHead n) where
  type Compat (ResultHead n) = ResultHeadCompat n

  toCompat = \case
    Arg RHU -> IsVarOrU
    Arg RHVar -> IsVar
    Arg (RHTop n) -> IsVarOrTop n
    Arg RHSigma -> IsVarOrSigma
    Arg RHProj1 -> IsVarOrProj1
    Arg RHProj2 -> IsVarOrProj2
  {-# INLINE toCompat #-}

  matchesCompat = \cases
    IsVar (Arg rh) -> rh == RHVar
    IsVarOrU (Arg rh) -> rh `elem` [RHVar, RHU]
    (IsVarOrTop n) (Arg rh) -> rh `elem` [RHVar, RHTop n]
    IsVarOrSigma (Arg rh) -> rh `elem` [RHVar, RHSigma]
    IsVarOrProj1 (Arg rh) -> rh `elem` [RHVar, RHProj1]
    IsVarOrProj2 (Arg rh) -> rh `elem` [RHVar, RHProj2]
  {-# INLINE matchesCompat #-}

--------------------------------------------------------------------------------
-- Polymorphic

-- | Polymorphic feature.
data Polymorphic = Monomorphic | Polymorphic
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

-- | The input type must be closed. Doesn't perform any reduction.
polymorphic :: Type -> Polymorphic
polymorphic = \case
  Pi _ a _ | endsInSort a -> Polymorphic
  Pi _ _ b -> polymorphic b
  _ -> Monomorphic

data PolymorphicCompat
  = IsPoly
  | AnyPoly
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance Feature Polymorphic where
  type Compat Polymorphic = PolymorphicCompat

  toCompat = \case
    Arg Polymorphic -> IsPoly
    Arg Monomorphic -> AnyPoly
  {-# INLINE toCompat #-}

  matchesCompat = \cases
    IsPoly (Arg poly) -> poly == Polymorphic
    AnyPoly _ -> True
  {-# INLINE matchesCompat #-}

--------------------------------------------------------------------------------

-- | Arity feature.
data Arity = Arity
  { hasVar :: Bool,
    arity :: Int
  }
  deriving stock (Eq, Ord, Show, Generic)

-- | The input type must be closed. Doesn't perform any reduction.
arity :: Type -> Arity
arity = go [] False 0
  where
    go ctx hasVar arity = \case
      Pi _ a b -> case headTerm a of
        Var i
          | endsInSort (ctx !! coerce i) ->
              go (a : ctx) True (arity + 1) b
        _ ->
          go (a : ctx) hasVar (arity + 1) b
      a -> case headTerm a of
        Var i
          | endsInSort (ctx !! coerce i) ->
              Arity {hasVar = True, ..}
        _ -> Arity {..}

data ArityCompat
  = HasVar
  | HasVarOrGe Int
  deriving stock (Eq, Ord, Show, Generic)

instance Feature Arity where
  type Compat Arity = ArityCompat

  toCompat (Arg Arity {..}) =
    if hasVar then HasVar else HasVarOrGe arity
  {-# INLINE toCompat #-}

  matchesCompat compat (Arg Arity {..}) = case compat of
    HasVar -> hasVar
    HasVarOrGe arity' -> hasVar || arity >= arity'
  {-# INLINE matchesCompat #-}

--------------------------------------------------------------------------------

data AllFeature n = AllFeature
  { resultHead :: ResultHead n,
    polymorphic :: Polymorphic,
    arity :: Arity
  }
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

allFeature :: Type -> AllFeature QName
allFeature typ =
  AllFeature
    { resultHead = resultHead typ,
      polymorphic = polymorphic typ,
      arity = arity typ
    }

data AllFeatureCompat n = AllFeatureCompat
  { resultHead :: ResultHeadCompat n,
    polymorphic :: PolymorphicCompat,
    arity :: ArityCompat
  }
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance (Eq n) => Feature (AllFeature n) where
  type Compat (AllFeature n) = AllFeatureCompat n

  toCompat (Arg AllFeature {..}) =
    AllFeatureCompat
      { resultHead = toCompat (Arg resultHead),
        polymorphic = toCompat (Arg polymorphic),
        arity = toCompat (Arg arity)
      }
  {-# INLINE toCompat #-}

  matchesCompat compat (Arg feat) =
    matchesCompat compat.resultHead (Arg feat.resultHead)
      && matchesCompat compat.polymorphic (Arg feat.polymorphic)
      && matchesCompat compat.arity (Arg feat.arity)
  {-# INLINE matchesCompat #-}

--------------------------------------------------------------------------------

data FilterFeature n = FilterFeature
  { resultHead :: ResultHead n,
    polymorphic :: Polymorphic,
    arity :: Arity
  }
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

filterFeatureQ :: Type -> Maybe (FilterFeature PQName)
filterFeatureQ typ = do
  resultHead <- resultHeadQ typ
  pure
    FilterFeature
      { resultHead,
        polymorphic = polymorphic typ,
        arity = arity typ
      }

data FilterFeatureCompat n = FilterFeatureCompat
  { resultHead :: ResultHeadCompat n,
    polymorphic :: PolymorphicCompat,
    arity :: ArityCompat
  }
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance (Eq n) => Feature (FilterFeature n) where
  type Compat (FilterFeature n) = FilterFeatureCompat n

  toCompat (Arg FilterFeature {..}) =
    FilterFeatureCompat
      { resultHead = toCompat (Arg resultHead),
        polymorphic = toCompat (Arg polymorphic),
        arity = toCompat (Arg arity)
      }
  {-# INLINE toCompat #-}

  matchesCompat compat (Arg feat) =
    matchesCompat compat.resultHead (Arg feat.resultHead)
      && matchesCompat compat.polymorphic (Arg feat.polymorphic)
      && matchesCompat compat.arity (Arg feat.arity)
  {-# INLINE matchesCompat #-}

_subWitness :: Lens' (AllFeature n) (FilterFeature n)
_subWitness = super
