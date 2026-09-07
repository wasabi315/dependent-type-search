module Aegle.Database.Feature where

import Aegle.Prelude
import Data.Generics.Product.Subtype

--------------------------------------------------------------------------------

-- | Search feature with a compatibility relation.
class Feature a where
  -- | @compatible query db@ means that a definition with feature @db@ is a
  -- possible candidate for a search query with feature @query@.
  -- Should be a preorder.
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
