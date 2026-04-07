module TypeSearch.Database.Feature where

import Data.Set qualified as S
import Database.PostgreSQL.Simple.FromField
import Database.PostgreSQL.Simple.Newtypes
import Database.PostgreSQL.Simple.ToField
import TypeSearch.Common
import TypeSearch.Raw
import TypeSearch.Term

--------------------------------------------------------------------------------
-- Features

data ReturnTypeHead n
  = RHU
  | RHVar
  | RHTop n
  | RHSigma
  | RHProj1
  | RHProj2
  | RHUnknown
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (ToJSON, FromJSON)
  deriving (ToField, FromField) via Aeson (ReturnTypeHead n)

-- | Doesn't perform any reduction.
computeReturnTypeHead :: Type -> ReturnTypeHead QName
computeReturnTypeHead t = case headTerm (returnType t) of
  U -> RHU
  Var {} -> RHVar
  Top x -> RHTop x
  Sigma {} -> RHSigma
  Proj1 {} -> RHProj1
  Proj2 {} -> RHProj2
  _ -> impossible

computeReturnTypeHeadRaw :: S.Set QName -> Raw -> Maybe (ReturnTypeHead PQName)
computeReturnTypeHeadRaw aliasSet (rteleView -> RTeleView tele cod) =
  case unRPos (rawHeadTerm cod) of
    RU -> Just RHU
    RVar (Unqual x)
      | Just {} <- lookup x tele -> Just RHVar
    RVar x | maybeAlias x -> Just RHUnknown
    RVar x -> Just $ RHTop x
    RSigma {} -> Just RHSigma
    RProj1 {} -> Just RHProj1
    RProj2 {} -> Just RHProj2
    _ -> Nothing
  where
    maybeAlias = \case
      Unqual x -> any (\y -> x == y.name) aliasSet
      Qual m x -> S.member (QName m x) aliasSet

--------------------------------------------------------------------------------

-- | Polymorphic feature.
data Polymorphic = NoPolymorphic | YesPolymorphic
  deriving stock (Eq, Ord, Show, Enum)
  deriving (ToField, FromField) via ViaEnum Polymorphic

-- | Doesn't perform any reduction.
computePolymorphic :: Type -> Polymorphic
computePolymorphic = \case
  Pi _ a _ | endsInSort a -> YesPolymorphic
  Pi _ _ b -> computePolymorphic b
  _ -> NoPolymorphic

computePolymorphicRaw :: Raw -> Polymorphic
computePolymorphicRaw = \case
  RPos t _ -> computePolymorphicRaw t
  RPi _ a _ | rawEndsInSort a -> YesPolymorphic
  RPi _ _ b -> computePolymorphicRaw b
  _ -> NoPolymorphic

--------------------------------------------------------------------------------

-- | Arity feature.
data Arity = Arity
  { hasVar :: Bool,
    arity :: Int
  }
  deriving stock (Eq, Show, Ord, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving (ToField, FromField) via Aeson Arity

computeArity :: Type -> Arity
computeArity = go [] False 0
  where
    go ctx hasVar arity = \case
      Pi _ a b -> case headTerm a of
        Var i
          | endsInSort (ctx !! coerce i) ->
              go (a : ctx) True (arity + 1) b
        _ ->
          go (a : ctx) hasVar (arity + 1) b
      _ -> Arity {..}

computeArityRaw :: Raw -> Arity
computeArityRaw = go [] False 0
  where
    go ctx hasVar arity = \case
      RPos t _ -> go ctx hasVar arity t
      RPi x a b -> case rawHeadTerm a of
        RVar (Unqual y)
          | Just t <- lookup y ctx,
            rawEndsInSort t ->
              go ((x, a) : ctx) True (arity + 1) b
        _ ->
          go ((x, a) : ctx) hasVar (arity + 1) b
      _ -> Arity {..}
