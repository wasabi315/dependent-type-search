module TypeSearch.Database.Feature where

import Data.Set qualified as S
import Database.PostgreSQL.Simple.Extra
import Database.PostgreSQL.Simple.FromField
import Database.PostgreSQL.Simple.Newtypes
import Database.PostgreSQL.Simple.ToField
import TypeSearch.Core.Name
import TypeSearch.Core.Term
import TypeSearch.Database.Query qualified as Q
import TypeSearch.Prelude

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

-- | The input type must be closed. Doesn't perform any reduction.
returnTypeHead :: Type -> ReturnTypeHead QName
returnTypeHead t = case headTerm (returnType t) of
  U -> RHU
  Var {} -> RHVar
  Top x -> RHTop x
  Sigma {} -> RHSigma
  Proj1 {} -> RHProj1
  Proj2 {} -> RHProj2
  _ -> impossible

-- | The input type must be closed.
returnTypeHeadQ :: S.Set QName -> Q.Type -> Maybe (ReturnTypeHead PQName)
returnTypeHeadQ transparentDefNames (Q.teleView -> TeleView tele cod) =
  case Q.headTerm cod of
    Q.U -> Just RHU
    Q.Var (Unqual x)
      | Just {} <- lookup x tele -> Just RHVar
    Q.Var x | maybeTransparentDef x -> Just RHUnknown
    Q.Var x -> Just $ RHTop x
    Q.Sigma {} -> Just RHSigma
    Q.Proj1 {} -> Just RHProj1
    Q.Proj2 {} -> Just RHProj2
    _ -> Nothing
  where
    maybeTransparentDef = \case
      Unqual x -> any (\y -> x == y.name) transparentDefNames
      Qual m x -> S.member (QName m x) transparentDefNames

--------------------------------------------------------------------------------

-- | Polymorphic feature.
data Polymorphic = NoPolymorphic | YesPolymorphic
  deriving stock (Eq, Ord, Show, Enum)
  deriving (ToField, FromField) via ViaEnum Polymorphic

-- | The input type must be closed. Doesn't perform any reduction.
polymorphic :: Type -> Polymorphic
polymorphic = \case
  Pi _ a _ | endsInSort a -> YesPolymorphic
  Pi _ _ b -> polymorphic b
  _ -> NoPolymorphic

-- | The input type must be closed.
polymorphicQ :: Q.Type -> Polymorphic
polymorphicQ = \case
  Q.Pi _ a _ | Q.endsInSort a -> YesPolymorphic
  Q.Pi _ _ b -> polymorphicQ b
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
      _ -> Arity {..}

-- | The input type must be closed.
arityQ :: Q.Type -> Arity
arityQ = go [] False 0
  where
    go ctx hasVar arity = \case
      Q.Pi x a b -> case Q.headTerm a of
        Q.Var (Unqual y)
          | Just t <- lookup y ctx,
            Q.endsInSort t ->
              go ((x, a) : ctx) True (arity + 1) b
        _ ->
          go ((x, a) : ctx) hasVar (arity + 1) b
      _ -> Arity {..}

--------------------------------------------------------------------------------

data Feature n = Feature
  { returnTypeHead :: ReturnTypeHead n,
    polymorphic :: Polymorphic,
    arity :: Arity
  }

feature :: Type -> Feature QName
feature typ =
  Feature
    { returnTypeHead = returnTypeHead typ,
      polymorphic = polymorphic typ,
      arity = arity typ
    }

featureQ :: S.Set QName -> Q.Type -> Maybe (Feature PQName)
featureQ transparentDefNames typ = do
  returnTypeHead <- returnTypeHeadQ transparentDefNames typ
  pure
    Feature
      { returnTypeHead,
        polymorphic = polymorphicQ typ,
        arity = arityQ typ
      }
