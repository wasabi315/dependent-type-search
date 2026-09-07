{-# LANGUAGE ApplicativeDo #-}

module Aegle.Index.Statistics
  ( Statistics (..),
    FeatureShape (..),
    statisticsBuilder,
  )
where

import Aegle.Core.Name
import Aegle.Database.Backend
import Aegle.Database.Feature
import Aegle.Prelude
import Control.Foldl qualified as Foldl
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Deriving.Aeson
import Prettyprinter

--------------------------------------------------------------------------------

data Statistics = Statistics
  { totalItems :: {-# UNPACK #-} Int,
    featureShapes :: [FeatureShape],
    nameCollisions :: [NameCollision]
  }
  deriving stock (Show, Generic)
  deriving (ToJSON) via Generically Statistics

data FeatureShape = FeatureShape
  { resultHead :: ResultHeadKind,
    resultHeadTop :: Maybe T.Text,
    polymorphic :: Bool,
    arity :: Int,
    fixedArity :: Bool,
    count :: Int
  }
  deriving stock (Eq, Ord, Show, Generic)
  deriving (ToJSON) via CustomJSON '[OmitNothingFields] FeatureShape

data ResultHeadKind
  = RHKU
  | RHKVar
  | RHKTop
  | RHKSigma
  | RHKProj1
  | RHKProj2
  deriving stock (Eq, Ord, Show, Generic)
  deriving
    (ToJSON)
    via CustomJSON
          '[ConstructorTagModifier '[StripPrefix "RHK", CamelToSnake]]
          ResultHeadKind

data NameCollision = NameCollision
  { name :: T.Text,
    canonicalNames :: Int
  }
  deriving stock (Show, Generic)
  deriving (ToJSON) via Generically NameCollision

--------------------------------------------------------------------------------

statisticsBuilder :: Foldl.Fold LibraryFragment Statistics
statisticsBuilder = do
  totalItems <-
    countOf (#definitions . traverse)
  featureShapes <-
    histogramOf (#definitions . traverse . #feature)
  nameCollisions <-
    fmap (M.filter (> 1)) do
      Foldl.handles (#exports . traverse) do
        Foldl.groupBy (.exportAs.name) do
          distinctCountOf #canonicalName
  pure
    Statistics
      { totalItems,
        featureShapes = formatFeatureShapes featureShapes,
        nameCollisions = formatNameCollisions nameCollisions
      }

countOf :: Foldl.Handler a b -> Foldl.Fold a Int
countOf h = Foldl.handles h Foldl.length

distinctCountOf :: (Ord b) => Foldl.Handler a b -> Foldl.Fold a Int
distinctCountOf h = Foldl.handles h (S.size <$> Foldl.set)

histogramOf :: (Ord b) => Foldl.Handler a b -> Foldl.Fold a (M.Map b Int)
histogramOf h = Foldl.handles h (Foldl.groupBy id Foldl.length)

toResultHeadKind :: ResultHead n -> ResultHeadKind
toResultHeadKind = \case
  RHU -> RHKU
  RHVar -> RHKVar
  RHTop _ -> RHKTop
  RHSigma -> RHKSigma
  RHProj1 -> RHKProj1
  RHProj2 -> RHKProj2

formatFeatureShapes :: M.Map (AllFeature QName) Int -> [FeatureShape]
formatFeatureShapes =
  map
    ( \(AllFeature {..}, count) ->
        FeatureShape
          { count,
            resultHead = toResultHeadKind resultHead,
            resultHeadTop = case resultHead of
              RHTop n -> Just $! T.show $ pretty n
              _ -> Nothing,
            polymorphic = polymorphic == Polymorphic,
            arity = arity.arity,
            fixedArity = not arity.hasVar
          }
    )
    . sortOn (Down . snd)
    . M.toList

formatNameCollisions :: M.Map Name Int -> [NameCollision]
formatNameCollisions =
  map
    (\(name, canonicalNames) -> NameCollision {name = T.show $ pretty name, ..})
    . sortOn (Down . snd)
    . M.toList
