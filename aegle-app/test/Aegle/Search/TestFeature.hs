module Aegle.Search.TestFeature
  ( tests,
  )
where

import Aegle.Prelude
import Aegle.Search.Feature
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.Hedgehog

--------------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "Aegle.Search.Feature"
    [ testsFor "ResultHead" $ genResultHead (pure ()),
      testsFor "Polymorphic" genPolymorphic,
      testsFor "Arity" genArity,
      testsFor "AllFeature" $ genAllFeature (pure ()),
      testsFor "FilterFeature" $ genFilterFeature (pure ())
    ]
  where
    testsFor name gen =
      testGroup
        name
        [ testPropertyNamed "compatible reflexive" "prop_compatible_reflexive" do
            prop_compatible_reflexive gen,
          testPropertyNamed "compatible transitive" "prop_compatible_transitive" do
            prop_compatible_transitive gen
        ]

--------------------------------------------------------------------------------
-- Properties

prop_compatible_reflexive :: (Feature a, Show a) => Gen a -> Property
prop_compatible_reflexive gen = property do
  feat <- forAll gen
  annotateShow feat
  compatible ! #query feat ! #db feat === True

prop_compatible_transitive :: (Feature a, Show a) => Gen a -> Property
prop_compatible_transitive gen = property do
  feat1 <- forAll gen
  feat2 <- forAll $ Gen.filterT (\db -> compatible ! #query feat1 ! #db db) gen
  feat3 <- forAll $ Gen.filterT (\db -> compatible ! #query feat2 ! #db db) gen
  annotateShow (feat1, feat2, feat3)
  (compatible ! #query feat1 ! #db feat3) === True

--------------------------------------------------------------------------------
-- Feature generators

genResultHead :: Gen n -> Gen (ResultHead n)
genResultHead gen =
  Gen.choice
    [ pure RHU,
      pure RHVar,
      RHTop <$> gen,
      pure RHSigma,
      pure RHProj1,
      pure RHProj2
    ]

genPolymorphic :: Gen Polymorphic
genPolymorphic = Gen.element [Monomorphic, Polymorphic]

genArity :: Gen Arity
genArity = do
  hasVar <- Gen.bool
  arity <- Gen.int (Range.constant 0 32)
  pure Arity {..}

genAllFeature :: Gen n -> Gen (AllFeature n)
genAllFeature gen = do
  resultHead <- genResultHead gen
  polymorphic <- genPolymorphic
  arity <- genArity
  pure AllFeature {..}

genFilterFeature :: Gen n -> Gen (FilterFeature n)
genFilterFeature gen = do
  resultHead <- genResultHead gen
  polymorphic <- genPolymorphic
  arity <- genArity
  pure FilterFeature {..}
