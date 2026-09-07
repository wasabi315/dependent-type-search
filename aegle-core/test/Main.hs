module Main
  ( main,
  )
where

import Aegle.Prelude
import Aegle.Database.TestFeature qualified
import Test.Tasty

--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ Aegle.Database.TestFeature.tests
    ]
