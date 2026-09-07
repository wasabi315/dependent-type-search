module Main
  ( main,
  )
where

import Aegle.Prelude
import Aegle.Search.TestFeature qualified
import Test.Tasty

--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ Aegle.Search.TestFeature.tests
    ]
