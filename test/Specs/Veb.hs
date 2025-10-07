module Specs.Veb (testPropsVeb) where

import Data.Conway.Conway
import Data.Conway.Dyadic
import Data.Conway.SignExpansion ()
import Data.Conway.SignExpansion.Types ()
import Data.Conway.Typeclasses
  ( AddSub (..),
    One (one),
    Zero (zero),
  )
import Gen
import Props
import Test.Hspec
import Test.QuickCheck

-- * Veblen Function

prop_vebIncrMap, prop_vebDecrMap :: OrdV0Gen -> OrdV0Gen -> Property

-- | @a < b ==> V[a, V[b, 0] + 1] > V[b, 0]@
prop_vebIncrMap (OrdV0 a) (OrdV0 b)
  | a == b = False ==> True
  | a < b = True ==> veb1 a (veb1 b zero `add` one) > (veb1 b zero :: Conway Dyadic)
  | otherwise = True ==> veb1 b (veb1 a zero `add` one) > (veb1 a zero :: Conway Dyadic)

-- | @a < b ==> V[a, V[b, 0] - 1] < V[b, 0]@
prop_vebDecrMap (OrdV0 a) (OrdV0 b)
  | a == b = False ==> True
  | a < b = True ==> veb1 a (veb1 b zero `sub` one) < (veb1 b zero :: Conway Dyadic)
  | otherwise = True ==> veb1 b (veb1 a zero `sub` one) < (veb1 a zero :: Conway Dyadic)

testPropsVeb :: SpecWith ()
testPropsVeb = do
  it "Veb increasing map" $ do
    qc prop_vebIncrMap
  it "Veb decreasing map" $ do
    qc prop_vebDecrMap
