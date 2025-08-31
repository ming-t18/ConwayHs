{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Gen where

import Conway
import Data.Foldable
import Dyadic
import SignExpansion (SignExpansion)
import qualified SignExpansion as SE
import SignExpansion.Dyadic (FSE)
import qualified SignExpansion.Dyadic as SED
import Test.QuickCheck
import Typeclasses
  ( AddSub (..),
    One (one),
    OrdRing,
    OrdZero (neg),
    Zero (isZero, zero),
  )

maxDepth :: Int
maxDepth = 4

maxLengthByDepth :: Int -> Gen Int
maxLengthByDepth d =
  case d of
    0 -> chooseInt (0, 1)
    1 -> chooseInt (0, 2)
    2 -> chooseInt (0, 3)
    3 -> chooseInt (0, 4)
    _ -> chooseInt (0, 5)

arbConway :: (Arbitrary order, Arbitrary gen, OrdRing a) => (order -> Ordinal) -> (gen -> a) -> Int -> Gen (Conway a)
arbConway fromOrder fromCoeff = recurse
  where
    -- recurse :: (OrdRing a) => Int -> Gen (Conway a)
    recurse d | d <= 0 = return zero
    recurse d = do
      l <- listOf (genMono d)
      n <- maxLengthByDepth d
      return $ foldr add zero $ take n l
    -- genMono :: (OrdRing a) => Int -> Gen (Conway a)
    genMono d = do
      a <- fromOrder <$> arbitrary
      p <- recurse (d - 1)
      veb a p . fromCoeff <$> arbitrary

shrinkFinite :: (OrdRing a) => a -> [a]
shrinkFinite c
  | isZero c = []
  | zero < c && c <= one = [zero]
  | one < c = [zero, one]
  | neg one <= c && c < zero = [zero]
  | otherwise = [zero, neg one]

shrinkTriple :: (OrdRing a) => (Ordinal, Conway a, a) -> [(Ordinal, Conway a, a)]
shrinkTriple (a, p, c) =
  [(a', p, c) | a' <- shrinkConway a]
    ++ [(a, p', c) | p' <- shrinkConway p]
    ++ [(a, p, c') | c' <- shrinkFinite c]

monosList :: Conway a -> [(Ordinal, Conway a, a)]
monosList x = map (\(VebMono a p, c) -> (a, p, c)) $ termsList x

shrinkConway :: (OrdRing a) => Conway a -> [Conway a]
shrinkConway x =
  [ foldl' (\s (a, p, c) -> add s (veb a p c)) zero list'
  | list' <- shrinkList shrinkTriple $ monosList x
  ]

newtype DyadicGen = DyadicGen {getDyadic :: Dyadic}
  deriving (Eq, Ord, Show)

newtype NaturalGen = NatGen {getNatural :: Natural}
  deriving (Eq, Ord, Show)

newtype FiniteOrdGen = FinOrd {getFiniteOrd :: Ordinal}
  deriving (Eq, Ord, Show)

newtype OrdV0Gen = OrdV0 {getOrdV0 :: Ordinal}
  deriving (Eq, Ord, Show)

newtype ConwayV0Gen a = ConwayV0 {getConwayV0 :: Conway a}
  deriving (Eq, Ord, Show)

newtype ConwayGen a = ConwayGen {getConway :: Conway a}
  deriving (Eq, Ord, Show)

instance Arbitrary DyadicGen where
  arbitrary = DyadicGen <$> (makeDyadic <$> arbitrary <*> arbitrary)
  shrink (DyadicGen d) =
    map
      DyadicGen
      ([a' `makeDyadic` p | a' <- shrink a] ++ [a `makeDyadic` p' | p' <- shrink p])
    where
      (a, p) = unmakeDyadic d

instance Arbitrary Dyadic where
  arbitrary = getDyadic <$> arbitrary

instance Arbitrary NaturalGen where
  arbitrary = NatGen . fromIntegral . (`mod` maxValue) . abs <$> (arbitrary :: Gen Integer)
    where
      maxValue = 16 :: Integer

instance Arbitrary Natural where
  arbitrary = getNatural <$> arbitrary

instance Arbitrary FiniteOrdGen where
  arbitrary = FinOrd . finite . getNatural <$> arbitrary

instance Arbitrary OrdV0Gen where
  arbitrary = OrdV0 <$> arbConway (\() -> zero :: Ordinal) getNatural maxDepth
  shrink (OrdV0 x) = OrdV0 <$> shrinkConway x

instance (Arbitrary a, OrdRing a) => Arbitrary (ConwayV0Gen a) where
  arbitrary = ConwayV0 <$> arbConway (\() -> zero :: Ordinal) (id :: a -> a) maxDepth
  shrink (ConwayV0 x) = ConwayV0 <$> shrinkConway x

instance (Arbitrary a, OrdRing a) => Arbitrary (ConwayGen a) where
  arbitrary = ConwayGen <$> arbConway getOrdV0 (id :: a -> a) maxDepth
  shrink (ConwayGen x) = ConwayGen <$> shrinkConway x

instance Arbitrary (Conway Natural) where
  arbitrary = getConway <$> arbitrary
  shrink x = map getConway $ shrink (ConwayGen x)

instance Arbitrary SignExpansion where
  arbitrary = SE.fromList <$> arbitrary
  shrink x = SE.fromList <$> shrink (SE.toList x)

instance Arbitrary FSE where
  arbitrary = SED.fromList <$> arbitrary
  shrink x = SED.fromList <$> shrink (SED.toList x)
