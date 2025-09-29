{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Gen
  ( ConwayGen (..),
    ConwayV0Gen (..),
    DyadicGen (..),
    NaturalGen (..),
    FiniteOrdGen (..),
    OrdV0Gen (..),
  )
where

import Data.Conway.Conway
import Data.Conway.Dyadic
import Data.Conway.SignExpansion (SignExpansion)
import qualified Data.Conway.SignExpansion as SE
import Data.Conway.SignExpansion.Dyadic (FSE)
import qualified Data.Conway.SignExpansion.Dyadic as SED
import Data.Conway.Typeclasses
  ( AddSub (..),
    OrdRing,
    OrdZero (..),
    Zero (..),
  )
import Data.Foldable
import Test.QuickCheck

maxDepth :: Int
maxDepth = 4

maxLengthByDepth :: Int -> Gen Int
maxLengthByDepth d =
  case d of
    0 -> chooseInt (0, 2)
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

-- TODO
shrinkFinite :: (SED.FiniteSignExpansion a) => a -> [a]
shrinkFinite = map (SED.parseFiniteSE' . SED.fromList) . shrink . SED.toList . SED.finiteSE

shrinkTriple :: (OrdRing a, SED.FiniteSignExpansion a) => (Ordinal, Conway a, a) -> [(Ordinal, Conway a, a)]
shrinkTriple (a, p, c) =
  [(a, p, c') | c' <- shrinkFinite c]
    ++ [(a', p, c) | a' <- shrinkConway a]
    ++ [(a, p', c) | p' <- shrinkConway p]

monosList :: Conway a -> [(Ordinal, Conway a, a)]
monosList x = map (\(VebMono a p, c) -> (a, p, c)) $ termsList x

shrinkConway :: (OrdRing a, SED.FiniteSignExpansion a) => Conway a -> [Conway a]
shrinkConway x =
  [ foldl' (\s (o, p, c) -> add s (veb o p c)) zero list'
  | list' <- shrinkList shrinkTriple $ monosList x
  ]

newtype DyadicGen = DyadicGen {getDyadic :: Dyadic}
  deriving (Eq, Ord, Show, Zero, OrdZero)

newtype NaturalGen = NatGen {getNatural :: Natural}
  deriving (Eq, Ord, Show, Zero, OrdZero)

newtype FiniteOrdGen = FinOrd {getFiniteOrd :: Ordinal}
  deriving (Eq, Ord, Show, Zero, OrdZero)

newtype OrdV0Gen = OrdV0 {getOrdV0 :: Ordinal}
  deriving (Eq, Ord, Show, Zero, OrdZero)

newtype ConwayV0Gen a = ConwayV0 {getConwayV0 :: Conway a}
  deriving (Eq, Ord, Show, Zero, OrdZero)

newtype ConwayGen a = ConwayGen {getConway :: Conway a}
  deriving (Eq, Ord, Show, Zero, OrdZero)

instance Arbitrary DyadicGen where
  arbitrary = DyadicGen <$> ((makeDyadic . (`mod` maxInt) <$> arbitrary) <*> ((`mod` maxPow) <$> arbitrary))
    where
      maxInt = 16
      maxPow = 8
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

instance (Arbitrary a, SED.FiniteSignExpansion a, OrdRing a) => Arbitrary (ConwayV0Gen a) where
  arbitrary = ConwayV0 <$> arbConway (\() -> zero :: Ordinal) (id :: a -> a) maxDepth
  shrink (ConwayV0 x) = ConwayV0 <$> shrinkConway x

instance (Arbitrary a, SED.FiniteSignExpansion a, OrdRing a) => Arbitrary (ConwayGen a) where
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
