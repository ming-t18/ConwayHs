{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props
  ( qc,
    propsOrdZero,
    propsOrdIso,
    propsOrdRing,
  )
where

import Data.Conway.SignExpansion ()
import Data.Conway.SignExpansion.Types ()
import Data.Conway.Typeclasses
  ( AddSub (..),
    Mult (..),
    One (one),
    OrdRing,
    OrdZero (..),
    Zero (isZero, zero),
  )
import Data.Function (on)
import Test.Hspec
import Test.QuickCheck

qc :: (Testable prop) => prop -> Property
qc = property

-- * Ordering

prop_compareTransitive :: (Ord a) => a -> a -> a -> Property
prop_compareTransitive a b c
  | a <= b && a <= c = True ==> a <= c
  | a <= c && c <= b = True ==> a <= b
  | a >= b && b >= c = True ==> a >= c
  | a >= c && c >= b = True ==> a >= b
  | b <= a && a <= c = True ==> b <= c
  | b >= a && a >= c = True ==> b >= c
  | otherwise = False ==> False

prop_compareReverse :: (Ord a) => a -> a -> Bool
prop_compareReverse a b = compare a b == f (compare b a)
  where
    f EQ = EQ
    f LT = GT
    f GT = LT

prop_compareNegation :: (OrdZero a) => a -> a -> Bool
prop_compareNegation a b = compare a b == f (compare (neg a) (neg b))
  where
    f EQ = EQ
    f LT = GT
    f GT = LT

-- * Natural sum and product

prop_orderedAdd :: (AddSub a) => a -> a -> a -> Bool
prop_orderedAdd a b c
  | a <= b = add a c <= add b c
  | otherwise = add a c >= add b c

prop_addZero :: (AddSub a, Show a) => a -> Property
prop_addZero a = add a zero === a

prop_addComm :: (AddSub a, Show a) => a -> a -> Property
prop_addComm a b = add a b === add b a

prop_addAssoc :: (AddSub a, Show a) => a -> a -> a -> Property
prop_addAssoc a b c = add a (add b c) === add (add a b) c

prop_dneg :: (OrdZero a, Show a) => a -> Property
prop_dneg a = a === neg (neg a)

prop_addNegIsSub :: (Show a, AddSub a) => a -> a -> Property
prop_addNegIsSub a b = a `add` neg b === a `sub` b

prop_multZero :: (Mult a) => a -> Bool
prop_multZero x = isZero (mult zero x) && isZero (mult x zero)

prop_multOne :: (Mult a) => a -> Bool
prop_multOne x = mult one x == x && mult x one == x

prop_multComm :: (Mult a, Show a) => a -> a -> Property
prop_multComm a b = mult a b === mult b a

prop_multAssoc :: (Mult a, Show a) => a -> a -> a -> Property
prop_multAssoc a b c = mult a (mult b c) === mult (mult a b) c

prop_multDistr :: (AddSub a, Mult a, Show a) => a -> a -> a -> Property
prop_multDistr a b c = mult a (add b c) === add (mult a b) (mult a c)

prop_multNeg :: (AddSub a, Mult a, Show a) => a -> a -> Property
prop_multNeg a b = neg (mult a b) === mult (neg a) b

prop_sqPos :: (Mult a) => a -> Bool
prop_sqPos a = if a == zero then mult a a == zero else mult a a > zero

prop_multPreserveOrder :: (Mult a) => a -> a -> a -> Property
prop_multPreserveOrder m a b
  | isZero m = False ==> True === True
  | isPositive m = True ==> (a <= b) === (mult m a <= mult m b)
  | otherwise = True ==> (b <= a) === (mult m a <= mult m b)

-- * Properties

propsOrdZero :: (OrdZero a, Show a, Arbitrary a) => (a -> a) -> SpecWith ()
propsOrdZero i = do
  describe "Zero" $ do
    it "isZero === (== zero)" $ qc (\(i -> x) -> isZero x === (x == zero))
    it "isZero/isPositive/isNegative in terms of (`compare` zero)" $
      qc
        ( \(i -> x) ->
            case x `compare` zero of
              LT -> isNegative x
              EQ -> isZero x
              GT -> isPositive x
        )

  describe "Ord" $ do
    it "comparability" $ qc (\(i -> x) (i -> y) -> x <= y || y <= x)
    it "transitivity" $
      qc
        ( \(i -> x) (i -> y) (i -> z) ->
            let xy = x <= y
                yz = y <= z
                xz = x <= z
                zy = z <= y
                yx = y <= x
                zx = z <= x
             in if xy && yz
                  then xz
                  else
                    if xz && zy
                      then xy
                      else
                        if zy && yx
                          then zx
                          else
                            not (zx && xy) || zy
        )
    it "reflexivity" $ qc (\(i -> x) -> x == x)
    it "antisymmetry" $ qc (\(i -> x) (i -> y) -> not (x <= y && y <= x) || (x == y))

  describe "OrdZero" $ do
    it "neg zero === zero" $ do
      (neg (i zero) == i zero) `shouldBe` True

    it "double negation" $ do
      qc (\(i -> x) -> neg (neg x) == x)

    it "compare `on` neg reverses comparison" $ do
      qc (\(i -> x) (i -> y) -> (compare `on` neg) x y == y `compare` x)

propsOrdIso :: (OrdZero a, OrdZero b, Show a, Arbitrary a) => String -> (a -> b) -> SpecWith ()
propsOrdIso desc f = do
  it ("order isomorphic: " ++ desc) $ qc (\x y -> f x `compare` f y === x `compare` y)
  it ("order isomorphic on negation: " ++ desc) $ qc (\x y -> f x `compare` f y === neg y `compare` neg x)

propsOrdRing :: (Show a, Show t, Arbitrary a, OrdRing t) => (a -> t) -> SpecWith ()
propsOrdRing i = do
  let i1 f a = f (i a)
  let i2 f a b = f (i a) (i b)
  let i3 f a b c = f (i a) (i b) (i c)

  describe "total order" $ do
    it "same equal" $ qc (i1 (\a -> (a `compare` a) === EQ))
    it "transitive" $ qc (i3 prop_compareTransitive)
    it "comparison reversal" $ qc (i2 prop_compareReverse)
    it "comparison negation" $ qc (i2 prop_compareNegation)
    it "comparison double negation" $ qc (i1 prop_dneg)

  describe "natural sum" $ do
    it "identity" $ qc (i1 prop_addZero)
    it "comm" $ qc (i2 prop_addComm)
    it "assoc" $ qc (i3 prop_addAssoc)
    it "assoc same value" $ qc (i1 (\a -> prop_addAssoc a a a))
    it "add negative value" $ qc (i2 prop_addNegIsSub)
    it "ordered add" $ qc (i3 prop_orderedAdd)

  describe "natural product" $ do
    it "zero" $ qc (i1 prop_multZero)
    it "identity" $ qc (i1 prop_multOne)
    it "comm" $ qc (i2 prop_multComm)
    it "assoc" $ qc (i3 prop_multAssoc)
    it "assoc same value" $ qc (i1 (\a -> prop_multAssoc a a a))
    it "negative" $ qc (i2 prop_multNeg)
    it "square is positive" $ qc (i1 prop_sqPos)
    it "preserves order" $ qc (i3 prop_multPreserveOrder)
    it "distr" $ qc (i3 prop_multDistr)
