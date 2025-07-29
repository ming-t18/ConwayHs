{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
import Control.Monad()
import Gen
import Test.Hspec
import Test.QuickCheck
import Lib
import Typeclasses
    ( OrdRing,
      OrdZero(neg, isPositive),
      Zero(zero, isZero),
      AddSub(..),
      Mult(..),
      One(one) )
import Dyadic
import FundamentalSeq

import qualified Data.List.NonEmpty as NE
import OrdinalArith
import Numeric.Natural

-- * Ordering

prop_compareTransitive :: Ord a => a -> a -> a -> Property
prop_compareTransitive a b c
    | a <= b && a <= c = True ==> a <= c
    | a <= c && c <= b = True ==> a <= b
    | a >= b && b >= c = True ==> a >= c
    | a >= c && c >= b = True ==> a >= b
    | b <= a && a <= c = True ==> b <= c
    | b >= a && a >= c = True ==> b >= c
    | otherwise = False ==> False

prop_compareReverse :: Ord a => a -> a -> Bool
prop_compareReverse a b = compare a b == f (compare b a) where
    f EQ = EQ
    f LT = GT
    f GT = LT

prop_compareNegation :: OrdZero a => a -> a -> Bool
prop_compareNegation a b = compare a b == f (compare (neg a) (neg b)) where
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

prop_multZero :: Mult a => a -> Bool
prop_multZero x = isZero (mult zero x) && isZero (mult x zero)

prop_multOne :: Mult a => a -> Bool
prop_multOne x = mult one x == x && mult x one == x

prop_multComm :: (Mult a, Show a) => a -> a -> Property
prop_multComm a b = mult a b === mult b a

prop_multAssoc :: (Mult a, Show a) => a -> a -> a -> Property
prop_multAssoc a b c = mult a (mult b c) === mult (mult a b) c

prop_multDistr :: (AddSub a, Mult a, Show a) => a -> a -> a -> Property
prop_multDistr a b c = mult a (add b c) === add (mult a b) (mult a c)

prop_multNeg :: (AddSub a, Mult a, Show a) => a -> a -> Property
prop_multNeg a b = neg (mult a b) === mult (neg a) b

prop_sqPos :: Mult a => a -> Bool
prop_sqPos a = if a == zero then mult a a == zero else mult a a > zero

prop_multPreserveOrder :: Mult a => a -> a -> a -> Property
prop_multPreserveOrder m a b
  | isZero m = False ==> True === True
  | isPositive m = True ==> (a <= b) === (mult m a <= mult m b)
  | otherwise = True ==> (b <= a) === (mult m a <= mult m b)

-- * Ordinal Arithmetic

prop_ordAddZero :: Ordinal -> Property
prop_ordAddZero x = x `ordAdd` 0 === x

prop_ordAddFinite :: Natural -> Natural -> Property
prop_ordAddFinite x y = finite x `ordAdd` finite y === finite (x + y)

prop_ordAddSucc :: Ordinal -> Ordinal -> Property
prop_ordAddSucc x y = x `ordAdd` (y + 1) === (x `ordAdd` y) + 1

prop_ordAddOrderPreservingLeft :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordAddOrderPreservingLeft x y z = x `compare` y === (z `ordAdd` x) `compare` (z `ordAdd` y)

prop_ordAddAssoc :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordAddAssoc x y z = (x `ordAdd` y) `ordAdd` z === x `ordAdd` (y `ordAdd` z)

prop_ordAddAssocSelf :: Ordinal -> Property
prop_ordAddAssocSelf x = (x `ordAdd` x) `ordAdd` x === x `ordAdd` (x `ordAdd` x)

prop_ordMultZero :: Ordinal -> Property
prop_ordMultZero x = x `ordMult` 0 === 0

prop_ordMultOne :: Ordinal -> Property
prop_ordMultOne x = x `ordMult` 1 === x

prop_ordMultFinite :: Natural -> Natural -> Property
prop_ordMultFinite x y = finite x `ordMult` finite y === finite (x * y)

prop_ordMultSucc :: Ordinal -> Ordinal -> Property
prop_ordMultSucc x y = x `ordMult` (y + 1) === (x `ordMult` y) `ordAdd` x

prop_ordMultAssoc :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordMultAssoc x y z = (x `ordMult` y) `ordMult` z === x `ordMult` (y `ordMult` z)

prop_ordMultAssocSelf :: Ordinal -> Property
prop_ordMultAssocSelf x = (x `ordMult` x) `ordMult` x === x `ordMult` (x `ordMult` x)

prop_ordMultLeftDistr :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordMultLeftDistr x y z = x `ordMult` (y `ordAdd` z) === (x `ordMult` y) `ordAdd` (x `ordMult` z)

prop_ordMultMono1 :: Ordinal -> Ordinal -> Property
prop_ordMultMono1 x y = mono1 x `ordMult` mono1 y === mono1 (x `ordAdd` y)

-- * Power

prop_ordZeroPow :: Ordinal -> Property
prop_ordZeroPow x = not (isZero x) ==> 0 `ordPow` x === 0

prop_ordPowZero :: Ordinal -> Property
prop_ordPowZero x = x `ordPow` 0 === 1

prop_ordPowOne :: Ordinal -> Property
prop_ordPowOne x = x `ordPow` 1 === x

-- | For finite @b, c@, @b^(w.c) = (b^w)^c = w^c@
prop_ordPowFiniteMultW :: Natural -> Natural -> Property
prop_ordPowFiniteMultW b c = b > 1 && c > 1 ==> finite b `ordPow` mono 1 c === mono1 (finite c)

-- | For finite @b, c@, @b^(w^c) = b^(w.w^(c-1)) = (b^w)^(w^(c-1)) = w^(w^(c-1))@
prop_ordPowFiniteWPFinite :: Natural -> Natural -> Property
prop_ordPowFiniteWPFinite b c = b > 1 && c > 1 ==> finite b `ordPow` mono1 (finite c) === mono1 (mono1 $ finite (c - 1))

prop_ordPowSucc :: Ordinal -> Ordinal -> Property
prop_ordPowSucc x y = x `ordPow` (y + 1) === (x `ordPow` y) `ordMult` x

prop_ordPowFinite :: Natural -> Natural -> Property
prop_ordPowFinite x y = finite x `ordPow` finite y === finite (x ^ y)

prop_ordPowExponentSum :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordPowExponentSum x y z = (x `ordPow` (y `ordAdd` z)) === (x `ordPow` y) `ordMult` (x `ordPow` z)

prop_ordPowInfiniteExponent :: Ordinal -> (Ordinal, Natural) -> Ordinal -> Property
prop_ordPowInfiniteExponent x (a0, b0) y
  = x > 1 && a0 > 0 && b0 > 0 && not (isFinite y) ==> ((x `ordPow` a0) `ordMult` finite b0 `ordAdd` 1) `ordMult` (x `ordPow` y) === x `ordPow` (a0 `ordAdd` y)

-- | large exponents can cause hangs
prop_ordPowExponentProduct :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordPowExponentProduct x y z =
    isPositive y && isPositive z ==> (x `ordPow` (y `ordMult` z)) === (x `ordPow` y) `ordPow` z

prop_ordPowOrderPreserving :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordPowOrderPreserving x y z
  | x == y = False ==> True
  | x < y = True ==> (x `ordPow` z) <= (y `ordPow` z)
  | otherwise = True ==> (x `ordPow` z) >= (y `ordPow` z)

-- | @x^(w^y) = x^(p0 . w^y)@ where @x = w^p0 . c0 + ...@
-- ProofWiki: https://proofwiki.org/wiki/Ordinal_Exponentiation_via_Cantor_Normal_Form/Corollary
-- with @w@ being the base.
prop_ordPowLeadingTerm :: Ordinal -> Ordinal -> Property
prop_ordPowLeadingTerm x y = not (isFinite x) && isPositive y ==> x `ordPow` mono1 y === mono1 (p0 `ordMult` mono1 y) where
    (v, _) = leadingTerm x
    p0 = unMono1 v

prop_ordPowMono1 :: Ordinal -> Property
prop_ordPowMono1 x = mono1 x === omega `ordPow` x

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

-- * Fundamental Sequences

-- | All elements of the fundamental sequence are smaller
-- @x[i] < x@
prop_fsOrd_smaller :: Int -> Ordinal -> Property
prop_fsOrd_smaller _ 0 = False ==> True
prop_fsOrd_smaller i x =
  case fsOrd x of
    Left _ -> False ==> True
    Right f -> i >= 0 ==> f NE.!! i < x

-- | Fundamental sequence is increasing:
-- @i < j ==> x[i] < x[j]@
prop_fsOrd_increasing :: Int -> Int -> Ordinal -> Property
prop_fsOrd_increasing i j x =
  i >= 0 && j >= 0 && i /= j ==> (
    case fsOrd x of
      Left _ -> False ==> True
      Right f -> True ==> (i `compare` j) === (f NE.!! i) `compare` (f NE.!! j)
  )

-- * Testing

-- qc :: Testable prop => prop -> IO ()
-- qc = quickCheckWith stdArgs { maxSuccess = 10000, maxShrinks = 1000 }
qc :: Testable prop => prop -> Property
qc p = property p

testPropsOrdRing :: (Show a, Show t, Arbitrary a, OrdRing t) => (a -> t) -> SpecWith ()
testPropsOrdRing i = do
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

testPropsOrdArith :: SpecWith ()
testPropsOrdArith = do
  describe "ordinal addition" $ do
    it "identity" $ qc prop_ordAddZero
    it "assoc" $ qc prop_ordAddAssoc
    it "assoc same value" $ qc prop_ordAddAssocSelf
    it "add finite" $ qc prop_ordAddFinite
    it "succ" $ qc prop_ordAddSucc
    it "preserves order" $ qc prop_ordAddOrderPreservingLeft

  describe "ordinal multiplication" $ do
    it "zero" $ qc prop_ordMultZero
    it "identity" $ qc prop_ordMultOne
    it "assoc" $ qc prop_ordMultAssoc
    it "assoc same value" $ qc prop_ordMultAssocSelf
    it "by finite" $ qc prop_ordMultFinite
    it "succ" $ qc prop_ordMultSucc
    it "left distr" $ qc prop_ordMultLeftDistr
    it "mono1" $ qc prop_ordMultMono1

  describe "ordinal power" $ do
    it "zero pow" $ qc prop_ordZeroPow
    it "pow zero" $ qc prop_ordPowZero
    it "pow on" $ qc prop_ordPowOne
    it "finite^w" $ qc prop_ordPowFiniteMultW
    it "w^finite" $ qc prop_ordPowFiniteWPFinite
    it "succ" $ qc prop_ordPowSucc
    it "finite" $ qc prop_ordPowFinite
    it "exp sum" $ qc prop_ordPowExponentSum
    it "finite^infinite" $ qc prop_ordPowInfiniteExponent
    it "exp product" $ qc prop_ordPowExponentProduct
    it "order preservation" $ qc prop_ordPowOrderPreserving
    it "leading term" $ qc prop_ordPowLeadingTerm
    it "mono1" $ qc prop_ordPowMono1

main :: IO ()
main = hspec $ do
  describe "Dyadic" $ do
    testPropsOrdRing (id :: Dyadic -> Dyadic)

  describe "ConwayV0 Integer" $ do
    testPropsOrdRing ((\(ConwayV0 x) -> x) :: ConwayV0Gen Integer -> Conway Integer)

  describe "Conway Integer" $ do
    testPropsOrdRing ((\(ConwayGen x) -> x) :: ConwayGen Integer -> Conway Integer)

  describe "Conway Dyadic" $ do
    testPropsOrdRing ((\(ConwayGen x) -> x) :: ConwayGen Dyadic -> Conway Dyadic)

  describe "Ordinal arithmetic" $ do
    testPropsOrdArith

  describe "Veb" $ do
    it "Veb increasing map" $ do
      qc prop_vebIncrMap
    it "Veb decreasing map" $ do
      qc prop_vebDecrMap

  describe "Ordinal fundamental sequences" $ do
    it "Entries are smaller" $ do
      qc prop_fsOrd_smaller
    it "FS is increasing" $ do
      qc prop_fsOrd_increasing
