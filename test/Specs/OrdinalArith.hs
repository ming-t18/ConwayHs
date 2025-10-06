module Specs.OrdinalArith (testPropsOrdArith) where

import Data.Conway.Conway
import Data.Conway.OrdinalArith
import Data.Conway.SignExpansion ()
import Data.Conway.SignExpansion.Types ()
import Data.Conway.Typeclasses
  ( OrdZero (..),
    Zero (isZero),
  )
import Gen ()
import Props
import Test.Hspec
import Test.QuickCheck

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
prop_ordPowInfiniteExponent x (a0, b0) y =
  x > 1 && a0 > 0 && b0 > 0 && not (isFinite y) ==> ((x `ordPow` a0) `ordMult` finite b0 `ordAdd` 1) `ordMult` (x `ordPow` y) === x `ordPow` (a0 `ordAdd` y)

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
prop_ordPowLeadingTerm x y = not (isFinite x) && isPositive y ==> x `ordPow` mono1 y === mono1 (p0 `ordMult` mono1 y)
  where
    (v, _) = leadingTerm x
    p0 = unMono1 v

prop_ordPowMono1 :: Ordinal -> Property
prop_ordPowMono1 x = mono1 x === omega `ordPow` x

prop_ordRightSubAddBack :: Ordinal -> Ordinal -> Property
prop_ordRightSubAddBack l r = case ordRightSub l r of
  Nothing -> False ==> True
  Just x -> (l `ordAdd` x) === r

prop_ordDivRemProduct :: Ordinal -> Ordinal -> Property
prop_ordDivRemProduct d q = d /= 0 ==> (d `ordMult` q) `ordDivRem` d === (q, 0)

prop_ordDivRemScalingZeroRem :: Ordinal -> Ordinal -> Conway Natural -> Property
prop_ordDivRemScalingZeroRem a b d = d /= 0 && r == 0 ==> fst ((a `ordMult` b) `ordDivRem` d) === q `ordMult` b
  where
    (q, r) = ordDivRem a d

prop_ordDivRemBy1 :: Ordinal -> Property
prop_ordDivRemBy1 n = n `ordDivRem` 1 === (n, 0)

prop_ordDivRemAddBack :: Ordinal -> Conway Natural -> Property
prop_ordDivRemAddBack n d = d /= 0 ==> let (q, r) = ordDivRem n d in (d `ordMult` q) `ordAdd` r === n

prop_ordDivRemRemainderSmallest :: Ordinal -> Ordinal -> Property
prop_ordDivRemRemainderSmallest n d = d /= 0 ==> snd (ordDivRem n d) < d

-- * Testing

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

  describe "ordinal right subtraction" $ do
    it "no solution" $ qc (\x y -> x > y ==> ordRightSub x y === Nothing)
    it "subtract zero" $ qc (\x -> ordRightSub 0 x === Just x)
    it "subtract itself" $ qc (\x -> ordRightSub x x === Just 0)
    it "from sum" $ qc (\a b -> ordRightSub a (a `ordAdd` b) === Just b)
    it "add back" $ qc prop_ordRightSubAddBack

  describe "ordinal long division" $ do
    it "examples" $ do
      (veb 2 0 2 `ordDivRem` (veb1 2 0 + 1)) `shouldBe` (1, veb1 2 0)

    it "by zero" $ qc (\x -> x /= 0 ==> 0 `ordDivRem` x === (0, 0))
    it "div by 1" $ qc prop_ordDivRemBy1

    it "scaling by multipler, zero remainder" $ qc prop_ordDivRemScalingZeroRem

    it "from product" $ qc prop_ordDivRemProduct
    describe "add back" $ do
      it "any pair" $ qc prop_ordDivRemAddBack
      it "x / (x + 1)" $ qc (\x -> prop_ordDivRemAddBack x (x `ordAdd` 1))
      it "2x / (x + 1)" $ qc (\x -> prop_ordDivRemAddBack (x `ordMult` 2) (x `ordAdd` 1))
      it "3x / (x + 1)" $ qc (\x -> prop_ordDivRemAddBack (x `ordMult` 3) (x `ordAdd` 1))

    describe "remainder is smallest possible" $ do
      it "any pair" $ qc prop_ordDivRemRemainderSmallest
      it "x / (x + 1)" $ qc (\x -> prop_ordDivRemRemainderSmallest x (x `ordAdd` 1))
      it "2x / (x + 1)" $ qc (\x -> prop_ordDivRemRemainderSmallest (x `ordMult` 2) (x `ordAdd` 1))
      it "3x / (x + 1)" $ qc (\x -> prop_ordDivRemRemainderSmallest (x `ordMult` 3) (x `ordAdd` 1))
