{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

import Control.Monad (when)
import Data.Conway.Conway
import Data.Conway.Dyadic
import Data.Conway.FundamentalSeq
import Data.Conway.OrdinalArith
import qualified Data.Conway.RangeCompression as RC
import qualified Data.Conway.Seq as Seq
import qualified Data.Conway.Seq.InfList as I
import qualified Data.Conway.Seq.InfList as NE
import Data.Conway.SignExpansion ()
import Data.Conway.SignExpansion as SE
import Data.Conway.SignExpansion.Dyadic (FSE, FiniteSignExpansion, finiteSE, parseDyadicSE)
import Data.Conway.SignExpansion.Reduce (Reduced (..))
import qualified Data.Conway.SignExpansion.Reduce as R
import Data.Conway.SignExpansion.Types ()
import Data.Conway.Simplicity
import Data.Conway.Typeclasses
  ( AddSub (..),
    Mult (..),
    One (one),
    OrdRing,
    OrdZero (..),
    Zero (isZero, zero),
  )
import Data.Function (on)
import Data.Maybe (fromJust, isJust)
import qualified Data.Set as S
import Gen
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

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
prop_fsOrd_smaller :: Natural -> Ordinal -> Property
prop_fsOrd_smaller _ 0 = False ==> True
prop_fsOrd_smaller i x =
  case fsOrd x of
    Left _ -> False ==> True
    Right f -> i >= 0 ==> f `NE.index` i < x

-- | Fundamental sequence is increasing:
-- @i < j ==> x[i] < x[j]@
prop_fsOrd_increasing :: Natural -> Natural -> Ordinal -> Property
prop_fsOrd_increasing i j x =
  i >= 0
    && j >= 0
    && i
      /= j
        ==> ( case fsOrd x of
                Left _ -> False ==> True
                Right f -> True ==> (i `compare` j) === (f `NE.index` i) `compare` (f `NE.index` j)
            )

-- * Sign Expansions

prop_SENoConsecutiveSigns :: SignExpansion -> Bool
prop_SENoConsecutiveSigns = f . map fst . SE.toList
  where
    f :: [Bool] -> Bool
    f [] = True
    f [_] = True
    f (a : xs@(b : _))
      | a == b = False
      | otherwise = f xs

-- * Testing

-- qc :: Testable prop => prop -> IO ()
-- qc = quickCheckWith stdArgs { maxSuccess = 10000, maxShrinks = 1000 }
qc :: (Testable prop) => prop -> Property
qc = property

prop_parseMono1_unparse :: SignExpansion -> Property
prop_parseMono1_unparse p = p' /= p ==> vebArgSE (fst $ parseVeb1 True 0 p') === p
  where
    p' = mono1SE p

prop_parseVeb1_unparse :: Ordinal -> SignExpansion -> Property
prop_parseVeb1_unparse o p = p' /= p ==> vebArgSE (fst $ parseVeb1 True o p') === p
  where
    p' = veb1SE o p

prop_parseVeb1_noRemain :: Ordinal -> SignExpansion -> Property
prop_parseVeb1_noRemain o p = p' /= p ==> snd (parseVeb1 True o p') === mempty
  where
    p' = veb1SE o p

prop_parseVeb1_ordIso :: Ordinal -> SignExpansion -> SignExpansion -> Property
prop_parseVeb1_ordIso o p1 p2 = (vebArgSE (p p1) `compare` vebArgSE (p p2)) === (p1 `compare` p2)
  where
    p = fst . parseVeb1 True o . veb1SE o

prop_parseVeb1_nPlus :: Ordinal -> SignExpansion -> Property
prop_parseVeb1_nPlus o p = p' /= p ==> nPlusArg (fst $ parseVeb1 True o p') === countSigns True p
  where
    p' = veb1SE o p

prop_parseMono_unparse :: Ordinal -> SignExpansion -> Dyadic -> Property
prop_parseMono_unparse o p c
  | isZero c = get (parseMono $ vebSE o p c') === (mempty, mempty)
  | otherwise = p' /= p ==> get (parseMono $ vebSE o p c') === (p, c')
  where
    get (ParseVeb {vebArgSE = pse, coeffSE = cse}, _) = (pse, cse)
    p' = veb1SE o p
    c' = finiteSE c

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

type CD = Conway Dyadic

testReducedSignExpansion :: SpecWith ()
testReducedSignExpansion = do
  describe "reduced sign expansion" $ do
    it "reduceSingle when both are all minuses" $ do
      qc
        ( \n0 n1 ->
            n1
              > n0
                ==> let (p0, p1) = (minus n0, minus n1)
                     in R.reduceSingle p0 p1 === Reduced (minus $ ordRightSub' n0 n1)
        )

    it "unreduceSingle p0 (reduceSingle p0 p) === p when both are all minuses and p < p0" $ do
      qc
        ( \n0 n1 ->
            n1
              > n0
                ==> let (p0, p1) = (minus n0, minus n1)
                     in R.unreduceSingle p0 (R.reduceSingle p0 p1) === p1
        )

    it "unreduceSingle p0 (reduceSingle p0 p) === p if p < p0" $ do
      qc (\p0 p1 -> p1 < p0 ==> R.unreduceSingle p0 (R.reduceSingle p0 p1) === p1)

    it "unreduce [Reduced p] === Just [p]" $ do
      qc (\p -> R.unreduce [Reduced p] === Just [p])

    it "unreduce [Reduced p0, reduceSingle p0 p] === Just [p0, unreduceSingle p0 p] if p < p0" $ do
      qc (\(p0, p) -> p < p0 ==> R.unreduce [Reduced p0, R.reduceSingle p0 p] === Just [p0, p])

    when True $ do
      it "unreduce . reduce === Just for descending lists of sign expansions of length 2" $ do
        qc
          ( \p0 p1 ->
              p0
                /= p1
                  ==> let ps = if p0 < p1 then [p1, p0] else [p0, p1]
                       in R.unreduce (R.reduce ps) === Just ps
          )

      it "unreduce . reduce === Just for descending lists of exactlty 3 sign expansions" $ do
        qc
          ( \(p0, p1, p2) ->
              let ps = S.toDescList $ S.fromList [p0, p1, p2]
               in Prelude.length ps == 3 ==> R.unreduce (R.reduce ps) === Just ps
          )

      it "unreduce . reduce === Just for descending lists of sign expansions" $ do
        qc (\(S.toDescList . S.fromList -> ps) -> R.unreduce (R.reduce ps) === Just ps)

testSignExpansionConway :: SpecWith ()
testSignExpansionConway = do
  describe "isAllPluses/isAllMinuses" $ do
    it "isAllPluses agrees with sign expansion" $ do
      qc
        ( \(ConwayGen x) ->
            let res = case toList $ conwaySE (x :: CD) of
                  [] -> True
                  [(True, _)] -> True
                  _ -> False
             in SE.isAllPluses x === res
        )

    it "isAllMinuses agrees with sign expansion" $ do
      qc
        ( \(ConwayGen x) ->
            let res = case toList $ conwaySE (x :: CD) of
                  [] -> True
                  [(False, _)] -> True
                  _ -> False
             in SE.isAllMinuses x === res
        )

  describe "signExpansionConway" $ do
    describe "examples, no Veblen" $ do
      it "finite values" $ do
        conwaySE (0 :: CD) `shouldBe` empty
        conwaySE (1 :: CD) `shouldBe` plus 1
        conwaySE (-1 :: CD) `shouldBe` minus 1
        conwaySE (finite half :: CD) `shouldBe` (plus 1 +++ minus 1)
        conwaySE (finite (half * half) :: CD) `shouldBe` (plus 1 +++ minus 2)

      it "containing infinitesimals" $ do
        conwaySE (mono1 (-1) :: CD) `shouldBe` (plus 1 +++ minus omega)
        conwaySE (2 + mono1 (-1) :: CD) `shouldBe` (plus 3 +++ minus omega)
        conwaySE (-2 + mono1 (-1) :: CD) `shouldBe` (minus 2 +++ plus 1 +++ minus omega)
        conwaySE (mono (-1) 2 :: CD) `shouldBe` (plus 1 +++ minus omega +++ plus 1)
        conwaySE (mono (-1) half :: CD) `shouldBe` (plus 1 +++ minus omega +++ minus 1)
        conwaySE (2 + mono (-1) half :: CD) `shouldBe` (plus 3 +++ minus omega +++ minus 1)

      it "containing infinites" $ do
        conwaySE (mono1 1 :: CD) `shouldBe` plus (mono1 1)

    describe "examples, containing Veblen" $ do
      it "epsilons" $ do
        conwaySE (veb1 1 0 :: CD) `shouldBe` plus epsilon0
        conwaySE (veb1 1 (-1) :: CD) `shouldBe` (plus epsilon0 +++ minus (mono1 (mono1 (epsilon0 + 1))))

    it "negation symmetry" $ qc (\(ConwayGen (x :: CD)) -> conwaySE (neg x) === neg (conwaySE x))
    propsOrdIso "mono1SE" mono1SE
    propsOrdIso "conwaySE" (conwaySE . getConway :: ConwayGen Dyadic -> SignExpansion)
    it "ordinal number should be all pluses" $ qc (\o -> conwaySE o === plus o)

  describe "(+++) forms a monoid" $ do
    it "identity" $ qc (\x -> empty +++ x === x)
    it "assoc" $ qc (\x y z -> x +++ (y +++ z) === (x +++ y) +++ z)

  describe "negation" $ do
    it "negation is not equal" $ qc (\(x :: SignExpansion) -> if isEmpty x then neg x === x else neg x =/= x)
    it "preserves length" $ qc (\x -> SE.length x === SE.length (neg x))
    it "inverse" $ qc (\(x :: SignExpansion) -> neg (neg x) === x)

  describe "total order" $ do
    it "reflexive" $ qc (\(x :: SignExpansion) -> x === x)
    it "negation symmetry" $ qc (\(x :: SignExpansion) y -> x `compare` y === neg y `compare` neg x)
    it "transitive" $ qc (\(x :: SignExpansion) y z -> x <= y && y <= z ==> x <= z)
    it "prepending common prefix" $ qc (\x y z -> y `compare` z === (x +++ y) `compare` (x +++ z))

  describe "toList" $ do
    it "no zero length entries" $ qc (\(x :: SignExpansion) -> not (any (isZero . snd) (SE.toList x)))
    it "no consecutive signs" $ qc prop_SENoConsecutiveSigns

  describe "commonPrefix" $ do
    it "empty" $ qc (\x -> commonPrefix x empty === empty)
    it "comm" $ qc (\x y -> commonPrefix x y === commonPrefix y x)
    it "assoc" $ qc (\x y z -> commonPrefix (commonPrefix x y) z === commonPrefix x (commonPrefix y z))
    it "common prefix with self" $ qc (\x -> commonPrefix x x === x)
    it "prepend common prefix" $ qc (\x y z -> commonPrefix (x +++ y) (x +++ z) === x +++ commonPrefix y z)
    it "length of common prefix" $ qc (\x y -> let l = SE.length (commonPrefix x y) in l <= SE.length x && l <= SE.length y)

  describe "takeCommonPrefix" $ do
    it "result of commonPrefix" $ qc (\x y -> commonPrefix x y === fst (takeCommonPrefix x y))
    it "recover length" $ qc (\x y -> let (z, (x', y')) = takeCommonPrefix x y in (SE.length (z +++ x'), SE.length (z +++ y')) === (SE.length x, SE.length y))
    it "recover pair" $ qc (\x y -> let (z, (x', y')) = takeCommonPrefix x y in (z +++ x', z +++ y') === (x, y))

  describe "veb1" $ do
    it "fixed point on mono1" $ qc (\o p -> not (isZero o) ==> (let p' = veb1SE o p in mono1SE p' === p'))
    it "fixed point on veb1 of lower order" $ qc (\o1 o p -> o1 < o ==> (let p' = veb1SE o p in veb1SE o1 p' === p'))

testParseSignExpansion :: SpecWith ()
testParseSignExpansion = modifyMaxSuccess (`div` 5) $ do
  describe "detectVebOrder" $ do
    it "example (resulting SE does not contain the Veb order)" $ do
      let p = veb1SE 2 (Seq.rep 1 True) <> Seq.rep 1 False
      let p' = veb1SE 1 p
      detectVebOrder p' `shouldBe` 1

    it "detects the order of 2-segments starting with a plus" $
      qc
        ( \o o' n2 ->
            let p = veb1SE o' (Seq.rep 1 True) <> Seq.rep n2 False
                p' = veb1SE o p
             in p' /= p ==> detectVebOrder p' === o
        )

    it "detects the order of 2-segments starting with any pluses" $
      qc
        ( \o o' n1 n2 ->
            let p = veb1SE o' (Seq.rep n1 True) <> Seq.rep n2 False
                p' = veb1SE o p
             in p' /= p ==> detectVebOrder p' === o
        )

    it "detects the order of veb1SE" $
      qc
        ( \o p ->
            let p' = veb1SE o p
             in p' /= p ==> detectVebOrder p' === o
        )

  describe "parsing" $ do
    describe "parseMono" $ do
      it "advances parsing" $ qc (\se -> not (Seq.null se) ==> snd (parseMono se) =/= se)

    describe "conwaySE/parseToConway" $ do
      it "inverse (ConwayV0)" $ qc (\(ConwayV0 x) -> parseToConway (conwaySE x) === (x :: CD))
      it "inverse (arbitrary SE)" $ qc (\se -> conwaySE (parseToConway se :: CD) === se)
      it "inverse" $ qc (\(ConwayGen x) -> parseToConway (conwaySE x) === (x :: CD))

    describe "parseToConway" $ do
      let show' = show :: CD -> String
      it "halts without error for all ordinals" $ qc (\(n :: Ordinal) -> Prelude.length (show' $ parseToConway $ Seq.rep n True) > -1)
      it "halts without error" $ qc (\x -> Prelude.length (show' $ parseToConway x) > -1)

    -- Important backtracking counterexamples (detected by unreduce failing):
    --   The last segment of the real part belongs to the next value
    --     [+^2 -^w]
    --     [+^w -^(w.2)]
    --
    --   Choosing the correct Veblen order for parseVeb1
    --     w^(eps0 - 1) = [+^eps0 -^(w^(eps0 + 1))]
    --   Should have been:
    --     [+^(w^eps0) -^(w^(eps0 + 1))]

    describe "parseVeb1" $ do
      it "unparse mono1" $ qc prop_parseMono1_unparse
      it "unparse any veb1" $ qc prop_parseVeb1_unparse
      it "no remaining" $ qc prop_parseVeb1_noRemain
      it "order isomorphism" $ qc prop_parseVeb1_ordIso
      it "correct value of nPlusArg" $ qc prop_parseVeb1_nPlus

    describe "parseMono" $ do
      it "unparse monomial" $ qc prop_parseMono_unparse

-- | Given a @ParentSeq@, index the limit sequence or return the value itself if it a point.
indexParentSeq :: (OrdRing a, FiniteSignExpansion a) => ParentSeq a -> Natural -> Maybe (Conway a)
indexParentSeq s i =
  ( \case
      EPoint p -> p
      ELimit l -> ((`I.index` i) $ conwaySeq l)
  )
    <$> s

checkOrd :: (Show a, Ord a) => Ordering -> a -> a -> Property
checkOrd o x y =
  counterexample ("(" ++ show x ++ " `compare` " ++ show y ++ ") " ++ interpret res ++ " " ++ show o) res
  where
    res = compare x y == o
    interpret True = " == "
    interpret False = " /= "

checkBetween :: (Show a, Ord a) => (Maybe a, Maybe a) -> a -> Property
checkBetween (x0, y0) z =
  case (x0, y0) of
    (Nothing, Nothing) -> True === True
    (Just x, Nothing) -> checkOrd LT x z
    (Nothing, Just y) -> checkOrd LT z y
    (Just x, Just y) -> checkOrd LT x z .&&. checkOrd LT z y

testSimplicity :: SpecWith ()
testSimplicity = do
  -- TODO doesn't work
  when False $ describe "limit sequences" $ do
    it "increasing birthday" $ do
      qc
        ( \(ConwayGen (x :: CD), i0 :: Natural, j0 :: Natural) -> do
            let (i, j) = if i0 < j0 then (i0, j0) else (j0, i0)
                (l, r) = toPair $ lrConway x
                get s k = birthday $ fromJust $ indexParentSeq s k
                pl = checkOrd LT (get l i) (get l j)
                pr = checkOrd LT (get r i) (get r j)
             in i
                  /= j ==> case (l, r) of
                    (Just (ELimit _), Just (ELimit _)) -> pl .&. pr
                    (Just (ELimit _), _) -> pl
                    (_, Just (ELimit _)) -> pr
                    (_, _) -> False ==> True
        )

    it "left limit sequence is increasing and right limit sequence is decreasing" $ do
      qc
        ( \(ConwayGen (x :: CD), i :: Natural, j :: Natural) -> do
            let (l, r) = toPair $ lrConway x
                get s k = indexParentSeq s k `compare` indexParentSeq s (k + 1)
                check o s = checkOrd o (get s i) (get s j)
                (pl, pr) = (check GT l, check LT r)
             in i
                  /= j ==> case (l, r) of
                    (Just (ELimit _), Just (ELimit _)) -> pl .&. pr
                    (Just (ELimit _), _) -> pl
                    (_, Just (ELimit _)) -> pr
                    (_, _) -> False ==> True
        )

  describe "simplicity sequences: x = { left | right }" $ do
    -- "sufficiently large i" for sequences in general,
    -- but for our way of generating sequences, the condition is "i > 0"
    it "left[i] < right[i] for i > 0 and both being non-empty" $ do
      qc
        ( \(ConwayGen (x :: CD), i :: Natural) -> do
            let (l, r) = toPair $ lrConway x
                pair = (,) <$> indexParentSeq l i <*> indexParentSeq r i
             in i
                  > 0 ==> case pair of
                    Just (x', y') -> checkOrd LT x' y'
                    Nothing -> False ==> True
        )

    it "left[i] < completion < right[i] for i > 0" $ do
      qc
        ( \(ConwayGen (x :: CD), i :: Natural) ->
            let xc = lrConway x
                (l, r) = toPair xc
             in i > 0 ==> checkBetween (indexParentSeq l i, indexParentSeq r i) $ limLR xc
        )

    it "left and right have lower birthdays than the completion" $ do
      qc
        ( \(ConwayGen (x :: CD), i :: Natural) ->
            let xc = lrConway x
                bx = birthday x
                (l, r) = toPair xc
                bl = fmap birthday (indexParentSeq l i)
                br = fmap birthday (indexParentSeq r i)
             in case (bl, br) of
                  (Nothing, Nothing) -> True === True
                  (Just bl', Nothing) -> checkOrd LT bl' bx
                  (Nothing, Just br') -> checkOrd LT br' bx
                  (Just bl', Just br') -> checkOrd LT bl' bx .&&. checkOrd LT br' bx
        )

    it "completion recovers the original value" $ do
      qc (\(ConwayGen (x :: CD)) -> limLR (lrConway x) === x)

testPropsRangeCompression :: SpecWith ()
testPropsRangeCompression = do
  it "examples (ord)" $ do
    RC.ord' 0 `shouldBe` 0
    RC.ord' 0.5 `shouldBe` 1
    RC.ord' 0.75 `shouldBe` 2
    RC.ord' 1 `shouldBe` w
    RC.ord' (9 / 8) `shouldBe` (w + 1)

  it "toDyadic is defined" $
    qc (\x -> x < eps0 ==> isJust (RC.toDyadic x))

  it "ord is inverse of toDyadic" $
    qc (\x -> x < eps0 ==> Just x === (RC.ord =<< RC.toDyadic x))

testDyadic :: SpecWith ()
testDyadic = do
  propsOrdRing (id :: Dyadic -> Dyadic)

  describe "OrdZero" $ do
    propsOrdZero (id :: Dyadic -> Dyadic)

  describe "sign expansion (FSE)" $ do
    describe "OrdZero" $ do
      propsOrdZero (id :: FSE -> FSE)
    propsOrdIso "generating SE" (finiteSE :: Dyadic -> FSE)
    propsOrdIso "parsing SE" (parseDyadicSE :: FSE -> Dyadic)
    it "negation symmetry" $ do
      qc (\x -> parseDyadicSE (neg (finiteSE x)) === neg x)

    it "parseDyadicFSE is inverse of finiteFSE" $ do
      qc (\x -> parseDyadicSE (finiteSE x) === x)

main :: IO ()
main = hspec $ parallel $ modifyMaxSuccess (const 500) $ do
  testSimplicity

  when True $ do
    describe "Dyadic" $ do
      testDyadic

    describe "ConwayV0 Integer" $ do
      propsOrdRing (getConwayV0 :: ConwayV0Gen Integer -> Conway Integer)

    describe "Conway Integer" $ do
      propsOrdRing (getConway :: ConwayGen Integer -> Conway Integer)

    describe "Conway Dyadic" $ do
      propsOrdRing (getConway :: ConwayGen Dyadic -> Conway Dyadic)

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

    describe "Range compression (Ordinal -> Dyadic)" $ do
      testPropsRangeCompression

  when True $ describe "SignExpansion" $ do
    describe "OrdZero" $ do
      propsOrdZero (id :: SignExpansion -> SignExpansion)

    describe "SignExpansion parser" $ do
      testParseSignExpansion

    describe "generator" $ do
      testSignExpansionConway
      testReducedSignExpansion
