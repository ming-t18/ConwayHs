import Control.Monad (when)
import Data.Conway.Conway
import Data.Conway.Dyadic
import Data.Conway.FundamentalSeq
import qualified Data.Conway.RangeCompression as RC
import qualified Data.Conway.Seq.InfList as NE
import Data.Conway.SignExpansion ()
import Data.Conway.SignExpansion as SE
import Data.Conway.SignExpansion.Dyadic (FSE, finiteSE, parseDyadicSE)
import Data.Conway.SignExpansion.Types ()
import Data.Conway.Typeclasses
  ( AddSub (..),
    One (one),
    OrdZero (..),
    Zero (zero),
  )
import Data.Maybe (isJust)
import Gen
import OrdinalArith
import Props
import SignExpansion
import Simplicity
import Test.Hspec
import Test.Hspec.QuickCheck
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
