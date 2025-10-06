{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Specs.Simplicity (testSimplicity) where

import Data.Conway.Conway
import Data.Conway.Dyadic
import qualified Data.Conway.Seq.InfList as I
import Data.Conway.SignExpansion ()
import Data.Conway.SignExpansion as SE
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.SignExpansion.Types ()
import Data.Conway.Simplicity
import Data.Conway.Simplicity.Prefix
import Data.Conway.Typeclasses (OrdRing)
import Data.Maybe (fromJust)
import Gen
import Props
import Test.Hspec
import Test.QuickCheck

type CD = Conway Dyadic

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
  counterexample ("(" ++ show x ++ " `compare` " ++ show y ++ ")" ++ interpret res ++ " " ++ show o) res
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

propIncreasingLR :: (Show a, OrdRing a, FiniteSignExpansion a) => Natural -> Natural -> Conway a -> Property
propIncreasingLR i j x =
  case (l, r) of
    (Just (ELimit _), Just (ELimit _)) -> pl .&. pr
    (Just (ELimit _), _) -> pl
    (_, Just (ELimit _)) -> pr
    (_, _) -> False ==> True
  where
    (l, r) = toPair $ lrConway x
    get = indexParentSeq
    check o s = checkOrd o (get s j) (get s i)
    (pl, pr) = (check GT l, check LT r)

testSimplicity :: SpecWith ()
testSimplicity = do
  describe "leadingPlusesOnly" $ do
    it "all pluses" $
      qc (\(ConwayGen (x :: CD)) -> isAllPluses $ leadingPlusesOnly x)

    it "sign expansion coherence" $
      qc (\(ConwayGen (x :: CD)) -> conwaySE (leadingPlusesOnly x) === SE.fromList (take 1 $ SE.toList $ conwaySE x))

  describe "limit sequences" $ do
    it "increasing birthday" $ do
      qc
        ( \(ConwayGen (x :: CD), i0 :: Natural, j0 :: Natural) ->
            i0
              /= j0 ==> do
                let (i, j) = (min i0 j0, max i0 j0)
                    (l, r) = toPair $ lrConway x
                    get s k = birthday $ fromJust $ indexParentSeq s k
                    pl = checkOrd LT (get l i) (get l j)
                    pr = checkOrd LT (get r i) (get r j)
                 in case (l, r) of
                      (Just (ELimit _), Just (ELimit _)) -> pl .&. pr
                      (Just (ELimit _), _) -> pl
                      (_, Just (ELimit _)) -> pr
                      (_, _) -> False ==> True
        )

    it "left limit sequence is increasing and right limit sequence is decreasing" $ do
      qc
        ( \(ConwayGen (x :: CD), i0 :: Natural, j0 :: Natural) ->
            i0 /= j0 ==> let (i, j) = (max i0 j0, min i0 j0) in propIncreasingLR i j x
        )

    it "left limit sequence is increasing and right limit sequence is decreasing at 0 and 1" $ do
      qc (\(ConwayGen (x :: CD)) -> propIncreasingLR 0 1 x)

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
