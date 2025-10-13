{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Specs.SignExpansion
  ( testReducedSignExpansion,
    testSignExpansionConway,
    testParseSignExpansion,
    testConstruct,
  )
where

import Control.Monad (when)
import Data.Conway.Conway
import Data.Conway.Dyadic
import Data.Conway.OrdinalArith
import qualified Data.Conway.Seq as Seq
import Data.Conway.SignExpansion as SE
import Data.Conway.SignExpansion.Dyadic (finiteSE)
import Data.Conway.SignExpansion.Reduce (Reduced (..))
import qualified Data.Conway.SignExpansion.Reduce as R
import Data.Conway.SignExpansion.Types ()
import Data.Conway.Typeclasses
  ( OrdZero (..),
    Zero (isZero),
  )
import qualified Data.Set as S
import Gen
import Props
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

type CD = Conway Dyadic

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

prop_SENoConsecutiveSigns :: SignExpansion -> Bool
prop_SENoConsecutiveSigns = f . map fst . SE.toList
  where
    f :: [Bool] -> Bool
    f [] = True
    f [_] = True
    f (a : xs@(b : _))
      | a == b = False
      | otherwise = f xs

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

testConstruct :: SpecWith ()
testConstruct = do
  describe "construct" $ do
    describe "base cases" $ do
      let ordSucc = (`ordAdd` 1)
      it "construct [] [+^n] = [+] for n > 1" $
        qc (\n -> n > 1 ==> construct empty (SE.fromList [(True, n)]) === SE.fromList [(True, 1)])
      it "construct [] [+^(n + 1) & S] = [+] for n > 1" $
        qc (\n s -> n > 1 ==> construct empty (SE.fromList [(True, ordSucc n)] +++ s) === SE.fromList [(True, 1)])
      it "construct [] [+ -^n] = [+ -^(n + 1)] for n >= 0" $
        qc (\n -> construct empty (SE.fromList [(True, 1), (False, n `ordAdd` 1)]) === SE.fromList [(True, 1), (False, n `ordAdd` 2)])

    it "negation symmetry" $ qc $ asc2 (\x y -> construct x y === neg (construct (neg y) (neg x)))
    it "prepend common prefix" $ qc (\p -> asc2 (\x y -> construct (p +++ x) (p +++ y) === p +++ construct x y))
    it "result shares a common prefix" $ qc (\x -> asc2 (\y z -> construct (x +++ y) (x +++ z) === x +++ construct y z))
    it "result is exclusively in between" $ qc $ asc2 (\x y -> let z = construct x y in x < z .&&. z < y)

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
