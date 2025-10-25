{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Conway.SignExpansion.Types
  ( -- * Construction and decomposition
    SignExpansion,
    empty,
    (+++),
    fromList,
    single,
    plus,
    minus,
    consSE,

    -- * Helpers
    toList,
    toConsSE,
    negate,
    isEmpty,
    index,
    takeLeading,
    takeUntilNthSign,
    lastSign,

    -- * Counting
    length,
    countSigns,

    -- * Common prefix
    commonPrefix,
    takeCommonPrefix,
    construct,
  )
where

import Data.Bifunctor (first)
import Data.Conway.Conway
import Data.Conway.MonoTerm
import Data.Conway.OrdinalArith
import qualified Data.Conway.Seq as Seq
import qualified Data.Conway.SignExpansion.CommonPrefix as C
import Data.Conway.Typeclasses
import qualified Data.Conway.Typeclasses.ConwayOps as CO
import qualified Data.Foldable as F
import Prelude hiding (length, negate)

infixr 5 +++

-- | A sign expansion represented as a list of blocks
-- of pluses or minuses.
-- The internal representation is a list of @(sign, len)@
-- pairs with @True@ being plus and @False@ beng minus.
newtype SignExpansion = SignExpansion [(Bool, Ordinal)]
  deriving (Eq, Show)

instance Seq.Seq SignExpansion Ordinal Bool where
  length = signExpansionLength
  (!) = index

instance Seq.RunLengthSeq SignExpansion Ordinal Bool where
  replicate n True = plus n
  replicate n False = minus n

instance Seq.ParsableSeq SignExpansion Ordinal Bool where
  lookahead :: SignExpansion -> Maybe (Bool, Ordinal)
  lookahead (SignExpansion []) = Nothing
  lookahead (SignExpansion (p : _)) = Just p
  consume :: SignExpansion -> (Bool, Ordinal) -> Maybe SignExpansion
  consume se (_, 0) = Just se
  consume (SignExpansion []) _ = Nothing
  consume (SignExpansion ((s', n') : ss)) (s, n)
    | s /= s' = Nothing
    | otherwise =
        case n `ordSymDiff` n' of
          (GT, _) -> Nothing
          (EQ, _) -> Just $ SignExpansion ss
          -- (LT, d) | d == n' -> error "consume: does not advance"
          (LT, d) -> Just $ SignExpansion ((s', d) : ss)

instance Zero SignExpansion where
  zero = empty
  isZero = isEmpty

instance Ord SignExpansion where
  compare (SignExpansion xs) (SignExpansion ys) = compareMonoTermList (map signPairToMonoTerm xs) (map signPairToMonoTerm ys)

instance OrdZero SignExpansion where
  neg = negate

instance Semigroup SignExpansion where
  (<>) = (+++)

instance Monoid SignExpansion where
  mempty = empty

isEmpty :: SignExpansion -> Bool
isEmpty (SignExpansion []) = True
isEmpty _ = False

empty :: SignExpansion
empty = SignExpansion []

negate :: SignExpansion -> SignExpansion
negate (SignExpansion xs) = SignExpansion $ map (first not) xs

toList :: SignExpansion -> [(Bool, Ordinal)]
toList (SignExpansion xs) = xs

fromList :: [(Bool, Ordinal)] -> SignExpansion
fromList = foldr consSE empty

single :: (Bool, Ordinal) -> SignExpansion
single = (`consSE` empty)

plus, minus :: Ordinal -> SignExpansion
plus n = single (True, n)
minus n = single (False, n)

consSE :: (Bool, Ordinal) -> SignExpansion -> SignExpansion
consSE (_, 0) xs = xs
consSE p (SignExpansion []) = SignExpansion [p]
consSE p0@(s0, n0) (SignExpansion xs0@((s1, n1) : xs))
  | s0 == s1 = SignExpansion ((s1, n0 `ordAdd` n1) : xs)
  | otherwise = SignExpansion (p0 : xs0)

toConsSE :: SignExpansion -> Maybe ((Bool, Ordinal), SignExpansion)
toConsSE (SignExpansion []) = Nothing
toConsSE (SignExpansion (x : xs)) = Just (x, SignExpansion xs)

(+++) :: SignExpansion -> SignExpansion -> SignExpansion
(+++) (SignExpansion ls) r = foldr consSE r ls

length, signExpansionLength :: SignExpansion -> Ordinal
length = signExpansionLength
signExpansionLength (SignExpansion xs) = F.foldl' (\a (_, b) -> a `ordAdd` b) 0 xs

index :: SignExpansion -> Ordinal -> Bool
index (SignExpansion []) _ = error "SignExpansion.index: out of bounds"
index (SignExpansion ((s, n) : ss)) i =
  case i `ordSymDiff` n of
    (LT, _) -> s
    (_, d) -> index (SignExpansion ss) d

countSigns :: Bool -> SignExpansion -> Ordinal
countSigns s0 (SignExpansion xs) = foldl (\c (s, n) -> if s == s0 then c `ordAdd` n else c) 0 xs

takeLeading :: Bool -> SignExpansion -> (Ordinal, SignExpansion)
takeLeading _ e@(SignExpansion []) = (0, e)
takeLeading s se@(SignExpansion ((s0, n0) : xs))
  | s /= s0 = (0, se)
  | otherwise = (n0, SignExpansion xs)

-- | Given @(s, n)@ and a sign expansion, take its longest prefix having exactly @n@ signs of @s@.
takeUntilNthSign :: (Bool, Ordinal) -> SignExpansion -> SignExpansion
takeUntilNthSign (s, n) = loop (n, empty)
  where
    loop :: (Ordinal, SignExpansion) -> SignExpansion -> SignExpansion
    loop (0, acc) (SignExpansion []) = acc
    loop (0, acc) (SignExpansion ((s0, n0) : _))
      | s0 == not s = acc +++ single (s0, n0)
      | otherwise = acc
    loop (n', acc) (SignExpansion ((s0, n0) : xs))
      | s0 /= s = loop (n', acc +++ single (s0, n0)) $ SignExpansion xs
      | otherwise =
          case n' `ordSymDiff` n0 of
            (EQ, _) -> acc +++ single (s0, n') +++ single (not s, fst $ takeLeading (not s) $ SignExpansion xs)
            (LT, _) -> acc +++ single (s0, n')
            (GT, d) -> loop (d, acc +++ single (s0, n0)) $ SignExpansion xs
    loop _ (SignExpansion []) = error "takeUntilNthSign: out of bounds"

commonPrefix, commonPrefix_ :: SignExpansion -> SignExpansion -> SignExpansion
commonPrefix (SignExpansion xs) (SignExpansion ys) = fromList $ C.commonPrefix xs ys
commonPrefix_ = commonPrefix

takeCommonPrefix :: SignExpansion -> SignExpansion -> (SignExpansion, (SignExpansion, SignExpansion))
takeCommonPrefix (SignExpansion xs) (SignExpansion ys) = (fromList cs', (fromList xs', fromList ys'))
  where
    (cs', (xs', ys')) = C.takeCommonPrefix ordSymDiff xs ys

-- | Returns the simplest @SignExpansion@ that is between the two arguments: @x < construct x y && construct x y < y@
construct :: SignExpansion -> SignExpansion -> SignExpansion
construct x@(SignExpansion xs) y@(SignExpansion ys)
  | x >= y = error "construct: the first arg must be less than the second arg"
  | otherwise = fromList $ C.construct ordSymDiff xs ys

lastSign :: SignExpansion -> Maybe Bool
lastSign (SignExpansion []) = Nothing
lastSign (SignExpansion [(s, _)]) = Just s
lastSign (SignExpansion (_ : xs)) = lastSign $ SignExpansion xs

instance CO.Birthday Ordinal SignExpansion where
  birthday = length

instance CO.CommonPrefix SignExpansion where
  commonPrefix = commonPrefix_

instance CO.BinaryConstruct SignExpansion where
  binaryConstruct = construct
