{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}

module SignExpansion.Types
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

    -- * Counting
    length,
    countSigns,

    -- * Common prefix
    commonPrefix,
    takeCommonPrefix,
  )
where

import Conway
import Data.Bifunctor (first)
import qualified Data.Foldable as F
import MonoTerm
import OrdinalArith
import qualified Seq.Types
import Typeclasses
import Prelude hiding (length, negate)

infixr 5 +++

-- | A sign expansion represented as a list of blocks
-- of pluses or minuses.
-- The internal representation is a list of @(sign, len)@
-- pairs with @True@ being plus and @False@ beng minus.
newtype SignExpansion = SignExpansion [(Bool, Ordinal)]
  deriving (Eq, Show)

instance Seq.Types.Seq SignExpansion Ordinal Bool where
  length = SignExpansion.Types.length
  (!) = index

instance Seq.Types.RunLengthSeq SignExpansion Ordinal Bool where
  replicate n True = plus n
  replicate n False = minus n

instance Seq.Types.ParsableSeq SignExpansion Ordinal Bool where
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

length :: SignExpansion -> Ordinal
length (SignExpansion xs) = F.foldl' (\a (_, b) -> a `ordAdd` b) 0 xs

index :: SignExpansion -> Ordinal -> Bool
index (SignExpansion []) _ = error "SignExpansion.index: out of bounds"
index (SignExpansion ((s, n) : ss)) i =
  case i `ordSymDiff` n of
    (LT, _) -> s
    (_, d) -> index (SignExpansion ss) d

commonPrefix :: SignExpansion -> SignExpansion -> SignExpansion
commonPrefix = curry $ recurse empty
  where
    recurse :: SignExpansion -> (SignExpansion, SignExpansion) -> SignExpansion
    recurse acc (SignExpansion [], _) = acc
    recurse acc (_, SignExpansion []) = acc
    recurse acc (SignExpansion (e0@(s0, n0) : xs0), SignExpansion ((s1, n1) : xs1))
      | s0 == s1 =
          if n0 == n1
            then recurse (acc +++ single e0) (SignExpansion xs0, SignExpansion xs1)
            else acc +++ single (s0, min n0 n1)
      | otherwise = acc

takeCommonPrefix :: SignExpansion -> SignExpansion -> (SignExpansion, (SignExpansion, SignExpansion))
takeCommonPrefix = curry $ recurse empty
  where
    recurse :: SignExpansion -> (SignExpansion, SignExpansion) -> (SignExpansion, (SignExpansion, SignExpansion))
    recurse acc p@(SignExpansion [], _) = (acc, p)
    recurse acc p@(_, SignExpansion []) = (acc, p)
    recurse acc p@(SignExpansion (e0@(s0, n0) : xs0), SignExpansion ((s1, n1) : xs1))
      | s0 == s1 =
          case n0 `ordSymDiff` n1 of
            (EQ, _) -> recurse (acc +++ single e0) (SignExpansion xs0, SignExpansion xs1)
            (LT, d) -> (acc +++ single (s0, n0), (SignExpansion xs0, single (s1, d) +++ SignExpansion xs1))
            (GT, d) -> (acc +++ single (s1, n1), (single (s0, d) +++ SignExpansion xs0, SignExpansion xs1))
      | otherwise = (acc, p)

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
