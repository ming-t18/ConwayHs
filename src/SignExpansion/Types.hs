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
import qualified Data.Bifunctor (first)
import qualified Data.Foldable as F
import OrdinalArith
import Typeclasses
import Prelude hiding (length, negate)

infixr 5 +++

-- | A sign expansion represented as a list of blocks
-- of pluses or minuses.
-- The internal representation is a list of @(sign, len)@
-- pairs with @True@ being plus and @False@ beng minus.
newtype SignExpansion = SignExpansion [(Bool, Ordinal)]
  deriving (Eq, Show)

instance Zero SignExpansion where
  zero = empty
  isZero = isEmpty

instance Ord SignExpansion where
  compare (SignExpansion []) (SignExpansion []) = EQ
  compare (SignExpansion ((True, _) : _)) (SignExpansion []) = GT
  compare (SignExpansion ((False, _) : _)) (SignExpansion []) = LT
  compare (SignExpansion []) (SignExpansion ((True, _) : _)) = LT
  compare (SignExpansion []) (SignExpansion ((False, _) : _)) = GT
  compare (SignExpansion ((s1, n1) : xs)) (SignExpansion ((s2, n2) : ys)) =
    case (s1, s2) of
      (True, True) | n1 == n2 -> SignExpansion xs `compare` SignExpansion ys
      (True, True) -> n1 `compare` n2
      (False, False) | n1 == n2 -> SignExpansion xs `compare` SignExpansion ys
      (False, False) -> n2 `compare` n1
      (False, True) -> LT
      (True, False) -> GT

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
negate (SignExpansion xs) = SignExpansion $ map (Data.Bifunctor.first not) xs

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
index (SignExpansion ((s, n) : ss)) i
  | i < n = s
  | otherwise = index (SignExpansion ss) (ordRightSub' i n)

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
          if n0 == n1
            then recurse (acc +++ single e0) (SignExpansion xs0, SignExpansion xs1)
            else
              if n0 < n1
                then
                  (acc +++ single (s0, n0), (SignExpansion xs0, single (s1, ordRightSub' n0 n1) +++ SignExpansion xs1))
                else
                  (acc +++ single (s1, n1), (single (s0, ordRightSub' n1 n0) +++ SignExpansion xs0, SignExpansion xs1))
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
      | n' == n0 = acc +++ single (s0, n') +++ single (not s, fst $ takeLeading (not s) $ SignExpansion xs)
      | n' < n0 = acc +++ single (s0, n')
      | otherwise = loop (ordRightSub' n' n0, acc +++ single (s0, n0)) $ SignExpansion xs
    loop _ (SignExpansion []) = error "takeUntilNthSign: out of bounds"
