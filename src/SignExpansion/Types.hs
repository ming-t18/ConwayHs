module SignExpansion.Types
  ( SignExpansion,
    (+++),
    empty,
    isEmpty,
    toList,
    fromList,
    single,
    length,
    plus,
    minus,
    consSE,
    toConsSE,
    negate,
    commonPrefix,
  )
where

import Conway
import qualified Data.Bifunctor (first)
import qualified Data.Foldable as F
import OrdinalArith (ordAdd)
import Typeclasses
import Prelude hiding (length, negate)

infixr 5 +++

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

commonPrefix :: SignExpansion -> SignExpansion -> SignExpansion
commonPrefix = recurse empty
  where
    recurse :: SignExpansion -> SignExpansion -> SignExpansion -> SignExpansion
    recurse acc (SignExpansion []) _ = acc
    recurse acc _ (SignExpansion []) = acc
    recurse acc (SignExpansion (e0@(s0, n0) : xs0)) (SignExpansion ((s1, n1) : xs1))
      | s0 == s1 =
          if n0 == n1
            then recurse (acc +++ single e0) (SignExpansion xs0) (SignExpansion xs1)
            else acc +++ single (s0, min n0 n1)
      | otherwise = acc
