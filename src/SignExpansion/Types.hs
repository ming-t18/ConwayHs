module SignExpansion.Types
  ( SignExpansion,
    (+++),
    empty,
    isEmpty,
    toList,
    fromList,
    single,
    consSE,
    toConsSE,
    negSE,
  )
where

import Conway
import qualified Data.Bifunctor (first)
import OrdinalArith (ordAdd)
import Typeclasses

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
      (True, True) -> n1 `compare` n2 <> SignExpansion xs `compare` SignExpansion ys
      (False, False) -> n1 `compare` n2 <> SignExpansion xs `compare` SignExpansion ys
      (False, True) -> LT
      (True, False) -> GT

instance OrdZero SignExpansion where
  neg = negSE

isEmpty :: SignExpansion -> Bool
isEmpty (SignExpansion []) = True
isEmpty _ = False

empty :: SignExpansion
empty = SignExpansion []

negSE :: SignExpansion -> SignExpansion
negSE (SignExpansion xs) = SignExpansion $ map (Data.Bifunctor.first not) xs

toList :: SignExpansion -> [(Bool, Ordinal)]
toList (SignExpansion xs) = xs

fromList :: [(Bool, Ordinal)] -> SignExpansion
fromList = foldr consSE empty

single :: (Bool, Ordinal) -> SignExpansion
single = (`consSE` empty)

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

instance Semigroup SignExpansion where
  (<>) = (+++)

instance Monoid SignExpansion where
  mempty = empty
