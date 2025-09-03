{-# LANGUAGE LambdaCase #-}

-- | Helpers for comparing Conway Normal Form terms and sign expansion entries.
module MonoTerm (MonoTerm (..), boolToOrder, flipOrder, prodOrder, pairToMonoTerm, signPairToMonoTerm, compareMonoTermList) where

import Typeclasses (OrdZero (..), Zero (..))

-- | Represents a monomial term @w^p . c@ where @c@ is the coefficient, which can be negative,
-- and @p@ is the exponent. The @OrdZero@ implementation is implemented according to that interpretation.
--
-- How @MonoTerm@s are compared, using @<>@ to combine the comparisons in the following order:
--
-- 1. Compare the signs of the coefficients
--
-- 2. Compare their exponents, reversing if both signs are negative
--
-- 3. Compare their coefficients
data MonoTerm p c = MT p c
  deriving (Eq, Show)

boolToOrder :: Bool -> Ordering
boolToOrder b = if b then GT else LT

flipOrder :: Ordering -> Ordering
flipOrder = neg

pairToMonoTerm :: (p, c) -> MonoTerm p c
pairToMonoTerm = uncurry MT

signPairToMonoTerm :: (Bool, p) -> MonoTerm p Ordering
signPairToMonoTerm (b, n) = MT n $ boolToOrder b

-- | Treating arguments and return type as @{LT, EQ, GT} -> {-1, 0, 1}@, and multiplies them.
prodOrder :: Ordering -> Ordering -> Ordering
prodOrder po = \case
  LT -> neg po
  EQ -> EQ
  GT -> po

compareMonoTermList :: (OrdZero p, OrdZero c) => [MonoTerm p c] -> [MonoTerm p c] -> Ordering
compareMonoTermList [] [] = EQ
compareMonoTermList (x : _) [] = x `compare` zero
compareMonoTermList [] (y : _) = zero `compare` y
compareMonoTermList (x : xs) (y : ys) = (x `compare` y) <> (xs `compareMonoTermList` ys)

instance (Ord p, OrdZero c) => Ord (MonoTerm p c) where
  compare (MT p1 c1) (MT p2 c2) = (sign1 `compare` sign2) <> sign1 `prodOrder` (p1 `compare` p2) <> (c1 `compare` c2)
    where
      (sign1, sign2) = (compareZero c1, compareZero c2)

instance (Zero p, Zero c) => Zero (MonoTerm p c) where
  zero = MT zero zero
  isZero (MT p c) = isZero p && isZero c

instance (OrdZero p, OrdZero c) => OrdZero (MonoTerm p c) where
  neg (MT p c) = MT p $ neg c
