{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Conway.SignExpansion.Dyadic
  ( FSE,
    FiniteSignExpansion (..),
    empty,

    -- * Helpers
    fromList,
    fromFSE,
    toList,
    (+++.),
    index,
    length,
    consFSE,
    omitLead,
    negFSE,
    plus,
    minus,

    -- * Sign Expansions of dyadics and subsets
    dyadicSE,
    naturalSE,
    integerSE,
    intSE,

    -- * Parsing
    parseDyadicSE,
  )
where

import Control.Arrow (first, second)
import Data.Conway.Conway
import Data.Conway.Dyadic as D
import Data.Conway.MonoTerm
import qualified Data.Conway.Seq.Types as Seq (RunLengthSeq (..), Seq (..))
import Data.Conway.SignExpansion.Types (SignExpansion)
import qualified Data.Conway.SignExpansion.Types as SE
import Data.Conway.Typeclasses
import Prelude hiding (length)

infixr 5 +++.

-- | Finite-length sign expansion.
--
-- Can represent the sign expansion of all @Dyadic@ values.
newtype FSE = FSE [(Bool, Natural)]
  deriving (Eq, Show)

instance Ord FSE where
  compare (FSE xs) (FSE ys) = compareMonoTermList (map signPairToMonoTerm xs) (map signPairToMonoTerm ys)

instance Zero FSE where
  zero = empty
  isZero = (==) zero

instance One FSE where
  one = FSE [(True, 1)]
  isOne = (==) one

instance OrdZero FSE where
  neg = negFSE

instance Semigroup FSE where
  (<>) = (+++.)

instance Monoid FSE where
  mempty = empty

instance Seq.Seq FSE Natural Bool where
  length = fseLength
  (!) = index

instance Seq.RunLengthSeq FSE Natural Bool where
  replicate n True = plus n
  replicate n False = minus n

empty :: FSE
empty = FSE []

toList :: FSE -> [(Bool, Natural)]
toList (FSE l) = l

fromList :: [(Bool, Natural)] -> FSE
fromList = foldl (\se (s, n) -> se +++. signs s n) empty

fromFSE :: FSE -> SignExpansion
fromFSE = SE.fromList . map (second finite) . toList

consFSE :: (Bool, Natural) -> FSE -> FSE
consFSE p (FSE []) = FSE [p]
consFSE (p0, n0) (FSE xs1@((p1, n1) : xs))
  | p0 == p1 = FSE ((p1, n0 + n1) : xs)
  | otherwise = FSE ((p0, n0) : xs1)

negFSE :: FSE -> FSE
negFSE = FSE . map (first not) . toList

(+++.) :: FSE -> FSE -> FSE
(+++.) (FSE []) (FSE ys) = FSE ys
(+++.) (FSE (x : xs)) (FSE ys) = x `consFSE` (FSE xs +++. FSE ys)

length, fseLength :: FSE -> Natural
length = fseLength
fseLength = sum . map snd . toList

index :: FSE -> Natural -> Bool
index (FSE []) _ = error "FSE.index: out of bounds"
index (FSE ((s, n) : ss)) i
  | i < n = s
  | otherwise = index (FSE ss) (i - n)

-- | Omits the leading sign of an @FSE@.
-- Requires the @FSE@ to be non-empty.
omitLead :: FSE -> FSE
omitLead (FSE []) = error "empty"
omitLead (FSE ((s, n) : xs)) = FSE ((s, n - 1) : xs)

-- | Typeclass for finite numeric datatypes with a finite number of signs
-- (or isomorphic to the sign expansion of a @Dyadic@).
class FiniteSignExpansion a where
  finiteSE :: a -> FSE

  finiteBirthday :: a -> Natural
  finiteBirthday = sum . map snd . toList . finiteSE

instance FiniteSignExpansion Dyadic where
  finiteSE = dyadicSE

instance FiniteSignExpansion Natural where
  finiteSE = naturalSE

instance FiniteSignExpansion Integer where
  finiteSE = integerSE

instance FiniteSignExpansion Int where
  finiteSE = intSE

instance FiniteSignExpansion FSE where
  finiteSE = id

nat1 :: Natural
nat1 = 1

dyadicSE :: Dyadic -> FSE
naturalSE :: Natural -> FSE
integerSE :: Integer -> FSE
intSE :: Int -> FSE
dyadicSE d =
  case unmakeDyadic d of
    (n, 0) -> integerSE n
    _ -> integerSE ip +++. dyadicSEFrac fp fm half (signs (fp > 0) nat1)
  where
    (ip, fp) = parts d
    fm = if fp > 0 then 1 else -1

dyadicSEFrac :: Dyadic -> Dyadic -> Dyadic -> FSE -> FSE
dyadicSEFrac x xm dx a =
  case x `compare` xm of
    EQ -> a
    LT -> dyadicSEFrac x (xm - dx) dx' (a +++. signs False nat1)
    GT -> dyadicSEFrac x (xm + dx) dx' (a +++. signs True nat1)
  where
    dx' = dx `shr` 1

plus, minus :: (Integral a) => a -> FSE
plus n = FSE [(True, fromIntegral n)]
minus n = FSE [(False, fromIntegral n)]

signs :: (Integral a) => Bool -> a -> FSE
signs _ 0 = empty
signs s n = FSE [(s, fromIntegral n)]

naturalSE 0 = empty
naturalSE n = plus n

integerSE 0 = empty
integerSE n
  | n > 0 = plus n
  | otherwise = minus $ -n

intSE 0 = empty
intSE n
  | n > 0 = plus n
  | otherwise = minus $ -n

parseDyadicSE :: FSE -> Dyadic
parseDyadicSE (FSE []) = 0
parseDyadicSE (FSE ((True, n) : xs)) = fromIntegral (n - 1) + parseFracSE 1 half xs
parseDyadicSE (FSE ((False, n) : xs)) = (-(fromIntegral n - 1)) + parseFracSE (-1) half xs

parseFracSE :: Dyadic -> Dyadic -> [(Bool, Natural)] -> Dyadic
parseFracSE x0 _ [] = x0
parseFracSE x0 dx ((sign, n) : xs) = parseFracSE x0' dx' xs
  where
    dx' = dx `shr` fromIntegral n
    delta = sum [dx `shr` fromIntegral (i - 1) | i <- [1 .. n]]
    x0' = if sign then x0 + delta else x0 - delta
