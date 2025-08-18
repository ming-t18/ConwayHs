module SignExpansion.Dyadic
  ( FSE,
    FiniteSignExpansion (..),

    -- * Helpers
    fromFSE,
    (+++.),
    consFSE,
    omitLead,
    negFSE,

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
import Conway
import Dyadic
import SignExpansion.Types

infixr 5 +++.

-- | Finite-length sign expansion.
type FSE = [(Bool, Natural)]

fromFSE :: FSE -> SignExpansion
fromFSE = fromList . map (second finite)

consFSE :: (Bool, Natural) -> FSE -> FSE
consFSE p [] = [p]
consFSE (p0, n0) xs1@((p1, n1) : xs)
  | p0 == p1 = (p1, n0 + n1) : xs
  | otherwise = (p0, n0) : xs1

negFSE :: FSE -> FSE
negFSE = map (first not)

(+++.) :: FSE -> FSE -> FSE
(+++.) [] ys = ys
(+++.) (x : xs) ys = x `consFSE` (xs +++. ys)

-- | Omits the leading sign of an @FSE@.
-- Requires the @FSE@ to be non-empty.
omitLead :: FSE -> FSE
omitLead [] = error "empty"
omitLead ((s, n) : xs) = (s, n - 1) : xs

-- | Typeclass for finite numeric datatypes with a finite number of signs
-- (or isomorphic to the sign expansion of a @Dyadic@).
class FiniteSignExpansion a where
  finiteSE :: a -> FSE

  finiteBirthday :: a -> Natural
  finiteBirthday = sum . map snd . finiteSE

instance FiniteSignExpansion Dyadic where
  finiteSE = dyadicSE

instance FiniteSignExpansion Natural where
  finiteSE = naturalSE

instance FiniteSignExpansion Integer where
  finiteSE = integerSE

instance FiniteSignExpansion Int where
  finiteSE = intSE

dyadicSE :: Dyadic -> FSE
naturalSE :: Natural -> FSE
integerSE :: Integer -> FSE
intSE :: Int -> FSE
dyadicSE d =
  case unmakeDyadic d of
    (n, 0) -> integerSE n
    _ -> integerSE ip +++. dyadicSEFrac fp fm half [(fp > 0, 1)]
  where
    (ip, fp) = parts d
    fm = if fp > 0 then 1 else -1

dyadicSEFrac :: Dyadic -> Dyadic -> Dyadic -> FSE -> FSE
dyadicSEFrac x xm dx a =
  case x `compare` xm of
    EQ -> a
    LT -> dyadicSEFrac x (xm - dx) dx' (a +++. [(False, 1)])
    GT -> dyadicSEFrac x (xm + dx) dx' (a +++. [(True, 1)])
  where
    dx' = dx `shr` 1

naturalSE 0 = []
naturalSE n = [(True, n)]

integerSE 0 = []
integerSE n
  | n > 0 = [(True, fromIntegral n)]
  | otherwise = [(False, fromIntegral $ -n)]

intSE 0 = []
intSE n
  | n > 0 = [(True, fromIntegral n)]
  | otherwise = [(False, fromIntegral $ -n)]

parseDyadicSE :: [(Bool, Natural)] -> Dyadic
parseDyadicSE [] = 0
parseDyadicSE ((True, n) : xs) = fromIntegral (n - 1) + parseFracSE 1 half xs
parseDyadicSE ((False, n) : xs) = (-(fromIntegral n - 1)) + parseFracSE (-1) half xs

parseFracSE :: Dyadic -> Dyadic -> [(Bool, Natural)] -> Dyadic
parseFracSE x0 _ [] = x0
parseFracSE x0 dx ((sign, n) : xs) = parseFracSE x0' dx' xs
  where
    dx' = dx `shr` fromIntegral n
    delta = sum [dx `shr` fromIntegral (i - 1) | i <- [1 .. n]]
    x0' = if sign then x0 + delta else x0 - delta
