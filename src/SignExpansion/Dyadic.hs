module SignExpansion.Dyadic
  ( FSE,
    FiniteSignExpansion (..),
    omitLead,
    fromFSE,
    dyadicSE,
    naturalSE,
    integerSE,
    intSE,
  )
where

import Control.Arrow (second)
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

(+++.) :: FSE -> FSE -> FSE
(+++.) [] ys = ys
(+++.) (x : xs) ys = x `consFSE` (xs +++. ys)

omitLead :: FSE -> FSE
omitLead [] = error "empty"
omitLead ((s, n) : xs) = (s, n - 1) : xs

-- | Typeclass for finite numeric datatypes with a finite number of signs
-- (or isomorphic to the sign expansion of a @Dyadic@).
class FiniteSignExpansion a where
  finiteSE :: a -> FSE

-- TODO add this
-- finiteBirthday :: a -> Natural

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
