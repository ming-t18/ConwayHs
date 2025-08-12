{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Conway
  ( -- |
    --  Ordinal numbers and surreal numbers with the two-argument Veblen function.
    --
    --  The ordinal values representable is up to and not including the Feferman–Schütte ordinal.
    --
    --  The surreal values representable must have finite Conway normal forms (number of terms and nesting depth).
    --
    --  The Veblen order (the @a@ of @veb1 a b@) must be an ordinal number and is not generalized to negatives or surreals.

    -- * Types
    Conway,
    VebMono (VebMono),
    Ordinal,
    Natural,

    -- * Creation/decomposition
    conway,
    toMap,
    termsList,
    leadingTerm,

    -- * Construction helpers
    finite,
    finiteView,
    mono,
    mono1,
    w',
    veb,
    veb1,
    phi,
    omega,
    w,
    epsilon0,
    epsilon,
    eps0,
    eps,
    fromVebMono,
    fromVebMono1,

    -- * Other
    isVebFixed,
    isMono,
    dropLeadingTerm,
    dropTrailingTerm,
  )
where

import Data.Foldable
import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Numeric.Natural (Natural)
import OrdBag (OrdBag)
import qualified OrdBag
import Typeclasses

-- * Types

type Ordinal = Conway Natural

-- | Represents an ordinal number or surreal number in Cantor or Conway normal form.
-- The underlying representing is a strict `Map` from the two Veblen arguments
-- to a non-zero coefficient of the generic type.
--
-- The map representation follows the no-zero-values invarant of @OrdBag@.
newtype Conway a = Conway (Map (VebMono a) a)
  deriving (Eq)

-- | Represents a Veblen hierarchy monomial with coefficient of 1,
-- with the arguments being type @Conway a@.
--
-- @VebMono a b@ represents @veb1 a b@
data VebMono a = VebMono !Ordinal !(Conway a)

-- * Typeclass Implementations

instance (OrdZero a, One a, Show a) => Show (Conway a) where
  show x =
    case termsList x of
      [] -> "0"
      xs' -> intercalate " + " $ map showTerm xs'
    where
      showTerm (m, c) = showTerm' (show m) $ show c
      showTerm' "1" c' = c'
      showTerm' e' "1" = e'
      showTerm' e' c' = e' ++ "." ++ c'

instance Zero (Conway a) where
  zero = Conway M.empty
  isZero = null . toMap

instance (OrdZero a, One a) => Ord (Conway a) where
  compare a b = compare a' b'
    where
      a', b' :: OrdBag (VebMono a) a
      a' = OrdBag.fromMapUnchecked $ toMap a
      b' = OrdBag.fromMapUnchecked $ toMap b

instance Zero (VebMono a) where
  zero = VebMono zero zero
  isZero (VebMono a b) = isZero a && isZero b

instance (OrdZero a, One a) => OrdZero (Conway a) where
  neg (Conway x) = Conway (M.map neg x)

instance (OrdZero a, One a) => One (Conway a) where
  one = Conway (M.singleton zero one)
  isOne = (==) one

instance (AddSub a, One a) => AddSub (Conway a) where
  add (Conway a) (Conway b) = Conway $ zeroNormalize $ M.unionWith add a b
  sub (Conway a) (Conway b) = Conway $ zeroNormalize $ M.fromList $ map (\k -> (k, f k)) ks
    where
      ks = S.toList (M.keysSet a `S.union` M.keysSet b)
      f k = case (M.lookup k a, M.lookup k b) of
        (Nothing, Nothing) -> zero
        (Just x, Nothing) -> x
        (Nothing, Just y) -> neg y
        (Just x, Just y) -> sub x y

instance (AddSub a, Mult a) => Mult (Conway a) where
  mult (Conway a) b = foldr add zero [multMono (k1, v1) b | (k1, v1) <- M.toList a]

instance (OrdRing a) => OrdRing (Conway a)

instance (OrdRing a, Num a) => Num (Conway a) where
  (+) = add
  (-) = sub
  (*) = mult
  abs a = if isNegative a then neg a else a
  signum a
    | isZero a = zero
    | isPositive a = one
    | otherwise = neg one

  fromInteger = mono zero . fromInteger
  negate = neg

instance (One a, OrdZero a) => Eq (VebMono a) where
  (==) l@(VebMono a p) r@(VebMono b q)
    | a == b = p == q
    | a < b = p == fromVebMono1 r
    | otherwise = fromVebMono1 l == q

instance (OrdZero a, One a) => Ord (VebMono a) where
  compare l@(VebMono a p) r@(VebMono b q)
    -- V[a, p] <= V[a, q] ==> p <= q
    | a == b = compare p q
    -- V[a, p] <= V[b, q] ==> V[a, p] <= V[a, V[b, q]] ==> p <= V[b, q]
    | a < b = compare p (fromVebMono1 r)
    | otherwise = compare (fromVebMono1 l) q

instance (OrdZero a, One a) => OrdZero (VebMono a) where
  neg = error "cannot negate a VebMono"

instance (OrdZero a, One a, Show a) => Show (VebMono a) where
  show (VebMono a p) = showTerm (show a) (show p)
    where
      showTerm "0" "0" = "1"
      showTerm "0" "1" = "w"
      showTerm "0" [c] = "w^" ++ [c]
      showTerm "0" p' = "w^{" ++ p' ++ "}"
      showTerm "1" [c] = "ε_" ++ [c]
      showTerm "1" p' = "ε_{" ++ p' ++ "}"
      showTerm a' p' = "φ[" ++ a' ++ ", " ++ p' ++ "]"

instance (OrdZero a, One a) => Veblen (Conway a) Ordinal where
  veblen = veb1
  unVeblen (Conway xs) =
    case M.toList xs of
      [] -> Just (zero, zero)
      [(VebMono p a, c)]
        | c == one -> Just (p, a)
        | otherwise -> Nothing
      _ : (_ : _) -> Nothing

-- | WARNING: @recip@ is only defined for finite values.
instance (Fractional a, OrdZero a, OrdRing a) => Fractional (Conway a) where
  fromRational = finite . fromRational
  recip x = case finiteView x of
    Just x' -> finite $ recip x'
    Nothing -> error "Conway.recip: not defined"

-- * Creation/decomposition

-- | Given a @Map@ from the 2 Veblen arguments (2-tuple) to the coefficient, constructs a new @Conway@.
conway :: (OrdZero a) => Map (VebMono a) a -> Conway a
conway = Conway . zeroNormalize

-- | Given a @Conway@, returns its @Map@ representation from the Veblen arguments (2-tuple) to the coefficient.
toMap :: Conway a -> Map (VebMono a) a
toMap (Conway x) = x

-- | Given a @Conway@, returns its terms list in Cantor/Conway normal form order, which is
-- descending by coefficient.
termsList :: Conway a -> [(VebMono a, a)]
termsList = M.toDescList . toMap

-- | Given a @Conway@, returns its term in Cantor/Conway normal form, or zero
leadingTerm :: (OrdZero a) => Conway a -> (VebMono a, a)
leadingTerm x = case termsList x of
  [] -> (VebMono zero zero, zero)
  (t : _) -> t

-- | Given a @Conway@, returns the leading term and the @Conway@ without it.
dropLeadingTerm :: (OrdZero a) => Conway a -> ((VebMono a, a), Conway a)

-- | Given a @Conway@, return the @Conway@ without the trailing term and the trailing term.
dropTrailingTerm :: (OrdZero a) => Conway a -> (Conway a, (VebMono a, a))

dropLeadingTerm (Conway m) = if M.null m then ((zero, zero), conway M.empty) else (p, conway m')
  where
    (p, m') = M.deleteFindMax m

dropTrailingTerm (Conway m) = if M.null m then (conway M.empty, (zero, zero)) else (conway m', p)
  where
    (p, m') = M.deleteFindMin m

-- | Similar to @veb@
fromVebMono :: (Mult a) => (VebMono a, a) -> Conway a
fromVebMono (VebMono a b, c) = veb a b c

-- | Similar to @veb1@
fromVebMono1 :: (One a, OrdZero a) => VebMono a -> Conway a
fromVebMono1 (VebMono a b) = veb1 a b

zeroNormalize :: (OrdZero v) => Map k v -> Map k v
zeroNormalize = M.filter (not . isZero)

matchMono :: (Zero a) => Conway a -> Maybe (VebMono a, a)
matchMono (Conway xs) =
  case M.toList xs of
    [] -> Just (VebMono zero zero, zero)
    [(v, c)] -> Just (v, c)
    _ : (_ : _) -> Nothing

-- | True if and only if @veb1 a b == b@
isVebFixed :: (Zero a, One a, Eq a) => Ordinal -> Conway a -> Bool
isVebFixed a b = case matchMono b of
  Nothing -> False
  Just (VebMono a' _, c) -> c == one && isPositive a' && a < a'

-- | Construct a finite ordinal or surreal value.
finite :: (OrdZero a) => a -> Conway a
finite = conway . M.singleton (VebMono zero zero)

-- | If the @Conway@ has zero or 1 terms and is finite, returns @Just@ of the finite value. Otherwise, @None@.
finiteView :: (Zero a) => Conway a -> Maybe a
finiteView x =
  case termsList x of
    [] -> Just zero
    [(z, x')] | isZero z -> Just x'
    _ -> Nothing

-- | T rue if and only if the argument is a monomial (is zero or has only one term in its Cantor/Conway normal form)
isMono :: Conway a -> Bool
isMono x = case termsList x of [] -> True; [_] -> True; _ -> False

-- * Specific values

-- | The power of omega times a coefficient, @mono p c == (veb1 0 p) * c@
mono :: (Mult a) => Conway a -> a -> Conway a
mono = veb zero

mono1, w' :: (Mult a) => Conway a -> Conway a

-- | The power of omega, @mono1 p === veb1 0 p@
mono1 p = veb zero p one

veb1, phi :: (One a, OrdZero a) => Ordinal -> Conway a -> Conway a

-- | The two-argument Veblen function, @V(a, p)@
veb1 a p
  | isVebFixed a p = p
  | otherwise = conway $ M.singleton (VebMono a p) one

-- | The two-argument Veblen function, times a coefficient, @V(a, p) * c@
veb :: (Mult a) => Ordinal -> Conway a -> a -> Conway a
veb a p c
  | c == one = veb1 a p
  | otherwise = conway $ M.singleton (VebMono a p) c

-- | A sum of two-argument Veblen function terms with coefficients, @sum [(veb a p) * c | ...]@.
multMono :: (AddSub a, Mult a) => (VebMono a, a) -> Conway a -> Conway a
multMono (VebMono a p, c) (Conway x) = foldl' combineMono zero $ M.toList x
  where
    -- a > 0 and a' > 0
    -- Notation: V[a, b] = veb1 a b, V[a, b].c = veb a b c, V[0, p] = mono p

    -- combineMono :: (AddSub a, Mult a) => Conway a -> (VebMono a, a) -> Conway a
    combineMono s (VebMono a' p', c')
      --   V[0, p].c * V[0, p'].c'
      -- = V[0, p + p'] . (c * c')
      | isZero a && isZero a' = add s $ mono (add p p') c''
      --   V[0, p].c * V[a', p'].c'
      -- = (V[0, p] * V[0, V[a', p']]) . (c * c')
      -- = V[0, p + V[a', p']] (c * c')
      | isZero a && not (isZero a') = add s $ mono (add p (veb1 a' p')) c''
      --   V[a, p].c * V[0,  p'].c'
      -- = V[0, V[a, p]] * V[0, p'] . (c * c')
      -- = V[0, V[a, p'] + p'] . (c * c')
      | not (isZero a) && isZero a' = add s $ mono (add (veb1 a p) p') c''
      --   V[a, p].c * V[a', p'].c'
      -- = V[0, V[a, p]] * V[0, V[a', p']] . (c * c')
      --              = V[0, V[a, p] + V[a', p']] * (c * c')
      | otherwise = add s $ mono (add (veb1 a p) (veb1 a' p')) c''
      where
        c'' = mult c c'

omega, w :: (One a, OrdZero a) => Conway a
epsilon0, eps0 :: (One a, OrdZero a) => Conway a
epsilon, eps :: (One a, OrdZero a) => Conway a -> Conway a

-- | The simplest infinite ordinal, @omega = veb1 0 1@.
omega = conway $ M.singleton (VebMono zero one) one

-- | The first fixed point of the omega-map, @epsilon0 = veb1 1 0@.
epsilon0 = conway $ M.singleton (VebMono one zero) one

-- | Returns an epsilon number, @epsilon x = veb1 1 x@.
epsilon = veb1 one

-- | Alias of @omega@.
w = omega

-- | Alias of @mono1@.
w' = mono1

-- | Alias of @epsilon0@.
eps0 = epsilon0

-- | Alias of @epsilon@.
eps = epsilon

-- | Alias of @veb1@.
phi = veb1
