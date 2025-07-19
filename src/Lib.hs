{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
module Lib (
    -- * Types
    Conway,
    VebMono(VebMono),
    Ordinal,
    -- * Creation/decomposition
    conway,
    toMap,
    termsList,
    -- * Construction helpers
    finite,
    mono,
    mono1,
    veb,
    veb1,
    omega,
    epsilon0,
    epsilon
) where

import Data.Map.Strict(Map)
import qualified Data.Map.Strict as M
import Typeclasses
import Data.List (intercalate, sortBy)
import Data.Ord (comparing, Down (Down))
import GHC.Natural (Natural)

type Ordinal = Conway Natural

newtype Conway a = Conway (Map (Ordinal, Conway a) a)
    deriving (Eq)

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

instance (OrdZero a, One a) => Ord (Conway a) where
    compare a b = comp ta tb where
        ta = termsList a
        tb = termsList b
        compPair :: (OrdZero a, One a) => (VebMono a, a) -> (VebMono a, a) -> Ordering
        compPair (p, c) (q, d)
            | s1 /= s2 = compare s1 s2
            | s1 == LT = compare q p <> compare c d
            | otherwise = compare p q <> compare c d
            where s1 = compareZero c
                  s2 = compareZero d

        z :: Zero a => (VebMono a, a)
        z = (VebMono zero zero, zero)
        comp :: (OrdZero a, One a) => [(VebMono a, a)] -> [(VebMono a, a)] -> Ordering
        comp [] [] = EQ
        comp (x:_) [] = compPair x z
        comp [] (y:_) = compPair z y
        comp (x:xs) (y:ys) =
            case compPair x y of
                EQ -> comp xs ys
                other -> other

instance (OrdZero a, One a) => OrdZero (Conway a) where
    neg (Conway x) = Conway (M.map neg x)

instance (One a) => One (Conway a) where
    one = Conway (M.singleton (zero, zero) one)

instance (AddSub a, One a) => AddSub (Conway a) where
  add (Conway a) (Conway b) = Conway $ zeroNormalize $ M.unionWith add a b

instance (AddSub a, Mult a) => Mult (Conway a) where
  mult (Conway a) b = foldr add zero [ multMono (k1, v1) b | (k1, v1) <- M.toList a]

instance (OrdRing a) => OrdRing (Conway a) where

instance (OrdRing a, Num a) => Num (Conway a) where
    (+) = add
    (*) = mult
    abs a = if isNegative a then neg a else a
    signum a
        | isZero a = zero
        | isPositive a = one
        | otherwise = neg one

    fromInteger = mono zero . fromInteger
    negate = neg

-- | Given a `Map` from monomial to its coefficient, constructs a new `Conway`.
conway :: OrdZero a => Map (Ordinal, Conway a) a -> Conway a
conway = Conway . zeroNormalize

-- | Given a `Conway`, returns its `Map` representation.
toMap :: Conway a -> Map (Ordinal, Conway a) a
toMap (Conway x) = x

-- | Given a `Conway`, returns its terms list in Conway normal form order.
termsList :: (OrdZero a, One a) => Conway a -> [(VebMono a, a)]
termsList = sortBy (comparing Data.Ord.Down) . map toMonoTerm . M.toDescList . toMap where
    toMonoTerm :: ((Ordinal, Conway a), a) -> (VebMono a, a)
    toMonoTerm ((a, p), c) = (VebMono a p, c)

{- |
Represents a Veblen hierarchy mono1 with the specified Veblen order and its argument.

A Veblen monomial `[a, p]` has the following equality rule:

* If `a < b`, then `[a, [b, p]] == [b, p]`
-}
data VebMono a = VebMono Ordinal (Conway a)

instance (One a, OrdZero a) => Eq (VebMono a) where
    (==) l@(VebMono a p) r@(VebMono b q)
        | a == b = p == q
        | a < b = p == fromVebMono r
        | otherwise = fromVebMono l == q

instance (OrdZero a, One a) => Ord (VebMono a) where
    compare l@(VebMono a p) r@(VebMono b q)
        | a == b = compare p q
        | a < b = compare p (fromVebMono r)
        | otherwise = compare (fromVebMono l) q

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

fromVebMono :: (One a, OrdZero a) => VebMono a -> Conway a
fromVebMono (VebMono a' p') = veb1 a' p'

zeroNormalize :: OrdZero v => Map k v -> Map k v
zeroNormalize = M.filter (not . isZero)

matchMono :: Zero a => Conway a -> Maybe ((Ordinal, Conway a), a)
matchMono (Conway xs) =
    case M.toList xs of
        [] ->  Just ((zero, zero), zero)
        [((a, p), c)] -> Just ((a, p), c)
        _ : (_ : _) -> Nothing

-- | True if and only if V_a(b) = b
isVebFixed :: Zero a => Ordinal -> Conway a -> Bool
isVebFixed a b = case matchMono b of
                   Nothing -> False
                   Just ((a', _), _) -> isPositive a' && a < a'

finite :: OrdZero a => a -> Conway a
finite = conway . M.singleton (zero, zero)

-- * Specific values

-- | Creates a Veblen monomial $w^p.c$.
mono :: (Mult a) => Conway a -> a -> Conway a
mono p c = case matchMono p of
            Nothing -> conway $ M.singleton (zero, p) c
            Just ((a', p'), c') ->
                if isZero a' then
                    conway $ M.singleton (zero, p) c
                else
                    conway $ M.singleton (a', p') (mult c c')

-- | Creates a Veblen mono1 $w^p$.
mono1 :: (One a, OrdZero a) => Conway a -> Conway a
mono1 p = case matchMono p of
            Nothing -> conway $ M.singleton (zero, p) one
            Just ((a', p'), c') ->
                if isZero a' then
                    conway $ M.singleton (zero, p) one
                else
                    conway $ M.singleton (a', p') c'

-- | V_a(p)
veb1 :: (One a, OrdZero a) => Ordinal -> Conway a -> Conway a
veb1 a p
    | isVebFixed a p = p
    | otherwise = conway $ M.singleton (a, p) one

-- | V_a(p).c
veb :: (Mult a, AddSub a) => Ordinal -> Conway a -> a -> Conway a
veb a p c
    | c == one = veb1 a p
    | isVebFixed a p = mult p $ finite c
    | otherwise = conway $ M.singleton (a, p) c

-- V_a(p).c * x = sum [ V_a(p).c * V | pi ]
multMono :: (AddSub a, Mult a) => ((Ordinal, Conway a), a) -> Conway a -> Conway a
multMono ((a, p), c) (Conway x) = foldl combineMono zero $ M.toList x where
    -- a > 0 and a' > 0
    -- Notation: [a, b] = veb1 a b, [a, b].c = veb a b c
    -- [0, p].c * [0,  p'].c' = [0, p + p'] (c * c')
    -- [0, p].c * [a', p'].c' = [0, p + [a', p']] (c * c')
    -- [a, p].c * [0,  p'].c' = [0, [a, p'] + p'] (c * c')
    -- [a, p].c * [a', p'].c' = [0, [a, p]] * [0, [a', p']] * (c * c')
    --                        = [0, [a, p] + [a', p']] * (c * c')
    combineMono s ((a', p'), c')
      | isZero a && isZero a'       = add s $ mono (add p p') c''
      | isZero a && not (isZero a') = add s $ mono (add p (veb1 a' p')) c''
      | not (isZero a) && isZero a' = add s $ mono (add (veb1 a p) p') c''
      | otherwise                   = add s $ mono (add (veb1 a p) (veb1 a' p')) c''
      where c'' = mult c c'

omega :: (One a, OrdZero a) => Conway a
omega = conway $ M.singleton (zero, one) one

epsilon0 :: (One a, OrdZero a) => Conway a
epsilon0 = conway $ M.singleton (one, zero) one

epsilon :: (One a, OrdZero a) => Conway a -> Conway a
epsilon = veb1 one
