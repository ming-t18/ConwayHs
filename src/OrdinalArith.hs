{-# LANGUAGE ScopedTypeVariables #-}
module OrdinalArith (
  ordAdd,
  ordMult,
  ordMultByFinite,
  ordPow,
  ordRightSub,
  ordRightSub',
  ordDivRem,
  isFinite,
  isInfinite,
  maybeFinite,
  unMono1,
) where

import Prelude hiding (isInfinite)
import Conway
import Numeric.Natural
import qualified Data.Map.Strict as M
import Typeclasses
import Data.Foldable

data VebMonoKind =
  -- | Finite value: @veb1 0 0@
  Fin
  -- | Power of @w@: @veb1 0 p@ where @p > 0@
  | WP !Ordinal
  -- | Veblen numbers above: @veb1 p c@
  | Other !(VebMono Natural)

-- | Classifies a @VebMono Natural@ into one of the @VebMonoKind@
classifyVebMono :: VebMono Natural -> VebMonoKind
classifyVebMono (VebMono 0 0) = Fin
classifyVebMono (VebMono 0 p) = WP p
classifyVebMono v = Other v

-- | Given a @VebMono@, rewrite it as @mono1 p@
-- and returns the @p@.
unMono1 :: VebMono Natural -> Ordinal
unMono1 (VebMono 0 p) = p
unMono1 v = fromVebMono1 v

-- | Is the ordinal number finite?
isFinite, isInfinite :: Ordinal -> Bool
isFinite x = case leadingTerm x of
  (v, _) | isZero v -> True
  _ -> False

isInfinite = not . isFinite

-- | Is the ordinal number finite?
--
-- * If yes, return @Some@ of the finite value as a @Natural@
--
-- * Otherwise, return @None@.
maybeFinite :: Ordinal -> Maybe Natural
maybeFinite x = case leadingTerm x of
  (v, a) | isZero v -> Just a
  _ -> Nothing

-- | Ordinal addition.
ordAdd :: Ordinal -> Ordinal -> Ordinal

ordAdd a b = a' + b where
  (VebMono p1 c1, _) = leadingTerm b
  pCutoff = veb1 p1 c1
  a' = conway $ M.filterWithKey (\(VebMono p c) _ -> veb1 p c >= pCutoff) $ toMap a

-- | Ordinal multiplication.
ordMult :: Ordinal -> Ordinal -> Ordinal
ordMult a = foldl' (\s -> (s `ordAdd`) . ordMultByMono a) 0 . termsList

ordMultByMono :: Ordinal -> (VebMono Natural, Natural) -> Ordinal
ordMultByMono o (v, c)
  | isZero c || isZero o = 0
  | isZero v =
      ordMultByFinite o c
  | otherwise =
    -- only leading terms matters: (V[p].c) is a limit ordinal
    -- https://proofwiki.org/wiki/Ordinal_Multiplication_via_Cantor_Normal_Form/Limit_Base
    -- (V[v0].c0 + ...).(V[v].c)
    let (v0, f) = leadingTerm o in
    ordMultMonoByMono1 (v0, f) v `ordMultByFinite` c


ordMultMonoByMono1 :: (VebMono Natural, Natural) -> VebMono Natural -> Ordinal
ordMultMonoByMono1 (v1, f) v2 =
  case (classifyVebMono v1, classifyVebMono v2) of
    -- (w^0.c) . w^0 = (1.c).1 = c
    (Fin, Fin) -> finite f
    -- f . V[p, c] = V[p, c]         -- where f is finite and V[p, c] is infinite
    (Fin, _) -> fromVebMono1 v2
    -- In the cases below, the finite term is absorbed
    -- w^a . w^b = w^[a + b]
    (WP a, WP b) -> mono1 $ a `ordAdd` b
    -- w^a . V[p', c'] = w^a . w^V[p', c'] = w^[a + V[p', c']]
    (WP a, _) -> mono1 $ a `ordAdd` fromVebMono1 v2
    -- w^a . V[p, c] = w^a . w^V[p, c] = w^[a + V[p, c]]
    (_, WP a) -> mono1 $ fromVebMono1 v1 `ordAdd` a
    -- = V[p, c] . V[p', c']
    -- = w^V[p, c] . w^V[p', c']     -- given p > 0 and p' > 0
    -- = w^[V[p, c] + V[p', c']]     -- law of exponents
    (_, _) -> mono1 $ fromVebMono1 v1 `ordAdd` fromVebMono1 v2

ordMultByFinite :: Ordinal -> Natural -> Ordinal
ordMultByFinite = repeatBinOp ordAdd 0

-- * Power

ordPow :: Ordinal -> Ordinal -> Ordinal
-- law of exponents: a^(b + c + ...) = a^b * a^c * ...
ordPow a b = foldl' (\p m -> p `ordMult` ordPowByMono a m) 1 $ termsList b

-- | Ordinal power @x^p@ where @p@ is a monomial
ordPowByMono :: Ordinal -> (VebMono Natural, Natural) -> Ordinal
ordPowByMono o p0@(v1, a) =
  case (maybeFinite o, classifyVebMono v1) of
    -- finite^finite
    (Just x, Fin) -> finite (x ^ a)
    -- finite^infinite
    (Just x, _) -> ordPowFiniteByMono x p0
    -- infinite^finite
    (Nothing, Fin) -> ordPowInfiniteByFinite o a
    -- infinite^infinite
    (Nothing, _) ->
      -- o = (w^v0.c0 + ...)
      -- exponent = w^v . a
      let (v0, _) = leadingTerm o in
      -- Applying https://proofwiki.org/wiki/Ordinal_Exponentiation_via_Cantor_Normal_Form/Corollary
      --   o^(w^v . a)
      -- = w^[v0 . w^v . a]
      mono1 (unMono1 v0 `ordMult` mono (unMono1 v1) a)

-- | Ordinal power @x^p@ where @x@ is finite and @p@ is infinite
ordPowFiniteByMono :: Natural -> (VebMono Natural, Natural) -> Ordinal

-- TODO doesn't work, law of exponent multiplication:
-- 2 `ordPow` (epsilon0 `ordMult` epsilon0) = mono1 (epsilon0 * 2)
-- (2 `ordPow` epsilon0) `ordPow` epsilon0 = mono1 (mono1 (epsilon0 * 2))
ordPowFiniteByMono 1 _ = 1
ordPowFiniteByMono 0 (_, _) = 0
ordPowFiniteByMono _ (_, 0) = 1
ordPowFiniteByMono _ (v, a) =
  case classifyVebMono v of
    -- x^a: finite by finite
    Fin -> error "ordPow(finite, finite): this case shouldn't be handled here"
    -- x^(w^b . a) = (x^(w^b))^a
    -- if b is finite:
    --   = (x^(w . w^(b-1)))^a
    --   = [ (x^w)^(w^(b-1)) ]^a
    --   = [ w^(w^(b-1)) ]^a
    -- if b is infinite:
    --   = (w^(w^b))^a
    WP b -> case maybeFinite b of
              Just b' -> ordPowInfiniteByFinite (mono1 $ mono1 $ finite $ b' - 1) a
              Nothing -> ordPowInfiniteByFinite (mono1 $ mono1 b) a
    -- x^(v.a) = x^(w^v.a) = (x^(w^v))^a = w^(v.a)
    _ -> mono1 (fromVebMono1 v `ordMult` finite a)


-- | Ordinal power @x^p@ where @x@ is finite and @p@ is finite
ordPowInfiniteByFinite :: Ordinal -> Natural -> Ordinal
ordPowInfiniteByFinite = repeatBinOp ordMult 1

-- * Right subtraction

-- | Given ordinals @l@ and @r@, solve for @x@ such that @l + x === y@
--
-- Returns a @Maybe@ based on if the solution exists.
ordRightSub :: Ordinal -> Ordinal -> Maybe Ordinal
ordRightSub 0 a = Just a
ordRightSub l r
  | l > r = Nothing
  | l == r = Just 0
  | otherwise =
    if p1 /= p2 then
      Just r
    else
      case c2 - c1 of
        0 -> ordRightSub l' r'
        dc -> Just (fromVebMono (p2, dc) `ordAdd` r')
    where
      ((p1, c1), l') = dropLeadingTerm l
      ((p2, c2), r') = dropLeadingTerm r

-- | Like @ordRightSub@, except it is a partial function.
ordRightSub' :: Ordinal -> Ordinal -> Ordinal
ordRightSub' a b =
  case ordRightSub a b of
    Just r -> r
    Nothing -> error "ordRightSub': arithmetic underflow"
    -- Nothing -> error $ "ordRightSub': arithmetic underflow: " ++ show (a,b)

-- * Long division

-- | Given ordinals @n@ and @d@, find @(q, r)@ such that:
--
-- @r < d && d.q + r === n@
ordDivRem :: Ordinal -> Ordinal -> (Ordinal, Ordinal)
ordDivRem n d
  | isZero d = error "ordDivRem: division by zero"
  | d == 1 = (n, 0)
  | d > n = (0, n)
  | n == d = (1, 0)
  | otherwise = recurse (0, n)
  where
    recurse :: (Ordinal, Ordinal) -> (Ordinal, Ordinal)
    recurse (acc, 0) = (acc, 0)
    recurse (acc, r)
      | d > r = (acc, r)
      | otherwise =
        if pr == pd then
          let q = cr `div` cd in
          let dr = mono pr (q * cd) in
          recurse (acc `ordAdd` finite q, ordRightSub' dr r)
        else
          -- let q = cr `div` cd in
          let q = cr in -- if cd >= cr then 1 else cr `div` cd in
          if q == 0 then
            --error $ "TODO fix this: ((acc, r), d) = " ++ show ((acc, r), d)
            (acc, r)
          else
            let dp = ordRightSub' pd pr in
            recurse (acc `ordAdd` mono dp q, ordRightSub' (fromVebMono (pr', cr)) r)
        where
          ((pr', cr), _) = dropLeadingTerm r
          pr = unMono1 pr'

    ((pd', cd), _) = dropLeadingTerm d
    pd = unMono1 pd'


-- * Helpers

-- | Repeats a binary operation on the same value a natural number times,
-- by repeatedly halving the natural number
repeatBinOp :: (a -> a -> a) -> a -> a -> Natural -> a
repeatBinOp binop v0 v1 = recurse where
  recurse 0 = v0
  recurse 1 = v1
  -- recurse k = recurse (k - 1) `binop` v1
  recurse k = if even k then b `binop` b  else (b `binop` b) `binop` v1
    where b = recurse (k `div` 2)

