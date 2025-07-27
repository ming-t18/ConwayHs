{-# LANGUAGE ScopedTypeVariables #-}
module OrdinalArith (
    ordAdd,
    ordMult,
    ordPow,
    isFinite,
    maybeFinite,
) where
import Lib
import Numeric.Natural
import qualified Data.Map.Strict as M
import Typeclasses

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

isFinite :: Ordinal -> Bool
isFinite x = case leadingTerm x of
    (v, _) | isZero v -> True
    _ -> False

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
ordMult a = foldl (\s -> (s `ordAdd`) . ordMultByMono a) 0 . termsList

ordMultByMono :: Ordinal -> (VebMono Natural, Natural) -> Ordinal
ordMultByMono a (p, c)
    | isZero p =
        ordMultByFinite a c
    | otherwise =
        foldl (\s t -> s `ordAdd` ordMultMonoByMono1 t p) 0 (termsList a) `ordMultByFinite` c

ordMultMonoByMono1 :: (VebMono Natural, Natural) -> VebMono Natural -> Ordinal
ordMultMonoByMono1 (v1, f) v2 =
    case (classifyVebMono v1, classifyVebMono v2) of
        -- (w^0.c) . w^0 = (1.c).1 = c
        (Fin, Fin) -> finite f
        -- f . V[p, c] = V[p, c]         -- where f is finite and V[p, c] is infinite
        (Fin, _) -> fromVebMono1 v2
        -- In the cases below, the finite term is absorbed
        -- w^a . w^b = w^[a + b]
        (WP a, WP b) -> mono1 $ a + b
        -- w^a . V[p', c'] = w^a . w^V[p', c'] = w^[a + V[p', c']]
        (WP a, _) -> mono1 $ a + fromVebMono1 v2
        -- w^a . V[p, c] = w^a . w^V[p, c] = w^[a + V[p, c]]
        (_, WP a) -> mono1 $ fromVebMono1 v1 + a
        -- = V[p, c] . V[p', c']
        -- = w^V[p, c] . w^V[p', c']     -- given p > 0 and p' > 0
        -- = w^[V[p, c] + V[p', c']]     -- law of exponents
        (_, _) -> mono1 $ fromVebMono1 v1 + fromVebMono1 v2

ordMultByFinite :: Ordinal -> Natural -> Ordinal
ordMultByFinite = repeatBinOp ordAdd 0

ordPow :: Ordinal -> Ordinal -> Ordinal
-- law of exponents: a^(b + c + ...) = a^b * a^c * ...
ordPow a b = foldl (\p m -> p `ordMult` ordPowByMono a m) 1 $ termsList b

-- | Ordinal power @x^p@ where @p@ is a monomial
ordPowByMono :: Ordinal -> (VebMono Natural, Natural) -> Ordinal
ordPowByMono o (v1, a) =
    case (maybeFinite o, classifyVebMono v1) of
        -- finite^finite
        (Just x, Fin) -> finite (x ^ a)
        -- finite^finite
        (Just x, _) -> ordPowFiniteByMono x (v1, a)
        -- infinite^finite
        (Nothing, Fin) -> ordPowByMonoFinite o a
        -- infinite^infinite
        (Nothing, c1) ->
            -- o = (w^v0.c0 + ...)
            -- exponent = w^v . a
            let (v0, _) = leadingTerm o in
            let vBase = case classifyVebMono v0 of
                            Fin -> error "not possible (o is infinite)"
                            WP p -> p
                            _ -> fromVebMono v0 in
            let vExponent = fromVebMono v1 in
            -- Applying https://proofwiki.org/wiki/Ordinal_Exponentiation_via_Cantor_Normal_Form/Corollary
            --   o^(w^v . a)
            -- = w^[v0 . w^v . a]
            mono1 (vBase `ordMult` vExponent `ordMult` finite a)

-- | Ordinal power @x^p@ where @x@ is finite and @p@ is infinite
ordPowFiniteByMono :: Natural -> (VebMono Natural, Natural) -> Ordinal

ordPowFiniteByMono 1 _ = 1
ordPowFiniteByMono _ (_, 0) = 1
ordPowFiniteByMono x (v, a) =
    case classifyVebMono v of
        -- x^a: finite by finite
        Fin -> finite (x ^ a)
        -- x^(w a) = (x^w)^a = w^a
        WP 1 -> mono1 $ finite a
        -- x^(w^b . a) = (x^(w^b))^a = (w^b)^a = w^(b.a)
        WP b -> mono1 (b `ordMult` finite a)
        -- x^(v.a) = x^(w^v.a) = (x^(w^v))^a = w^(v.a)
        _ -> mono1 (fromVebMono1 v `ordMult` finite a)


-- | Ordinal power @x^p@ where @x@ is finite and @p@ is finite
ordPowByMonoFinite :: Ordinal -> Natural -> Ordinal
ordPowByMonoFinite = repeatBinOp ordMult 1

-- * Helpers

-- | Repeats a binary operation on the same value a natural number times,
-- by repeatedly halving the natural number
repeatBinOp :: (a -> a -> a) -> a -> a -> Natural -> a
repeatBinOp binop v0 v1 = recurse where
    recurse 0 = v0
    recurse 1 = v1
    recurse k
        | even k = let { b = recurse k' } in b `binop` b
        | otherwise = let { b = recurse k' } in (b `binop` b) `binop` v1 where
            k' = k `div` 2
