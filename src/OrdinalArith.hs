module OrdinalArith (

    isFinite,
    ordAdd,
    ordMult,
)where
import Lib
import Numeric.Natural
import qualified Data.Map.Strict as M

isFinite :: Ordinal -> Bool
isFinite x = p == 0 && a == 0 where
    (VebMono p a, _) = leadingTerm x

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
ordMultByMono _ (_, 0) = 0
ordMultByMono a (VebMono 0 0, c) = ordMultByFinite a c
-- using distributive property: a.(b + c + ...) = a.b + a.c + ...
ordMultByMono a (p, c) = foldl (\s t -> s `ordAdd` ordMultMonoByMono1 t p) 0 (termsList a) `ordMultByFinite` c

ordMultMonoByMono1 :: (VebMono Natural, Natural) -> VebMono Natural -> Ordinal
-- (w^0.c) . w^0 = (1.c).1 = c
ordMultMonoByMono1 (VebMono 0 0, c) (VebMono 0 0) = finite c
-- f . V[p, c] = V[p, c]         -- where f is finite and V[p, c] is infinite
ordMultMonoByMono1 (VebMono 0 0, _) (VebMono p c) = veb1 p c
-- In the cases below, the finite term is absorbed
-- w^a . w^b = w^[a + b]
ordMultMonoByMono1 (VebMono 0 a, _) (VebMono 0 b) = mono1 $ a + b
--   w^a . V[b, c]
-- = w^a . w^V[b, c]
-- = w^[a + V[b, c]]
ordMultMonoByMono1 (VebMono 0 a, _) (VebMono b c) = mono1 (a + veb1 b c)
ordMultMonoByMono1 (VebMono a b, _) (VebMono 0 c) = mono1 (veb1 a b + c)

-- = V[p, c] . V[p', c']
-- = w^V[p, c] . w^V[p', c']     -- given p > 0 and p' > 0
-- = w^[V[p, c] + V[p', c']]     -- law of exponents
ordMultMonoByMono1 (VebMono p c, _) (VebMono p' c') = mono1 (veb1 p c + veb1 p' c')

-- | Ordinal multiplication by a finite ordinal, which is a repeated ordinal addition
ordMultByFinite :: Ordinal -> Natural -> Ordinal
ordMultByFinite _ 0 = 0
ordMultByFinite a 1 = a
ordMultByFinite a k
    | even k = let { b = ordMultByFinite a k' } in b `ordAdd` b
    | otherwise =  let { b = ordMultByFinite a k' } in (b `ordAdd` b) `ordAdd` a where
        k' = k `div` 2
