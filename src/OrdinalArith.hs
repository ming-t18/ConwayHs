module OrdinalArith (

    isFinite,
    ordAdd,
    ordMult,
)where
import Lib (conway, Ordinal, toMap, leadingTerm, VebMono (..), veb1)
import Numeric.Natural
import qualified Data.Map.Strict as M

isFinite :: Ordinal -> Bool
isFinite x = p == 0 && a == 0 where
    (VebMono p a, _) = leadingTerm x

ordAdd :: Ordinal -> Ordinal -> Ordinal
ordMult :: Ordinal -> Ordinal -> Ordinal
ordMultByMono :: Ordinal -> (VebMono Natural, Natural) -> Ordinal

ordAdd a b = a' + b where
    (VebMono p1 c1, _) = leadingTerm b
    pCutoff = veb1 p1 c1
    a' = conway $ M.filterWithKey (\(VebMono p c) _ -> veb1 p c >= pCutoff) $ toMap a

ordMult a b = a * b

ordMultByMono a (VebMono 0 0, c) = ordMultByFinite a c
ordMultByMono a (VebMono p b, c) = error "TODO implement"

ordMultByFinite :: Ordinal -> Natural -> Ordinal
ordMultByFinite _ _ = error "TODO implement"
-- ordMultByFinite _ 0 = 0
-- ordMultByFinite a 1 = a
-- ordMultByFinite a k
--     | even k = let { k' = k / 2; b = ordMultByFinite a k' } in b `ordAdd` b
--     | otherwise =  let { k' = (k - 1) / 2; b = ordMultByFinite a k' } in (b `ordAdd` b) `ordAdd` a
