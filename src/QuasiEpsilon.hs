-- | The quasi-epsilon number is the fixed point of @mono1 . neg@ (@f(x) = w^-x@).
-- It is described in [Gonshor] Theorem 9.9 to 9.12.
--
-- We cannot represent entire quasi-epsilon number but we can generate the sequence
-- of values or sign expansions for it.
--
-- The quasi-epsilon number can also generalized for arbitrary Veblen orders
-- @o@, @veb1 o . neg@.
module QuasiEpsilon
  ( mono1Neg,
    veb1Neg,
    mono1NegSE,
    veb1NegSE,
    quasiEpsSeq,
    quasiEpsSeqSE,
  )
where

import Conway
import SignExpansion
import Typeclasses

mono1Neg :: (Mult a) => Conway a -> Conway a
mono1Neg = mono1 . neg

veb1Neg :: (Mult a) => Ordinal -> Conway a -> Conway a
veb1Neg o = veb1 o . neg

mono1NegSE :: SignExpansion -> SignExpansion
mono1NegSE = mono1SE . neg

veb1NegSE :: Ordinal -> SignExpansion -> SignExpansion
veb1NegSE o = veb1SE o . neg

-- | The fundamental sequence of the quasi-epsilon number.
quasiEpsSeq :: (Mult a) => [Conway a]
quasiEpsSeq = iterate mono1Neg zero

-- | The fundamental sequence of the quasi-epsilon number.
--
-- >>> take 5 quasiEpsSeq :: [Conway Dyadic]
-- [0,1,w^{-1},w^{w^{-1}.-1},w^{w^{w^{-1}.-1}.-1}]
-- >>> take 5 $ quasiEpsSeqSE
-- [SignExpansion [],SignExpansion [(True,1)],SignExpansion [(True,1),(False,w)],SignExpansion [(True,1),(False,w),(True,w^w)],SignExpansion [(True,1),(False,w),(True,w^w),(False,w^{w.2})]]
quasiEpsSeqSE :: [SignExpansion]
quasiEpsSeqSE = iterate mono1NegSE empty
