-- | Module dealing with the sign expansions of surreal numbers.
--
-- A sign expansion (or sign sequence) is a transfinite sequence of pluses and minuses
-- ordered lexicographically.
--
-- Basic properties of sign expansions:
--
-- 1. Bijection: @conwaySE . parseSE === id@
--
-- 2. Order isomorphism: @x `compare` y === conwaySE x `compare` conwaySE y@
--
-- 3. Birthday-length: @birthday x === length (conwaySE x)@
--
-- 4. Left and right sequences: @x === { L(conwaySE x) | R(conwaySE x) }@ where @L@ and @R@ are the sequences of lower and upper bounds and @{ | }@ is the standard way to construct a surreal number from left and right sides.
--
-- Outline of converting from @Conway@ to sign expansions (@SignExpansion@):
--
-- * @conwaySE@: For each term in descending lexicographical order, combine their sign expansion contributions.
--
-- * @reduce@ and @reduceSingle@: For each term, convert their exponents to reduced sign expansions ([Gonshor] Theorem 5.11, final page of proof)
--
-- * @monoSE@: For each term, the sign expansion contribution of the real part comes after the monomial part (lexicographical order: exponent is compared before the real part) ([Gonshor] Theorems 5.11 and 5.12).
--
-- * @mono1SE, veb1SE@: For each monomial (@mono1@ or @veb1@), derive their sign expansions based on the parameters ([Gonshor] Theorem 5.11).
module SignExpansion
  ( -- * @SignExpansion@ type
    SignExpansion,
    (+++),
    toList,
    fromList,
    empty,
    consSE,
    length,
    index,

    -- ** Factory
    single,
    plus,
    minus,

    -- ** Helpers
    isEmpty,
    negate,
    countSigns,
    commonPrefix,
    takeCommonPrefix,

    -- * Generation

    -- ** Operations
    mono1SE,
    mono1SE',
    veb1SE,
    veb1SE',
    mono1SELead,
    veb1SELead,
    conwaySE,

    -- * Parsing

    -- ** Generic
    parseMono,
    parseMono1,

    -- ** @SignExpansion@ and @FSE@
    parseMonoSE,
    parseMono1SE,

    -- * Birthday
    isAllPluses,
    birthday,
  )
where

import Conway (Ordinal)
import SignExpansion.Conway (birthday, conwaySE, isAllPluses)
import SignExpansion.Dyadic (FSE)
import SignExpansion.Parser (parseMono, parseMono1)
import SignExpansion.Types
import SignExpansion.Veb
import Prelude hiding (length, negate)

parseMono1SE :: Bool -> SignExpansion -> ((Ordinal, SignExpansion), SignExpansion)
parseMono1SE = parseMono1

parseMonoSE :: SignExpansion -> (((Ordinal, SignExpansion), FSE), SignExpansion)
parseMonoSE = parseMono
