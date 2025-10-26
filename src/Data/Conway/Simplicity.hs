-- | Module containing tools to represent surreal numbers in terms of
-- their simpler versions.
--
-- * Ranges
--
-- A surreal number @x@ can be defined in terms of @{left | right}@
-- where @left@ and @right@ are sets of surreals. They are often
-- called "ranges"
--
-- When talking about surreals, we often write expressions to perform
-- arithmetic on the ranges, and apply cofinality ([Gonshor] Chapter 2)
-- to simplify the ranges.
--
-- In this library, ranges are modeled as a collection of range elements.
--
-- A range element (@RangeElem a@) is basically @base + seq@ or @base - seq@
-- where @seq :: MonoSeq a@ is a sequence with the limit of a monomial.
--
-- The type @Range a@ represents a @Set@ of range elements.
--
-- Arithmetic operations can be performed on ranges. They include
-- @add, sub, mult, mono1, veb1@.
--
-- * Left/right forms
--
-- The type @LRRange a@ represents the @{left | right}@ form of a @Conway a@.
--
-- It is constructed by the operator @left :|: right@ where @left :|: right@
-- are both of type @Range a@.
--
-- * More details on ranges and their simplifications
-- Let @S + veb o p c@ be a @Conway@ with a trailing term.
--
-- Let @'@ be the left parent of a surreal number, and @''@ be the right parent.
--
-- The range can be empty (zero), singleton (successor) or range (limit).
--
-- @n = 0, 1, 2, ...@ is the index of a limit range.
--
-- Sum of terms rules:
--
--   * SumL: @(S + veb o p c)' = S + (veb1 o p c)'@
--
--   * SumR: @(S + veb o p c)'' = S + (veb1 o p c)''@
--
-- If the last monomial has an empty range, remove the last term and try again with the second last term.
-- This process repeats from the rightmost term to the first term until the first term with non-empty
-- range has been found or if all terms have been exhausted.
--
-- Monomial with non-trivial coefficient rules:
--
--   * CoeffLSucc: @(mono p c)' = mono p c' + mono p' n@
--
--   * CoeffRSucc: @(mono p c)'' = mono p c'' - mono p' n@
--
--   * CoeffLLimit: @(mono p c)' = {0, mono p' c}@
--
--   * CoeffRLimit: @(mono p c)'' = mono p''@
--
-- Monomial with coefficient of 1 rules:
--
--   * Mono1LEmpty: @(mono1 p)' = 0@ where @p'@ is empty
--
--   * Mono1REmpty: @(mono1 p)'' = {}@ where @p''@ is empty
--
--   * Mono1LSucc: @(mono1 p)' = veb 0 p' n@
--
--   * Mono1RSucc: @(mono1 p)'' = veb 0 p'' (1 `shr` n)@
--
--   * Mono1LLimit: @(mono1 p)' = {0, mono1 p'}@
--
--   * Mono1RLimit: @(mono1 p)'' = mono1 p''@
--
-- * Veb1 rules
--
-- The @Veb1@ rules are based on the "CGV Googology part 1: veblen function" definition of the surreal single-argument Veblen function:
--
-- @veb1 o p = { iterate (veb1 o') {0, p' * n} | iterate (veb1 o') (p'' * (1 `shr` n)) }@
--
-- where @n@ is the range @{0, 1, 2, 3, 4, ...}@ and @1 `shr` n@ is the range @{1, 1/2, 1/4, 1/8, 1/16, ...}@
--
-- Zero argument:
--
--   * Veb1LSuccZero: @(veb1 o 0)' = iterate (veb1 o') 0@
--
--   * Veb1RSuccZero: @(veb1 o 0)'' = {}@
--
--   * Veb1LLimitZero: @(veb1 o 0)' = veb1 o' 0@
--
--   * Veb1RLimitZero: @(veb1 o 0)'' = {}@
--
-- Empty argument:
--
--   * Veb1LSuccEmpty: @(veb1 o p)' = veb1 o' 0@ where @p'@ is empty
--
--   * Veb1RSuccEmpty: @(veb1 o p)'' = {}@ where @p''@ is empty
--
-- Successor argument:
--
--   * Veb1LSuccSucc: @(veb1 o p)' = iterate (veb1 o') (veb1 o p' + 1)@
--
--   * Veb1RSuccSucc: @(veb1 o p)'' = iterate (veb1 o') (veb1 o p'' - 1)@
--
--   * Veb1LLimitSucc: @(veb1 o p)' = veb1 o' (veb1 o p' + 1)@
--
--   * Veb1RLimitSucc: @(veb1 o p)'' = veb1 o' (veb1 o p'' - 1)@
--
-- Limit argument:
--
--   * Veb1LSuccLimit: @(veb1 o p)' = veb1 o p'@
--
--   * Veb1RSuccLimit: @(veb1 o p)'' = veb1 o p''@
--
--   * Veb1LLimitLimit: @(veb1 o p)' = veb1 o p'@
--
--   * Veb1RLimitLimit: @(veb1 o p)'' = veb1 o p''@
module Data.Conway.Simplicity
  ( -- * Left-Right forms
    LRRange (..),

    -- * Range
    Range,
    point,
    rangeCv,
    rangeDv,

    -- * RangeElem
    ParentSeq,
    ParentSeq0,
    RangeElem (..),
    RangeElemMono (..),
    ConwaySeq,
    MonoSeq (..),
    FixBase,
    Veb1Seq (..),
    csBase,
    csSign,
    csTerm,

    -- * SignExpansion
    OrdMonoSeq,
    SignExpansionSeq (..),
    ParentSeqSignExpansion,
    SignExpansionRangeElem (..),

    -- * Parent sequence
    parentDyadic,
    parentConway,
    parentMono,
    parentVeb1,
    lrConway,

    -- * Sequence generation
    HasParentSeq (..),
    ParentRepr (..),
    Limit (..),
    ToSeq (..),

    -- * Limit completion
    limParentSeq,
    limLR,

    -- * Descent
    descend,
    descent,
  )
where

import Data.Conway.Simplicity.Completion
import Data.Conway.Simplicity.Descent
import Data.Conway.Simplicity.LeftRightRange
import Data.Conway.Simplicity.Parent
import Data.Conway.Simplicity.Range
import Data.Conway.Simplicity.Seq
import Data.Conway.Simplicity.SignExpansionSeq
import Data.Conway.Simplicity.Types
