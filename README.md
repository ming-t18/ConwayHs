# ConwayHs

Haskell-based library for ordinal numbers and surreal numbers with support for Veblen hierarchy.

# Supported features

- Equality and comparison (`Eq` and `Ord` typeclasses)
- Natural sum and product for ordinal numbers and surreal numbers (`Num` typeclass)
- Displaying in Cantor/Conway normal forms (`Show` typeclass)
- The 2-argument Veblen function. The exclusive upper bound is the Feferman–Schütte ordinal
- Generating and parsing sign expansions

# Setting up

Set up [Stack](https://docs.haskellstack.org/en/stable/).

```
stack build
stack repl
```

## Running tests

```
stack test
```

# API

Top-level module: `Data.Conway`

## Basic datatypes

 - Finite values
    - `Natural`: natural number from Haskell standard library
    - `Dyadic`: dyadic rational numbers -- rationals with power of 2 denominators
 - Ordinals and surreals -- `Conway`
    - `Conway a`: surreal numbers with coefficient type `a`
    - `Conway Dyadic`: representable surreal numbers
    - `Ordinal`: representable ordinal numbers, alias of `Conway Natural`
    - `VebMono`: a Veblen function monomial: $\phi(o, a)$
 - Sign expansions
    - `SignExpansion`: sign expansions of `Conway Dyadic`
    - `FSE`: sign expansions of dyadic rationals
    - `Reduced a`: wrapper for reduced sign expansions as explained in Gonshor's book
 - Ranges and sequences
    - `ParentSeq a`: the immediate parent sequence of a `Conway a`
    - `ConwaySeq a`: the limit sequence completing to a `Conway a`
    - `MonoSeq a`: the limit sequence of a monomial
    - `Veb1Seq a`: the limit sequence of a Veblen monomial $\phi(o, a)$
    - `FixBase a`: the base of a fixed-point iteration
    - `LeftRight a`: the `{ left | right }` representation of a `Conway a`
 - Transfinite sequences
    - `Infinite a`: an infinite list with order type $\omega$

## Typeclasses

- `Data.Conway.Typeclasses`
  - `Zero a`: has zero elemnt
  - `OrdZero a`: total order with zero element and negation around the zero
  - `AddSub a`: has natural addition and subtraction
  - `Mult a`: has natural multiplication
  - `OrdRing a`: combination of `OrdZero, AddSub, Mult`
  - `Veblen a o`: type `a` has the Veblen function with Veblen argument(s) `o`
- `Data.Conway.SignExpansion`
  - `FiniteSignExpansion`: type `a` has order isomorphism with `FSE`
  - `HasSignExpansion`: type `a` has order isomorphish with `SignExpansion` -- **NOT IMPLEMENTED**
- `Data.Conway.Seq`
  - `Seq s o a`: `s` is a transfinite sequence with index/length type `o` and element type `a`
  - `SeqEnum s o a`: `a` has transfinite sequences `Seq` as their ranges -- **NOT IMPLEMENTED**
  - `RunLengthSeq s o a`: transfinite repetitions of an element can be constructed
  - `ParseableSeq s o a`: transfinite repetitions of an element can be parsed from the beginning
- `Data.Conway.OrdLim`
  - `OrdLim a`: `a` is a well-ordering with order type of a limit ordinal

## Veblen Monomial

The Veblen hierarchy is a sequence of fixed point functions starting from the $\omega$-map (`mono1`).

The first fixed point of the $\omega$-map is $V_0(-)$ (`veb1`).

The `veb1` function is a two-argument function that evaluates $\phi_a(b)$ given ordinal $a$.

The datatype `VebMono` represents Veblen monomials.

```hs
mono1 :: Conway a -> Conway a
veb1 :: Ordinal -> Conway a -> Conway a

data VebMono a = VebMono Ordinal (Conway a)
```
## Cantor/Conway Normal Form

The `Conway` type represents the Cantor/Conway normal form, that is a weighted sum of Veblen monomials.

This is a computable and serializable subset of surreal numbers with computable and serializable sign expansions.

Uncomputable aspects of surreal numbers include real number coefficients and infinite sums.

The type parameter `a` is the type of the coefficients.

It is represented as a mapping (`Data.Map.Strict`) from the Veblen monomial to the coefficient with keys sorted
descending. Zero-coefficients are eliminated from the mapping.

Ordinal numbers are represented as `Conway` with natural numbers (`Numeric.Natural(Natural)`) as coefficients.

```hs
newtype Conway a = ...
type Ordinal = Conway Natural

conway :: Map (Ordinal, Conway a) a -> Conway a
toMap :: Conway a -> Map (Ordinal, Conway a) a

finiteView :: Conway a -> Maybe a
leadingView :: Conway a -> Maybe ((VebMono a, a), a)
```

## Dyadic rationals

A dyadic rational is a rational number in the form of $\frac{a}{2^b}$ for numerator `a` and exponent `b`. Both `a` and `b` must be integers.

The `makeDyadic` function constructs a new `Dyadic` from `a` and `b` and simplifying denominator.

`(%/)` is the infix operator for `makeDyadic`.

Decimal literals (`-1.25`) and the division symbol (`/`) are supported, as long as the denominator is a power of 2.

```hs
data Dyadic = ...

makeDyadic :: Integer -> Integer -> Dyadic
(%/) :: (Integral a, Integral b) => a -> b -> Dyadic
unmakeDyadic :: Dyadic -> (Integer, Integer)
```

```hs
ghci> 1 :: Dyadic
1
ghci> 0.5 :: Dyadic
1/2
ghci> 0.2 :: Dyadic
*** Exception: Dyadic.fromRational: denominator is not a power of 2: 1 % 5
...
ghci> (-5) %/ 3 :: Dyadic
-5/8
ghci> 2 %/ 2 + (-5) %/ 4
3/16
ghci> unmakeDyadic 0.125
(-1,3)
```

## Veblen hierarchy

```hs
-- Veblen hierarchy
veb1 :: Ordinal -> Conway a -> Conway a
veb :: Ordinal -> Conway a -> a -> Conway a

-- powers of omega
mono1, w' :: Ordinal -> Ordinal
mono1 = veb1 0

-- omega^p * c
mono :: Conway a -> a -> Conway a
finite :: a -> Conway a
finite = mono 0

-- epsilon numbers
eps' :: Conway a -> Conway a -> Conway a
eps0 :: Conway a
eps' = veb1 1
eps0 = veb1 1 0

```

```hs
ghci> 0.5 :: Conway Dyadic
1/2
ghci> mono1 2 - 1 + mono (-2) 3 :: Conway Dyadic
w^2 - 1 + w^(-2).3
ghci> veb 1 (-1) 2.5 - 5.125 + w' (-1) + w' (-veb1 w 0 + 1) :: Conway Dyadic
ε_{-1}.5/2 + -41/8 + w^{-1} + w^{φ[w, 0].-1 + 1}
````

## Ordinal numbers

```hs
ghci> 1 :: Ordinal
1
ghci> w :: Ordinal
w
ghci> w + 1
w + 1
ghci> mono1 (w + 4) + 2 * w
w^{w + 4} + w.2
```

## Sign expansions

```hs
conwaySE :: Conway a -> SignExpansion
parseToConway :: SignExpansion -> Conway Dyadic

-- Repeats a sign an ordinal number times
rep :: Ordinal -> Boolean -> SignExpansion

-- Repeats a sign finite number of times (Dyadic sign expansions)
rep :: Natural -> Boolean -> FSE

-- Combining sign expansions
instance Monoid SignExpansion where
  ...
instance Monoid FSE where
  ...

```

## Fundamental Sequences

```hs
-- predecessor or fundamental sequence as an infinite list
fsOrd :: Ordinal -> Either Ordinal (NonEmpty Ordinal)
```

### Fundamental sequence of $\Gamma_0$

```
ghci> take 8 $ iterate (`veb1` 0) 0
[0,1,ε_0,φ[ε_0, 0],φ[φ[ε_0, 0], 0],φ[φ[φ[ε_0, 0], 0], 0],φ[φ[φ[φ[ε_0, 0], 0], 0], 0],φ[φ[φ[φ[φ[ε_0, 0], 0], 0], 0], 0]]
```

## Representing values larger than $\Gamma_0$

In theory the type `Conway (Conway a)` can be used to represent the arguments to ordinal collapsing functions, but currently there are no implementations to specially handle them.

## Ranges ("parent", "fundamental sequence", "canonical sequence", "simplicity sequence")

A surreal number `x` can be defined in terms of `x = { L | R }` where `L` and `R` are sequences of surreal numbers (zero, finite or infinite length sequences). For the sequence to be value, everything in `L` are less than everything in `R`, and `{ L | R }` denotes the simplest (by birthday) surreal number between `L` and `R`.

There are infinitely many ways to write the `L` and `R` for a given surreal number, but there is
a system for the "canonical" way of defining the left and right sequences.

The `Data.Conway.Simplicity` module contains the functions to convert from a surreal to its immediate parent sequence, functions to enumerate the sequences, and functions to complete the limit sequences.
