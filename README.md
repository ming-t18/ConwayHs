# ConwayHs

Haskell-based library for ordinal numbers and surreal numbers with support for Veblen hierarchy.

# Supported features

- Equality and comparison (`Eq` and `Ord` typeclasses)
- Natural sum and product for ordinals and surreals (`Num` typeclass)
- Displaying in Cantor/Conway normal forms (`Show` typeclass)
- The exclusive upper bound is the Feferman–Schütte ordinal. All larger values are unsupported
- Fundamental sequences

# Setting up

Set up [Stack](https://docs.haskellstack.org/en/stable/).

```
stack build
stack repl
```

# API

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
## Conway Normal Form

The `Conway` type represents the Cantor/Conway normal form, that is a weighted sum of Veblen monomials.

The type parameter `a` is the type of the coefficients.

It is represented as a mapping (`Data.Map(Map)`) from the Veblen monomial to the coefficient with keys sorted
descending. Zero-coefficients are eliminated from the mapping.

Ordinal numbers are represented as `Conway` with natural numbers (`Numeric.Natural(Natural)`) as coefficients.

```hs
newtype Conway a = ...
type Ordinal = Conway Natural

conway :: Map (Ordinal, Conway a) a -> Conway a
toMap :: Conway a -> Map (Ordinal, Conway a) a
```

## Dyadic rationals

A dyadic rational is a rational number in the form of $\frac{a}{2^b}$ for numerator `a` and exponent `b`. Both `a` and `b` must be integers.

The `makeDyadic` function constructs a new `Dyadic` from `a` and `b` and simplifying denominator.

```hs
data Dyadic = ...

makeDyadic :: Integer -> Integer -> Dyadic
unmakeDyadic :: Dyadic -> (Integer, Integer)
```

```hs
ghci> 1 :: Dyadic
1
ghci> makeDyadic (-5) 3
-5/8
ghci> makeDyadic 2 2 + makeDyadic (-5) 4
3/16
ghci> unmakeDyadic (makeDyadic (-5) 4)
(-5,4)
```

## Veblen Hierarchy

```hs
veb1 :: Ordinal -> Conway a -> Conway a
veb :: Ordinal -> Conway a -> a -> Conway a
```

## Ordinal numbers

```hs
ghci> 1 :: Ordinal
1
ghci> omega :: Ordinal
w
ghci> (omega :: Ordinal) + 1
w + 1
ghci> mono1 ((omega :: Ordinal) + 4) + 2 * omega
w^{w + 4} + w.2
```

## Fundamental Sequences

```hs
-- predecessor or fundamental sequence as an infinite list
fsOrd :: Ordinal -> Either Ordinal (NonEmpty Ordinal)
```

## Fundamental sequence of $\Gamma_0$

```
ghci> take 8 $ iterate (`veb1` 0) 0
[0,1,ε_0,φ[ε_0, 0],φ[φ[ε_0, 0], 0],φ[φ[φ[ε_0, 0], 0], 0],φ[φ[φ[φ[ε_0, 0], 0], 0], 0],φ[φ[φ[φ[φ[ε_0, 0], 0], 0], 0], 0]]
```
