{-# LANGUAGE DeriveTraversable #-}

module Data.Conway.Simplicity.HelperTypes (OneOrTwo (..), Signed (..), signedPos, signedNeg, listFrom12) where

data OneOrTwo a = One a | Two a a
  deriving (Eq, Ord, Functor, Foldable, Traversable)

newtype Signed a = Signed (Bool, a)
  deriving (Eq, Ord, Functor, Foldable, Traversable)

signedPos, signedNeg :: a -> Signed a
signedPos x = Signed (True, x)
signedNeg x = Signed (False, x)

listFrom12 :: OneOrTwo a -> [a]
listFrom12 (One x) = [x]
listFrom12 (Two x y) = [x, y]
