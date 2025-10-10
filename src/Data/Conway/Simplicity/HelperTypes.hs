{-# LANGUAGE DeriveTraversable #-}

module Data.Conway.Simplicity.HelperTypes (OneOrTwo (..), Signed (..), signedPos, signedNeg, listFrom12, flipSigned, withSign) where

data OneOrTwo a = One a | Two a a
  deriving (Eq, Ord, Functor, Foldable, Traversable)

newtype Signed a = Signed {getSigned :: (Bool, a)}
  deriving (Eq, Ord, Functor, Foldable, Traversable)

withSign :: Bool -> a -> Signed a
withSign = curry Signed

signedPos, signedNeg :: a -> Signed a
signedPos x = Signed (True, x)
signedNeg x = Signed (False, x)

listFrom12 :: OneOrTwo a -> [a]
listFrom12 (One x) = [x]
listFrom12 (Two x y) = [x, y]

flipSigned :: Bool -> Signed a -> Signed a
flipSigned True si = si
flipSigned False (Signed (s, x)) = Signed (not s, x)
