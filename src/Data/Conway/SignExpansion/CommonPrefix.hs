module Data.Conway.SignExpansion.CommonPrefix (commonPrefix, takeCommonPrefix, construct) where

commonPrefix :: (Ord n, Eq s) => [(s, n)] -> [(s, n)] -> [(s, n)]
commonPrefix = curry $ recurse []
  where
    recurse acc ([], _) = acc
    recurse acc (_, []) = acc
    recurse acc (e0@(s0, n0) : xs0, (s1, n1) : xs1)
      | s0 == s1 =
          if n0 == n1
            then recurse (acc ++ [e0]) (xs0, xs1)
            else acc ++ [(s0, min n0 n1)]
      | otherwise = acc

takeCommonPrefix :: (Eq s) => (n -> n -> (Ordering, n)) -> [(s, n)] -> [(s, n)] -> ([(s, n)], ([(s, n)], [(s, n)]))
takeCommonPrefix symDiff = curry $ recurse []
  where
    recurse acc p@([], _) = (acc, p)
    recurse acc p@(_, []) = (acc, p)
    recurse acc p@(e0@(s0, n0) : xs0, (s1, n1) : xs1)
      | s0 == s1 =
          case n0 `symDiff` n1 of
            (EQ, _) -> recurse (acc ++ [e0]) (xs0, xs1)
            (LT, d) -> (acc ++ [(s0, n0)], (xs0, (s1, d) : xs1))
            (GT, d) -> (acc ++ [(s1, n1)], ((s0, d) : xs0, xs1))
      | otherwise = (acc, p)

construct :: (Num n, Eq n) => (n -> n -> (Ordering, n)) -> [(Bool, n)] -> [(Bool, n)] -> [(Bool, n)]
construct symDiff x y =
  c ++ case (xr, yr) of
    ([], [(True, 1)]) -> [(True, 1), (False, 1)]
    ([], [(True, 1), (False, n)]) -> [(True, 1), (False, n + 1)]
    ([], (True, _) : _) -> [(True, 1)]
    ([(False, 1)], []) -> [(False, 1), (True, 1)]
    ([(False, 1), (True, n)], []) -> [(False, 1), (True, n + 1)]
    ((False, _) : _, []) -> [(False, 1)]
    -- diverging signs
    (_, _) -> []
  where
    (c, (xr, yr)) = takeCommonPrefix symDiff x y
