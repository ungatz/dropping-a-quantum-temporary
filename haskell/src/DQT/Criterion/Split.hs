-- |
-- Module      : DQT.Criterion.Split
--
-- Splitting a state across a cut, exactly: the state factors exactly when
-- its coefficient matrix @M@ has rank at most one.  Recovering the factors
-- divides by a nonzero pivot, why "DQT.Algebra.Scalar" is a field.
module DQT.Criterion.Split
  ( -- * The cut
    coefficientMatrix
  , schmidtRank
    -- * The product test
  , Split(..)
  , factorSplit
  , factorsAcross
  , failingMinor
    -- * Lines (states up to scalar)
  , canonicalLine
  , lineEqual
  ) where

import DQT.Algebra.Linear
import DQT.Algebra.Scalar

-- | @coefficientMatrix dims regsA psi@ is the matrix of @psi@ for the cut that
-- puts the registers at positions @regsA@ (in increasing position order) on the
-- left and all the others on the right.
coefficientMatrix :: [Int] -> [Int] -> Vec -> Mat
coefficientMatrix dims regsA psi =
  [ [ entry a b | b <- [0 .. nB - 1] ] | a <- [0 .. nA - 1] ]
  where
    n     = length dims
    aPos  = [ i | i <- [0 .. n-1], i `elem` regsA ]
    bPos  = [ i | i <- [0 .. n-1], i `notElem` regsA ]
    dimsA = [ dims !! i | i <- aPos ]
    dimsB = [ dims !! i | i <- bPos ]
    nA    = dimProduct dimsA
    nB    = dimProduct dimsB
    entry a b =
      let la = indexToLevels dimsA a
          lb = indexToLevels dimsB b
          ls = [ pick i | i <- [0 .. n-1] ]
          pick i = case lookup i (zip aPos la) of
                     Just l  -> l
                     Nothing -> maybe (error "DQT.Criterion.Split: bad cut") id
                                      (lookup i (zip bPos lb))
      in psi !! levelsToIndex dims ls

-- | The Schmidt rank of a state across a cut: the rank of its coefficient
-- matrix.  @1@ means product, @0@ means the zero state, @>= 2@ means entangled.
schmidtRank :: [Int] -> [Int] -> Vec -> Int
schmidtRank dims regsA = rank . coefficientMatrix dims regsA

-- | A successful split: @splitLeft (x) splitRight@ reproduces the state
-- exactly.
data Split = Split { splitLeft :: Vec, splitRight :: Vec }

-- | The exact product test. Returns 'Nothing' when the state is zero or
-- does not factor; otherwise the two factors.
--
-- Asymmetric: the left factor is a column of the coefficient matrix, the
-- right a row divided by the pivot (a @1@ in the pivot column). Any other
-- split differs by @(lambda, lambda^{-1})@; 'canonicalLine' fixes the choice.
factorSplit :: [Int] -> [Int] -> Vec -> Maybe Split
factorSplit dims regsA psi =
  case pivots of
    []            -> Nothing                       -- the zero state
    ((a0,b0) : _) ->
      let p = e a0 b0
      in if all (\(a,b) -> kmul (e a b) p == kmul (e a b0) (e a0 b)) cells
           then Just Split { splitLeft  = [ e a b0 | a <- [0 .. nA-1] ]
                           , splitRight = [ kdiv (e a0 b) p | b <- [0 .. nB-1] ] }
           else Nothing
  where
    m      = coefficientMatrix dims regsA psi
    nA     = matRows m
    nB     = matCols m
    e a b  = m !! a !! b
    cells  = [ (a,b) | a <- [0 .. nA-1], b <- [0 .. nB-1] ]
    pivots = [ c | c <- cells, not (kIsZero (uncurry e c)) ]

factorsAcross :: [Int] -> [Int] -> Vec -> Bool
factorsAcross dims regsA psi =
  maybe False (const True) (factorSplit dims regsA psi)

-- | A 2x2 minor that does not vanish, if there is one.  It reports the four
-- index pairs and the two products that differ, making an "unsafe" verdict
-- inspectable rather than a bare 'False'.
failingMinor :: [Int] -> [Int] -> Vec -> Maybe ((Int,Int),(Int,Int),K,K)
failingMinor dims regsA psi =
  case [ ((a,b),(a',b'), kmul (e a b) (e a' b'), kmul (e a b') (e a' b))
       | a <- [0 .. nA-1], a' <- [a+1 .. nA-1]
       , b <- [0 .. nB-1], b' <- [b+1 .. nB-1]
       , kmul (e a b) (e a' b') /= kmul (e a b') (e a' b) ] of
    []      -> Nothing
    (x : _) -> Just x
  where
    m     = coefficientMatrix dims regsA psi
    nA    = matRows m
    nB    = matCols m
    e a b = m !! a !! b

-- Lines

-- | The canonical representative of the /line/ (one-dimensional subspace)
-- through a nonzero vector: scale so the first nonzero coordinate is @1@.
--
-- Turns "constant on the same ray for every input" into an equality
-- test rather than a proportionality search: the criterion is about the
-- ray @[g]@, never a chosen vector on it.
canonicalLine :: Vec -> Vec
canonicalLine v =
  case filter (not . kIsZero) v of
    []      -> error "DQT.Criterion.Split.canonicalLine: the zero vector spans no line"
    (p : _) -> map (`kdiv` p) v

lineEqual :: Vec -> Vec -> Bool
lineEqual u v = canonicalLine u == canonicalLine v
