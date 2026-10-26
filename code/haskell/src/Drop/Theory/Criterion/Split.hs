-- Drop.Theory.Criterion.Split: splitting a state across a cut, exactly.
--
-- Question: Does a state factor across a cut of its registers, and into which two factors?
-- Answer:   The coefficient matrix of a state across a cut has the cut's left registers on its rows
--           and the others on its columns. The state factors exactly when that matrix has rank at
--           most one, and factorSplit returns the factors, the left one a
--           column of the matrix and the right one a row divided by the pivot, which is why K is a
--           field. Any other split differs by (lambda, 1/lambda); canonicalLine fixes the choice
--           by scaling the first nonzero coordinate to 1. failingMinor returns a 2 x 2 minor that
--           does not vanish, as evidence for a refusal.
-- Paper:    sec:factor (a state across a cut, and when it factors).
-- Shapes:   Split   the two factors of a state: splitLeft (x) splitRight is the state.

module Drop.Theory.Criterion.Split
  ( -- * The product test
    Split(..)
  , factorSplit
  , failingMinor
    -- * Lines (states up to scalar)
  , canonicalLine
  , lineEqual
  ) where

import Drop.Theory.Algebra.Linear
import Drop.Theory.Algebra.Scalar

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
    -- impossible: aPos holds positions below the number of registers
    dimsA = [ dims !! i | i <- aPos ]
    -- impossible: bPos holds positions below the number of registers
    dimsB = [ dims !! i | i <- bPos ]
    nA    = dimProduct dimsA
    nB    = dimProduct dimsB
    entry a b =
      let la = indexToLevels dimsA a
          lb = indexToLevels dimsB b
          ls = [ pick i | i <- [0 .. n-1] ]
          pick i = case lookup i (zip aPos la) of
                     Just l  -> l
                     -- impossible: every position is in aPos or in bPos
                     Nothing -> maybe (error "Drop.Theory.Criterion.Split: bad cut") id
                                      (lookup i (zip bPos lb))
      -- impossible: ls has a level below its dimension for every register, so the index is below the length of psi
      in psi !! levelsToIndex dims ls

-- Two qubits: a product state and a Bell state, cut between the registers.
-- >>> coefficientMatrix [2, 2] [0] [kone, kzero, kone, kzero]
-- [[1,0],[1,0]]
-- >>> coefficientMatrix [2, 2] [0] [kone, kzero, kzero, kone]
-- [[1,0],[0,1]]
-- >>> coefficientMatrix [2, 2] [1] [kone, ktwo, kzero, kzero]
-- [[1,0],[2,0]]

-- | A successful split: @splitLeft (x) splitRight@ reproduces the state
-- exactly.
data Split = Split { splitLeft :: Vec, splitRight :: Vec }

-- The left factor is a column of the coefficient matrix; the right is a row divided by the pivot.
-- >>> let Just s = factorSplit [2, 2] [0] [ktwo, kzero, ktwo, kzero]
-- >>> splitLeft s
-- [2,2]
-- >>> splitRight s
-- [1,0]

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
    -- impossible: a and b range over the rows and columns of m
    e a b  = m !! a !! b
    cells  = [ (a,b) | a <- [0 .. nA-1], b <- [0 .. nB-1] ]
    pivots = [ c | c <- cells, not (kIsZero (uncurry e c)) ]

-- >>> fmap splitLeft (factorSplit [2, 2] [0] [kone, kone, kone, kone])
-- Just [1,1]
-- >>> fmap splitRight (factorSplit [2, 2] [0] [kone, kone, kone, kone])
-- Just [1,1]
-- >>> fmap splitLeft (factorSplit [2, 2] [0] [kone, kzero, kzero, kone])
-- Nothing
-- >>> fmap splitLeft (factorSplit [2, 2] [0] [kzero, kzero, kzero, kzero])
-- Nothing
-- >>> fmap (\t -> tensorV (splitLeft t) (splitRight t)) (factorSplit [2, 2] [0] [ktwo, kone, kzero, kzero])
-- Just [2,1,0,0]

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
    -- impossible: a and b range over the rows and columns of m
    e a b = m !! a !! b

-- The first 2 x 2 minor that does not vanish: the products of its diagonals differ.
-- >>> failingMinor [2, 2] [0] [kone, kzero, kzero, kone]
-- Just ((0,0),(1,1),1,0)
-- >>> failingMinor [2, 2] [0] [kone, kzero, kone, kzero]
-- Nothing

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
    -- refusal: the zero vector spans no line
    []      -> error "Drop.Theory.Criterion.Split.canonicalLine: the zero vector spans no line"
    (p : _) -> map (`kdiv` p) v

-- Scale so the first nonzero coordinate is 1.
-- >>> canonicalLine [kzero, ktwo, kone]
-- [0,1,1/2]
-- >>> canonicalLine [kimag, kone]
-- [1,-1i]
-- >>> canonicalLine [kone, kzero]
-- [1,0]

lineEqual :: Vec -> Vec -> Bool
lineEqual u v = canonicalLine u == canonicalLine v

-- >>> lineEqual [kone, kone] [ktwo, ktwo]
-- True
-- >>> lineEqual [kone, kone] [kone, kneg kone]
-- False
-- >>> lineEqual [kzero, kone] [kzero, kimag]
-- True
