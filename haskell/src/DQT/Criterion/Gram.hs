-- |
-- Module      : DQT.Criterion.Gram
--
-- Drop safety as a one-dimensionality statement: @K = g (x) W@ exactly when
-- its @d@ Kraus operators lie on one line in matrix space, built here as
-- three matrix forms whose ranks 'ranksAgree' checks coincide.
module DQT.Criterion.Gram
  ( -- * Kraus operators
    slices
  , sliceMatrix
    -- * The three matrices
  , gramMatrix
  , choiMatrix
    -- * Ranks
  , sliceRank, gramRank, choiRank
  , ranksAgree
    -- * The decision
  , slicesAreCollinear
    -- * The Gram identity, and the ray it carries
  , gramTrace
  , gramIsRankAtMostOne
  , parkedProjector
    -- * Reassembly
  , fromSlices
  ) where

import DQT.Algebra.Linear
import DQT.Algebra.Scalar

-- | The @d@ Kraus operators @K_i : H_m -> H_m@ of a denotation @K : H_m -> H_d (x) H_m@.
--
-- The row of @K@ indexed by the pair @(i, a)@ becomes row @a@ of Kraus
-- operator @i@, the mixed-radix convention of "DQT.Algebra.Linear" read backwards.
slices :: Int -> Int -> Mat -> [Mat]
slices d m k =
  [ [ k !! (i*m + a) | a <- [0 .. m-1] ] | i <- [0 .. d-1] ]

-- | Reassemble a denotation from its Kraus operators.  Inverse to 'slices'; used to check
-- that no information was lost in the decomposition.
fromSlices :: [Mat] -> Mat
fromSlices = concat

-- | The slice matrix: @d@ rows, @m^2@ columns, row @i@ being the Kraus
-- operator @K_i@ written out entry by entry.
--
-- @K@ factors as @g (x) W@ exactly when this matrix has rank at most one;
-- then @g@ is (any nonzero) column and @W@ is the corresponding row.
sliceMatrix :: Int -> Int -> Mat -> Mat
sliceMatrix d m k = [ concat s | s <- slices d m k ]

-- | @G_ij = tr(K_i^dagger K_j)@, computed as the ordinary Hermitian inner
-- product of the two Kraus operators written out flat.
gramMatrix :: Int -> Int -> Mat -> Mat
gramMatrix d m k =
  [ [ vdot ri rj | rj <- rows ] | ri <- rows ]
  where rows = sliceMatrix d m k

-- | @Choi = M^dagger M = sum_i vec(K_i) vec(K_i)^dagger@, an @m^2@-by-@m^2@
-- matrix.  Its rank is the number of Kraus operators the channel
-- @X |-> sum_i K_i X K_i^dagger@ needs.
choiMatrix :: Int -> Int -> Mat -> Mat
choiMatrix d m k = matMul (matConjTranspose mm) mm
  where mm = sliceMatrix d m k

sliceRank, gramRank, choiRank :: Int -> Int -> Mat -> Int
sliceRank d m = rank . sliceMatrix d m
gramRank  d m = rank . gramMatrix  d m
choiRank  d m = rank . choiMatrix  d m

-- | The three ranks coincide.  This is linear algebra over a field with an
-- involution whose associated form is definite: the continuation-side
-- statement and the minor-side statement are the same statement.  Checking
-- it on every example is one of the two independent routes of
-- "DQT.Criterion".
ranksAgree :: Int -> Int -> Mat -> Bool
ranksAgree d m k =
  sliceRank d m k == gramRank d m k && gramRank d m k == choiRank d m k

-- | Do the Kraus operators span a space of dimension at most one?  This is the
-- criterion, in the form "the temporary carried nothing".
slicesAreCollinear :: Int -> Int -> Mat -> Bool
slicesAreCollinear d m k = sliceRank d m k <= 1

-- | @tr(G) = sum_i ||K_i||^2@, the squared Frobenius norm of the denotation.
gramTrace :: Int -> Int -> Mat -> K
gramTrace d m k = ksum [ g !! i !! i | i <- [0 .. d-1] ]
  where g = gramMatrix d m k

-- | The criterion as one matrix identity: @G^2 = tr(G) G@.
--
-- @G@ is Hermitian, positive semidefinite: eigenvalues real, nonnegative,
-- summing to @tr(G)@, each forced by the identity to @0@ or @tr(G)@, so
-- at most one is nonzero and @G@ has rank at most one (and conversely).
-- Same decision as 'slicesAreCollinear', with no elimination.
gramIsRankAtMostOne :: Int -> Int -> Mat -> Bool
gramIsRankAtMostOne d m k = matMul g g == matScale (gramTrace d m k) g
  where g = gramMatrix d m k

-- | The projector onto the constant ray, read off the Gram matrix alone.
--
-- For a safe map @K = g (x) W@, @G_ij = conj(g_i) g_j tr(W^dagger W)@, so
-- @G^T / tr(G) = g g^dagger / ||g||^2@, the projector onto the line of
-- @g@. 'Nothing' when @G = 0@; on an unsafe map the same formula is not
-- a projector, so callers test 'gramIsRankAtMostOne' first.
parkedProjector :: Int -> Int -> Mat -> Maybe Mat
parkedProjector d m k
  | kIsZero t = Nothing
  | otherwise = Just (matTranspose (matScale (kinv t) g))
  where g = gramMatrix d m k
        t = gramTrace d m k
