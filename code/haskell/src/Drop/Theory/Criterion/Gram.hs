-- Drop.Theory.Criterion.Gram: the Kraus operators of a denotation, and when they lie on one line.
--
-- Question: When do the d Kraus operators of a denotation K : H_m -> H_d (x) H_m span at most a line?
-- Answer:   The slices of K are its d Kraus operators, each an m x m matrix. Three matrices record
--           them: the slice matrix (d rows, m^2 columns, each operator written out flat), the Gram
--           matrix G_ij = tr(K_i^dagger K_j) (d x d) and the Choi matrix, the slice matrix's
--           adjoint times itself (m^2 x m^2). ranksAgree tests that the three ranks coincide. K is
--           g (x) W exactly when that rank is at most one (slicesAreCollinear), and for a Gram
--           matrix that is the identity G^2 = tr(G) G (gramIsRankAtMostOne), which needs no
--           elimination. parkedProjector reads the projector onto the line of g from G alone.
-- Paper:    sec:factor (the factorization), app:criterion (the criterion, in detail).
-- Shapes:   Mat   a matrix over K; a denotation is a Mat with d * m rows and m columns.

module Drop.Theory.Criterion.Gram
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
  , gramIsRankAtMostOne
  , parkedProjector
    -- * Reassembly
  ) where

import Drop.Theory.Algebra.Linear
import Drop.Theory.Algebra.Scalar

-- | The @d@ Kraus operators @K_i : H_m -> H_m@ of a denotation @K : H_m -> H_d (x) H_m@.
--
-- The row of @K@ indexed by the pair @(i, a)@ becomes row @a@ of Kraus
-- operator @i@, the mixed-radix convention of "Drop.Theory.Algebra.Linear" read backwards.
slices :: Int -> Int -> Mat -> [Mat]
slices d m k =
  -- impossible: k has d * m rows
  [ [ k !! (i*m + a) | a <- [0 .. m-1] ] | i <- [0 .. d-1] ]

-- Two Kraus operators of 2 x 2 size. The first denotation is g (x) I with g = e_0; the second reads the temporary into the visible bit.
-- >>> let safeK = kron [[kone], [kzero]] (matId 2)
-- >>> let readK = [[kone, kzero], [kzero, kzero], [kzero, kzero], [kzero, kone]]
-- >>> slices 2 2 safeK
-- [[[1,0],[0,1]],[[0,0],[0,0]]]
-- >>> slices 2 2 readK
-- [[[1,0],[0,0]],[[0,0],[0,1]]]

-- | The slice matrix: @d@ rows, @m^2@ columns, row @i@ being the Kraus
-- operator @K_i@ written out entry by entry.
--
-- @K@ factors as @g (x) W@ exactly when this matrix has rank at most one;
-- then @g@ is (any nonzero) column and @W@ is the corresponding row.
sliceMatrix :: Int -> Int -> Mat -> Mat
sliceMatrix d m k = [ concat s | s <- slices d m k ]

-- One row for each Kraus operator, written out flat.
-- >>> sliceMatrix 2 2 safeK
-- [[1,0,0,1],[0,0,0,0]]
-- >>> sliceMatrix 2 2 readK
-- [[1,0,0,0],[0,0,0,1]]

-- | @G_ij = tr(K_i^dagger K_j)@, computed as the ordinary Hermitian inner
-- product of the two Kraus operators written out flat.
gramMatrix :: Int -> Int -> Mat -> Mat
gramMatrix d m k =
  [ [ vdot ri rj | rj <- rows ] | ri <- rows ]
  where rows = sliceMatrix d m k

-- >>> gramMatrix 2 2 safeK
-- [[2,0],[0,0]]
-- >>> gramMatrix 2 2 readK
-- [[1,0],[0,1]]

-- | @Choi = M^dagger M = sum_i vec(K_i) vec(K_i)^dagger@, an @m^2@-by-@m^2@
-- matrix.  Its rank is the number of Kraus operators the channel
-- @X |-> sum_i K_i X K_i^dagger@ needs.
choiMatrix :: Int -> Int -> Mat -> Mat
choiMatrix d m k = matMul (matConjTranspose mm) mm
  where mm = sliceMatrix d m k

-- >>> choiMatrix 2 2 safeK
-- [[1,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,1]]
-- >>> choiMatrix 2 2 readK
-- [[1,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,1]]

sliceRank, gramRank, choiRank :: Int -> Int -> Mat -> Int
sliceRank d m = rank . sliceMatrix d m
gramRank  d m = rank . gramMatrix  d m
choiRank  d m = rank . choiMatrix  d m

-- The three ranks of a safe denotation are 1; of the read denotation, 2.
-- >>> (sliceRank 2 2 safeK, gramRank 2 2 safeK, choiRank 2 2 safeK)
-- (1,1,1)
-- >>> (sliceRank 2 2 readK, gramRank 2 2 readK, choiRank 2 2 readK)
-- (2,2,2)
-- >>> (sliceRank 2 2 (matZero 4 2), gramRank 2 2 (matZero 4 2), choiRank 2 2 (matZero 4 2))
-- (0,0,0)

-- | Do the ranks of the slice, Gram and Choi matrices coincide?  They are
-- equal for complex entries; this tests it on the given denotation.
ranksAgree :: Int -> Int -> Mat -> Bool
ranksAgree d m k =
  sliceRank d m k == gramRank d m k && gramRank d m k == choiRank d m k

-- >>> ranksAgree 2 2 safeK
-- True
-- >>> ranksAgree 2 2 readK
-- True
-- >>> ranksAgree 2 2 (matZero 4 2)
-- True

-- | Do the Kraus operators span a space of dimension at most one?  This is the
-- criterion, in the form "the temporary carried nothing".
slicesAreCollinear :: Int -> Int -> Mat -> Bool
slicesAreCollinear d m k = sliceRank d m k <= 1

-- >>> slicesAreCollinear 2 2 safeK
-- True
-- >>> slicesAreCollinear 2 2 readK
-- False
-- >>> slicesAreCollinear 2 2 (matZero 4 2)
-- True

-- | @tr(G) = sum_i ||K_i||^2@, the squared Frobenius norm of the denotation.
gramTrace :: Int -> Int -> Mat -> K
-- impossible: the Gram matrix is d x d
gramTrace d m k = ksum [ g !! i !! i | i <- [0 .. d-1] ]
  where g = gramMatrix d m k

-- The squared Frobenius norm of the denotation: 2 in both cases.
-- >>> gramTrace 2 2 safeK
-- 2
-- >>> gramTrace 2 2 readK
-- 2

-- | The criterion as one matrix identity: @G^2 = tr(G) G@.
--
-- @G@ is Hermitian, positive semidefinite: eigenvalues real, nonnegative,
-- summing to @tr(G)@, each forced by the identity to @0@ or @tr(G)@, so
-- at most one is nonzero and @G@ has rank at most one (and conversely).
-- Same decision as 'slicesAreCollinear', with no elimination.
gramIsRankAtMostOne :: Int -> Int -> Mat -> Bool
gramIsRankAtMostOne d m k = matMul g g == matScale (gramTrace d m k) g
  where g = gramMatrix d m k

-- >>> gramIsRankAtMostOne 2 2 safeK
-- True
-- >>> gramIsRankAtMostOne 2 2 readK
-- False
-- >>> gramIsRankAtMostOne 2 2 (matZero 4 2)
-- True

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

-- For a safe denotation, the projector onto the line of g; none for the zero map.
-- >>> parkedProjector 2 2 safeK
-- Just [[1,0],[0,0]]
-- >>> parkedProjector 2 2 (matZero 4 2)
-- Nothing
