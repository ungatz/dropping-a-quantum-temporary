-- |
-- Module      : Drop.Theory.Program.Gates
--
-- The gate library. Every matrix is exact over "Drop.Theory.Algebra.Scalar", and each
-- Haddock says what the gate does and where the calculus uses it.
module Drop.Theory.Program.Gates
  ( -- * One-register matrices
    mId, mX, mZ, mH, mS, mT
  , mShift, mTilt
  , mDiag
    -- * Two-register matrices (temporary most significant)
  , mAdd, mCX, mCZ, mSwap, mCompute
  , permMat
    -- * Ready-made calculus gates
  , gHt, gXt, gTiltT, gIdent
  , gRead, gCopy, gCZ, gCompute, gComputeAt, gZt
  ) where

import Drop.Theory.Algebra.Linear
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Program.Syntax (Gate, onTmp, onVis, joint)

-- one-register matrices

mId :: Int -> Mat
mId = matId

mX :: Mat
mX = [[kzero, kone], [kone, kzero]]

mZ :: Mat
mZ = [[kone, kzero], [kzero, kneg kone]]

-- | @H = (1\/sqrt2) [[1,1],[1,-1]]@.  Exact because @sqrt 2@ lives in the
-- scalar field.  This is the gate the two-gate program of the introduction applies
-- twice, and the gate a @qfree@ producer rule refuses.
mH :: Mat
mH = [ [kinvsqrt2, kinvsqrt2]
     , [kinvsqrt2, kneg kinvsqrt2] ]

mS :: Mat
mS = mDiag [kone, kimag]

mT :: Mat
mT = mDiag [kone, komega]

mDiag :: [K] -> Mat
mDiag xs = [ [ if i == j then x else kzero | j <- [0 .. n-1] ]
           | (i, x) <- zip [0 ..] xs ]
  where n = length xs

-- | The cyclic shift on @d@ basis states, @|j> |-> |j+1 mod d>@.  The read family of
-- the per-record table (the record-dependent reclaim section) is built from it.
mShift :: Int -> Mat
mShift d = permMat d (\j -> (j + 1) `mod` d)

-- | The @tilt@ matrix:
--
-- > tilt = (1/3) * [[2,2,1],[2,-1,-2],[1,-2,2]],   tilt|0> = (1/3)(2,2,1)^T.
--
-- Needs an allocated state with a foot inside the measured block
-- @S = {0,1}@ and a foot outside it, so both outcomes are reachable and
-- the verdicts differ; orthogonal to be a legal gate, tilting @|0>@ off
-- the block boundary rather than rotating within it or permuting across.
-- Entries come from @2^2 + 2^2 + 1^2 = 3^2@, giving branch weights
-- @8\/9@ and @1\/9@.
mTilt :: Mat
mTilt = [ [q 2, q 2, q 1]
        , [q 2, q (-1), q (-2)]
        , [q 1, q (-2), q 2] ]
  where q :: Integer -> K
        q n = fromRat (fromInteger n / 3)

-- two-register matrices

-- | @permMat d p@ is the permutation matrix whose column @j@ has its @1@ in
-- row @p j@: the matrix of @|j> |-> |p j>@.
permMat :: Int -> (Int -> Int) -> Mat
permMat d p = [ [ if i == p j then kone else kzero | j <- [0 .. d-1] ]
              | i <- [0 .. d-1] ]

-- | The read gate @v := v + t@ on @tmp[d] (x) vis[d]@:
--
-- > |t, v> |-> |t, (v + t) mod d>
--
-- At @d = 2@ it is exactly @CNOT@ with the temporary as control: the
-- /only/ way this calculus can make @v@ depend on the temporary.
mAdd :: Int -> Mat
mAdd d = permMat (d*d) (\k -> let t = k `div` d
                                  v = k `mod` d
                              in t * d + ((v + t) `mod` d))

-- | @CNOT@ with the temporary as control: @mAdd 2@.
mCX :: Mat
mCX = mAdd 2

-- | Controlled-@Z@ on one temporary bit and one visible bit:
-- @|t,v> |-> (-1)^{t v} |t,v>@.
--
-- @mCX@ and @mCZ@ leave each basis state on its own temporary label, yet
-- compose differently (@mCX;mCX@ safe, @mCZ;mCX@ makes a Bell state): the
-- no-go for forgetful procedure summaries.
mCZ :: Mat
mCZ = mDiag [kone, kone, kone, kneg kone]

-- | The compute gate @t := t (+) v@: temporary is the /target/, visible
-- register the /control/, @|t, v> |-> |t (+) v, v>@.
--
-- Writes a function of @v@ into the temporary, the first half of
-- compute-uncompute. 'mAdd' reads the opposite register; the two differ
-- only there, yet their drop verdicts differ completely.
mCompute :: Mat
mCompute = permMat 4 (\k -> let t = k `div` 2
                                v = k `mod` 2
                            in ((t + v) `mod` 2) * 2 + v)

-- | Swap two registers of equal dimension @d@.
mSwap :: Int -> Mat
mSwap d = permMat (d*d) (\k -> (k `mod` d) * d + (k `div` d))

-- ready-made calculus gates

-- | @t := H t@ over a visible register of dimension @m@.
gHt :: Int -> Gate
gHt = onTmp "H" mH

-- | @t := X t@ over a visible register of dimension @m@.
gXt :: Int -> Gate
gXt = onTmp "X" mX

-- | @t := tilt t@ over a visible register of dimension @m@.
gTiltT :: Int -> Gate
gTiltT = onTmp "tilt" mTilt

-- | The identity gate on @tmp[d] (x) vis[m]@: a legal gate, and the @W@ of
-- the shape when a safe program does no visible work.
gIdent :: Int -> Int -> Gate
gIdent d m = onVis "1" d (matId m)

-- | @v := v + t@ at @d = m@.
gRead :: Int -> Gate
gRead d = joint "READ" d d (mAdd d)

-- | @copy@: @|t,x> |-> |t, x (+) t>@ on two bits.
gCopy :: Gate
gCopy = joint "copy" 2 2 mCX

-- | @cZ@ on two bits.
gCZ :: Gate
gCZ = joint "cZ" 2 2 mCZ

-- | @t := t (+) v@ on two bits: the compute half of compute-uncompute.
gCompute :: Gate
gCompute = joint "compute" 2 2 mCompute

-- | @t := t (+) v@ at every dimension: @|t, v> |-> |t + v mod d, v>@ on a
-- @d@-dimensional temporary and visible register ('gCompute' at @d = 2@).
--
-- A permutation, hence classical, accepted by any superposition-only
-- discipline; writes @v@ into the temporary, Kraus operators pairwise
-- non-proportional, drop leaks at rank @d@: one witness per dimension.
gComputeAt :: Int -> Gate
gComputeAt d = joint "compute" d d
  (permMat (d*d) (\k -> let t = k `div` d; v = k `mod` d
                        in ((t + v) `mod` d) * d + v))

-- | @t := Z t@ over a visible register of dimension @m@: a phase on the
-- temporary, how a compute-uncompute oracle marks its answer.
gZt :: Int -> Gate
gZt = onTmp "Z" mZ
