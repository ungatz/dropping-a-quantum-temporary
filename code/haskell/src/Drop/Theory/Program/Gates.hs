-- Drop.Theory.Program.Gates: the gates the example programs apply.
--
-- Question: Which gates do the example programs use, and which register does each one touch?
-- Answer:   Matrices exact over K. On one register: the identity, X, Z, the Hadamard gate mH, the
--           diagonal and permutation matrices (mDiag, permMat), the cyclic
--           shift mShift, and mTilt, an orthogonal 3 x 3 matrix that sends |0> to (2, 2, 1)/3. On a
--           temporary and a visible register, the temporary most significant: the read mAdd d,
--           |t, v> to |t, (v + t) mod d>; the compute gate mCompute, |t, v> to |t (+) v, v>;
--           and controlled-Z. The g-functions wrap them as Gates of Drop.Theory.Program.Syntax:
--           gHt, gXt, gTiltT and gZt act on the temporary, gIdent on the visible register, and
--           gRead, gCopy, gCZ and gCompute are joint.
-- Paper:    sec:lang:syntax (the gate statement).
-- Shapes:   Mat   a matrix over K (Drop.Theory.Algebra.Linear); a Gate is a matrix with its kind.

module Drop.Theory.Program.Gates
  ( -- * One-register matrices
    mId, mX, mZ, mH
  , mShift, mTilt
    -- * Two-register matrices (temporary most significant)
  , mCX
  , permMat
    -- * Ready-made calculus gates
  , gHt, gXt, gTiltT, gIdent
  , gRead, gCopy, gCZ, gCompute, gZt
  ) where

import Drop.Theory.Algebra.Linear
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Program.Syntax (Gate, onTmp, onVis, joint)

-- one-register matrices

mId :: Int -> Mat
mId = matId

-- >>> mId 2
-- [[1,0],[0,1]]

mX :: Mat
mX = [[kzero, kone], [kone, kzero]]

-- >>> mX
-- [[0,1],[1,0]]
-- >>> matMul mX mX == mId 2
-- True

mZ :: Mat
mZ = [[kone, kzero], [kzero, kneg kone]]

-- >>> mZ
-- [[1,0],[0,-1]]
-- >>> matMul mZ mX == matScale (kneg kone) (matMul mX mZ)
-- True

-- | @H = (1\/sqrt2) [[1,1],[1,-1]]@.  Exact because @sqrt 2@ lives in the
-- scalar field.  The two-gate program ('Drop.Theory.Corpus.Examples.twoGateSilq') applies
-- it twice.
mH :: Mat
mH = [ [kinvsqrt2, kinvsqrt2]
     , [kinvsqrt2, kneg kinvsqrt2] ]

-- H is unitary and its own inverse.
-- >>> mH
-- [[sqrt2/2,sqrt2/2],[sqrt2/2,-sqrt2/2]]
-- >>> matIsUnitary mH
-- True
-- >>> matMul mH mH == mId 2
-- True

mDiag :: [K] -> Mat
mDiag xs = [ [ if i == j then x else kzero | j <- [0 .. n-1] ]
           | (i, x) <- zip [0 ..] xs ]
  where n = length xs

-- >>> mDiag [kone, kimag, kneg kone]
-- [[1,0,0],[0,i,0],[0,0,-1]]
-- >>> mDiag []
-- []

-- | The cyclic shift on @d@ basis states, @|j> |-> |j+1 mod d>@.
mShift :: Int -> Mat
mShift d = permMat d (\j -> (j + 1) `mod` d)

-- The shift sends |j> to |j+1 mod d>: three shifts of a three-level register are the identity.
-- >>> mShift 3
-- [[0,0,1],[1,0,0],[0,1,0]]
-- >>> foldr matMul (mId 3) (replicate 3 (mShift 3)) == mId 3
-- True

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

-- The first column is tilt|0> = (2, 2, 1)/3; the matrix is orthogonal; the weight of the block {0, 1} is 8/9.
-- >>> matColumn mTilt 0
-- [2/3,2/3,1/3]
-- >>> matIsUnitary mTilt
-- True
-- >>> ksum (map knorm2 (take 2 (matColumn mTilt 0)))
-- 8/9

-- two-register matrices

-- | @permMat d p@ is the permutation matrix whose column @j@ has its @1@ in
-- row @p j@: the matrix of @|j> |-> |p j>@.
permMat :: Int -> (Int -> Int) -> Mat
permMat d p = [ [ if i == p j then kone else kzero | j <- [0 .. d-1] ]
              | i <- [0 .. d-1] ]

-- Column j has its 1 in row p j.
-- >>> permMat 3 (\j -> (j + 1) `mod` 3)
-- [[0,0,1],[1,0,0],[0,1,0]]
-- >>> permMat 2 id == mId 2
-- True

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

-- At d = 2 the read adds the temporary to the visible bit: |1, 1> goes to |1, 0>.
-- >>> matVec (mAdd 2) (vbasis 4 3)
-- [0,0,1,0]
-- >>> mAdd 2 == mCX
-- True
-- >>> matIsUnitary (mAdd 3)
-- True

-- | @CNOT@ with the temporary as control: @mAdd 2@.
mCX :: Mat
mCX = mAdd 2

-- >>> mCX
-- [[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]]
-- >>> matVec mCX (vbasis 4 2)
-- [0,0,0,1]

-- | Controlled-@Z@ on one temporary bit and one visible bit:
-- @|t,v> |-> (-1)^{t v} |t,v>@.
--
-- @mCX@ and @mCZ@ leave each basis state on its own temporary label, yet
-- compose differently (@mCX;mCX@ safe, @mCZ;mCX@ makes a Bell state): the
-- no-go for forgetful procedure summaries.
mCZ :: Mat
mCZ = mDiag [kone, kone, kone, kneg kone]

-- >>> mCZ
-- [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,-1]]
-- >>> matMul mCZ mCZ == mId 4
-- True

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

-- The temporary is the target: |0, 1> goes to |1, 1>.
-- >>> matVec mCompute (vbasis 4 1)
-- [0,0,0,1]
-- >>> mCompute == permMat 4 (\k -> (k `mod` 2) * 2 + (k `div` 2))
-- False

-- ready-made calculus gates

-- | @t := H t@ over a visible register of dimension @m@.
gHt :: Int -> Gate
gHt = onTmp "H" mH

-- The gates that act on the temporary alone.
-- >>> :m + Drop.Theory.Program.Syntax
-- >>> gHt 2
-- H
-- >>> (gateKind (gHt 2), gateVisDim (gHt 2))
-- (OnTmp,2)
-- >>> gateMat (gHt 3) == kron mH (mId 3)
-- True

-- | @t := X t@ over a visible register of dimension @m@.
gXt :: Int -> Gate
gXt = onTmp "X" mX

-- >>> (gXt 2, gateKind (gXt 2))
-- (X,OnTmp)

-- | @t := tilt t@ over a visible register of dimension @m@.
gTiltT :: Int -> Gate
gTiltT = onTmp "tilt" mTilt

-- >>> (gTiltT 3, gateKind (gTiltT 3), gateDim (gTiltT 3))
-- (tilt,OnTmp,9)

-- | The identity gate on @tmp[d] (x) vis[m]@: a legal gate, and the @W@ of
-- the shape when a safe program does no visible work.
gIdent :: Int -> Int -> Gate
gIdent d m = onVis "1" d (matId m)

-- The identity on the visible register of a program that does no visible work.
-- >>> (gIdent 2 2, gateKind (gIdent 2 2))
-- (1,OnVis)
-- >>> gateMat (gIdent 2 3) == mId 6
-- True

-- | @v := v + t@ at @d = m@.
gRead :: Int -> Gate
gRead d = joint "READ" d d (mAdd d)

-- >>> (gRead 2, gateKind (gRead 2), gateDim (gRead 3))
-- (READ,Joint,9)
-- >>> gateMat (gRead 2) == mAdd 2
-- True

-- | @copy@: @|t,x> |-> |t, x (+) t>@ on two bits.
gCopy :: Gate
gCopy = joint "copy" 2 2 mCX

-- >>> (gCopy, gateKind gCopy)
-- (copy,Joint)
-- >>> gateMat gCopy == mCX
-- True

-- | @cZ@ on two bits.
gCZ :: Gate
gCZ = joint "cZ" 2 2 mCZ

-- >>> (gCZ, gateKind gCZ)
-- (cZ,Joint)

-- | @t := t (+) v@ on two bits: the compute half of compute-uncompute.
gCompute :: Gate
gCompute = joint "compute" 2 2 mCompute

-- >>> (gCompute, gateKind gCompute)
-- (compute,Joint)
-- >>> gateMat gCompute == mCompute
-- True

-- | @t := Z t@ over a visible register of dimension @m@: a phase on the
-- temporary, how a compute-uncompute oracle marks its answer.
gZt :: Int -> Gate
gZt = onTmp "Z" mZ

-- >>> (gZt 2, gateKind (gZt 2))
-- (Z,OnTmp)
