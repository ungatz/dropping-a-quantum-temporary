-- Drop.Lang.Compile.Emit: the OpenQASM 3 text, and the gate that returns a dropped block.
--
-- Question: What OpenQASM 3 text does each construct become, and which gate returns a dropped block?
-- Answer:   compileTerm emits the source gates and inserts, at each drop, the gate that returns the
--           dropped block; buildHeader and outputMeasureLines add the declarations and the
--           measurements of the registers the program returns. A drop forgets a name and erases
--           no state, so what is inserted is the gate that puts the block back: for temporaries
--           emitReclaim chooses nothing, a basis transposition, a single U, the two-support
--           short form, or the general reflection (the inverse axis preparation, a sign flip of
--           |0...0>, the axis preparation). A block that holds loans gets the return gate T
--           with T B = J (emitLoanReturn): the identity, a one-qubit unitary or a basis
--           permutation keep a short form, alone or beside the temporaries' certificate; every
--           other isometric factor gets at most one reflection per column of B and
--           one diagonal (emitFrameReturnOps). Op describes these gates before they are printed and renderOp
--           prints them, which keeps the matrix construction apart from the wire spelling. A
--           real rotation under a control prints as ry(theta), never as a controlled
--           U(theta,0,0): OpenQASM 3's built-in U adds exp(i theta/2), which becomes a relative
--           phase once controlled. This is the only module of the package, with its test, where
--           an inexact numeric type occurs; the SAFE/UNSAFE decision stays exact (Safety).
-- Paper:    sec:lang:compile, app:compile (the constructions), app:emitter-contract (the contract).
-- Shapes:   Op  one gate of the reflections' circuits: OpU (a one-qubit U), OpP (a phase), OpX,
--               OpZ, each with its controls as (qubit, required bit) pairs and its target qubit.

module Drop.Lang.Compile.Emit
  ( compileTerm
  , compileDrop
  , buildHeader
  , outputMeasureLines
  , wireAllocOf
  , leavesWithExpected
  -- exported for the unit test (the reclaiming proposition's gate):
  , reflectionR
  , u3OfMatrix
  , proportionalTo
  , toC
  -- exported for the unit test of the general k-qubit reclaiming
  -- reflection: the internal gate representation, its dense-matrix reading
  -- (so a test can simulate exactly the object that gets rendered, via
  -- Drop.Lang.State.applyGate, with no re-parsing of the emitted text), and the
  -- op-list builder itself.
  , Op (..)
  , opDense
  , emitGeneralReflectionOps
  -- exported for the unit test of the two-support short form:
  , emitTwoSupportReflectionOps
  , emitFrameReturnOps, frameReturnMatrix, placementIndex
  , emittedReturnResidualOK
  ) where

import Control.Monad (foldM)
import Data.Char (isAlphaNum)
import Data.Complex
import Data.List (intercalate, nub)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, listToMaybe)
import Text.Printf (printf)

import Drop.Lang.Compile.Layout
import Drop.Lang.Compile.Safety
import Drop.Lang.Machine
import Drop.Lang.Scalar (Cyclo (..), Conj(conj))
import Drop.Lang.State
import Drop.Lang.Syntax


-- Numeric evaluation of the exact scalars (angle synthesis only) --------------

-- | The complex number a scalar of the tower stands for, by evaluating its
-- coefficients at e^(2 pi i / 2^k); used for angles only.
toC :: Cyclo -> Complex Double
toC (Cyclo k cs) = sum [ (fromRational c :+ 0) * (w ^^ i) | (i, c) <- zip [0 :: Int ..] cs ]
  where
    n = (2 :: Integer) ^ k
    w = cis (2 * pi / fromIntegral n)

-- >>> :m + Drop.Lang.Scalar Drop.Lang.Parser
-- >>> toC 1
-- 1.0 :+ 0.0
-- >>> toC (-1)
-- (-1.0) :+ 0.0

-- sqrt 2 is the sum of zeta_8 and its inverse; the answer is sqrt 2 as a double, with a rounding residue in the imaginary part.
-- >>> toC sqrt2C
-- 1.414213562373095 :+ (-2.220446049250313e-16)

-- The primitive eighth root of unity, omega_8 = e^(2 pi i / 8): both coordinates are 1/sqrt 2.
-- >>> toC (zetaC 3)
-- 0.7071067811865476 :+ 0.7071067811865475
-- >>> toC (zetaC 3 ^ 8)
-- 1.0 :+ 0.0

-- Divide real components directly: Complex (/ (s :+ 0)) can underflow
-- internally even when each component divided by s is representable.
divideReal :: Double -> Complex Double -> Complex Double
divideReal s z = (realPart z / s) :+ (imagPart z / s)

-- >>> divideReal 2 (4 :+ 6)
-- 2.0 :+ 3.0
-- >>> divideReal 1e-300 (3e-300 :+ 4e-300)
-- 3.0 :+ 4.0

-- | A real number that is neither NaN nor infinite.
finiteDouble :: Double -> Bool
finiteDouble x = not (isNaN x || isInfinite x)

-- >>> map finiteDouble [1, 0 / 0, 1 / 0]
-- [True,False,False]

-- | A complex number whose two coordinates are finite.
finiteComplex :: Complex Double -> Bool
finiteComplex z = finiteDouble (realPart z) && finiteDouble (imagPart z)

-- >>> finiteComplex (1 :+ 2)
-- True
-- >>> finiteComplex (1 :+ (1 / 0))
-- False

-- | The length of the first vector in a list of vectors, 0 for none: the
-- dimension of a column list, the width of a row list.
firstLength :: [[a]] -> Int
firstLength = maybe 0 length . listToMaybe

-- >>> firstLength [[1, 2, 3], [4, 5, 6 :: Int]]
-- 3
-- >>> firstLength ([] :: [[Int]])
-- 0

-- Normalize after scaling, without squaring the original tiny/huge entries.
unitVectorC :: [Complex Double] -> Maybe [Complex Double]
unitVectorC v
  | not (all finiteComplex v) || scale == 0 = Nothing
  | otherwise = Just (map (divideReal norm) scaled)
  where
    scale = maximum (0 : concat [[abs (realPart z), abs (imagPart z)] | z <- v])
    scaled = map (divideReal scale) v
    norm = sqrt (sum [realPart z ** 2 + imagPart z ** 2 | z <- scaled])

-- >>> unitVectorC [3 :+ 0, 0 :+ 4]
-- Just [0.6 :+ 0.0,0.0 :+ 0.8]
-- >>> unitVectorC [0, 0]
-- Nothing

-- Entries too small to square are scaled first, so the answer is still a unit vector.
-- >>> unitVectorC [1e-200 :+ 0, 1e-200 :+ 0]
-- Just [0.7071067811865475 :+ 0.0,0.7071067811865475 :+ 0.0]
-- >>> unitVectorC [1 :+ (1 / 0), 0]
-- Nothing

-- canonicalLine is right for exact ray equality, but its first coordinate
-- can divide by a tiny Galois conjugate. Convert a bounded projector column
-- instead. Its exact diagonal entries choose a nonzero pivot before the
-- column is converted; no approximate data enters the safety decision.
unitOfExactRay :: [Cyclo] -> Maybe [Complex Double]
unitOfExactRay v
  | norm == 0 || not (all finiteComplex weights) = Nothing
  | otherwise = case candidates of
      [] -> Nothing
      (p : ps) ->
        -- impossible: i, j and pivot index v; weights has one entry per entry of v
        let pivot = foldl (\i j -> if realPart (weights !! j) > realPart (weights !! i)
                                  then j else i) p ps
        -- impossible: i, j and pivot index v; weights has one entry per entry of v
        in unitVectorC [toC (x * conj (v !! pivot) / norm) | x <- v]
  where
    norm = sum [conj x * x | x <- v]
    weights = [toC (conj x * x / norm) | x <- v]
    -- impossible: i, j and pivot index v; weights has one entry per entry of v
    candidates = [i | (i, x) <- zip [0 ..] v, x /= 0, realPart (weights !! i) > 0]

-- >>> unitOfExactRay [1, 0]
-- Just [1.0 :+ 0.0,0.0 :+ 0.0]
-- >>> unitOfExactRay [1, 1]
-- Just [0.7071067811865475 :+ 0.0,0.7071067811865475 :+ 0.0]
-- >>> unitOfExactRay [0, 0]
-- Nothing

-- The ray of (1, omega_8): a unit vector with a relative phase of an eighth turn.
-- >>> unitOfExactRay [1, zetaC 3]
-- Just [0.7071067811865475 :+ 0.0,0.5 :+ 0.49999999999999994]

-- | A matrix of the tower as a matrix of complex numbers.
matC :: Matrix Cyclo -> [[Complex Double]]
matC = map (map toC)

-- >>> matC [[1, 0], [0, 1]]
-- [[1.0 :+ 0.0,0.0 :+ 0.0],[0.0 :+ 0.0,1.0 :+ 0.0]]
-- >>> matC [[0, iC], [1, 0]]
-- [[0.0 :+ 0.0,6.123233995736766e-17 :+ 1.0],[1.0 :+ 0.0,0.0 :+ 0.0]]

-- | @proportionalTo psi g@ holds when 'g' is a unit complex scalar multiple
-- of 'psi', i.e. there is c with |c| = 1 and g = c * psi. This is the third
-- disjunct of the domain predicate 'Admissible psi g' --
-- one qubit, OR psi and g both basis states, OR g proportional to psi --
-- the exact case in which the reclaiming gate is the identity (nothing to
-- emit), matching reflectionR's own "R = I when g is already proportional
-- to psi" above. Both arguments are assumed unit vectors, as reflectionR
-- already assumes. Phase-aligns g to psi via their inner product, the same
-- way reflectionR computes gTilde, and checks the residual is zero to the
-- 1e-12 tolerance emitReclaim already uses for its own norm check.
proportionalTo :: [Complex Double] -> [Complex Double] -> Bool
proportionalTo psi g =
  let ip = sum (zipWith (\x y -> conjugate x * y) psi g)
  in magnitude ip > 1e-9 &&
     let gTilde = map (* cis (negate (phase ip))) g
         w = zipWith (-) psi gTilde
         wnorm = sqrt (sum [ magnitude z ** 2 | z <- w ])
     in wnorm < 1e-12

-- >>> proportionalTo [1, 0] [0 :+ 1, 0]
-- True
-- >>> proportionalTo [1, 0] [0, 1]
-- False

-- A vector is proportional to itself up to a unit phase of an eighth turn.
-- >>> proportionalTo [1 / sqrt 2 :+ 0, 1 / sqrt 2 :+ 0] (map (* toC (zetaC 3)) [1 / sqrt 2 :+ 0, 1 / sqrt 2 :+ 0])
-- True

-- | Convert a square exact factor B with B^dagger B = t I, t > 0,
-- without converting its arbitrary nonzero scale first. The flattened
-- exact ray has squared norm n*t, so sqrt(n) times its unit representative
-- is B/sqrt(t), up to one overall phase. Shape recognition remains exact.
normaliseSquareIso :: String -> Matrix Cyclo -> Either CompileError [[Complex Double]]
normaliseSquareIso label b
  | n == 0 || any ((/= n) . length) b = failure
  | otherwise = case unitOfExactRay (concat b) of
      Nothing -> failure
      Just v ->
        let scaled = map (* (sqrt (fromIntegral n) :+ 0)) v
        in if all finiteComplex scaled
             then Right [ take n (drop (i*n) scaled) | i <- [0 .. n-1] ]
             else failure
  where
    n = length b
    failure = Left (Other ("drop " ++ label ++ ": numerical loan factor cannot be normalized"))

-- >>> normaliseSquareIso "t" [[0, 1], [1, 0]]
-- Right [[0.0 :+ 0.0,1.0 :+ 0.0],[1.0 :+ 0.0,0.0 :+ 0.0]]

-- The scale of the factor does not matter: 2 X normalises to X.
-- >>> normaliseSquareIso "t" [[0, 2], [2, 0]]
-- Right [[0.0 :+ 0.0,1.0 :+ 0.0],[1.0 :+ 0.0,0.0 :+ 0.0]]
-- >>> either showCompileError show (normaliseSquareIso "t" [[0, 0], [0, 0]])
-- "drop t: numerical loan factor cannot be normalized"
-- >>> either showCompileError show (normaliseSquareIso "t" [[1, 0, 0], [0, 1, 0]])
-- "drop t: numerical loan factor cannot be normalized"

-- | Convert an exact isometric factor B (n rows, m columns, B^dagger B = t I
-- with t > 0) to its unit representative B / sqrt t, up to one overall
-- phase, without converting its arbitrary nonzero scale first: the
-- flattened exact ray has squared norm m t. 'normaliseSquareIso' is the
-- square case.
normaliseIso :: String -> Matrix Cyclo -> Either CompileError [[Complex Double]]
normaliseIso label b
  | n == 0 || m == 0 || any ((/= m) . length) b = failure
  | otherwise = case unitOfExactRay (concat b) of
      Nothing -> failure
      Just v ->
        let scaled = map (* (sqrt (fromIntegral m) :+ 0)) v
        in if all finiteComplex scaled
             then Right [ take m (drop (i*m) scaled) | i <- [0 .. n-1] ]
             else failure
  where
    n = length b
    m = firstLength b
    failure = Left (Other ("drop " ++ label ++ ": numerical loan factor cannot be normalized"))

-- >>> normaliseIso "t" [[1, 0], [0, 1], [0, 0], [0, 0]]
-- Right [[1.0 :+ 0.0,0.0 :+ 0.0],[0.0 :+ 0.0,1.0 :+ 0.0],[0.0 :+ 0.0,0.0 :+ 0.0],[0.0 :+ 0.0,0.0 :+ 0.0]]

-- A factor that is not rectangular is refused by name.
-- >>> either showCompileError show (normaliseIso "t" [[1, 0], [0]])
-- "drop t: numerical loan factor cannot be normalized"
-- >>> either showCompileError show (normaliseIso "t" [])
-- "drop t: numerical loan factor cannot be normalized"

daggerC :: [[Complex Double]] -> [[Complex Double]]
-- impossible: daggerC takes a square matrix: n rows of n entries, i and j below n
daggerC m = [ [ conjugate (m !! j !! i) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
  where n = length m

-- >>> map (map (\z -> (round (realPart z), round (imagPart z)))) (daggerC [[0, 0 :+ 1], [1, 0]])
-- [[(0,0),(1,0)],[(0,-1),(0,0)]]
-- >>> map (map (\z -> (round (realPart z), round (imagPart z)))) (daggerC [[1, 0], [0, 1]])
-- [[(1,0),(0,0)],[(0,0),(1,0)]]

-- | The square loan factors with a dedicated short form: the identity
-- (nothing to undo), a factor on one qubit (a U(theta,phi,lambda)), and a
-- permutation of the basis states (the inverse permutation as a chain of
-- transpositions). Every other isometric factor goes through the general
-- return gate ('emitFrameReturnOps'). 'compileDrop' takes the short form
-- exactly when this holds and 'expectedFinalState' applies B^dagger exactly
-- when this holds, so the two cannot drift apart. Shape is decided exactly.
squareFactorEmittable :: Matrix Cyclo -> Bool
squareFactorEmittable b =
  length b == 2 || maybe False (const True) (scalarPermutation b)

-- X on one qubit, and the identity of two qubits (a permutation): both have a short form.
-- >>> squareFactorEmittable [[0, 1], [1, 0]]
-- True
-- >>> squareFactorEmittable [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
-- True

-- The Hadamard of two qubits is neither: it takes the general return gate.
-- >>> squareFactorEmittable [[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]]
-- False

-- | A block that holds temporaries beside its loans has a rectangular block
-- factor B : H_loan -> H_block (the site definition's clause (3), Drop.Lang.Criterion.loanResultS).
-- When B is a product B' (x) g~ of a square factor on the loans and a
-- certificate on the temporaries -- the shape under which the emitted gate
-- is B'^dagger on the loans, then the reclaiming reflection on the
-- temporaries, the two acting on disjoint registers --
-- this returns @Just (B', g~)@, both exact, B' a @dLoan x dLoan@ matrix and
-- g~ a vector of length @dTemp@, each indexed in the drop's order restricted
-- to its kind. 'Nothing' when B is not a product B' (x) g (a site still
-- safe by the site definition's clause (3), returned by the general return
-- gate instead) or when the block is not mixed at all. The rows of B are indexed in the drop's
-- order over all its registers (Drop.Lang.State.reindexABOrd); @kinds@ lists,
-- in that order, each register's dimension and whether it is a loan.
splitMixedFactor :: [(Int, Bool)] -> Matrix Cyclo -> Maybe (Matrix Cyclo, StateV Cyclo)
splitMixedFactor kinds bMat
  | null loanDims || null tempDims = Nothing
  | length bMat /= product dims || any ((/= dLoan) . length) bMat = Nothing
  | otherwise = case factorSplit [dTemp, dLoan * dLoan] [0] flat of
      Nothing -> Nothing
      Just (gT, bFlat) ->
        -- impossible: bFlat has dLoan * dLoan entries (the loan factor of the split), lo and li are below dLoan
        Just ( [ [ bFlat !! (lo * dLoan + li) | li <- [0 .. dLoan - 1] ] | lo <- [0 .. dLoan - 1] ]
             , gT )
  where
    dims     = map fst kinds
    loanDims = [ d | (d, True) <- kinds ]
    tempDims = [ d | (d, False) <- kinds ]
    dLoan    = product loanDims
    dTemp    = product tempDims
    -- the block's row whose loan registers carry the digits of @lo@ and
    -- whose temporaries carry the digits of @to@, interleaved as the drop
    -- orders them
    rowOf to lo = levelsToIdx dims (interleave kinds (idxToLevels loanDims lo) (idxToLevels tempDims to))
    interleave [] _ _ = []
    interleave ((_, True) : ks) (l : ls) ts = l : interleave ks ls ts
    interleave ((_, False) : ks) ls (t : ts) = t : interleave ks ls ts
    -- impossible: idxToLevels gives one digit per loan and one per temporary, exactly the counts kinds asks for
    interleave _ _ _ = error "splitMixedFactor: digit count mismatch"
    -- B as a vector over [temporaries out, (loans out, loans in)], the
    -- grouping on which the product form is a rank-one condition
    -- impossible: rowOf is a row of bMat (its length is product dims) and li is below the row length dLoan, both checked above
    flat = [ bMat !! rowOf to lo !! li
           | to <- [0 .. dTemp - 1], lo <- [0 .. dLoan - 1], li <- [0 .. dLoan - 1] ]

-- B = identity on the loan beside the temporary state |0>: B' = I, g = |0>.
-- >>> fmap (\(b, g) -> (map (map showAmp) b, map showAmp g)) (splitMixedFactor [(2, True), (2, False)] [[1, 0], [0, 0], [0, 1], [0, 0]])
-- Just ([["1","0"],["0","1"]],["1","0"])

-- No temporary beside the loan, or no loan beside the temporary: there is nothing to split.
-- >>> splitMixedFactor [(2, True)] [[1, 0], [0, 1]]
-- Nothing
-- >>> splitMixedFactor [(2, False)] [[1], [0]]
-- Nothing

-- A factor that is not a product of a loan factor and a temporary certificate does not split.
-- >>> splitMixedFactor [(2, True), (2, False)] [[1, 0], [0, 1], [0, 1], [1, 0]]
-- Nothing

-- The reclaiming gate, over the complex numbers -------------------------------

-- | @gTildeAndW psi g@ is the phase-adjusted representative g~ of g (the
-- tie-break of the reclaiming proposition at <psi,g> = 0: align to the phase of g's own
-- first nonzero coordinate rather than leaving g~ undefined), the difference
-- w = psi - g~, and its squared norm -- factored out of 'reflectionR' so
-- that the general k-qubit reclaiming-reflection circuit (below) reflects
-- through the exact same w, by the exact same tie-break, as the matrix
-- 'reflectionR' itself computes; neither duplicates the other's logic.
gTildeAndW :: [Complex Double] -> [Complex Double]
           -> ([Complex Double], [Complex Double], Double)
gTildeAndW psi g =
  let ip = innerProd psi g
      gTilde
        | ip /= 0 = map (* cis (negate (phase ip))) g
        | otherwise =
            let j = case [ i | (i, a) <- zip [0 ..] g, a /= 0 ] of
                      (i : _) -> i
                      -- refusal: g is the zero vector; every caller passes a unit vector
                      []      -> error "gTildeAndW: g is the zero vector"
            -- impossible: j indexes a nonzero entry of g, found by zip over g
            in map (* cis (negate (phase (g !! j)))) g
      rawW = zipWith (-) psi gTilde
      -- For a basis allocation, avoid cancellation in 1 - <psi,g~>.
      w = case [j | (j, a) <- zip [0 ..] psi, a /= 0] of
            -- impossible: psi and g have the same length, and j indexes a nonzero entry of psi
            [j] | magnitude (psi !! j) == 1 ->
              -- impossible: psi and g have the same length, and j indexes a nonzero entry of psi
              let c = realPart (conjugate (psi !! j) * (gTilde !! j))
                  tailNorm2 = sum [magnitude a ** 2 | (i, a) <- zip [0 ..] gTilde, i /= j]
                  -- impossible: psi and g have the same length, and j indexes a nonzero entry of psi
                  first = (psi !! j) * (tailNorm2 / (1 + c) :+ 0)
              in [if i == j then first else a | (i, a) <- zip [0 ..] rawW]
            _ -> rawW
      wnorm2 = sum [ (magnitude x) ** 2 | x <- w ]
  in (gTilde, w, wnorm2)
  where
    innerProd a b = sum (zipWith (\x y -> conjugate x * y) a b)

-- psi = |0>, g = |1>: orthogonal, so g keeps its own first nonzero phase, and w = psi - g~ has squared norm 2.
-- >>> gTildeAndW [1, 0] [0, 1]
-- ([0.0 :+ 0.0,1.0 :+ 0.0],[1.0 :+ 0.0,(-1.0) :+ 0.0],2.0)

-- g already equal to psi: w is zero.
-- >>> gTildeAndW [1, 0] [1, 0]
-- ([1.0 :+ 0.0,0.0 :+ 0.0],[0.0 :+ 0.0,0.0 :+ 0.0],0.0)

-- | @reflectionR psi g@ is the unitary R^psi of the reclaiming proposition: the
-- Householder reflection through (a phase-adjusted representative of) g and
-- psi, satisfying R psi = g~ and R g~ = psi, with the tie-break at
-- <psi,g> = 0 stated there. Both vectors are unit vectors of the same
-- dimension; R = I when g is already proportional to psi.
reflectionR :: [Complex Double] -> [Complex Double] -> [[Complex Double]]
reflectionR psi g =
  let (_, w, _) = gTildeAndW psi g
      n = length psi
  in case unitVectorC w of
       Nothing -> [ [ if i == j then 1 else 0 | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
       -- impossible: u has the length n of psi, and i and j are below n
       Just u -> [ [ (if i == j then 1 else 0) - 2 * (u !! i) * conjugate (u !! j)
                   | j <- [0 .. n - 1] ]
                 | i <- [0 .. n - 1] ]

-- The reflection that exchanges |0> and |1> is X.
-- >>> map (map (\z -> (round (1000 * realPart z), round (1000 * imagPart z)))) (reflectionR [1, 0] [0, 1])
-- [[(0,0),(1000,0)],[(1000,0),(0,0)]]

-- g proportional to psi: R is the identity.
-- >>> map (map (\z -> (round (1000 * realPart z), round (1000 * imagPart z)))) (reflectionR [1, 0] [1, 0])
-- [[(1000,0),(0,0)],[(0,0),(1000,0)]]

-- R psi = g~: psi = |0>, g = (|0> + |1>) / sqrt 2.
-- >>> map (\z -> (round (1000 * realPart z), round (1000 * imagPart z))) (let r = reflectionR [1, 0] [1 / sqrt 2, 1 / sqrt 2] in [sum (zipWith (*) row [1, 0]) | row <- r])
-- [(707,0),(707,0)]

-- | theta, phi, lambda of OpenQASM 3's U(theta,phi,lambda) so that
-- U(theta,phi,lambda) equals the given 2x2 unitary up to a global phase:
-- U3 = [[cos(t/2), -e^{iL} sin(t/2)], [e^{iP} sin(t/2), e^{i(P+L)} cos(t/2)]].
-- OpenQASM 3's built-in U is exp(i*t/2) times U3.
-- theta = 2*atan2(|c|,|a|) always determines |a| = cos(t/2), |c| = sin(t/2);
-- the phase of a (or, when a ~ 0, of c) is absorbed as the free global
-- phase, then phi and lambda are read off the remaining two entries.
u3OfMatrix :: [[Complex Double]] -> (Double, Double, Double)
u3OfMatrix [[a, b], [c, d]] =
  let theta = 2 * atan2 (magnitude c) (magnitude a)
  in if magnitude a > 0
       then
         let ph = cis (phase a)
             b' = b / ph; c' = c / ph; d' = d / ph
             phi = if magnitude c' > 0 then phase c' else 0
             lam | magnitude b' > 0 = phase (negate b')
                 | magnitude d' > 0 = phase d'
                 | otherwise = 0
         in (theta, phi, lam)
       else
         let ph = cis (phase c)
             b' = b / ph
             lam = phase (negate b')
         in (theta, 0, lam)
-- refusal: not a 2x2 matrix; every caller passes the matrix of a one-qubit gate
u3OfMatrix _ = error "u3OfMatrix: not a 2x2 matrix"

-- >>> u3OfMatrix [[1, 0], [0, 1]]
-- (0.0,0.0,0.0)
-- >>> u3OfMatrix [[0, 1], [1, 0]]
-- (3.141592653589793,0.0,-3.141592653589793)

-- The Hadamard: theta = pi/2, phi = 0, lambda = -pi (up to a global phase).
-- >>> u3OfMatrix (matC [[invSqrt2C, invSqrt2C], [invSqrt2C, -invSqrt2C]])
-- (1.5707963267948966,0.0,-3.141592653589793)

-- Operations and the reflections ----------------------------------------------

-- The general k-qubit reclaiming reflection (k >= 2), the reclaiming proposition's
-- 'reflectionR' realised as a circuit: R = V^dagger . (I - 2|0..0><0..0|) . V,
-- V u = |0..0>, u = w / ||w||, w = psi - g~ exactly as 'gTildeAndW' computes
-- it (shared with 'reflectionR' itself, not re-derived). V^dagger is "prepare
-- u from |0..0>": a real-amplitude recursion (a controlled-Ry, i.e.
-- U(theta,0,0), per prefix pattern per level) that reaches |u| = the
-- entrywise magnitudes of u, then a diagonal phase fixup (multi-controlled
-- p(theta) gates, mirroring 'diagCircuit' below) that turns |u| into u
-- exactly; V is the reverse, adjointed. Built from an internal 'Op'
-- representation (rather than string-level surgery) so the adjoint is
-- structural and a test can simulate the operations before rendering them.

-- | One gate of the circuit fragment this section emits: a one-qubit
-- U(theta,phi,lambda), a one-qubit phase p(theta), or x/z, each with its
-- uniform controls as (qubit, required bit) pairs -- the same convention
-- 'modifiersFor' below already reads (bit 1 = ctrl, bit 0 = negctrl) -- and
-- its target qubit.
data Op
  = OpU Double Double Double [(Int, Int)] Int
  | OpP Double [(Int, Int)] Int
  | OpX [(Int, Int)] Int
  | OpZ [(Int, Int)] Int
  deriving (Eq, Show)

-- A CNOT is an X on qubit 1 controlled to read 1 on qubit 0; a U carries three angles.
-- >>> OpX [(0, 1)] 1
-- OpX [(0,1)] 1
-- >>> OpU 0 0 0 [] 0
-- OpU 0.0 0.0 0.0 [] 0
-- >>> [OpP 0.5 [(0, 1)] 1, OpZ [(0, 0)] 1]
-- [OpP 0.5 [(0,1)] 1,OpZ [(0,0)] 1]

-- | The adjoint of a single ideal 'Op':
-- U(theta,phi,lambda)^dagger = U(-theta,-lambda,-phi) (controls unchanged);
-- p(theta)^dagger = p(-theta); x and z are self-adjoint. The adjoint of a
-- whole circuit (a list of operations, time order first-to-last) is the reverse
-- of the list with each operation replaced by 'adjointOp' -- ordinary circuit
-- adjoint, not specific to this construction.
adjointOp :: Op -> Op
adjointOp (OpU t p l c q) = OpU (negate t) (negate l) (negate p) c q
adjointOp (OpP t c q)     = OpP (negate t) c q
adjointOp (OpX c q)       = OpX c q
adjointOp (OpZ c q)       = OpZ c q

-- >>> adjointOp (OpU 1 2 3 [] 0)
-- OpU (-1.0) (-3.0) (-2.0) [] 0
-- >>> adjointOp (OpP 0.5 [(0, 1)] 1)
-- OpP (-0.5) [(0,1)] 1
-- >>> adjointOp (OpX [(0, 1)] 1)
-- OpX [(0,1)] 1

-- | Render Euler U3 = P(phi) RY(theta) P(lambda). QASM3's built-in U
-- adds exp(i*theta/2), which is a relative phase under quantum control.
-- Controlled rotations therefore use the standard p/ry gates directly.
-- The magnitude tree has phi=lambda=0, so each node remains one ry gate.
-- An uncontrolled U differs only by an overall phase, which cancels in a
-- preparation followed by its adjoint and does not change a local return.
renderOp :: Op -> [String]
renderOp (OpU t p l c q)
  | null c =
      [ "U(" ++ angleLabel t ++ ", " ++ angleLabel p ++ ", " ++ angleLabel l ++ ") "
        ++ qArg q ++ ";" ]
  | otherwise = [ angleGate "p" l | l /= 0 ]
             ++ [ angleGate "ry" t | t /= 0 ]
             ++ [ angleGate "p" p | p /= 0 ]
  where
    angleGate name a = modifiersFor c ++ name ++ "(" ++ angleLabel a ++ ") "
                   ++ qArgs (map fst c ++ [q]) ++ ";"
renderOp (OpP t c q) =
  [ modifiersFor c ++ "p(" ++ angleLabel t ++ ") " ++ qArgs (map fst c ++ [q]) ++ ";" ]
renderOp (OpX c q) = [ modifiersFor c ++ "x " ++ qArgs (map fst c ++ [q]) ++ ";" ]
renderOp (OpZ c q) = [ modifiersFor c ++ "z " ++ qArgs (map fst c ++ [q]) ++ ";" ]

-- >>> renderOp (OpX [] 0)
-- ["x q[0];"]
-- >>> renderOp (OpX [(0, 1)] 1)
-- ["ctrl @ x q[0], q[1];"]
-- >>> renderOp (OpZ [(0, 0)] 1)
-- ["negctrl @ z q[0], q[1];"]
-- >>> renderOp (OpP (pi / 2) [(0, 1)] 1)
-- ["ctrl @ p(pi/2) q[0], q[1];"]

-- Uncontrolled, a U stays a U; controlled, it is spelled p; ry; p.
-- >>> renderOp (OpU (pi / 2) 0 pi [] 0)
-- ["U(pi/2, 0, pi) q[0];"]
-- >>> renderOp (OpU 1 0 0 [(0, 1)] 1)
-- ["ctrl @ ry(1.00000000000000000) q[0], q[1];"]

-- | 'Op' as a (targets, dense matrix) pair usable with
-- 'Drop.Lang.State.applyGate': targets are the controls (in order) followed by
-- the actual target qubit, matching 'renderOp's own qArgs order, and the
-- dense matrix is 'gateMat' spread over 2^(#controls) copies -- identity
-- outside the pattern the controls require, 'gateMat' inside it -- by the
-- same MSB-first bit convention 'bitsOfIndex' uses everywhere else in this
-- file. This is the intended Euler matrix: an uncontrolled printed QASM3 U
-- can differ by the overall phase described above. Printed-text checks use
-- the QASM3 convention independently, including its controlled phases.
opDense :: Op -> ([Int], [[Complex Double]])
opDense (OpU t p l c q) = (map fst c ++ [q], controlledMat (map snd c) (u3Mat t p l))
opDense (OpP t c q)     = (map fst c ++ [q], controlledMat (map snd c) (pMat t))
opDense (OpX c q)       = (map fst c ++ [q], controlledMat (map snd c) xMat)
opDense (OpZ c q)       = (map fst c ++ [q], controlledMat (map snd c) zMat)

-- >>> fst (opDense (OpX [] 0))
-- [0]
-- >>> fst (opDense (OpX [(0, 1)] 1))
-- [0,1]

-- A controlled X is the CNOT matrix (real parts, rounded).
-- >>> map (map (round . realPart)) (snd (opDense (OpX [(0, 1)] 1)))
-- [[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]]

u3Mat :: Double -> Double -> Double -> [[Complex Double]]
u3Mat t p l =
  [ [ cos (t / 2) :+ 0, negate (cis l) * (sin (t / 2) :+ 0) ]
  , [ cis p * (sin (t / 2) :+ 0), cis (p + l) * (cos (t / 2) :+ 0) ] ]

-- >>> map (map (\z -> (round (realPart z), round (imagPart z)))) (u3Mat 0 0 0)
-- [[(1,0),(0,0)],[(0,0),(1,0)]]

-- U(pi, 0, 0) is the rotation by a half turn about y (rounded).
-- >>> map (map (\z -> (round (1000 * realPart z), round (1000 * imagPart z)))) (u3Mat pi 0 0)
-- [[(0,0),(-1000,0)],[(1000,0),(0,0)]]

pMat :: Double -> [[Complex Double]]
pMat t = [ [1, 0], [0, cis t] ]

-- >>> pMat 0
-- [[1.0 :+ 0.0,0.0 :+ 0.0],[0.0 :+ 0.0,1.0 :+ 0.0]]
-- >>> map (map (\z -> (round (1000 * realPart z), round (1000 * imagPart z)))) (pMat pi)
-- [[(1000,0),(0,0)],[(0,0),(-1000,0)]]

xMat, zMat :: [[Complex Double]]
xMat = [ [0, 1], [1, 0] ]

-- >>> xMat
-- [[0.0 :+ 0.0,1.0 :+ 0.0],[1.0 :+ 0.0,0.0 :+ 0.0]]

zMat = [ [1, 0], [0, -1] ]

-- >>> map (map realPart) zMat
-- [[1.0,0.0],[0.0,-1.0]]

-- | 'gateMat' (2x2) uniformly controlled by 'ctrlVals' (the required bit of
-- each control, MSB-first, matching 'bitsOfIndex'): the (length ctrlVals +
-- 1)-qubit matrix that is 'gateMat' on the target when every control reads
-- its required bit, and the identity otherwise.
controlledMat :: [Int] -> [[Complex Double]] -> [[Complex Double]]
controlledMat ctrlVals gateMat =
  [ [ entry i j | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
  where
    m = length ctrlVals
    n = 2 ^ (m + 1)
    entry i j =
      let bitsI = bitsOfIndex (m + 1) i
          bitsJ = bitsOfIndex (m + 1) j
          -- impossible: bitsOfIndex (m + 1) has m + 1 bits, so index m is in range
          (ctrlI, tI) = (take m bitsI, bitsI !! m)
          -- impossible: bitsOfIndex (m + 1) has m + 1 bits, so index m is in range
          (ctrlJ, tJ) = (take m bitsJ, bitsJ !! m)
      in if ctrlI == ctrlVals && ctrlJ == ctrlVals
           -- impossible: tI and tJ are bits, and gateMat is 2 x 2
           then gateMat !! tI !! tJ
           else if i == j then 1 else 0

-- No control: the matrix itself.
-- >>> controlledMat [] xMat
-- [[0.0 :+ 0.0,1.0 :+ 0.0],[1.0 :+ 0.0,0.0 :+ 0.0]]

-- One control that reads 1: the CNOT.
-- >>> map (map (round . realPart)) (controlledMat [1] xMat)
-- [[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]]

-- One control that reads 0: X fires when the control is |0>.
-- >>> map (map (round . realPart)) (controlledMat [0] xMat)
-- [[0,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,1]]

-- | The error share one angle of a return on k qubits may use; an angle below
-- it is pruned as the identity. A return on k qubits emits at most 2^k - 1 reflections (the last column is
-- aligned once every other target is placed) and one diagonal; each reflection
-- costs at most 2 (2^(k+1) - 1) shares and the diagonal one share, so this
-- denominator keeps all of them two shares below 1e-9 in exact arithmetic.
-- At k = 1 it is 1e-9/9.
pruneShare :: Int -> Double
pruneShare k = 1e-9 / fromIntegral ((2 ^ k - 1) * (2 ^ (k + 2) - 2) + 3 :: Integer)

-- >>> pruneShare 1
-- 1.1111111111111112e-10
-- >>> map pruneShare [2, 3]
-- [2.2222222222222225e-11,4.694835680751174e-12]

-- | The real-amplitude magnitude tree: one OpU theta 0 0 per (level, prefix).
-- Internally this is Ry(theta); under controls it prints as ry(theta),
-- with theta = 2*atan2(r1,r0), r0/r1 the norms of the prefix's two
-- sub-vectors of 'mags' at that level's qubit -- the standard recursive
-- construction preparing the vector of magnitudes |u_0|,...,|u_{2^k-1}| from
-- |0..0> on 'qs' (MSB-first, the file's own convention -- 'bitsOfIndex').
-- 'theta = 2*atan2(0,0) = 0' at a prefix whose sub-vector is entirely zero
-- (the parent branch carried no mass there), so that node -- and, since its
-- own children see the same all-zero restriction, every node below it -- is
-- pruned by the identity check with no separate pruning logic.
-- Pruning estimates error on the prepared axis, not the operator norm
-- of each omitted gate. Comparing the full reflections also requires
-- the axis perturbation and numerical angle errors.
prepMagTreeOps :: [Int] -> [Double] -> [Op]
prepMagTreeOps qs mags =
  [ OpU theta 0 0 controls target
  | j <- [0 .. k - 1]
  , prefix <- sequence (replicate j [0, 1])
  , let idxs      = [ i | i <- [0 .. n - 1], take j (bitsOfIndex k i) == prefix ]
  -- impossible: j is below k and bitsOfIndex k has k bits
  , let idxs0     = [ i | i <- idxs, bitsOfIndex k i !! j == 0 ]
  -- impossible: j is below k and bitsOfIndex k has k bits
  , let idxs1     = [ i | i <- idxs, bitsOfIndex k i !! j == 1 ]
  -- impossible: i is below 2^k and mags has 2^k entries, one per basis state of the k qubits
  , let r0        = sqrt (sum [ (mags !! i) ** 2 | i <- idxs0 ])
  -- impossible: i is below 2^k and mags has 2^k entries, one per basis state of the k qubits
  , let r1        = sqrt (sum [ (mags !! i) ** 2 | i <- idxs1 ])
  , let theta     = 2 * atan2 r1 r0
  -- impossible: t is below j, which is below k: prefix has j bits and qs has k qubits
  , let controls  = [ (qs !! t, prefix !! t) | t <- [0 .. j - 1] ]
  -- impossible: j is below k = length qs
  , let target    = qs !! j
  , abs theta / 2 > pruneShare k
  ]
  where
    k = length qs
    n = 2 ^ k

-- One qubit, magnitudes (0.6, 0.8): one rotation by 2 atan2 0.8 0.6.
-- >>> prepMagTreeOps [0] [0.6, 0.8]
-- [OpU 1.8545904360032246 0.0 0.0 [] 0]

-- Two equal halves on two qubits: three rotations, the last two controlled by the first qubit.
-- >>> prepMagTreeOps [0, 1] [0.5, 0.5, 0.5, 0.5]
-- [OpU 1.5707963267948966 0.0 0.0 [] 0,OpU 1.5707963267948966 0.0 0.0 [(0,0)] 1,OpU 1.5707963267948966 0.0 0.0 [(0,1)] 1]

-- All the weight on one state: every angle is zero and is pruned.
-- >>> prepMagTreeOps [0] [1, 0]
-- []

-- | The phase fixup: for every basis index i with u_i not (numerically) zero
-- and phase(u_i) not (numerically) 0, a multi-controlled p(phase(u_i)) on a
-- fixed swing qubit (the last one, LSB) -- exactly 'diagCircuit's own
-- pattern (X-conjugate the swing qubit when its own bit of i is 0, so the
-- control pattern on the remaining qubits alone selects i), specialised to a
-- diagonal read off a numeric unit vector u instead of an exact Cyclo
-- matrix. Before numerical pruning, the magnitude and phase constructions
-- prepare u: u_i = |u_i| * e^{i phase(u_i)}. The emitted angles use Double.
prepPhaseOps :: [Int] -> [Complex Double] -> [Op]
prepPhaseOps qs u = concat
  [ pre ++ [ OpP theta ctrlBits swing ] ++ pre
  | i <- [0 .. n - 1]
  -- impossible: i is below 2^k and u has 2^k entries
  , 2 * magnitude (u !! i) > pruneShare k
  -- impossible: i is below 2^k and u has 2^k entries
  , let theta = phase (u !! i)
  -- impossible: i is below 2^k and u has 2^k entries
  , abs theta * magnitude (u !! i) > pruneShare k
  , let bits      = bitsOfIndex k i
  -- impossible: bits has k entries and tPos = k - 1; a returned block has at least one qubit
  , let tBit      = bits !! tPos
  -- impossible: p is at most k - 2, below the k bits and k qubits
  , let ctrlBits  = [ (qs !! p, bits !! p) | p <- [0 .. k - 2] ]
  -- impossible: tPos = k - 1 is below k = length qs
  , let swing     = qs !! tPos
  , let pre       = [ OpX [] swing | tBit == 0 ]
  ]
  where
    k = length qs
    n = 2 ^ k
    tPos = k - 1

-- A real vector needs no phase fix.
-- >>> prepPhaseOps [0] [0.6 :+ 0, 0.8 :+ 0]
-- []

-- A phase of a quarter turn on the second entry: one p on the qubit (its bit is 1, so no x around it).
-- >>> prepPhaseOps [0] [0.6 :+ 0, 0 :+ 0.8]
-- [OpP 1.5707963267948966 [] 0]

-- | I - 2|0..0><0..0| on 'qs' (any k >= 1; at k = 1 the z has no controls): x the last qubit, a Z on the last
-- qubit negated-controlled by every other qubit (so it fires, after the x,
-- exactly when every qubit's ORIGINAL value was 0), x the last qubit again.
-- By hand: after the first x, the last qubit reads 1 exactly when its
-- original value was 0; the negctrl block then gives -1 exactly when every
-- OTHER qubit is 0 and the (x-ed) last qubit is 1, i.e. exactly at |0..0>,
-- +1 everywhere else (either some other qubit is nonzero, so the negctrl
-- block does not fire at all, or the last qubit's original value was 1, so
-- after the x it reads 0 and Z gives +1); the closing x restores every
-- qubit's value.
phaseFlipOps :: [Int] -> [Op]
phaseFlipOps qs = [ OpX [] lastQ, OpZ [ (q, 0) | q <- init qs ] lastQ, OpX [] lastQ ]
  where lastQ = last qs

-- >>> phaseFlipOps [0]
-- [OpX [] 0,OpZ [] 0,OpX [] 0]
-- >>> phaseFlipOps [0, 1]
-- [OpX [] 1,OpZ [(0,0)] 1,OpX [] 1]

-- | The general k-qubit (k >= 2) reclaiming reflection, the reclaiming proposition's
-- 'reflectionR psi g' realised as a circuit on 'qs' (MSB-first): V, then the
-- phase flip, then V^dagger, so that (as operators, last-applied leftmost)
-- V^dagger . (I - 2|0..0><0..0|) . V = 'reflectionR psi g' for the ideal
-- construction before numerical pruning and angle error. No phase fixing
-- is needed there: the magnitude and phase constructions prepare u including
-- its global phase, and V := (that circuit)^dagger takes u to |0..0>.
-- Line count: V^dagger's magnitude tree has 2^k - 1 nodes and its
-- phase fixup at most 2^k lines (no global phase is factored out, so every
-- index may carry one), V mirrors both, plus the 3-line flip: at most
-- 2^(k+2) + 1 controlled gates, and in the printed text up to 6*2^k + 1
-- lines since a phase line whose swing bit is 0 is spelled x; p; x. Fewer
-- once a node or a phase line is pruned as the identity ('pruneShare').
emitGeneralReflectionOps :: [Int] -> [Complex Double] -> [Complex Double] -> [Op]
emitGeneralReflectionOps qs psi g =
  let (_, w, _) = gTildeAndW psi g
      u = fromMaybe (replicate (length w) 0) (unitVectorC w)
      prepU = prepMagTreeOps qs (map magnitude u) ++ prepPhaseOps qs u  -- = V^dagger
      vOps  = map adjointOp (reverse prepU)                              -- = V
  in vOps ++ phaseFlipOps qs ++ prepU

-- The reflection exchanging |00> and the uniform vector: three layers, the preparation of the axis, the flip, the preparation again.
-- >>> length (emitGeneralReflectionOps [0, 1] [1, 0, 0, 0] [0.5, 0.5, 0.5, 0.5])
-- 19
-- >>> take 2 (emitGeneralReflectionOps [0, 1] [1, 0, 0, 0] [0.5, 0.5, 0.5, 0.5])
-- [OpP (-3.141592653589793) [(0,1)] 1,OpX [] 1]

-- | The short form for a two-support axis: when u = w / ||w||
-- (the same u 'emitGeneralReflectionOps' would feed to its magnitude/phase
-- tree) is nonzero on exactly two basis indices a /= b, the whole tree
-- collapses to: align a and b onto a single differing qubit m by CNOTs from
-- m to every other position where they differ (mirroring
-- 'transpositionLines'), an UNCONTROLLED one-qubit rotation on m carrying
-- the two surviving amplitudes to (0, 1), the phase flip I - 2|p,1><p,1|
-- as ONE z on m controlled by the pattern p the alignment leaves on the
-- other qubits (no X conjugation: aiming at |1> rather than |0> is what
-- makes the flip a single line), then the rotation's adjoint and the same
-- CNOTs again. The Bell pair is exactly five lines: cx; U; negctrl @ z;
-- U^dagger; cx.
--
-- The rotation carries no controls on the other qubits, unlike a first
-- guess from "reflect only on the p branch" might suggest: on every OTHER
-- pattern q /= p, the flip step between the rotation and its adjoint is the
-- identity regardless of qubit m's value (the flip's own controls already
-- select p), so rotation-then-identity-then-adjoint is just A . A^-1 = I on
-- every q /= p branch whether or not the rotation itself is also
-- p-controlled; only the p branch is meant to do work, and there the
-- uncontrolled rotation conjugates the flip exactly as a controlled one
-- would: the rotation carries no control on the second qubit. That is
-- checked numerically against 'reflectionR' by 'generalReflectionChecks' in the
-- test suite, entrywise, with no phase fit -- not merely argued here.
--
-- Nothing when u's support is not exactly two indices (the caller falls
-- back to 'emitGeneralReflectionOps').
emitTwoSupportReflectionOps :: [Int] -> [Complex Double] -> [Complex Double] -> Maybe [Op]
emitTwoSupportReflectionOps qs psi g =
  let (_, w, wnorm2) = gTildeAndW psi g
  in if wnorm2 < 1e-18
       then Nothing
       else twoSupportAxisOps qs (fromMaybe (replicate (length w) 0) (unitVectorC w))
                               [ i | (i, x) <- zip [0 :: Int ..] w, x /= 0 ]

-- The Bell pair is the paper's case: exactly five lines, cx; U; negctrl @ z; U; cx.
-- >>> fmap (concatMap renderOp) (emitTwoSupportReflectionOps [0, 1] [1, 0, 0, 0] [1 / sqrt 2 :+ 0, 0, 0, 1 / sqrt 2 :+ 0])
-- Just ["ctrl @ x q[0], q[1];","U(pi/4, 0, -pi) q[0];","negctrl @ z q[1], q[0];","U(-pi/4, pi, 0) q[0];","ctrl @ x q[0], q[1];"]

-- An axis with four nonzero entries is not a two-support axis.
-- >>> fmap length (emitTwoSupportReflectionOps [0, 1] [1, 0, 0, 0] [0.5, 0.5, 0.5, 0.5])
-- Nothing

-- g equal to psi: the axis is zero and there is nothing to reflect.
-- >>> fmap length (emitTwoSupportReflectionOps [0, 1] [1, 0, 0, 0] [1, 0, 0, 0])
-- Nothing

-- | The short form for a GIVEN unit axis u with the given support: the body
-- of 'emitTwoSupportReflectionOps' after its axis line, shared with the
-- return gate below. Nothing unless the support has exactly two indices.
twoSupportAxisOps :: [Int] -> [Complex Double] -> [Int] -> Maybe [Op]
twoSupportAxisOps qs u support =
            case support of
              [a, b] ->
                let k = length qs
                    bitsA = bitsOfIndex k a
                    bitsB = bitsOfIndex k b
                    -- impossible: i is below k and bitsA, bitsB have k bits
                    diffIdx = [ i | i <- [0 .. k - 1], bitsA !! i /= bitsB !! i ]
                in case diffIdx of
                     [] -> Nothing  -- a == b: cannot happen, support indices are distinct
                     (m : _) ->
                       -- impossible: m is one of diffIdx, below k
                       let zeroIdx = if bitsA !! m == 0 then a else b
                           oneIdx  = if zeroIdx == a then b else a
                           -- impossible: zeroIdx and oneIdx are the support indices, below 2^k = length u
                           alpha   = u !! zeroIdx
                           -- impossible: zeroIdx and oneIdx are the support indices, below 2^k = length u
                           beta    = u !! oneIdx
                           others  = [ i | i <- [0 .. k - 1], i /= m ]
                           zBits   = bitsOfIndex k zeroIdx
                           -- impossible: i is below k: qs has k qubits and zBits has k bits
                           pattern = [ (qs !! i, zBits !! i) | i <- others ]
                           -- impossible: m is below k = length qs
                           alignOps = [ OpX [(qs !! m, 1)] (qs !! i) | i <- diffIdx, i /= m ]
                           -- rows orthogonal; u3OfMatrix normalizes, so the emitted gate reflects through the normalized truncation; (alpha, beta) |-> (0, 1)
                           mMat = [ [negate beta, alpha]
                                  , [conjugate alpha, conjugate beta] ]
                           (theta, phi, lam) = u3OfMatrix mMat
                           -- impossible: m is below k = length qs
                           rotOp = OpU theta phi lam [] (qs !! m)
                           -- impossible: m is below k = length qs
                           flipOps = [ OpZ pattern (qs !! m) ]
                           undoAlign = reverse (map adjointOp alignOps)
                       in Just (alignOps ++ [rotOp] ++ flipOps ++ [adjointOp rotOp] ++ undoAlign)
              _ -> Nothing

-- The axis (|00> - |11>) / sqrt 2 has the support 0 and 3.
-- >>> fmap length (twoSupportAxisOps [0, 1] [1 / sqrt 2 :+ 0, 0, 0, (-1) / sqrt 2 :+ 0] [0, 3])
-- Just 5

-- A support of one index, or of three, is not a two-support axis.
-- >>> fmap length (twoSupportAxisOps [0, 1] [1, 0, 0, 0] [0])
-- Nothing
-- >>> fmap length (twoSupportAxisOps [0, 1] [1, 0, 0, 0] [0, 1, 2])
-- Nothing

-- The return gate at a loan site ----------------------------------------------

-- The return gate at a safe site holding loans: any
-- isometric block factor B : H_loan -> H_block is undone by a T with T B = J,
-- built as at most m = dim H_loan reflections and one diagonal. With the unit
-- columns b_l = B e_l and the block basis index j_l of J e_l (the loans
-- unchanged beside the temporaries' allocation state, in the drop's order),
-- step l reflects x_l = H_{l-1} ... H_0 b_l onto c_l e_{j_l}, choosing
-- the opposite phase to x_l[j_l] to avoid cancellation in the axis
-- x_l - c_l e_{j_l}. An already aligned column needs no reflection; the diagonal then
-- multiplies e_{j_l} by conj c_l. Each reflection fixes the earlier targets,
-- so T b_l = e_{j_l} for every l (prop:loanreturn). With m = 1 and
-- no loans it is the reclaiming reflection of 'emitReclaim' followed by one
-- phase (the diagonal), which that path omits since it only needs the ray.

-- | The reflection I - 2 u u^dagger about a GIVEN unit axis u:
-- 'emitGeneralReflectionOps' with its axis supplied instead of computed.
emitAxisReflectionOps :: [Int] -> [Complex Double] -> [Op]
emitAxisReflectionOps qs u =
  let prepU = prepMagTreeOps qs (map magnitude u) ++ prepPhaseOps qs u  -- = V^dagger
      vOps  = map adjointOp (reverse prepU)                             -- = V
  in vOps ++ phaseFlipOps qs ++ prepU

-- >>> length (emitAxisReflectionOps [0, 1] [0.5, 0.5, 0.5, 0.5])
-- 9
-- >>> length (emitAxisReflectionOps [0] [1 / sqrt 2 :+ 0, 1 / sqrt 2 :+ 0])
-- 5

-- | The axes w_l and phases c_l of the construction, and the product
-- H_{m-1} ... H_0 of its reflections, from the unit columns of B and the
-- block indices of J's columns.
frameReturnSteps :: [[Complex Double]] -> [Int]
                 -> ([[Complex Double]], [Complex Double], [[Complex Double]])
frameReturnSteps bCols jIdx = go identityN (zip bCols jIdx) [] [] []
  where
    n = firstLength bCols
    identityN = [ [ if i == j then 1 else 0 | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
    go g [] ws cs _ = (reverse ws, reverse cs, g)
    go g ((b, ji) : rest) ws cs placed =
      -- Exact orthogonality makes these coordinates zero. Remove roundoff
      -- there so this reflection fixes all previously placed columns.
      let x = [ if i `elem` placed then 0 else sum (zipWith (*) row b)
              | (i, row) <- zip [0 ..] g ]
          -- impossible: ji is below n: emitFrameReturnOps and placementIndex only supply block indices below n
          z = x !! ji
          aligned = and [ xi == 0 | (i, xi) <- zip [0 ..] x, i /= ji ]
          unitPhase = if z == 0 then 1 else z / (magnitude z :+ 0)
          c = if aligned || z == 0 then unitPhase else negate unitPhase
          r = sqrt (sum [ magnitude xi ** 2 | xi <- x ])
          w = if aligned then replicate n 0
              else [ if i == ji then xi - (r :+ 0) * c else xi
                   | (i, xi) <- zip [0 ..] x ]
      in go (matMulC (householderMat w) g) rest (w : ws) (c : cs) (ji : placed)
    householderMat w =
      let nn = sum [ magnitude a ** 2 | a <- w ]
      in if nn < 1e-24 then identityN
         -- impossible: w has n entries and i, j are below n
         else [ [ (if i == j then 1 else 0) - 2 * (w !! i) * conjugate (w !! j) / (nn :+ 0)
                | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
    -- impossible: a and b are n x n matrices and i, j, l are below n
    matMulC a b = [ [ sum [ (a !! i !! l) * (b !! l !! j) | l <- [0 .. n - 1] ]
                    | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]

-- B = X on one qubit: its columns are |1> and |0>, to be carried to |0> and |1>. The first needs a reflection; after it the second is in place, so its axis is zero.
-- >>> (\(ws, cs, _) -> (map (map (\z -> (round (1000 * realPart z), round (1000 * imagPart z)))) ws, map (\z -> (round (1000 * realPart z), round (1000 * imagPart z))) cs)) (frameReturnSteps [[0, 1], [1, 0]] [0, 1])
-- ([[(-1000,0),(1000,0)],[(0,0),(0,0)]],[(1000,0),(1000,0)])

-- B = I: both columns are already in place, so both axes are zero.
-- >>> (\(ws, _, _) -> map (map magnitude) ws) (frameReturnSteps [[1, 0], [0, 1]] [0, 1])
-- [[0.0,0.0],[0.0,0.0]]

-- | The return gate as a dense matrix, D . H_{m-1} ... H_0: the matrix the
-- leaf reference 'expectedFinalState' applies.
frameReturnMatrix :: [[Complex Double]] -> [Int] -> [[Complex Double]]
frameReturnMatrix bCols jIdx =
  let (_, cs, h) = frameReturnSteps bCols jIdx
      n = firstLength bCols
      d = [ maybe 1 conjugate (lookup i (zip jIdx cs)) | i <- [0 .. n - 1] ]
  -- impossible: d has n entries and h is n x n
  in [ [ (d !! i) * (h !! i !! j) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]

-- T B = J for B = X, J = I, so T = X (rounded).
-- >>> map (map (\z -> (round (1000 * realPart z), round (1000 * imagPart z)))) (frameReturnMatrix [[0, 1], [1, 0]] [0, 1])
-- [[(0,0),(1000,0)],[(1000,0),(0,0)]]
-- >>> map (map (\z -> (round (1000 * realPart z), round (1000 * imagPart z)))) (frameReturnMatrix [[1, 0], [0, 1]] [0, 1])
-- [[(1000,0),(0,0)],[(0,0),(1000,0)]]

-- | The return gate as operations: one reflection per nonzero axis (the
-- two-support short form when the unit axis has exactly two entries above
-- 1e-12, else the general form), then ONE diagonal, 'prepPhaseOps' on the
-- vector d with d_{j_l} = conj c_l and 1 elsewhere. At most m reflections
-- and one diagonal. Nothing on a malformed B.
emitFrameReturnOps :: [Int] -> [[Complex Double]] -> [Int] -> Maybe [Op]
emitFrameReturnOps qs bCols jIdx
  | null bCols || any ((/= n) . length) bCols || n /= 2 ^ length qs
    || length jIdx /= length bCols || any (\j -> j < 0 || j >= n) jIdx = Nothing
  | otherwise =
      let (ws, cs, _) = frameReturnSteps bCols jIdx
          reflOps = concat
            [ case unitVectorC w of
                Nothing -> []
                Just u  ->
                  let support = [ i | (i, x) <- zip [0 :: Int ..] u, magnitude x > 1e-12 ]
                  in fromMaybe (emitAxisReflectionOps qs u) (twoSupportAxisOps qs u support)
            | w <- ws, not (sum [ magnitude a ** 2 | a <- w ] < 1e-24) ]  -- the same skip as 'householderMat'
          d = [ maybe 1 conjugate (lookup i (zip jIdx cs)) | i <- [0 .. n - 1] ]
      in Just (reflOps ++ prepPhaseOps qs d)
  where
    n = firstLength bCols

-- The return gate for B = X on one qubit: a reflection, the diagonal, and the reflection's partner (3 operations).
-- >>> fmap length (emitFrameReturnOps [0] [[0, 1], [1, 0]] [0, 1])
-- Just 3

-- Nothing on a malformed B: no columns, or columns of the wrong length.
-- >>> emitFrameReturnOps [0] [] []
-- Nothing
-- >>> fmap length (emitFrameReturnOps [0, 1] [[0, 1], [1, 0]] [0, 1])
-- Nothing

-- | The emitted operations, on local qubits 0..k-1, carry every converted
-- column of B to its target within 1e-9 entrywise (Double evaluation, the same
-- tolerance as 'frameReturnInput', which checks only the dense matrix).
emittedReturnResidualOK :: Int -> [Op] -> [[Complex Double]] -> [Int] -> Bool
emittedReturnResidualOK k ops cols jIdx = and
  [ not (isNaN d || isInfinite d || d > 1e-9)
  | (col, j) <- zip cols jIdx
  , (i, y) <- zip [0 :: Int ..] (foldl applyOp col ops)
  , let d = magnitude (y - (if i == j then 1 else 0)) ]
  where
    dims = replicate k 2
    applyOp st op = let (targets, m) = opDense op in applyGate dims m targets st

-- X carries the columns |1> and |0> of B = X to |0> and |1>: within the tolerance.
-- >>> emittedReturnResidualOK 1 [OpX [] 0] [[0, 1], [1, 0]] [0, 1]
-- True

-- The empty circuit does not.
-- >>> emittedReturnResidualOK 1 [] [[0, 1], [1, 0]] [0, 1]
-- False

-- | The block basis index of J e_l: the loans' digits of the loan index l
-- interleaved with the temporaries' digits of their allocation basis index
-- t0, in the drop's order ('splitMixedFactor's row convention). @kinds@
-- lists each register's dimension and whether it is a loan, in that order.
placementIndex :: [(Int, Bool)] -> Int -> Int -> Int
placementIndex kinds t0 l =
  levelsToIdx dims (interleave kinds (idxToLevels loanDims l) (idxToLevels tempDims t0))
  where
    dims     = map fst kinds
    loanDims = [ d | (d, True) <- kinds ]
    tempDims = [ d | (d, False) <- kinds ]
    interleave [] _ _ = []
    interleave ((_, True) : ks) (x : ls) ts = x : interleave ks ls ts
    interleave ((_, False) : ks) ls (t : ts) = t : interleave ks ls ts
    -- impossible: idxToLevels gives one digit per loan and one per temporary, exactly the counts kinds asks for
    interleave _ _ _ = error "Drop.Lang.Compile.Emit.placementIndex: digit count mismatch"

-- One loan and one temporary on |0>: the loan's digit first, in the drop's order.
-- >>> placementIndex [(2, True), (2, False)] 0 1
-- 2

-- The same with the temporary on |1>.
-- >>> placementIndex [(2, True), (2, False)] 1 1
-- 3

-- A temporary alone (no loan, a single placement).
-- >>> placementIndex [(2, False)] 1 0
-- 1

-- | Every angle of an operation is finite.
opIsFinite :: Op -> Bool
opIsFinite (OpU t p l _ _) = all finiteDouble [t, p, l]
opIsFinite (OpP t _ _)     = finiteDouble t
opIsFinite _               = True

-- >>> opIsFinite (OpX [] 0)
-- True
-- >>> opIsFinite (OpU 1 2 3 [] 0)
-- True
-- >>> opIsFinite (OpP (0 / 0) [] 0)
-- False

-- | The input of the return gate at a block: the unit columns of the block
-- factor B and the block index of each target J e_l, from the exact B, the
-- registers' kinds in the drop's order and the temporaries' allocation
-- state. Refuses a B that is not an isometry up to scale, since the
-- construction assumes orthonormal columns: the built gate must carry every
-- converted column of B to its target within 1e-9, entrywise, using the dense
-- frameReturnMatrix. The emitter and leaf reference share these inputs; this
-- residual check does not evaluate the emitted operations.
frameReturnInput :: String -> [(Int, Bool)] -> StateV Cyclo -> Matrix Cyclo
                 -> Either CompileError ([[Complex Double]], [Int])
frameReturnInput label kinds psi b = do
  bN <- normaliseIso label b
  t0 <- maybe (Left (Other ("drop " ++ label ++ ": the temporaries' allocation state is not a basis state")))
              Right (basisIndexOfExact psi)
  -- impossible: l is below the row length of bN, and every row of bN has that length (normaliseIso checks it)
  let cols = [ [ row !! l | row <- bN ] | l <- [0 .. firstLength bN - 1] ]
      jIdx = [ placementIndex kinds t0 l | l <- [0 .. length cols - 1] ]
      t    = frameReturnMatrix cols jIdx
      n    = firstLength cols
      badResidual d = isNaN d || isInfinite d || d > 1e-9
      offTarget col j = or [ badResidual (magnitude (sum (zipWith (*) row col) - (if i == j then 1 else 0)))
                           | (i, row) <- zip [0 .. n - 1] t ]
  if or (zipWith offTarget cols jIdx)
    then Left (Other ("drop " ++ label ++ ": numerical return construction failed its residual check"))
    else Right (cols, jIdx)

-- B = X on a loan of one qubit, no temporaries (psi = [1]): the unit columns of X and where J puts them.
-- >>> fmap (\(cols, jIdx) -> (map (map (\z -> (round (realPart z), round (imagPart z)))) cols, jIdx)) (frameReturnInput "a" [(2, True)] [1] [[0, 1], [1, 0]])
-- Right ([[(0,0),(1,0)],[(1,0),(0,0)]],[0,1])

-- The temporaries' allocation state must be a basis state.
-- >>> either showCompileError show (frameReturnInput "a" [(2, True), (2, False)] [1, 1] [[1, 0], [0, 0], [0, 1], [0, 0]])
-- "drop a: the temporaries' allocation state is not a basis state"

-- A factor that is zero cannot be normalised.
-- >>> either showCompileError show (frameReturnInput "a" [(2, True)] [1] [[0, 0], [0, 0]])
-- "drop a: numerical loan factor cannot be normalized"

-- QASM text helpers -----------------------------------------------------------

-- | The OpenQASM 3 name of one qubit.
qArg :: Int -> String
qArg i = "q[" ++ show i ++ "]"

-- >>> qArg 0
-- "q[0]"
-- >>> qArg 12
-- "q[12]"

-- | A comma-separated list of qubits, in the order given.
qArgs :: [Int] -> String
qArgs = intercalate ", " . map qArg

-- >>> qArgs [0, 2]
-- "q[0], q[2]"
-- >>> qArgs []
-- ""

-- Render the numerical angle without replacing nearby values.
-- Symbolic eighths are used only when the Double equals that value.
angleLabel :: Double -> String
angleLabel t =
  let k  = t / (pi / 8)
      kr = fromIntegral (round k :: Integer) :: Double
  in if t == kr * (pi / 8) then eighths (round kr) else printf "%.17g" t
  where
    -- ki eighths of pi, reduced by gcd.  The sign rides on the numerator.
    eighths :: Integer -> String
    eighths 0  = "0"
    eighths ki =
      let g = gcd (abs ki) 8
          n = ki `quot` g          -- numerator: 1, -1, 3, 2, ...
          d = 8 `quot` g           -- denominator: 1, 2, 4 or 8
          num | n ==  1   = "pi"
              | n == -1   = "-pi"
              | otherwise = show n ++ "*pi"
      in if d == 1 then num else num ++ "/" ++ show d

-- >>> map angleLabel [0, pi, pi / 2, - pi / 4, 3 * pi / 8, 2 * pi]
-- ["0","pi","pi/2","-pi/4","3*pi/8","2*pi"]

-- Close to pi/4 but not equal to it: the decimal is printed, not the name.
-- >>> angleLabel (pi / 4 + 1e-12)
-- "0.78539816339844830"
-- >>> angleLabel 0.1
-- "0.10000000000000000"

-- | The control prefix of a gate: @ctrl @@ @ for a control that must read 1, @negctrl @@ @ for 0.
modifiersFor :: [(Int, Int)] -> String
modifiersFor = concatMap (\(_, b) -> if b == 1 then "ctrl @ " else "negctrl @ ")

-- >>> modifiersFor []
-- ""
-- >>> modifiersFor [(0, 1)]
-- "ctrl @ "
-- >>> modifiersFor [(0, 1), (1, 0)]
-- "ctrl @ negctrl @ "

-- | Lines indented one level, for the body of an if.
indent :: [String] -> [String]
indent = map ("  " ++)

-- >>> indent []
-- []
-- >>> indent ["x q[0];", "h q[1];"]
-- ["  x q[0];","  h q[1];"]


-- Gate recognition and emission: the domain table -----------------------------

-- | A square matrix whose off-diagonal entries are all zero.
isDiagonalMatrix :: Matrix Cyclo -> Bool
isDiagonalMatrix g =
  let n = length g
  -- impossible: the second conjunct runs only when every row has n entries, and i, j are below n
  in all ((== n) . length) g && and [ g !! i !! j == 0 | i <- [0 .. n - 1], j <- [0 .. n - 1], i /= j ]

-- >>> isDiagonalMatrix [[1, 0], [0, -1]]
-- True
-- >>> isDiagonalMatrix [[0, 1], [1, 0]]
-- False

-- A ragged matrix is not diagonal, and is not looked into further.
-- >>> isDiagonalMatrix [[1, 0], [0]]
-- False

-- | The diagonal of a matrix.
diagEntriesOf :: Matrix Cyclo -> [Cyclo]
-- impossible: callers test isDiagonalMatrix first, so g is square and i is below its size
diagEntriesOf g = [ g !! i !! i | i <- [0 .. length g - 1] ]

-- >>> map showAmp (diagEntriesOf [[1, 0], [0, -1]])
-- ["1","-1"]
-- >>> map showAmp (diagEntriesOf (diagOfList [1, 1, 1, zetaC 3]))
-- ["1","1","1","1*z8"]

-- | The images of the basis states when the matrix is a permutation matrix, else Nothing.
permOfMat :: Matrix Cyclo -> Maybe [Int]
permOfMat g
  | all ((== n) . length) g = do
      imgs <- mapM colImg [0 .. n - 1]
      if length (nub imgs) == n then Just imgs else Nothing
  | otherwise = Nothing
  where
    n = length g
    -- impossible: all rows have n entries (checked at the top of permOfMat) and i, j are below n
    colImg j = case [ i | i <- [0 .. n - 1], g !! i !! j /= 0 ] of
      -- impossible: all rows have n entries (checked at the top of permOfMat) and i, j are below n
      [i] | g !! i !! j == 1 -> Just i
      _                      -> Nothing

-- >>> permOfMat [[0, 1], [1, 0]]
-- Just [1,0]
-- >>> permOfMat [[1, 0], [0, 1]]
-- Just [0,1]
-- >>> permOfMat [[1, 0], [0, 2]]
-- Nothing
-- >>> permOfMat [[1, 1], [0, 0]]
-- Nothing
-- >>> permOfMat [[1, 0], [0]]
-- Nothing

-- A loan factor is fixed only up to a nonzero scalar.
scalarPermutation :: Matrix Cyclo -> Maybe [Int]
scalarPermutation m = case filter (/= 0) (concat m) of
  [] -> Nothing
  c : _ -> permOfMat (map (map (/ c)) m)

-- 2 X is a nonzero multiple of a permutation matrix.
-- >>> scalarPermutation [[0, 2], [2, 0]]
-- Just [1,0]
-- >>> scalarPermutation [[0, 0], [0, 0]]
-- Nothing
-- >>> scalarPermutation [[1, 1], [1, -1]]
-- Nothing

-- | A nonzero multiple of the identity matrix.
scalarIdentity :: Matrix Cyclo -> Bool
scalarIdentity m = scalarPermutation m == Just [0 .. length m - 1]

-- >>> scalarIdentity [[3, 0], [0, 3]]
-- True
-- >>> scalarIdentity [[0, 1], [1, 0]]
-- False
-- >>> scalarIdentity [[1, 0], [0, 2]]
-- False

-- | The index of the one nonzero entry of a vector, when there is exactly one.
basisLine :: StateV Cyclo -> Maybe Int
basisLine v = case [i | (i, a) <- zip [0 ..] v, a /= 0] of
  [i] -> Just i
  _ -> Nothing

-- >>> basisLine [0, 5]
-- Just 1
-- >>> basisLine [1, 1]
-- Nothing
-- >>> basisLine [0, 0]
-- Nothing

-- | The inverse of a permutation given as an image list.
inversePerm :: [Int] -> [Int]
inversePerm imgs = [ j | i <- [0 .. length imgs - 1]
                   , j <- take 1 [ k | (k, v) <- zip [0 ..] imgs, v == i ] ]

-- >>> inversePerm [1, 2, 0]
-- [2,0,1]
-- >>> inversePerm [1, 0]
-- [1,0]
-- >>> inversePerm []
-- []

-- | The diagonal matrix with the given entries.
diagOfList :: [Cyclo] -> Matrix Cyclo
-- impossible: i is below n = length xs
diagOfList xs = [ [ if i == j then xs !! i else 0 | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
  where n = length xs

-- >>> map (map showAmp) (diagOfList [1, -1])
-- [["1","0"],["0","-1"]]
-- >>> map (map showAmp) (diagOfList [1, 1, 1, iC])
-- [["1","0","0","0"],["0","1","0","0"],["0","0","1","0"],["0","0","0","1*z4"]]

-- | H, X, Z, S, T, CX, CCX, Swap, Diff, cz by exact match against the
-- gate table (Drop.Lang.Gates), plus cp(theta) for a general
-- diag(1,1,1,z) on two qubits.
recognizeGate :: Matrix Cyclo -> Maybe String
recognizeGate g
  | g == gateH   = Just "h"
  | g == gateX   = Just "x"
  | g == gateZ   = Just "z"
  | g == gateS   = Just "s"
  | g == gateT   = Just "t"
  | g == gateCX  = Just "cx"
  | g == gateCCX = Just "ccx"
  | g == gateSwap = Just "swap"
  | g == gateDiff = Just "diff"
  | g == diagOfList [1, 1, 1, -1] = Just "cz"
  | otherwise = Nothing
  where
    gateH = [[invSqrt2, invSqrt2], [invSqrt2, -invSqrt2]]
    gateX = [[0, 1], [1, 0]]
    gateZ = [[1, 0], [0, -1]]
    gateS = [[1, 0], [0, iC]]
    gateT = [[1, 0], [0, z8]]
    gateCX = [ [1,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]
    gateCCX = [ [ if (i,j) `elem` [(6,7),(7,6)] then 1 else if i==j && i<6 then 1 else 0
                | j <- [0..7 :: Int] ] | i <- [0..7 :: Int] ]
    gateSwap = [ [1,0,0,0], [0,0,1,0], [0,1,0,0], [0,0,0,1] ]
    gateDiff = [ [ (if i == j then -1 else 0) + 1/2 | j <- [0 .. 3 :: Int] ] | i <- [0 .. 3 :: Int] ]
    invSqrt2 = sqrt2C / 2
    sqrt2C = zetaC' 3 + conjC (zetaC' 3)
    iC = zetaC' 2
    z8 = zetaC' 3
    zetaC' k = mkZeta k
    conjC (Cyclo k cs) = mkZetaConj k cs
    mkZeta k = Cyclo k (0 : 1 : replicate (2 ^ (k - 1) - 2) 0)
    mkZetaConj k cs = Cyclo k [ get i | i <- [0 .. n - 1] ]
      -- impossible: cs has 2^(k-1) = n entries (the Cyclo invariant), 0 and n - i, for i below n, are in range
      where n = 2 ^ (k - 1); get 0 = cs !! 0; get i = negate (cs !! (n - i))

-- >>> recognizeGate [[0, 1], [1, 0]]
-- Just "x"
-- >>> recognizeGate [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]]
-- Just "cx"

-- The Hadamard, by exact match: 1/sqrt 2 is zeta_8 + zeta_8^-1, over 2.
-- >>> recognizeGate [[invSqrt2C, invSqrt2C], [invSqrt2C, -invSqrt2C]]
-- Just "h"
-- >>> recognizeGate [[1, 0], [0, zetaC 3]]
-- Just "t"

-- A diagonal gate with the entries 1, 1, 1, -1 is cz.
-- >>> recognizeGate (diagOfList [1, 1, 1, -1])
-- Just "cz"

-- A gate outside the table.
-- >>> recognizeGate [[1, 0], [0, zetaC 4]]
-- Nothing

cpOf :: Matrix Cyclo -> Maybe (Complex Double)
cpOf g
  | length g == 4, isDiagonalMatrix g
  , [d0, d1, d2, d3] <- diagEntriesOf g
  , d0 == 1, d1 == 1, d2 == 1
  = Just (toC d3)
  | otherwise = Nothing

-- The controlled phase diag(1, 1, 1, z): the angle of z is pi/4 for z = omega_8.
-- >>> fmap phase (cpOf (diagOfList [1, 1, 1, zetaC 3]))
-- Just 0.7853981633974483
-- >>> cpOf (diagOfList [1, iC, 1, 1])
-- Nothing
-- >>> cpOf [[1, 0], [0, 1]]
-- Nothing

-- | Cycle decomposition of a permutation image list into transpositions,
-- via the standard identity: a cycle (a0 a1 .. a_{m-1}) (a0->a1->..->a0) is
-- the product T(a_{m-2},a_{m-1}) ; .. ; T(a0,a1) (earliest first in circuit
-- order), each transposition an involution, disjoint cycles commuting.
cyclesOf :: [Int] -> [[Int]]
cyclesOf imgs = filter ((> 1) . length) (go [0 .. length imgs - 1] [])
  where
    go [] found = found
    go (x : xs) found
      | any (x `elem`) found = go xs found
      | otherwise = go xs (chase x [x] : found)
    chase start acc =
      -- impossible: imgs is a permutation of 0..n-1, so every entry indexes it, and acc is not empty
      let nxt = imgs !! last acc
      in if nxt == start then acc else chase start (acc ++ [nxt])

-- >>> cyclesOf [1, 0, 2]
-- [[0,1]]
-- >>> cyclesOf [1, 2, 0]
-- [[0,1,2]]
-- >>> cyclesOf [0, 1, 2]
-- []

cycleToTranspositions :: [Int] -> [(Int, Int)]
-- impossible: i runs from m - 2 down to 0 and cyc has m >= 2 entries (cyclesOf keeps cycles longer than one)
cycleToTranspositions cyc = [ (cyc !! i, cyc !! (i + 1)) | i <- [m - 2, m - 3 .. 0] ]
  where m = length cyc

-- >>> cycleToTranspositions [0, 1]
-- [(0,1)]
-- >>> cycleToTranspositions [0, 1, 2]
-- [(1,2),(0,1)]

-- | The circuit for one transposition |a> <-> |b> on the qubits 'qs' (MSB
-- first): CNOTs from a fixed differing bit 'm' to every other differing
-- bit, align the two states outside bit m, one multi-controlled X on bit m
-- controlled by the (now shared) values of every other qubit, then the same
-- CNOTs undone. Correctness is the numeric leaf comparison of
-- qasm3/compile_check.py.
transpositionLines :: [Int] -> (Int, Int) -> [String]
transpositionLines qs (a, b) =
  alignCNOTs ++ [ctrlLine] ++ alignCNOTs
  where
    k = length qs
    bitsA = bitsOfIndex k a
    bitsB = bitsOfIndex k b
    -- a and b are distinct basis indices, so they differ in some bit
    -- impossible: i and m are below k = length qs, the number of bits of a and b; zeroState has k bits
    diffIdx = [ i | i <- [0 .. k - 1], bitsA !! i /= bitsB !! i ]
    m = case diffIdx of
          (i : _) -> i
          -- impossible: a and b are distinct basis indices (the two ends of one transposition), so they differ in a bit
          []      -> error "Drop.Lang.Compile.Emit.transpositionLines: a == b"
    -- impossible: i and m are below k = length qs, the number of bits of a and b; zeroState has k bits
    zeroState = if bitsA !! m == 0 then bitsA else bitsB
    others = [ i | i <- [0 .. k - 1], i /= m ]
    -- impossible: i and m are below k = length qs, the number of bits of a and b; zeroState has k bits
    alignCNOTs = [ "cx " ++ qArgs [qs !! m, qs !! i] ++ ";" | i <- diffIdx, i /= m ]
    -- impossible: i and m are below k = length qs, the number of bits of a and b; zeroState has k bits
    ctrlBits = [ (qs !! i, zeroState !! i) | i <- others ]
    -- impossible: i and m are below k = length qs, the number of bits of a and b; zeroState has k bits
    ctrlLine = modifiersFor ctrlBits ++ "x " ++ qArgs (map fst ctrlBits ++ [qs !! m]) ++ ";"

-- One qubit: the transposition of |0> and |1> is X.
-- >>> transpositionLines [0] (0, 1)
-- ["x q[0];"]

-- |00> and |11> differ in both bits: a cx aligns them, a controlled x flips, the cx is undone.
-- >>> transpositionLines [0, 1] (0, 3)
-- ["cx q[0], q[1];","negctrl @ x q[1], q[0];","cx q[0], q[1];"]

-- |01> and |10> on three qubits' last two.
-- >>> transpositionLines [0, 1, 2] (1, 6)
-- ["cx q[0], q[1];","cx q[0], q[2];","negctrl @ ctrl @ x q[1], q[2], q[0];","cx q[0], q[1];","cx q[0], q[2];"]

permCircuit :: [Int] -> [Int] -> [String]
permCircuit qs imgs = concatMap (transpositionLines qs) (concatMap cycleToTranspositions (cyclesOf imgs))

-- The permutation |10> <-> |11> of two qubits is a CNOT.
-- >>> permCircuit [0, 1] [0, 1, 3, 2]
-- ["ctrl @ x q[0], q[1];"]
-- >>> permCircuit [0, 1] [0, 1, 2, 3]
-- []
-- >>> permCircuit [0, 1] [1, 0, 2, 3]
-- ["negctrl @ x q[0], q[1];"]

-- | Multi-controlled phase gates, one per basis state whose diagonal entry
-- is not 1 (the compiler's stated
-- domain, the compilation subsection): a fixed "swing" qubit (the last one) carries the phase gate,
-- X-conjugated when the pattern's bit there is 0, all other qubits become
-- ctrl/negctrl controls at their pattern bit.
diagCircuit :: [Int] -> Matrix Cyclo -> [String]
-- A gate on the unit value has no target qubit; its scalar is a global phase.
diagCircuit [] [[z]] = [ "gphase(" ++ angleLabel (phase (toC z)) ++ ");" | z /= 1 ]
-- impossible: i is below d = length mat = length entries
diagCircuit qs mat = concat [ phaseGateFor i (entries !! i) | i <- [0 .. d - 1], entries !! i /= 1 ]
  where
    d = length mat
    k = length qs
    entries = diagEntriesOf mat
    tPos = k - 1
    phaseGateFor i z =
      let bits = bitsOfIndex k i
          theta = phase (toC z)
          -- impossible: p and tPos are below k = length qs
          tBit = bits !! tPos
          -- impossible: p and tPos are below k = length qs
          ctrlBits = [ (qs !! p, bits !! p) | p <- [0 .. k - 2] ]
          -- impossible: p and tPos are below k = length qs
          pre = [ "x " ++ qArg (qs !! tPos) ++ ";" | tBit == 0 ]
          line = modifiersFor ctrlBits ++ "p(" ++ angleLabel theta ++ ") "
                 -- impossible: p and tPos are below k = length qs
                 ++ qArgs (map fst ctrlBits ++ [qs !! tPos]) ++ ";"
      in pre ++ [line] ++ pre

-- Z on one qubit is a phase of pi.
-- >>> diagCircuit [0] (diagOfList [1, -1])
-- ["p(pi) q[0];"]

-- cz on two qubits: one controlled phase.
-- >>> diagCircuit [0, 1] (diagOfList [1, 1, 1, -1])
-- ["ctrl @ p(pi) q[0], q[1];"]

-- A phase on the state |00> needs the swing qubit conjugated by x.
-- >>> diagCircuit [0, 1] (diagOfList [-1, 1, 1, 1])
-- ["x q[1];","negctrl @ p(pi) q[0], q[1];","x q[1];"]

-- | One U(theta, phi, lambda) on one qubit for a unitary given numerically; refused when an angle is not finite.
u3Circuit :: String -> [Int] -> [[Complex Double]] -> Either CompileError [String]
u3Circuit label [q] m =
  let (theta, phi, lam) = u3OfMatrix m
  in if all finiteComplex (concat m) && all finiteDouble [theta, phi, lam]
       then Right [ "U(" ++ angleLabel theta ++ ", " ++ angleLabel phi ++ ", " ++ angleLabel lam ++ ") " ++ qArg q ++ ";" ]
       else Left (Other (label ++ ": non-finite single-qubit gate parameters"))
-- refusal: not a single qubit; compileGate calls it only when length qs == 1
u3Circuit _ _ _ = error "u3Circuit: not a single qubit"

-- The Hadamard as one U.
-- >>> u3Circuit "gate h" [0] (matC [[invSqrt2C, invSqrt2C], [invSqrt2C, -invSqrt2C]])
-- Right ["U(pi/2, 0, -pi) q[0];"]
-- >>> either showCompileError show (u3Circuit "gate g" [0] [[1 / 0, 0], [0, 1]])
-- "gate g: non-finite single-qubit gate parameters"

-- | The lines for a gate on the named registers: by name if the table knows the matrix, else a controlled phase,
-- phases, transpositions or one U; any other gate is refused.
compileGate :: [Name] -> Map Name [Int] -> Matrix Cyclo -> Either CompileError [String]
compileGate names wireQ mat = do
  qs <- Right (concatMap (\n -> Map.findWithDefault [] n wireQ) names)
  case recognizeGate mat of
    Just nm -> Right [ nm ++ " " ++ qArgs qs ++ ";" ]
    Nothing -> case cpOf mat of
      Just z -> Right [ "cp(" ++ angleLabel (phase z) ++ ") " ++ qArgs qs ++ ";" ]
      Nothing
        | isDiagonalMatrix mat -> Right (diagCircuit qs mat)
        | Just imgs <- permOfMat mat -> Right (permCircuit qs imgs)
        | length qs == 1 -> u3Circuit ("gate " ++ intercalate "," names) qs (matC mat)
        | otherwise -> Left (GateNotInDomain names "not diagonal, a permutation, or a single-qubit unitary")

-- One qubit, a named gate of the table: H and T.
-- >>> compileGate ["x"] (Map.fromList [("x", [0])]) [[invSqrt2C, invSqrt2C], [invSqrt2C, -invSqrt2C]]
-- Right ["h q[0];"]
-- >>> compileGate ["x"] (Map.fromList [("x", [0])]) [[1, 0], [0, zetaC 3]]
-- Right ["t q[0];"]

-- A gate outside the table on one qubit becomes one U.
-- >>> compileGate ["x"] (Map.fromList [("x", [0])]) [[1, 0], [0, zetaC 4]]
-- Right ["p(0.39269908169872420) q[0];"]

-- On two qubits: a table gate by name, a diagonal as phases, a permutation as transpositions.
-- >>> compileGate ["x", "y"] (Map.fromList [("x", [0]), ("y", [1])]) [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]]
-- Right ["cx q[0], q[1];"]
-- >>> compileGate ["x", "y"] (Map.fromList [("x", [0]), ("y", [1])]) (diagOfList [1, iC, 1, 1])
-- Right ["negctrl @ p(pi/2) q[0], q[1];"]
-- >>> compileGate ["x", "y"] (Map.fromList [("x", [0]), ("y", [1])]) [[1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 1, 0, 0]]
-- Right ["ctrl @ x q[0], q[1];","ctrl @ x q[1], q[0];"]

-- A gate that is none of these is refused by name.
-- >>> either showCompileError show (compileGate ["x", "y"] (Map.fromList [("x", [0]), ("y", [1])]) [[1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
-- "gate on x y is not in the compile domain (not diagonal, a permutation, or a single-qubit unitary)"

-- new, loan, lift, if ---------------------------------------------------------

-- | A basis-state allocation on fresh qubits in |0>: an X on each qubit
-- whose bit of the allocation index is set ('compileTerm' has already
-- refused any non-basis allocation).
compileNew :: Int -> Int -> [Int] -> [String]
compileNew d i0 qs =
  let bits = bitsOfIndex (ilog2 d) i0
  in [ "x " ++ qArg q ++ ";" | (q, b) <- zip qs bits, b == 1 ]

-- A register of four levels allocated on |10>: one x, on the first of its two qubits.
-- >>> compileNew 4 2 [0, 1]
-- ["x q[0];"]
-- >>> compileNew 2 0 [3]
-- []
-- >>> compileNew 4 3 [5, 6]
-- ["x q[5];","x q[6];"]

-- | A loan: an input register with no declared state at all, so nothing is
-- emitted to prepare it -- the circuit's own qubit register is exactly
-- where the loan lands, whatever state that is (Drop.Lang.Criterion's "Loans"
-- section: it joins the input context the same way a visible register
-- does).
compileLoan :: Name -> [String]
compileLoan x = [ "// input register " ++ x ++ ", a loan: arrives in a state this program does not know" ]

-- >>> compileLoan "a"
-- ["// input register a, a loan: arrives in a state this program does not know"]

-- lift: the direct single-qubit rule, or the block form.

compileLift :: LayoutInfo -> Name -> Name -> [Int] -> Either CompileError [String]
compileLift layout p x s = do
  qsX <- maybe (Left (Other ("Drop.Lang.Compile: unknown wire " ++ x))) Right (Map.lookup x (liWireQ layout))
  let d = Map.findWithDefault 2 x (liWireDim layout)
      (bitIdx, sv) = Map.findWithDefault (0, 1) p (liLiftInfo layout)
  if d == 2 && (s == [0] || s == [1])
    then case qsX of
      (q0 : _) -> Right
        [ "c[" ++ show bitIdx ++ "] = measure " ++ qArg q0
          ++ ";   // lift " ++ p ++ ": survived <=> c[" ++ show bitIdx ++ "] == " ++ show sv ]
      [] -> Left (Other ("Drop.Lang.Compile: wire " ++ x ++ " was laid out on no qubit"))
    else do
      anc <- maybe (Left (Other ("Drop.Lang.Compile: no ancilla laid out for lift " ++ p))) Right
                   (Map.lookup p (liLiftAncilla layout))
      let k = length qsX
          uLine j = let bits = bitsOfIndex k j
                        ctrlBits = zip qsX bits
                    in modifiersFor ctrlBits ++ "x " ++ qArgs (qsX ++ [anc]) ++ ";"
      Right ( map uLine s
              ++ [ "c[" ++ show bitIdx ++ "] = measure " ++ qArg anc ++ ";   // lift " ++ p
                   ++ " (block " ++ show s ++ ")" ]
              ++ [ "if (c[" ++ show bitIdx ++ "] == 1) { x " ++ qArg anc ++ "; }   // reclaim the indicator" ] )

-- The lift m of temp-and.s reads qubit a directly: bit 0, survived when it reads 1.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileLift l "m" "a" [1] })) (parseTyped src)
-- "c[0] = measure q[2];   // lift m: survived <=> c[0] == 1"

-- A lift on a register of 16 levels is the block form: shor.s marks the block {7} on an indicator qubit.
-- >>> readFile "programs/shor.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileLift l "s" "w" [7] })) (parseTyped src)
-- "negctrl @ ctrl @ ctrl @ ctrl @ x q[3], q[4], q[5], q[6], q[7];"
-- "c[0] = measure q[7];   // lift s (block [7])"
-- "if (c[0] == 1) { x q[7]; }   // reclaim the indicator"

-- A wire never laid out is refused by name.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileLift l "m" "nothing" [1] })) (parseTyped src)
-- Drop.Lang.Compile: unknown wire nothing

-- if/else: a boolean over lift-bound bits to an OpenQASM 3 condition.

boolExprOf :: LayoutInfo -> BExpr -> String
boolExprOf layout be = case be of
  BParam p -> let (idx, sv) = Map.findWithDefault (0, 1) p (liLiftInfo layout)
              in "c[" ++ show idx ++ "] == " ++ show sv
  BNot e   -> "!(" ++ boolExprOf layout e ++ ")"
  BAnd a b -> "(" ++ boolExprOf layout a ++ " && " ++ boolExprOf layout b ++ ")"
  BOr a b  -> "(" ++ boolExprOf layout a ++ " || " ++ boolExprOf layout b ++ ")"
  -- A 'BLit' is what Step-Lift substitutes for the parameter it consumed, so
  -- it occurs only in a term the machine has already stepped. The compiler
  -- walks the term the FILE names, which has none; a constant condition is
  -- emitted correctly anyway rather than left as a partial match.
  BLit v   -> if v then "true" else "false"

-- The condition of the guard m is the raw bit that means survived.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (boolExprOf l (BParam "m")) })) (parseTyped src)
-- "c[0] == 1"
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (map (boolExprOf l) [BNot (BParam "m"), BAnd (BParam "m") (BParam "m"), BOr (BParam "m") (BLit False), BLit True]) })) (parseTyped src)
-- ["!(c[0] == 1)","(c[0] == 1 && c[0] == 1)","(c[0] == 1 || false)","true"]

-- drop: the reclaiming gate on a safe record ----------------------------------

-- | The tensor product of two vectors: every entry of the first times every
-- entry of the second, so the first factor is the more significant.
tensorVec :: Num a => [a] -> [a] -> [a]
tensorVec xs ys = [ x * y | x <- xs, y <- ys ]

-- >>> tensorVec [1, 2] [3, 4]
-- [3,4,6,8]
-- >>> tensorVec [1] [5, 6, 7]
-- [5,6,7]
-- >>> tensorVec [] [1, 2]
-- []

-- | What a drop of the named registers becomes on the record the enclosing
-- ifs have fixed so far: a comment for an unreachable or an unsafe record, the
-- reclaiming gate for a safe one, and when the records of the site differ in
-- their outcome, one guarded block per record.
compileDrop :: LayoutInfo -> SafetyInfo -> [(Name, Int)] -> SiteId -> [Name] -> Either CompileError [String]
-- @drop ()@: a block of dimension one, safe with the unit scalar as its
-- certificate (the site definition's clause (1)) and nothing to reclaim -- the reclaiming gate
-- is the identity on no qubit.
compileDrop _ _ _ _ [] = Right [ "// drop (): nothing to reclaim" ]
compileDrop layout safety fixedBits site names =
  case siteRecords layout safety fixedBits site of
    [] -> Right [ "// drop " ++ label ++ ": unreachable on this record" ]
    records -> case nub (map snd records) of
      [SafeCert cert]      -> emitReclaim label qs psi cert
      [SafeIso bMat]       -> emitLoanReturn label qs qsLoan qsTemp kinds psi bMat
      [UnsafeOutcome]      -> Right [ "// " ++ label ++ " dropped unsafe: stays live" ]
      [UnreachableOutcome] -> Right [ "// drop " ++ label ++ ": unreachable on this record" ]
      _ -> fmap concat (mapM (emitRecord layout label qs qsLoan qsTemp kinds psi) records)
  where
    label = intercalate "," names
    qs = concatMap (\n -> Map.findWithDefault [] n (liWireQ layout)) names
    -- A loan has no allocation vector (it arrives in whatever state the
    -- caller holds), so it contributes the scalar 1: 'psi' is the allocation
    -- state of the block's temporaries, in the drop's order.
    psi = foldr tensorVec [1] [ Map.findWithDefault [1] n (liWireAlloc layout) | n <- names ]
    -- A register without an allocation vector is a loan or an input not
    -- marked loan; 'fragmentSafety' has refused every safe site naming the
    -- latter, so at a site that emits a gate it is a loan.
    isLoan n = not (Map.member n (liWireAlloc layout))
    kinds  = [ (Map.findWithDefault 1 n (liWireDim layout), isLoan n) | n <- names ]
    qsLoan = concat [ Map.findWithDefault [] n (liWireQ layout) | n <- names, isLoan n ]
    qsTemp = concat [ Map.findWithDefault [] n (liWireQ layout) | n <- names, not (isLoan n) ]

-- >>> :m + Drop.Lang.Parser

-- A drop of nothing reclaims nothing.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in mapM_ print (either (\e -> [showCompileError e]) id (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileDrop l sf [] 0 [] }))) (parseTyped src)
-- "// drop (): nothing to reclaim"

-- The temporary AND (temp-and.s), site 0, on the record where the lift m survived: the block a holds |1> and the gate carries it back to |0>.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in mapM_ print (either (\e -> [showCompileError e]) id (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileDrop l sf [("m", 1)] 0 ["a"] }))) (parseTyped src)
-- "U(3.14159265358979270, 0, -pi) q[2];"

-- On the record where m did not survive the block already holds |0>: nothing to emit.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in print (either (\e -> [showCompileError e]) id (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileDrop l sf [("m", 0)] 0 ["a"] }))) (parseTyped src)
-- []

-- Before the enclosing if has fixed m, the two records differ, and each gets its own guarded block.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in mapM_ print (either (\e -> [showCompileError e]) id (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileDrop l sf [] 0 ["a"] }))) (parseTyped src)
-- "if (c[0] == 1) {"
-- "  U(3.14159265358979270, 0, -pi) q[2];"
-- "}"

-- A record the program cannot reach: no record of the site agrees with it.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in mapM_ print (either (\e -> [showCompileError e]) id (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileDrop l sf [("m", 7)] 0 ["a"] }))) (parseTyped src)
-- "// drop a: unreachable on this record"

-- An unsafe drop emits no gate: copy-input.s drops its input x and leaves it live.
-- >>> readFile "programs/copy-input.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in mapM_ print (either (\e -> [showCompileError e]) id (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileDrop l sf [] 0 ["x"] }))) (parseTyped src)
-- "// x dropped unsafe: stays live"

-- A loan (mcx-dirty-x.s): the drop of a is safe with B = X, and the return gate is X.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in mapM_ print (either (\e -> [showCompileError e]) id (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileDrop l sf [] 0 ["a"] }))) (parseTyped src)
-- "U(pi, 0, -pi) q[4];"

-- | The records of a site that agree with the bits the enclosing ifs fixed,
-- each with its open bits: the lifts before the site that no enclosing if has
-- decided.
siteRecords :: LayoutInfo -> SafetyInfo -> [(Name, Int)] -> SiteId -> [([(Name, Int)], SafetyOutcome)]
siteRecords layout safety fixedBits site =
  [ (openOf prefix, outcome)
  | (prefix, outcome) <- Map.toList siteMap
  , length prefix == depth, consistentWith prefix ]
  where
    depth = Map.findWithDefault 0 site (liSiteDepth layout)
    siteMap = Map.findWithDefault Map.empty site safety
    fixedNames = map fst fixedBits
    consistentWith prefix = all (\(n, v) -> lookup n prefix == Just v) fixedBits
    openOf prefix = [ nb | nb@(n, _) <- prefix, n `notElem` fixedNames ]

-- Before any if has fixed m, the site has both records.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (map fst (siteRecords l sf [] 0)) })) (parseTyped src)
-- [[("m",0)],[("m",1)]]

-- Inside the arm where m survived, only the record that agrees with it is left, and it has no open bit.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (map fst (siteRecords l sf [("m", 1)] 0)) })) (parseTyped src)
-- [[]]

-- A record no site holds.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (map fst (siteRecords l sf [("m", 7)] 0)) })) (parseTyped src)
-- []

-- | The condition on the measured bits that picks out one record: one
-- @c[i] == v@ per open bit, joined by @&&@.
recordCondition :: LayoutInfo -> [(Name, Int)] -> String
recordCondition layout openBits = intercalate " && "
  -- 'b' is the record's "1 = survived" flag (Drop.Lang.Machine's own
  -- convention, cfgBits); 'sv' is the *raw* qasm-measured value
  -- that means "survived" for this lift (liLiftInfo). The two
  -- share {0,1} but are not the same bit: translate, do not compare.
  [ "c[" ++ show idx ++ "] == " ++ show (if b == 1 then sv else 1 - sv)
  | (n, b) <- openBits
  , let (idx, sv) = Map.findWithDefault (0, 1) n (liLiftInfo layout) ]

-- Two open bits of measured-and-twice.s: lifts m1 (bit 0) and m2 (bit 1), each surviving when it reads 1.
-- >>> readFile "programs/measured-and-twice.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (recordCondition l [("m1", 1), ("m2", 0)]) })) (parseTyped src)
-- "c[0] == 1 && c[1] == 0"

-- A lift of {0} (superdense.s) survives when it reads 0: the survived flag 1 is the raw value 0.
-- >>> readFile "programs/superdense.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (recordCondition l [("p0", 1), ("p1", 0)]) })) (parseTyped src)
-- "c[0] == 0 && c[1] == 1"
-- >>> readFile "programs/superdense.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (recordCondition l []) })) (parseTyped src)
-- ""

-- | The text for one record of a site whose records differ in their outcome:
-- nothing for an unreachable record, a comment for an unsafe one, and for a
-- safe one its gate under the condition that picks the record out.
emitRecord :: LayoutInfo -> String -> [Int] -> [Int] -> [Int] -> [(Int, Bool)] -> StateV Cyclo
           -> ([(Name, Int)], SafetyOutcome) -> Either CompileError [String]
emitRecord layout label qs qsLoan qsTemp kinds psi (openBits, outcome) = case outcome of
  UnreachableOutcome -> Right []
  UnsafeOutcome -> Right [ "// " ++ label ++ " dropped unsafe on record "
                            ++ show openBits ++ ": stays live" ]
  SafeIso bMat -> fmap guarded (emitLoanReturn label qs qsLoan qsTemp kinds psi bMat)
  SafeCert cert -> fmap guarded (emitReclaim label qs psi cert)
  where
    guarded body
      | null body = []
      | otherwise = ["if (" ++ (if null cond then "true" else cond) ++ ") {"] ++ indent body ++ ["}"]
    cond = recordCondition layout openBits

-- The record where the lift survived gets a guarded block with its gate.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; emitRecord l "a" (wireQubits l "a") [] (wireQubits l "a") [(2, False)] [1, 0] ([("m", 1)], SafeCert [0, 1]) })) (parseTyped src)
-- "if (c[0] == 1) {"
-- "  U(3.14159265358979270, 0, -pi) q[2];"
-- "}"

-- An unsafe record is a comment; an unreachable one is nothing.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; emitRecord l "a" (wireQubits l "a") [] (wireQubits l "a") [(2, False)] [1, 0] ([("m", 0)], UnsafeOutcome) })) (parseTyped src)
-- "// a dropped unsafe on record [(\"m\",0)]: stays live"
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; emitRecord l "a" (wireQubits l "a") [] (wireQubits l "a") [(2, False)] [1, 0] ([("m", 0)], UnreachableOutcome) })) (parseTyped src)
-- []

-- A record whose gate is empty emits nothing, not an empty block.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; emitRecord l "a" (wireQubits l "a") [] (wireQubits l "a") [(2, False)] [1, 0] ([("m", 0)], SafeCert [1, 0]) })) (parseTyped src)
-- []

-- | The gate that returns a block of temporaries: it carries the certificate
-- line @cert@ back to the allocation state @psi@ on the qubits @qs@ (it
-- exchanges the two). Nothing when they are already the same line; a
-- basis transposition when both are basis states; a single U on one qubit;
-- else the two-support short form or the general reflection.
emitReclaim :: String -> [Int] -> StateV Cyclo -> StateV Cyclo -> Either CompileError [String]
emitReclaim label qs psi cert
  | canonicalLine psi == canonicalLine cert = Right []
  | otherwise = case unitOfExactRay cert of
      Nothing -> numericalFailure
      Just g ->
        let psiC = map toC psi
            (_, w, wnorm2) = gTildeAndW psiC g
            psiNorm2 = sum [magnitude z ** 2 | z <- psiC]
            -- A representable basis axis may have an underflowed squared
            -- norm. Use the scaled unit axis for validity; retain the
            -- conservative relative cutoff for non-basis differences.
            invalidAxis = not (all finiteComplex psiC && finiteDouble psiNorm2 &&
                               psiNorm2 > 0 && finiteDouble wnorm2) ||
                          unitVectorC w == Nothing
            illConditioned = basisLine psi == Nothing &&
                             wnorm2 < 1e-18 * psiNorm2
        in if invalidAxis || illConditioned
             then numericalFailure
             else case qs of
               [q] -> let (theta, phi, lam) = u3OfMatrix (reflectionR psiC g)
                      in checkedOps [OpU theta phi lam [] q]
               _ -> case (basisLine psi, basisLine cert) of
                 (Just i, Just j)
                   | i == j    -> Right []
                   | otherwise -> Right (transpositionLines qs (i, j))
                 _ -> checkedOps
                        (fromMaybe (emitGeneralReflectionOps qs psiC g)
                                   (emitTwoSupportReflectionOps qs psiC g))
  where
    numericalFailure = Left (Other ("drop " ++ label ++
      ": numerical reclaiming axis is non-finite, zero, or ill-conditioned"))
    checkedOps ops
      | all opIsFinite ops = Right (concatMap renderOp ops)
      | otherwise = numericalFailure

-- One qubit: the gate that carries the certificate |1> back to the allocation state |0> is one U.
-- >>> emitReclaim "a" [0] [1, 0] [0, 1]
-- Right ["U(3.14159265358979270, 0, -pi) q[0];"]

-- The certificate already is the allocation state: nothing to emit.
-- >>> emitReclaim "a" [0] [1, 0] [1, 0]
-- Right []

-- Two qubits, both basis states: a transposition, here |00> <-> |11>.
-- >>> emitReclaim "t" [0, 1] [1, 0, 0, 0] [0, 0, 0, 1]
-- Right ["cx q[0], q[1];","negctrl @ x q[1], q[0];","cx q[0], q[1];"]

-- A certificate on two basis states (the Bell pair): the five-line two-support form of the paper.
-- >>> emitReclaim "t" [0, 1] [1, 0, 0, 0] [1, 0, 0, 1]
-- Right ["ctrl @ x q[0], q[1];","U(pi/4, 0, -pi) q[0];","negctrl @ z q[1], q[0];","U(-pi/4, pi, 0) q[0];","ctrl @ x q[0], q[1];"]

-- Four nonzero entries: the general reflection, 19 lines here (at most 6 * 2^k + 1 = 25 for k = 2).
-- >>> fmap length (emitReclaim "t" [0, 1] [1, 0, 0, 0] [1, 1, 1, 1])
-- Right 19


-- | A block holding loans is returned by a gate T with T B = J, where B
-- is the block factor of the site definition's clause (3) and J places
-- the loans unchanged beside the temporaries' allocation state. B is
-- fixed only up to a nonzero scalar by the factorization
-- (Drop.Lang.Criterion.loanResultS), so it is normalised before any angle is
-- read off it.
--
-- Three shapes keep a short form ('squareFactorEmittable'): a square B
-- that is the identity (nothing to undo), on one qubit (a
-- U(theta,phi,lambda)), or a permutation of the basis states (the inverse
-- permutation, through the same transposition circuit the temporary path
-- uses), alone or as the loan factor B' of a product B = B' (x) g~ with
-- the temporaries' certificate ('splitMixedFactor'), where B'^dagger on
-- the loan qubits is followed by the reclaiming reflection through
-- psi - g~ on the temporary qubits. Every other isometric B, square or
-- rectangular, gets the general return gate: at most dim H_loan
-- reflections and one diagonal ('emitFrameReturnOps'), the matrix
-- 'expectedFinalState' applies.
emitLoanReturn :: String -> [Int] -> [Int] -> [Int] -> [(Int, Bool)] -> StateV Cyclo -> Matrix Cyclo
               -> Either CompileError [String]
emitLoanReturn label qs qsLoan qsTemp kinds psi bMat
  | square, Just lines_ <- squareShortForm label qs bMat = lines_
  | Just (bPrime, gT) <- splitMixedFactor kinds bMat
  , squareFactorEmittable bPrime = do
      loanLines <- maybe (Left (Other ("drop " ++ label ++ ": the split loan factor lost its shape")))
                         id (squareShortForm label qsLoan bPrime)
      tempLines <- emitReclaim label qsTemp psi gT
      Right (loanLines ++ tempLines)
  | otherwise = do
      (cols, jIdx) <- frameReturnInput label kinds psi bMat
      let k = length qs
      case (emitFrameReturnOps qs cols jIdx, emitFrameReturnOps [0 .. k - 1] cols jIdx) of
        (Just ops, Just localOps)
          | all opIsFinite ops, emittedReturnResidualOK k localOps cols jIdx
            -> Right (concatMap renderOp ops)
          | all opIsFinite ops
            -> Left (Other ("drop " ++ label ++ ": the emitted return gate failed its residual check"))
        _ -> Left (Other ("drop " ++ label ++ ": numerical return gate is non-finite or malformed"))
  where
    n      = length bMat
    square = not (null bMat) && all ((== n) . length) bMat

-- B = I: the loan came back as it arrived, nothing to emit.
-- >>> emitLoanReturn "a" [0] [0] [] [(2, True)] [1] [[1, 0], [0, 1]]
-- Right []

-- B = X on one qubit (mcx-dirty-x.s): one U.
-- >>> emitLoanReturn "a" [0] [0] [] [(2, True)] [1] [[0, 1], [1, 0]]
-- Right ["U(pi, 0, -pi) q[0];"]

-- B = a permutation of two loan qubits: the inverse permutation, by transpositions.
-- >>> emitLoanReturn "ab" [0, 1] [0, 1] [] [(2, True), (2, True)] [1] [[1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 1, 0, 0]]
-- Right ["ctrl @ x q[0], q[1];","cx q[0], q[1];","ctrl @ x q[1], q[0];","cx q[0], q[1];"]

-- B = B' (x) g with the loan factor B' = X and the temporary left on |1> (allocated on |0>): X on the loan qubit, then the temporary's reflection.
-- >>> emitLoanReturn "at" [0, 1] [0] [1] [(2, True), (2, False)] [1, 0] [[0, 0], [0, 1], [0, 0], [1, 0]]
-- Right ["U(pi, 0, -pi) q[0];","U(3.14159265358979270, 0, -pi) q[1];"]

-- Any other isometry takes the general return gate: here a 4 x 2 factor that is not a product.
-- >>> fmap length (emitLoanReturn "at" [0, 1] [0] [1] [(2, True), (2, False)] [1, 0] [[1, 0], [0, 1], [0, 1], [1, 0]])
-- Right 16

-- | The short forms of a square loan factor, decided exactly before numerical
-- normalization; 'Nothing' when the factor has none of the three shapes.
squareShortForm :: String -> [Int] -> Matrix Cyclo -> Maybe (Either CompileError [String])
squareShortForm label qsq m
  | scalarIdentity m = Just (Right [])
  | length qsq == 1 = Just $ do
      bN <- normaliseSquareIso label m
      u3Circuit ("drop " ++ label) qsq (daggerC bN)
  | Just imgs <- scalarPermutation m =
      Just (Right (concatMap (concatMap (transpositionLines qsq) . cycleToTranspositions)
                             (cyclesOf (inversePerm imgs))))
  | otherwise = Nothing

-- >>> squareShortForm "a" [0] [[1, 0], [0, 1]]
-- Just (Right [])
-- >>> squareShortForm "a" [0] [[0, 1], [1, 0]]
-- Just (Right ["U(pi, 0, -pi) q[0];"])
-- >>> squareShortForm "ab" [0, 1] [[1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 1, 0, 0]]
-- Just (Right ["ctrl @ x q[0], q[1];","cx q[0], q[1];","ctrl @ x q[1], q[0];","cx q[0], q[1];"])

-- No short form for the Hadamard of two qubits.
-- >>> squareShortForm "ab" [0, 1] [[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]]
-- Nothing

-- Structural recursion --------------------------------------------------------

-- | @atReturn@ is what a @return@ emits where it stands: nothing when every
-- branch returns the same value (the output measurements then follow the
-- whole body, once), the output measurements of its own value otherwise.
compileTerm :: LayoutInfo -> SafetyInfo -> (Value -> [String]) -> [(Name, Int)] -> Term Cyclo
            -> Either CompileError [String]
compileTerm layout safety atReturn fixedBits term = case term of
  Return v -> Right (atReturn v)
  Do (StGate g v) m -> do
    gl <- compileGate (valueNames v) (liWireQ layout) g
    rest <- compileTerm layout safety atReturn fixedBits m
    Right (gl ++ rest)
  Do (StNew nm d psi) m -> do
    let qs = Map.findWithDefault [] nm (liWireQ layout)
    -- the compilation fragment requires basis-state allocations (the
    -- paper's fragment sentence): refuse a non-basis one
    i0 <- maybe (Left (OutsideFragment ("new " ++ nm ++ ": the allocation state is not a computational basis state, and the compilation fragment requires basis-state allocations")))
                Right (basisIndexOfExact psi)
    rest <- compileTerm layout safety atReturn fixedBits m
    Right (compileNew d i0 qs ++ rest)
  Do (StLoan nm _) m -> do
    rest <- compileTerm layout safety atReturn fixedBits m
    Right (compileLoan nm ++ rest)
  Do (StDrop site v) m -> do
    dl <- compileDrop layout safety fixedBits site (valueNames v)
    rest <- compileTerm layout safety atReturn fixedBits m
    let poolLines = case Map.lookup site (liPoolClears layout) of
          Nothing -> []
          Just qs -> [ "x " ++ qArg q ++ ";" | q <- qs ]
                  ++ [ "// pool site " ++ show site ++ ": " ++ unwords (valueNames v) ]
    Right (dl ++ poolLines ++ rest)
  Do (StLift pname s x) m -> do
    ll <- compileLift layout pname x s
    rest <- compileTerm layout safety atReturn fixedBits m
    Right (ll ++ rest)
  If e m1 m2 -> do
    let cond = boolExprOf layout e
        fixed1 = case e of BParam pn -> fixedBits ++ [(pn, 1)]; _ -> fixedBits
        fixed2 = case e of BParam pn -> fixedBits ++ [(pn, 0)]; _ -> fixedBits
    l1 <- compileTerm layout safety atReturn fixed1 m1
    l2 <- compileTerm layout safety atReturn fixed2 m2
    Right (["if (" ++ cond ++ ") {"] ++ indent l1 ++ ["} else {"] ++ indent l2 ++ ["}"])

-- The temporary AND (temp-and.s), whole: the lift, the if, the drop under it.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileTerm l sf (const []) [] core })) (parseTyped src)
-- "ccx q[0], q[1], q[2];"
-- "h q[2];"
-- "c[0] = measure q[2];   // lift m: survived <=> c[0] == 1"
-- "if (c[0] == 1) {"
-- "  cz q[0], q[1];"
-- "  U(3.14159265358979270, 0, -pi) q[2];"
-- "} else {"
-- "}"

-- A loan emits only a comment; the drop of the loan is the return gate, here X (mcx-dirty-x.s).
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; compileTerm l sf (const []) [] core })) (parseTyped src)
-- "// input register a, a loan: arrives in a state this program does not know"
-- "x q[4];"
-- "ccx q[2], q[4], q[3];"
-- "ccx q[0], q[1], q[4];"
-- "ccx q[2], q[4], q[3];"
-- "ccx q[0], q[1], q[4];"
-- "U(pi, 0, -pi) q[4];"

-- A basis-state allocation is an x per set bit; anything else is refused as outside the fragment.
-- >>> either showCompileError show (compileTerm (LayoutInfo (Map.fromList [("t", [0])]) (Map.fromList [("t", 2)]) Map.empty Map.empty Map.empty Map.empty 1 0 Map.empty) Map.empty (const []) [] (Do (StNew "t" 2 [1, 1]) (Return VUnit)))
-- "outside the compilation fragment: new t: the allocation state is not a computational basis state, and the compilation fragment requires basis-state allocations"

-- Header, outputs, the reference ----------------------------------------------

-- | The header is built after the body, because the only gate this emitter
-- declares itself -- Grover's diffusion -- is declared only when the body
-- actually calls it.  Everything else comes from @stdgates.inc@. The
-- comments name the input registers' qubits; @width@ is the returned
-- value's qubit count, and a program that returns @()@ declares no @result@.
buildHeader :: LayoutInfo -> [Name] -> Int -> [String] -> [String]
buildHeader layout visNames width body =
  [ "OPENQASM 3.0;"
  , "include \"stdgates.inc\";"
  , ""
  , "// emitted by Drop.Lang.Compile, the compiler of the paper's language."
  , "// Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller."
  ]
  ++ [ "gate diff a, b { h a; h b; x a; x b; cz a, b; x a; x b; h a; h b; }   // Grover diffusion, up to global phase"
     | usesDiff ]
  ++ [ "qubit[" ++ show (liTotalQubits layout) ++ "] q;" | liTotalQubits layout > 0 ]
  ++ [ "bit[" ++ show (liTotalBits layout) ++ "] c;" | liTotalBits layout > 0 ]
  ++ [ "bit[" ++ show width ++ "] result;" | width > 0 ]
  ++ [""]
  ++ [ "// q[" ++ show q ++ "] = " ++ n | n <- visNames, q <- wireQubits layout n ]
  ++ [""]
  where
    -- Token match, not a substring: a line reading "diff q[0], q[1];" counts,
    -- a comment mentioning "difference" does not.
    usesDiff = any (elem "diff" . identifiers) body
    identifiers = words . map (\ch -> if isAlphaNum ch || ch == '_' then ch else ' ')

-- The header of temp-and.s: three qubits, one classical bit, a two-bit result.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (buildHeader l ["x", "y"] 2 ["h q[0];"]) })) (parseTyped src)
-- "OPENQASM 3.0;"
-- "include \"stdgates.inc\";"
-- ""
-- "// emitted by Drop.Lang.Compile, the compiler of the paper's language."
-- "// Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller."
-- "qubit[3] q;"
-- "bit[1] c;"
-- "bit[2] result;"
-- ""
-- "// q[0] = x"
-- "// q[1] = y"
-- ""

-- A body that calls diff declares the Grover diffusion gate first.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) (mapM_ print) (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (take 7 (buildHeader l ["x", "y"] 2 ["diff q[0], q[1];"])) })) (parseTyped src)
-- "OPENQASM 3.0;"
-- "include \"stdgates.inc\";"
-- ""
-- "// emitted by Drop.Lang.Compile, the compiler of the paper's language."
-- "// Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller."
-- "gate diff a, b { h a; h b; x a; x b; cz a, b; x a; x b; h a; h b; }   // Grover diffusion, up to global phase"
-- "qubit[3] q;"

-- | The output measurements: the registers the returned value names, in its
-- order, one @result@ bit per qubit. A register the header does not name
-- (it names the inputs) is named here, in the header's own form, so that
-- every register the file measures is named in it.
outputMeasureLines :: LayoutInfo -> [Name] -> Value -> [String]
outputMeasureLines layout inputs v =
  [ "// q[" ++ show q ++ "] = " ++ n | n <- names, n `notElem` inputs, q <- wireQubits layout n ]
  ++ [ "result[" ++ show i ++ "] = measure " ++ qArg q ++ ";"
     | (i, q) <- zip [0 :: Int ..] (concatMap (wireQubits layout) names) ]
  where names = valueNames v

-- The returned registers are measured, one result bit per qubit.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (outputMeasureLines l ["x", "y"] (VPair (VVar "x") (VVar "y"))) })) (parseTyped src)
-- ["result[0] = measure q[0];","result[1] = measure q[1];"]

-- A register the header does not name is named here first.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (outputMeasureLines l ["x", "y"] (VVar "a")) })) (parseTyped src)
-- ["// q[2] = a","result[0] = measure q[2];"]
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; Right (outputMeasureLines l ["x", "y"] VUnit) })) (parseTyped src)
-- []

-- | The theorem's target (the per-record compilation theorem's required equality):
-- for every leaf, apply the reclaiming proposition's gate to
-- Drop.Lang.Machine's own (unreclaimed -- drop is denotationally the
-- identity) leaf amplitude, at every site the leaf crosses that
-- 'computeSafety' finds SAFE, leaving an UNSAFE site's register untouched.
-- This shares the reflection formula with 'compileDrop' (so it does not
-- catch a bug in 'reflectionR' itself -- the unit test above is what
-- checks that), but is otherwise independent of the gate emission code
-- ('compileGate', 'diagCircuit', 'permCircuit', 'u3Circuit',
-- 'transpositionLines'), which qasm3/compile_check.py's own simulator
-- checks against it.
expectedFinalState :: LayoutInfo -> SafetyInfo -> Config Cyclo -> Either CompileError [Complex Double]
expectedFinalState layout safety leaf = foldM applyReclaim (map toC (cfgAmp leaf)) (cfgSites leaf)
  where
    dimsC = cfgDims leaf
    namesC = cfgNames leaf
    restoreTemp label psi cert positions amp
      | canonicalLine psi == canonicalLine cert = Right amp
      | otherwise = case unitOfExactRay cert of
          Nothing -> Left (Other ("drop " ++ label ++ ": numerical reclaiming axis cannot be normalized"))
          Just g -> Right (applyGate dimsC (reflectionR (map toC psi) g) positions amp)
    undoSquare label b positions amp
      | scalarIdentity b = Right amp
      | length b == 2 = do
          bN <- normaliseSquareIso label b
          Right (applyGate dimsC (daggerC bN) positions amp)
      | Just imgs <- scalarPermutation b =
          let n = length imgs
              -- impossible: j is below n = length imgs
              p = [[if imgs !! j == i then 1 else 0 | j <- [0 .. n-1]] | i <- [0 .. n-1]]
          in Right (applyGate dimsC (daggerC p) positions amp)
      -- impossible: positions index the machine's registers, so they are below length dimsC
      | otherwise = undoFrame label [ (dimsC !! p, True) | p <- positions ] [1] b positions amp
    -- the general return gate T B = J: the same matrix
    -- 'compileDrop' prints through 'emitFrameReturnOps'
    undoFrame label kinds psiT b positions amp = do
      (cols, jIdx) <- frameReturnInput label kinds psiT b
      Right (applyGate dimsC (frameReturnMatrix cols jIdx) positions amp)
    applyReclaim amp rec_ =
      let depth = Map.findWithDefault 0 (srSite rec_) (liSiteDepth layout)
          prefix = take depth (cfgBits leaf)
          outcome = Map.findWithDefault UnreachableOutcome prefix
                      (Map.findWithDefault Map.empty (srSite rec_) safety)
          hiddenNames = srHidden rec_
          label = intercalate "," hiddenNames
          positions = [ i | n <- hiddenNames, (i,nm) <- zip [0 ..] namesC, nm == n ]
          allocation ns = foldr tensorVec [1] [ Map.findWithDefault [1] n (liWireAlloc layout) | n <- ns ]
      in case outcome of
           _ | null hiddenNames -> Right amp
           SafeCert cert -> restoreTemp label (allocation hiddenNames) cert positions amp
           SafeIso bMat ->
             let n = length bMat
                 square = n > 0 && all ((== n) . length) bMat
                 isLoan nm = not (Map.member nm (liWireAlloc layout))
                 -- impossible: positions index the machine's registers, so they are below length dimsC
                 kinds = [ (dimsC !! i,isLoan nm) | (nm,i) <- zip hiddenNames positions ]
                 loanPositions = [ i | (i,(_,True)) <- zip positions kinds ]
                 tempPositions = [ i | (i,(_,False)) <- zip positions kinds ]
                 psiTemp = allocation [ nm | nm <- hiddenNames, not (isLoan nm) ]
             in if square
                  then undoSquare label bMat positions amp
                  else case splitMixedFactor kinds bMat of
                    Just (bPrime,gT) | squareFactorEmittable bPrime -> do
                      amp1 <- undoSquare label bPrime loanPositions amp
                      restoreTemp label psiTemp gT tempPositions amp1
                    _ -> undoFrame label kinds psiTemp bMat positions amp
           _ -> Right amp

-- The reference leaf of temp-and.s on |00>, after the reclaiming gate of its record: the amplitude per basis state, rounded.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in either (putStrLn . showCompileError) print (do { l <- layoutProgram prog; sf <- fragmentSafety prog core l; mapM (\leaf -> fmap (map (\z -> (round (1000 * realPart z), round (1000 * imagPart z)))) (expectedFinalState l sf leaf)) (run (initConfigL (progCtx prog) [1, 0, 0, 0] [] core)) })) (parseTyped src)
-- [[(707,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],[(707,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)]]

-- | Every 'new'-allocated wire's physical qubits and its allocation vector
-- psi -- so a checker can seed a non-basis temporary's qubits at psi
-- directly, since (by the domain's own rule) 'compile' emits no
-- preparation gates for it. A wire whose psi is a computational basis
-- state assumes fresh scratch starts at |0..0>; OpenQASM declarations
-- alone do not initialize it. 'compile' emits the X gates that reach
-- psi from there.
wireAllocOf :: Program Cyclo -> Either CompileError [(Name, [Int], [Complex Double])]
wireAllocOf prog = do
  layout <- layoutProgram prog
  Right [ (n, Map.findWithDefault [] n (liWireQ layout), map toC psi) | (n, psi) <- Map.toList (liWireAlloc layout) ]

-- The temporary of temp-and.s: qubit 2, allocated on |0>.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (wireAllocOf prog)) (parseTyped src)
-- Right [("a",[2],[1.0 :+ 0.0,0.0 :+ 0.0])]

-- A program with no allocation lists nothing.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (wireAllocOf prog)) (parseTyped src)
-- Right []

-- | Every leaf reached from a given (exact) input on the visible registers,
-- paired with its theorem-predicted physical state.
leavesWithExpected :: Program Cyclo -> StateV Cyclo -> Either CompileError [(Config Cyclo, [Complex Double])]
leavesWithExpected prog inp = do
  layout <- layoutProgram prog
  let core = toTerm (progTerm prog)
  safety <- fragmentSafety prog core layout
  let -- Every loan seeded at |0>, matching the emitted circuit's own qubit
      -- register (no preparation gate is emitted for a loan, so its
      -- physical qubits start at OpenQASM's own |0>): this leaf export is
      -- an internal check that the emitted circuit matches this reference
      -- machine on ONE concrete run, not a re-statement of the abstract
      -- safety claim (which Drop.Lang.Criterion's loan criterion already decides
      -- for every possible incoming state).
      loanEnv0 = [ (n, ket [d] [0]) | (n, d) <- loanBindersOf core ]
      leaves = run (initConfigL (progCtx prog) inp loanEnv0 core)
  -- Do not export a reference target for a circuit emission would refuse.
  _ <- compileTerm layout safety (const []) [] core
  mapM (\leaf -> do
    final <- expectedFinalState layout safety leaf
    Right (leaf, final)) leaves

-- Two leaves for temp-and.s on |00>: the lift keeps or loses the temporary.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (fmap length (leavesWithExpected prog [1, 0, 0, 0]))) (parseTyped src)
-- Right 2

-- One leaf for the loan program (no lift).
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (fmap length (leavesWithExpected prog (replicate 16 0)))) (parseTyped src)
-- Right 1

