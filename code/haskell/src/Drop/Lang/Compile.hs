-- Compile.hs: OpenQASM 3 compilation of the typed surface language.
-- The paper's *Compilation to circuits* states the compiler's domain; this
-- module is that statement made executable.
--
-- 'compile' walks the expanded term (Drop.Lang.Typed.toTerm) by
-- structural recursion and is total on its domain: every register named in
-- a joint gate, allocation or lift must have dimension a power of two (a
-- k-qubit register); the domain of gates, allocation, lift and drop is
-- described construct by construct below, next to the code that realises
-- it. Outside the domain, 'compile' returns a named 'CompileError' rather
-- than guessing.
-- Drops are part of the domain ('fragmentSafety'): a program that drops a
-- loan after a lift or an if, or drops an input not marked loan at a site
-- that is safe, with a nonzero site map, on some record, is refused with
-- the drop it names.
--
-- Two passes precede emission, both pure and both over the *whole* term
-- (the fragment 'compileFragment' checks first -- no allocation, lift or
-- drop inside an `if` branch, a name bound once, one site id per surface
-- drop -- makes both well defined; the parser enforces the same rules, and
-- Drop.Lang.Check, which follows the paper's If rule, does not):
--
--   * 'layoutProgram' assigns physical qubit indices to every named wire
--     (in program order) and a classical bit index to every lift, deciding
--     for each lift whether it is the direct one-qubit rule or the block
--     form (needing one ancilla qubit). It also records,
--     for every 'drop' occurrence, the number of lifts crossed before it
--     ('siteDepth') -- a purely structural count, invariant across the
--     branches an `if` later duplicates a drop into, because branches never
--     allocate or lift.
--
--   * 'computeSafety' reuses 'Drop.Lang.Machine.run' on every basis probe of
--     the visible input plus the all-ones vector (Drop.Lang.Interp.probesFor,
--     unmodified) to reach every leaf, and reuses 'Drop.Lang.QState.factorSplit'
--     and 'canonicalLine' at each leaf's recorded site state
--     ('Drop.Lang.Machine.SiteRecord') exactly as Drop.Lang.Interp's own
--     'semanticVerdict'/'probeResult' do, but indexed by the *full* record
--     (the lift outcomes crossed before the site, by name), not just by a
--     selection word -- because a drop occurrence compiled inside an `if`
--     branch already has some of those bits fixed by the branch, and the
--     reclaiming gate may still depend on the rest, being conditioned on the
--     record's bits.
--
-- The emission pass ('compileTerm') is a plain function of
-- (layout, safety, the record fixed by the enclosing `if`s so far, the core
-- term); no monad is needed because the resource layout is already decided.
module Drop.Lang.Compile
  ( compile
  , CompileError (..)
  , showCompileError
  , liftInfoOf
  , wireAllocOf
  , visQubitsOf
  , wireQubitsOf
  , leavesWithExpected
  , liftAncillaOf
  -- exported for the unit test (the reclaiming proposition's gate):
  , reflectionR
  , u3OfMatrix
  , basisIndexOfC
  , proportionalTo
  , toC
  -- exported for the unit test of the general k-qubit reclaiming
  -- reflection: the internal gate representation, its dense-matrix reading
  -- (so a test can simulate exactly the object that gets rendered, via
  -- Drop.Lang.QState.applyGate, with no re-parsing of the emitted text), and the
  -- op-list builder itself.
  , Op (..)
  , opDense
  , emitGeneralReflectionOps
  -- exported for the unit test of the two-support short form:
  , emitTwoSupportReflectionOps
  ) where

import Data.Bits (testBit, (.&.))
import Data.Char (isAlphaNum)
import Data.Complex
import Data.List (intercalate, nub)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Text.Printf (printf)

import Drop.Lang.Check (checkProgram, showTypeError)
import Drop.Lang.Cyclo (Cyclo (..))
import Drop.Lang.Elab (elabE)
import Drop.Lang.Interp (probesFor, loanEnvs, semanticVerdictS, semanticLoanCertS, Verdict (..))
import Drop.Lang.Machine
import Drop.Lang.QState
import Drop.Lang.Typed

-- ---------------------------------------------------------------------
-- Numeric evaluation of the exact scalar field, for angle synthesis only
-- (the SAFE/UNSAFE decision itself stays exact, over Cyclo -- see
-- 'computeSafety'). A level-k Cyclo is a coefficient vector in the basis
-- 1, zeta, ..., zeta^(N-1) of the primitive 2^k-th root of unity.
-- ---------------------------------------------------------------------

toC :: Cyclo -> Complex Double
toC (Cyclo k cs) = sum [ (fromRational c :+ 0) * (w ^^ i) | (i, c) <- zip [0 :: Int ..] cs ]
  where
    n = (2 :: Integer) ^ k
    w = cis (2 * pi / fromIntegral n)

matC :: Matrix Cyclo -> [[Complex Double]]
matC = map (map toC)

-- | The index of the single nonzero (magnitude ~1) entry, if the vector is
-- a computational basis state up to floating tolerance.
basisIndexOfC :: [Complex Double] -> Maybe Int
basisIndexOfC v = case [ i | (i, a) <- zip [0 ..] v, magnitude a > 1e-6 ] of
  [i] | abs (magnitude (v !! i) - 1) < 1e-6 -> Just i
  _ -> Nothing

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

isApproxIdentity :: [[Complex Double]] -> Bool
isApproxIdentity m = and [ close (m !! i !! j) (if i == j then 1 else 0)
                          | i <- [0 .. n - 1], j <- [0 .. n - 1] ]
  where
    n = length m
    close a b = magnitude (a - b) < 1e-6

-- | A square block factor B with B^dagger B = t I, t > 0 real
-- (Drop.Lang.Interp.isScalarIdentity: the factorization of 'loanResultS'
-- fixes B only up to a nonzero scalar, since (cB) (x) (W/c) = B (x) W),
-- divided by sqrt t -- the squared norm of any column -- so that it is
-- unitary before an angle is read off it, and then by the phase of the
-- first nonzero entry of its first column, so that a unit-scalar multiple
-- of the identity or of a basis permutation is exactly that matrix before
-- 'squareFactorEmittable' tests its shape. Without the second step a SWAP
-- read as i SWAP (a program that applies diag(i,1) to another register
-- first) was left live with a "not emitted" comment.
normaliseSquareIso :: [[Complex Double]] -> [[Complex Double]]
normaliseSquareIso bC =
  let t = sum [ magnitude (row !! 0) ** 2 | row <- bC, not (null row) ]
      scaled = if t < 1e-24 then bC else map (map (/ (sqrt t :+ 0))) bC
  in case [ z | (z : _) <- scaled, magnitude z > 1e-9 ] of
       (z : _) -> map (map (/ (z / (magnitude z :+ 0)))) scaled
       []      -> scaled

daggerC :: [[Complex Double]] -> [[Complex Double]]
daggerC m = [ [ conjugate (m !! j !! i) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
  where n = length m

-- | The square loan factors the emitter has a clause for, and no other:
-- the identity (nothing to undo), a factor on one qubit (a
-- U(theta,phi,lambda)), and a permutation of the basis states (the inverse
-- permutation as a chain of transpositions). 'compileDrop' emits exactly
-- when this holds and 'expectedFinalState' applies B^dagger exactly when
-- this holds, so the two cannot drift apart. The argument is normalised.
squareFactorEmittable :: [[Complex Double]] -> Bool
squareFactorEmittable bN =
  isApproxIdentity bN || length bN == 2 || maybe False (const True) (permOfMatC bN)

-- | A block that holds temporaries beside its loans has a rectangular block
-- factor B : H_loan -> H_block (the site definition's clause (3), Drop.Lang.Interp.loanResultS).
-- When B is a product B' (x) g~ of a square factor on the loans and a
-- certificate on the temporaries -- the shape under which the emitted gate
-- is B'^dagger on the loans, then the reclaiming reflection on the
-- temporaries, the two acting on disjoint registers --
-- this returns @Just (B', g~)@, both exact, B' a @dLoan x dLoan@ matrix and
-- g~ a vector of length @dTemp@, each indexed in the drop's order restricted
-- to its kind. 'Nothing' when B entangles the loans with the temporaries (a
-- site still safe by the site definition's clause (3), with no product gate to write) or when
-- the block is not mixed at all. The rows of B are indexed in the drop's
-- order over all its registers (Drop.Lang.QState.reindexABOrd); @kinds@ lists,
-- in that order, each register's dimension and whether it is a loan.
splitMixedFactor :: [(Int, Bool)] -> Matrix Cyclo -> Maybe (Matrix Cyclo, StateV Cyclo)
splitMixedFactor kinds bMat
  | null loanDims || null tempDims = Nothing
  | length bMat /= product dims || any ((/= dLoan) . length) bMat = Nothing
  | otherwise = case factorSplit [dTemp, dLoan * dLoan] [0] flat of
      Nothing -> Nothing
      Just (gT, bFlat) ->
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
    interleave _ _ _ = error "splitMixedFactor: digit count mismatch"
    -- B as a vector over [temporaries out, (loans out, loans in)], the
    -- grouping on which the product form is a rank-one condition
    flat = [ bMat !! rowOf to lo !! li
           | to <- [0 .. dTemp - 1], lo <- [0 .. dLoan - 1], li <- [0 .. dLoan - 1] ]

-- ---------------------------------------------------------------------
-- The reclaiming proposition: the reclaiming gate, over C.
-- ---------------------------------------------------------------------

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
        | magnitude ip > 1e-9 = map (* cis (negate (phase ip))) g
        | otherwise =
            let j = case [ i | (i, a) <- zip [0 ..] g, magnitude a > 1e-9 ] of
                      (i : _) -> i
                      []      -> error "gTildeAndW: g is the zero vector"
            in map (* cis (negate (phase (g !! j)))) g
      w = zipWith (-) psi gTilde
      wnorm2 = sum [ (magnitude x) ** 2 | x <- w ]
  in (gTilde, w, wnorm2)
  where
    innerProd a b = sum (zipWith (\x y -> conjugate x * y) a b)

-- | @reflectionR psi g@ is the unitary R^psi of the reclaiming proposition: the
-- Householder reflection through (a phase-adjusted representative of) g and
-- psi, satisfying R psi = g~ and R g~ = psi, with the tie-break at
-- <psi,g> = 0 stated there. Both vectors are unit vectors of the same
-- dimension; R = I when g is already proportional to psi.
reflectionR :: [Complex Double] -> [Complex Double] -> [[Complex Double]]
reflectionR psi g =
  let (_, w, wnorm2) = gTildeAndW psi g
      n = length psi
  in if wnorm2 < 1e-18
       then [ [ if i == j then 1 else 0 | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
       else [ [ (if i == j then 1 else 0) - 2 * (w !! i) * conjugate (w !! j) / (wnorm2 :+ 0)
              | j <- [0 .. n - 1] ]
            | i <- [0 .. n - 1] ]

-- | theta, phi, lambda of OpenQASM 3's U(theta,phi,lambda) so that
-- U(theta,phi,lambda) equals the given 2x2 unitary up to a global phase:
-- U = [[cos(t/2), -e^{iL} sin(t/2)], [e^{iP} sin(t/2), e^{i(P+L)} cos(t/2)]].
-- theta = 2*atan2(|c|,|a|) always determines |a| = cos(t/2), |c| = sin(t/2);
-- the phase of a (or, when a ~ 0, of c) is absorbed as the free global
-- phase, then phi and lambda are read off the remaining two entries.
u3OfMatrix :: [[Complex Double]] -> (Double, Double, Double)
u3OfMatrix [[a, b], [c, d]] =
  let theta = 2 * atan2 (magnitude c) (magnitude a)
  in if magnitude a > 1e-9
       then
         let ph = a / (magnitude a :+ 0)
             b' = b / ph; c' = c / ph; d' = d / ph
             phi = if magnitude c' > 1e-9 then phase c' else 0
             lam | magnitude b' > 1e-9 = phase (negate b')
                 | magnitude d' > 1e-9 = phase d'
                 | otherwise = 0
         in (theta, phi, lam)
       else
         let ph = c / (magnitude c :+ 0)
             b' = b / ph
             lam = phase (negate b')
         in (theta, 0, lam)
u3OfMatrix _ = error "u3OfMatrix: not a 2x2 matrix"

-- ---------------------------------------------------------------------
-- The general k-qubit reclaiming reflection (k >= 2), the reclaiming proposition's
-- 'reflectionR' realised as a circuit: R = V^dagger . (I - 2|0..0><0..0|) . V,
-- V u = |0..0>, u = w / ||w||, w = psi - g~ exactly as 'gTildeAndW' computes
-- it (shared with 'reflectionR' itself, not re-derived). V^dagger is "prepare
-- u from |0..0>": a real-amplitude recursion (a controlled-Ry, i.e.
-- U(theta,0,0), per prefix pattern per level) that reaches |u| = the
-- entrywise magnitudes of u, then a diagonal phase fixup (multi-controlled
-- p(theta) gates, mirroring 'diagCircuit' below) that turns |u| into u
-- exactly; V is the reverse, adjointed. Built from an internal 'Op'
-- representation (rather than string-level surgery) so the adjoint and the
-- test's simulation are both exact and neither re-parses the other.
-- ---------------------------------------------------------------------

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

-- | The adjoint of a single 'Op', as a circuit fragment of one line:
-- U(theta,phi,lambda)^dagger = U(-theta,-lambda,-phi) (controls unchanged);
-- p(theta)^dagger = p(-theta); x and z are self-adjoint. The adjoint of a
-- whole circuit (a list of lines, time order first-to-last) is the reverse
-- of the list with each line replaced by 'adjointOp' -- ordinary circuit
-- adjoint, not specific to this construction.
adjointOp :: Op -> Op
adjointOp (OpU t p l c q) = OpU (negate t) (negate l) (negate p) c q
adjointOp (OpP t c q)     = OpP (negate t) c q
adjointOp (OpX c q)       = OpX c q
adjointOp (OpZ c q)       = OpZ c q

-- | 'Op' as an OpenQASM 3 line, via the file's own 'modifiersFor'/'qArgs'.
renderOp :: Op -> String
renderOp (OpU t p l c q) =
  modifiersFor c ++ "U(" ++ angleLabel t ++ ", " ++ angleLabel p ++ ", " ++ angleLabel l ++ ") "
    ++ qArgs (map fst c ++ [q]) ++ ";"
renderOp (OpP t c q) =
  modifiersFor c ++ "p(" ++ angleLabel t ++ ") " ++ qArgs (map fst c ++ [q]) ++ ";"
renderOp (OpX c q) = modifiersFor c ++ "x " ++ qArgs (map fst c ++ [q]) ++ ";"
renderOp (OpZ c q) = modifiersFor c ++ "z " ++ qArgs (map fst c ++ [q]) ++ ";"

-- | 'Op' as a (targets, dense matrix) pair usable with
-- 'Drop.Lang.QState.applyGate': targets are the controls (in order) followed by
-- the actual target qubit, matching 'renderOp's own qArgs order, and the
-- dense matrix is 'gateMat' spread over 2^(#controls) copies -- identity
-- outside the pattern the controls require, 'gateMat' inside it -- by the
-- same MSB-first bit convention 'bitsOfIndex' uses everywhere else in this
-- file. Exported so a test can simulate exactly the object 'renderOp' prints,
-- not a re-parse of the printed text.
opDense :: Op -> ([Int], [[Complex Double]])
opDense (OpU t p l c q) = (map fst c ++ [q], controlledMat (map snd c) (u3Mat t p l))
opDense (OpP t c q)     = (map fst c ++ [q], controlledMat (map snd c) (pMat t))
opDense (OpX c q)       = (map fst c ++ [q], controlledMat (map snd c) xMat)
opDense (OpZ c q)       = (map fst c ++ [q], controlledMat (map snd c) zMat)

u3Mat :: Double -> Double -> Double -> [[Complex Double]]
u3Mat t p l =
  [ [ cos (t / 2) :+ 0, negate (cis l) * (sin (t / 2) :+ 0) ]
  , [ cis p * (sin (t / 2) :+ 0), cis (p + l) * (cos (t / 2) :+ 0) ] ]

pMat :: Double -> [[Complex Double]]
pMat t = [ [1, 0], [0, cis t] ]

xMat, zMat :: [[Complex Double]]
xMat = [ [0, 1], [1, 0] ]
zMat = [ [1, 0], [0, -1] ]

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
          (ctrlI, tI) = (take m bitsI, bitsI !! m)
          (ctrlJ, tJ) = (take m bitsJ, bitsJ !! m)
      in if ctrlI == ctrlVals && ctrlJ == ctrlVals
           then gateMat !! tI !! tJ
           else if i == j then 1 else 0

-- | The real-amplitude magnitude tree: one U(theta,0,0) per (level, prefix)
-- with theta = 2*atan2(r1,r0), r0/r1 the norms of the prefix's two
-- sub-vectors of 'mags' at that level's qubit -- the standard recursive
-- construction preparing the vector of magnitudes |u_0|,...,|u_{2^k-1}| from
-- |0..0> on 'qs' (MSB-first, the file's own convention -- 'bitsOfIndex').
-- 'theta = 2*atan2(0,0) = 0' at a prefix whose sub-vector is entirely zero
-- (the parent branch carried no mass there), so that node -- and, since its
-- own children see the same all-zero restriction, every node below it -- is
-- pruned by the identity check with no separate pruning logic.
-- The pruning budget, term by term: a
-- pruned rotation of angle theta moves its branch by 2|sin(theta/4)|, at
-- most |theta|/2, times the branch's mass; a pruned phase line at index i
-- moves the state by 2|sin(theta/2)|*|u_i|, at most |theta|*|u_i|; skipping
-- an index leaves |u_i| for u_i, an error of at most 2|u_i|; and along a
-- circuit of unitary lines the per-line errors ADD. A per-line threshold
-- therefore guarantees nothing about the whole clause unless it is the
-- line's share of the tolerance: with 2^(k+2) + 1 lines in the clause
-- (below), each line may spend 1e-9 / (2^(k+2) + 1), and the pruned clause
-- then stays within the 1e-9 entrywise tolerance the tests use, in operator
-- norm, for every axis -- not only the ones the randomised test happened to
-- draw. Exactly-zero lines (a prefix with no mass, a real positive
-- amplitude) are pruned at any threshold and cost nothing.
pruneShare :: Int -> Double
pruneShare k = 1e-9 / fromIntegral (2 ^ (k + 2) + 1 :: Integer)

prepMagTreeOps :: [Int] -> [Double] -> [Op]
prepMagTreeOps qs mags =
  [ OpU theta 0 0 controls target
  | j <- [0 .. k - 1]
  , prefix <- sequence (replicate j [0, 1])
  , let idxs      = [ i | i <- [0 .. n - 1], take j (bitsOfIndex k i) == prefix ]
  , let idxs0     = [ i | i <- idxs, bitsOfIndex k i !! j == 0 ]
  , let idxs1     = [ i | i <- idxs, bitsOfIndex k i !! j == 1 ]
  , let r0        = sqrt (sum [ (mags !! i) ** 2 | i <- idxs0 ])
  , let r1        = sqrt (sum [ (mags !! i) ** 2 | i <- idxs1 ])
  , let theta     = 2 * atan2 r1 r0
  , let controls  = [ (qs !! t, prefix !! t) | t <- [0 .. j - 1] ]
  , let target    = qs !! j
  , abs theta / 2 > pruneShare k
  ]
  where
    k = length qs
    n = 2 ^ k

-- | The phase fixup: for every basis index i with u_i not (numerically) zero
-- and phase(u_i) not (numerically) 0, a multi-controlled p(phase(u_i)) on a
-- fixed swing qubit (the last one, LSB) -- exactly 'diagCircuit's own
-- pattern (X-conjugate the swing qubit when its own bit of i is 0, so the
-- control pattern on the remaining qubits alone selects i), specialised to a
-- diagonal read off a numeric unit vector u instead of an exact Cyclo
-- matrix. Applied after 'prepMagTreeOps' (which reaches |u|), this reaches u
-- exactly: u_i = |u_i| * e^{i phase(u_i)}.
prepPhaseOps :: [Int] -> [Complex Double] -> [Op]
prepPhaseOps qs u = concat
  [ pre ++ [ OpP theta ctrlBits swing ] ++ pre
  | i <- [0 .. n - 1]
  , 2 * magnitude (u !! i) > pruneShare k
  , let theta = phase (u !! i)
  , abs theta * magnitude (u !! i) > pruneShare k
  , let bits      = bitsOfIndex k i
  , let tBit      = bits !! tPos
  , let ctrlBits  = [ (qs !! p, bits !! p) | p <- [0 .. k - 2] ]
  , let swing     = qs !! tPos
  , let pre       = [ OpX [] swing | tBit == 0 ]
  ]
  where
    k = length qs
    n = 2 ^ k
    tPos = k - 1

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

-- | The general k-qubit (k >= 2) reclaiming reflection, the reclaiming proposition's
-- 'reflectionR psi g' realised as a circuit on 'qs' (MSB-first): V, then the
-- phase flip, then V^dagger, so that (as operators, last-applied leftmost)
-- V^dagger . (I - 2|0..0><0..0|) . V = 'reflectionR psi g' exactly -- no
-- phase fixing needed, since 'prepMagTreeOps' followed by 'prepPhaseOps'
-- prepares u exactly (not merely up to a global phase), and V := (that
-- circuit)^dagger satisfies V u = |0..0> exactly because that circuit is
-- unitary. Line count: V^dagger's magnitude tree has 2^k - 1 nodes and its
-- phase fixup at most 2^k lines (no global phase is factored out, so every
-- index may carry one), V mirrors both, plus the 3-line flip: at most
-- 2^(k+2) + 1 controlled gates, and in the printed text up to 6*2^k + 1
-- lines since a phase line whose swing bit is 0 is spelled x; p; x. Fewer
-- once a node or a phase line is pruned as the identity ('pruneShare').
emitGeneralReflectionOps :: [Int] -> [Complex Double] -> [Complex Double] -> [Op]
emitGeneralReflectionOps qs psi g =
  let (_, w, wnorm2) = gTildeAndW psi g
      wnorm = sqrt wnorm2
      u = map (/ (wnorm :+ 0)) w
      prepU = prepMagTreeOps qs (map magnitude u) ++ prepPhaseOps qs u  -- = V^dagger
      vOps  = map adjointOp (reverse prepU)                              -- = V
  in vOps ++ phaseFlipOps qs ++ prepU

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
       else
         let wnorm = sqrt wnorm2
             u = map (/ (wnorm :+ 0)) w
             support = [ i | (i, x) <- zip [0 :: Int ..] u, magnitude x > 1e-12 ]
         in case support of
              [a, b] ->
                let k = length qs
                    bitsA = bitsOfIndex k a
                    bitsB = bitsOfIndex k b
                    diffIdx = [ i | i <- [0 .. k - 1], bitsA !! i /= bitsB !! i ]
                in case diffIdx of
                     [] -> Nothing  -- a == b: cannot happen, support indices are distinct
                     (m : _) ->
                       let zeroIdx = if bitsA !! m == 0 then a else b
                           oneIdx  = if zeroIdx == a then b else a
                           alpha   = u !! zeroIdx
                           beta    = u !! oneIdx
                           others  = [ i | i <- [0 .. k - 1], i /= m ]
                           zBits   = bitsOfIndex k zeroIdx
                           pattern = [ (qs !! i, zBits !! i) | i <- others ]
                           alignOps = [ OpX [(qs !! m, 1)] (qs !! i) | i <- diffIdx, i /= m ]
                           -- rows orthonormal, (alpha, beta) |-> (0, 1)
                           mMat = [ [negate beta, alpha]
                                  , [conjugate alpha, conjugate beta] ]
                           (theta, phi, lam) = u3OfMatrix mMat
                           rotOp = OpU theta phi lam [] (qs !! m)
                           flipOps = [ OpZ pattern (qs !! m) ]
                           undoAlign = reverse (map adjointOp alignOps)
                       in Just (alignOps ++ [rotOp] ++ flipOps ++ [adjointOp rotOp] ++ undoAlign)
              _ -> Nothing

-- ---------------------------------------------------------------------
-- Errors
-- ---------------------------------------------------------------------

data CompileError
  = NonPowerOfTwo Name Int
  | GateNotInDomain [Name] String
  | DropOutsideFragment [Name] String
  | NotWellTyped String
  | OutsideFragment String
  | Other String
  deriving (Eq, Show)

showCompileError :: CompileError -> String
showCompileError e = case e of
  NonPowerOfTwo x d -> "register " ++ x ++ " has dimension " ++ show d ++ ", not a power of two"
  GateNotInDomain xs msg -> "gate on " ++ unwords xs ++ " is not in the compile domain (" ++ msg ++ ")"
  DropOutsideFragment xs msg -> "drop " ++ tupleText xs ++ " is outside the compilation fragment: " ++ msg
  NotWellTyped msg -> "type error: " ++ msg
  OutsideFragment msg -> "outside the compilation fragment: " ++ msg
  Other s -> s
  where
    tupleText [x] = x
    tupleText xs = "(" ++ intercalate ", " xs ++ ")"

-- | What every entry point of the compiler asks of a program before it lays
-- it out. First the statics and the loan discipline ('checkProgram'): a term
-- that was built directly, not parsed, may name a dropped wire or return a
-- loan, and the layout below would give it qubits all the same. Then three
-- rules of the parser that the statics do not impose, because the paper's
-- If rule lets a branch allocate, lift and drop: the compiler lays out one
-- branch for both, keys its layout by name and its safety table by site id,
-- so it needs no binder in a branch, every name bound once, and a site id
-- per surface drop.
compileFragment :: Program Cyclo -> Either CompileError ()
compileFragment prog = do
  either (Left . NotWellTyped . showTypeError) (const (Right ())) (checkProgram prog)
  case [ st | st <- inBranch False (progTerm prog), binder st ] of
    (st : _) -> Left (OutsideFragment (stmtWord st ++ " inside an if branch"))
    []       -> Right ()
  let names = map fst (progCtx prog) ++ [ x | st <- inBranch True (progTerm prog), Just x <- [stmtBinds st] ]
  case [ x | (i, x) <- zip [0 :: Int ..] names, x `elem` take i names ] of
    (x : _) -> Left (OutsideFragment ("the name " ++ x ++ " is bound twice"))
    []      -> Right ()
  let sites = [ i | StDrop i _ <- inBranch True (progTerm prog) ]
  case [ i | (k, i) <- zip [0 :: Int ..] sites, i `elem` take k sites ] of
    (i : _) -> Left (OutsideFragment ("two drops carry the site id " ++ show i))
    []      -> Right ()
  where
    -- the statements of a surface term: with True all of them, with False
    -- only those under an if
    inBranch top t = case t of
      SReturn _      -> []
      SDo st m       -> [ st | top ] ++ inBranch top m
      SIf _ m1 m2    -> inBranch True m1 ++ inBranch True m2
      SBlock _ m1 m2 -> inBranch top m1 ++ inBranch top m2
    binder st = case st of
      StGate {} -> False
      _         -> True
    stmtWord st = case st of
      StNew {}  -> "new"
      StLoan {} -> "loan"
      StLift {} -> "lift"
      StDrop {} -> "drop"
      StGate {} -> "gate"

-- ---------------------------------------------------------------------
-- Layout: qubits, classical bits, and every drop's lift-depth.
-- ---------------------------------------------------------------------

data LayoutInfo = LayoutInfo
  { liWireQ       :: Map Name [Int]         -- MSB-first physical qubit indices
  , liWireDim     :: Map Name Int
  , liWireAlloc   :: Map Name [Complex Double]  -- allocation vector psi, 'new'-bound wires only
  , liLiftInfo    :: Map Name (Int, Int)    -- param -> (classical bit index, qasm value meaning "survived")
  , liLiftAncilla :: Map Name Int           -- param -> ancilla qubit index (block-lift form only)
  , liSiteDepth   :: Map SiteId Int
  , liTotalQubits :: Int
  , liTotalBits   :: Int
  } deriving Show

isPow2 :: Int -> Bool
isPow2 n = n >= 2 && (n .&. (n - 1)) == 0

ilog2 :: Int -> Int
ilog2 n = go n 0 where go 1 acc = acc; go m acc = go (m `div` 2) (acc + 1)

data LayoutSt = LayoutSt
  { lsNextQubit   :: Int
  , lsNextBit     :: Int
  , lsWireQ       :: Map Name [Int]
  , lsWireDim     :: Map Name Int
  , lsWireAlloc   :: Map Name [Complex Double]
  , lsLiftInfo    :: Map Name (Int, Int)
  , lsLiftAncilla :: Map Name Int
  , lsSiteDepth   :: Map SiteId Int
  }

layoutProgram :: Program Cyclo -> Either CompileError LayoutInfo
layoutProgram prog = do
  compileFragment prog
  let vis = progCtx prog
      st0 = LayoutSt 0 0 Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty
  st1 <- foldEither addVis st0 vis
  stF <- layoutTerm 0 st1 (toTerm (progTerm prog))
  Right LayoutInfo
    { liWireQ = lsWireQ stF, liWireDim = lsWireDim stF, liWireAlloc = lsWireAlloc stF
    , liLiftInfo = lsLiftInfo stF, liLiftAncilla = lsLiftAncilla stF, liSiteDepth = lsSiteDepth stF
    , liTotalQubits = lsNextQubit stF, liTotalBits = lsNextBit stF
    }
  where
    foldEither f = go where go st [] = Right st; go st (x : xs) = f st x >>= \st' -> go st' xs
    addVis st (n, d)
      | not (isPow2 d) = Left (NonPowerOfTwo n d)
      | otherwise =
          let k = ilog2 d
              qs = [lsNextQubit st .. lsNextQubit st + k - 1]
          in Right st { lsNextQubit = lsNextQubit st + k
                      , lsWireQ = Map.insert n qs (lsWireQ st)
                      , lsWireDim = Map.insert n d (lsWireDim st) }

    layoutTerm :: Int -> LayoutSt -> Term Cyclo -> Either CompileError LayoutSt
    layoutTerm depth st term = case term of
      Return _ -> Right st
      Do (StGate _ _) m -> layoutTerm depth st m
      Do (StNew nm d psi) m -> do
        if not (isPow2 d) then Left (NonPowerOfTwo nm d) else Right ()
        let k = ilog2 d
            qs = [lsNextQubit st .. lsNextQubit st + k - 1]
            st' = st { lsNextQubit = lsNextQubit st + k
                     , lsWireQ = Map.insert nm qs (lsWireQ st)
                     , lsWireDim = Map.insert nm d (lsWireDim st)
                     , lsWireAlloc = Map.insert nm (map toC psi) (lsWireAlloc st) }
        layoutTerm depth st' m
      -- A loan has no allocation vector to record: it is a genuine input
      -- register (Drop.Lang.Interp's "Loans" section), laid out exactly like
      -- 'StNew' otherwise.
      Do (StLoan nm d) m -> do
        if not (isPow2 d) then Left (NonPowerOfTwo nm d) else Right ()
        let k = ilog2 d
            qs = [lsNextQubit st .. lsNextQubit st + k - 1]
            st' = st { lsNextQubit = lsNextQubit st + k
                     , lsWireQ = Map.insert nm qs (lsWireQ st)
                     , lsWireDim = Map.insert nm d (lsWireDim st) }
        layoutTerm depth st' m
      Do (StDrop site _) m ->
        layoutTerm depth (st { lsSiteDepth = Map.insert site depth (lsSiteDepth st) }) m
      -- A lift binds no register: x stays live under its own name, so there
      -- is no second wire to give the first one's qubits to.
      Do (StLift pname s x) m -> do
        d <- maybe (Left (Other ("Drop.Lang.Compile: unknown wire " ++ x))) Right (Map.lookup x (lsWireDim st))
        let direct = d == 2 && (s == [0] || s == [1])
            sv = if s == [1] then 1 else 0
            bitIdx = lsNextBit st
            st1 = st { lsNextBit = bitIdx + 1 }
        (anc, st2) <- if direct
                        then Right (Nothing, st1)
                        else Right (Just (lsNextQubit st1), st1 { lsNextQubit = lsNextQubit st1 + 1 })
        let st3 = st2 { lsLiftInfo = Map.insert pname (bitIdx, if direct then sv else 1) (lsLiftInfo st2) }
            st4 = case anc of
                    Just a  -> st3 { lsLiftAncilla = Map.insert pname a (lsLiftAncilla st3) }
                    Nothing -> st3
        layoutTerm (depth + 1) st4 m
      If _ m1 _ -> layoutTerm depth st m1  -- resources are branch-invariant ('compileFragment': no alloc/lift/drop in a branch)

-- ---------------------------------------------------------------------
-- Safety: per drop site, per full record, SAFE (certificate) / UNSAFE /
-- unreachable -- reusing Drop.Lang.Machine's per-leaf
-- SiteRecord and Drop.Lang.QState's factorSplit/canonicalLine exactly as
-- Drop.Lang.Interp's probeResult/semanticVerdict do.
-- ---------------------------------------------------------------------

-- | A temporary's certificate is the line it is left constant on
-- ('SafeCert', unchanged from before the loan redesign); a block holding a
-- loan carries instead the isometry B its drop reclaims with ('SafeIso',
-- B : H_loan -> H_block of the site definition's clause (3) -- square when the block is
-- its loans and nothing else, taller than wide when temporaries sit beside
-- them).
data SafetyOutcome = SafeCert (StateV Cyclo) | SafeIso (Matrix Cyclo)
                   | UnsafeOutcome | UnreachableOutcome
  deriving (Eq, Show)

data ProbeAtSite = PZero' | PFail' | PLine' (StateV Cyclo) deriving (Eq, Show)

type SafetyInfo = Map SiteId (Map [(Name, Int)] SafetyOutcome)

probeOutcome :: SiteRecord Cyclo -> ProbeAtSite
probeOutcome rec_
  | isZeroS (srAmp rec_) = PZero'
  | otherwise = case factorSplitOrd (srDims rec_) regsA (srAmp rec_) of
      Nothing      -> PFail'
      Just (vA, _) -> PLine' (canonicalLine vA)
  where
    -- The block's machine positions in the order the drop names its
    -- registers ('srHidden'), so the certificate is indexed as the
    -- allocation state 'psi' and the qubit list of 'compileDrop' are: a
    -- tuple dropped out of allocation order reads the same way everywhere.
    regsA = [ i | n <- srHidden rec_, (i, nm) <- zip [0 ..] (srNames rec_), nm == n ]

aggregate :: [ProbeAtSite] -> SafetyOutcome
aggregate prs = case live of
  []                                        -> UnreachableOutcome
  _ | all isLine live, (l : _) <- lns, allSameLine lns -> SafeCert l
    | otherwise                             -> UnsafeOutcome
  where
    live = [ p | p <- prs, p /= PZero' ]
    isLine (PLine' _) = True
    isLine _          = False
    lns = [ l | PLine' l <- live ]
    allSameLine [] = True
    allSameLine (x : xs) = all (== x) xs

-- | Every name a loan binds, with its dimension (structural scan; an
-- @if@'s branches are resource-invariant -- 'compileFragment' -- so
-- either one, or their union, sees every loan).
loanBindersOf :: Term a -> [(Name, Int)]
loanBindersOf term = case term of
  Return _             -> []
  Do (StLoan x d) m    -> (x, d) : loanBindersOf m
  Do _ m               -> loanBindersOf m
  If _ m1 m2           -> loanBindersOf m1 ++ loanBindersOf m2

-- | The registers each 'drop' occurrence names, by site id, in the order it
-- names them -- a tuple drop is ONE site (the composite-temporary proposition), so the entry is a
-- list, and a block that holds a loan is recognised as a loan site below
-- whether it is that loan alone or that loan beside other registers.
dropTargetsOf :: Term a -> Map SiteId [Name]
dropTargetsOf term = case term of
  Return _ -> Map.empty
  Do (StDrop site v) m -> Map.insert site (valueNames v) (dropTargetsOf m)
  Do _ m -> dropTargetsOf m
  If _ m1 m2 -> Map.union (dropTargetsOf m1) (dropTargetsOf m2)

computeSafety :: Program Cyclo -> Term Cyclo -> Map SiteId Int -> SafetyInfo
computeSafety prog core siteDepthMap =
  Map.unionWith Map.union tempInfo loanInfo
  where
    vis = progCtx prog
    loanNames = map fst (loanBindersOf core)
    dTargets  = dropTargetsOf core
    isLoanSite s = maybe False (any (`elem` loanNames)) (Map.lookup s dTargets)

    -- The temporary path (New/NewState targets), restricted to sites that
    -- are not a loan. A program mixing a loan with a temporary needs the
    -- loan's own value run through to reach every temp site at all, and
    -- the site definition makes that loan a factor of the site map's domain
    -- [[Omega]], so the probe space is every basis arrival of every loan
    -- crossed with the dim+1 visible probes -- exactly
    -- Drop.Lang.Interp.tempProbes' space, so the two engines decide these
    -- sites alike. Seeding every loan at |0> instead would call a temporary
    -- safe whenever it is safe on a |0> loan, and `new t; CX a t; drop t`
    -- is safe on a |0> loan and unsafe on any other.
    loanEnvs0 = loanEnvs (loanBindersOf core) :: [[(Name, StateV Cyclo)]]
    probes = map snd (probesFor vis) :: [StateV Cyclo]
    raw =
      [ (site, prefix, probeOutcome rec_)
      | loanEnv <- loanEnvs0
      , inp <- probes
      , leaf <- run (initConfigL vis inp loanEnv core)
      , rec_ <- cfgSites leaf
      , let site = srSite rec_
      , not (isLoanSite site)
      , Just depth <- [Map.lookup site siteDepthMap]
      , let prefix = take depth (cfgBits leaf)
      , length prefix == depth
      ]
    grouped = Map.fromListWith (++) [ ((site, prefix), [pr]) | (site, prefix, pr) <- raw ]
    tempInfo = Map.fromListWith Map.union
      [ (site, Map.singleton prefix (aggregate prs))
      | ((site, prefix), prs) <- Map.toList grouped
      ]

    -- The loan path: reuses Drop.Lang.Interp's own loan criterion exactly
    -- (via 'elabE'; in this domain a loan is dropped before the first lift
    -- and the first if, so its verdict at the empty record prefix is its
    -- verdict on every record), so the emitted
    -- circuit's safety decision is the one and only implementation of the
    -- criterion, not a second one that could drift from it. Only the
    -- depth-0 (no lift before the loan) case is populated: 'fragmentSafety'
    -- refuses every program that drops a loan after a lift or an if before
    -- this map is asked for, and 'compileDrop' only ever looks up the prefix
    -- matching the site's own (structural) depth.
    loanInfo = Map.fromList
      [ (site, Map.singleton ([] :: [(Name, Int)]) (loanOutcomeFor names))
      | (site, names) <- Map.toList dTargets, any (`elem` loanNames) names
      ]
    loanOutcomeFor names = case elabE core of
      Left _ -> UnsafeOutcome
      Right flatProg -> case semanticVerdictS vis flatProg names [] of
        Safe -> case semanticLoanCertS vis flatProg names [] of
          Just b  -> SafeIso b
          Nothing -> UnsafeOutcome
        Unreachable -> UnreachableOutcome
        Unsafe -> UnsafeOutcome

-- ---------------------------------------------------------------------
-- The fragment's conditions on drops, checked before any drop is emitted.
-- ---------------------------------------------------------------------

-- | Every drop naming a loan that follows a lift or sits in an arm of an
-- if, once each. The loan criterion ('computeSafety', through
-- Drop.Lang.Interp.loanResultS) runs the expanded term with no lift
-- outcomes, and the expansion copies an if's continuation into both arms,
-- where Drop.Lang.Interp.runStmts does not look for the site; so these
-- drops have no verdict here, and asking for one stops the program.
lateLoanDrops :: [Name] -> Term a -> [[Name]]
lateLoanDrops loans = nub . go False
  where
    go _ (Return _) = []
    go late (Do (StDrop _ v) m)
      | late, any (`elem` loans) (valueNames v) = valueNames v : go late m
    go _ (Do (StLift {}) m) = go True m
    go late (Do _ m) = go late m
    go _ (If _ m1 m2) = go True m1 ++ go True m2

-- | Every drop naming an input not marked @loan@ whose site is safe, with a
-- nonzero site map, on some record: 'isSafe' counts 'SafeCert' and 'SafeIso' only, and a
-- record on which the site map is zero is 'UnreachableOutcome', which does not
-- count (unmunreach.s compiles). A reclaiming gate returns a temporary to its allocation state and
-- hands a loan back to the caller; such an input has neither, so no
-- reclaiming gate is defined for it. An unsafe drop of one emits no gate,
-- like any unsafe drop, and is not refused.
unmarkedSafeDrops :: [(Name, Int)] -> Term a -> SafetyInfo -> [[Name]]
unmarkedSafeDrops vis core safety =
  [ names
  | (site, names) <- Map.toList (dropTargetsOf core)
  , any (`elem` map fst vis) names
  , any isSafe (Map.elems (Map.findWithDefault Map.empty site safety)) ]
  where
    isSafe (SafeCert _) = True
    isSafe (SafeIso _)  = True
    isSafe _            = False

-- | The safety map of a program in the fragment, or the refusal of its
-- first drop outside it. The late loans are refused first, before the map
-- is built: the map is strict, and building it asks for their verdicts.
fragmentSafety :: Program Cyclo -> Term Cyclo -> LayoutInfo -> Either CompileError SafetyInfo
fragmentSafety prog core layout =
  case lateLoanDrops (map fst (loanBindersOf core)) core of
    (xs : _) -> Left (DropOutsideFragment xs
                  "it drops a loan after a lift or an if, and this compiler decides a loan's drop only before both")
    [] ->
      let safety = computeSafety prog core (liSiteDepth layout)
      in case unmarkedSafeDrops (progCtx prog) core safety of
           (xs : _) -> Left (DropOutsideFragment xs
                         "it drops an input not marked loan at a site that is safe, with a nonzero site \
                         \map, on some record, and a reclaiming gate is defined only for temporaries and loans")
           [] -> Right safety

-- ---------------------------------------------------------------------
-- QASM text helpers
-- ---------------------------------------------------------------------

qArg :: Int -> String
qArg i = "q[" ++ show i ++ "]"

qArgs :: [Int] -> String
qArgs = intercalate ", " . map qArg

-- | An exact multiple of pi/8 -- the domain's convention for 8th and 16th
-- roots of unity -- printed in lowest terms: @pi@, @-pi/2@, @3*pi/8@, @2*pi@.
-- Anything else is a decimal.  OpenQASM 3 has @pi@ as a built-in constant, so
-- the reduced form is both shorter and what a reader expects; @8*pi/8@ is @pi@.
angleLabel :: Double -> String
angleLabel t =
  let k  = t / (pi / 8)
      kr = fromIntegral (round k :: Integer) :: Double
  in if abs (k - kr) < 1e-6 then eighths (round kr) else printf "%.12f" t
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

modifiersFor :: [(Int, Int)] -> String
modifiersFor = concatMap (\(_, b) -> if b == 1 then "ctrl @ " else "negctrl @ ")

bitsOfIndex :: Int -> Int -> [Int]
bitsOfIndex k x = [ if testBit x (k - 1 - i) then 1 else 0 | i <- [0 .. k - 1] ]

-- ---------------------------------------------------------------------
-- Gate recognition and emission -- the domain table.
-- ---------------------------------------------------------------------

isDiagonalMatrix :: Matrix Cyclo -> Bool
isDiagonalMatrix g =
  let n = length g
  in all ((== n) . length) g && and [ g !! i !! j == 0 | i <- [0 .. n - 1], j <- [0 .. n - 1], i /= j ]

diagEntriesOf :: Matrix Cyclo -> [Cyclo]
diagEntriesOf g = [ g !! i !! i | i <- [0 .. length g - 1] ]

permOfMat :: Matrix Cyclo -> Maybe [Int]
permOfMat g
  | all ((== n) . length) g = do
      imgs <- mapM colImg [0 .. n - 1]
      if length (nub imgs) == n then Just imgs else Nothing
  | otherwise = Nothing
  where
    n = length g
    colImg j = case [ i | i <- [0 .. n - 1], g !! i !! j /= 0 ] of
      [i] | g !! i !! j == 1 -> Just i
      _                      -> Nothing

-- | 'permOfMat' over the numeric field, for a matrix already normalised to
-- a unitary: the image list of the permutation it realises, or 'Nothing'.
permOfMatC :: [[Complex Double]] -> Maybe [Int]
permOfMatC m
  | not (null m) && all ((== n) . length) m = do
      imgs <- mapM colImg [0 .. n - 1]
      if length (nub imgs) == n then Just imgs else Nothing
  | otherwise = Nothing
  where
    n = length m
    colImg j = case [ i | i <- [0 .. n - 1], magnitude (m !! i !! j) > 1e-6 ] of
      [i] | magnitude (m !! i !! j - 1) < 1e-6 -> Just i
      _                                        -> Nothing

-- | The inverse of a permutation given as an image list.
inversePerm :: [Int] -> [Int]
inversePerm imgs = [ j | i <- [0 .. length imgs - 1]
                   , j <- take 1 [ k | (k, v) <- zip [0 ..] imgs, v == i ] ]

diagOfList :: [Cyclo] -> Matrix Cyclo
diagOfList xs = [ [ if i == j then xs !! i else 0 | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
  where n = length xs

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
      where n = 2 ^ (k - 1); get 0 = cs !! 0; get i = negate (cs !! (n - i))

cpOf :: Matrix Cyclo -> Maybe (Complex Double)
cpOf g
  | length g == 4, isDiagonalMatrix g
  , [d0, d1, d2, d3] <- diagEntriesOf g
  , d0 == 1, d1 == 1, d2 == 1
  = Just (toC d3)
  | otherwise = Nothing

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
      let nxt = imgs !! last acc
      in if nxt == start then acc else chase start (acc ++ [nxt])

cycleToTranspositions :: [Int] -> [(Int, Int)]
cycleToTranspositions cyc = [ (cyc !! i, cyc !! (i + 1)) | i <- [m - 2, m - 3 .. 0] ]
  where m = length cyc

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
    diffIdx = [ i | i <- [0 .. k - 1], bitsA !! i /= bitsB !! i ]
    m = case diffIdx of
          (i : _) -> i
          []      -> error "Drop.Lang.Compile.transpositionLines: a == b"
    zeroState = if bitsA !! m == 0 then bitsA else bitsB
    others = [ i | i <- [0 .. k - 1], i /= m ]
    alignCNOTs = [ "cx " ++ qArgs [qs !! m, qs !! i] ++ ";" | i <- diffIdx, i /= m ]
    ctrlBits = [ (qs !! i, zeroState !! i) | i <- others ]
    ctrlLine = modifiersFor ctrlBits ++ "x " ++ qArgs (map fst ctrlBits ++ [qs !! m]) ++ ";"

permCircuit :: [Int] -> [Int] -> [String]
permCircuit qs imgs = concatMap (transpositionLines qs) (concatMap cycleToTranspositions (cyclesOf imgs))

-- | Multi-controlled phase gates, one per basis state whose diagonal entry
-- is not 1 (the compiler's stated
-- domain, the compilation subsection): a fixed "swing" qubit (the last one) carries the phase gate,
-- X-conjugated when the pattern's bit there is 0, all other qubits become
-- ctrl/negctrl controls at their pattern bit.
diagCircuit :: [Int] -> Matrix Cyclo -> [String]
diagCircuit qs mat = concat [ phaseGateFor i (entries !! i) | i <- [0 .. d - 1], entries !! i /= 1 ]
  where
    d = length mat
    k = length qs
    entries = diagEntriesOf mat
    tPos = k - 1
    phaseGateFor i z =
      let bits = bitsOfIndex k i
          theta = phase (toC z)
          tBit = bits !! tPos
          ctrlBits = [ (qs !! p, bits !! p) | p <- [0 .. k - 2] ]
          pre = [ "x " ++ qArg (qs !! tPos) ++ ";" | tBit == 0 ]
          line = modifiersFor ctrlBits ++ "p(" ++ angleLabel theta ++ ") "
                 ++ qArgs (map fst ctrlBits ++ [qs !! tPos]) ++ ";"
      in pre ++ [line] ++ pre

u3Circuit :: [Int] -> [[Complex Double]] -> [String]
u3Circuit [q] m
  | isApproxIdentity m = []
  | otherwise =
      let (theta, phi, lam) = u3OfMatrix m
      in [ "U(" ++ angleLabel theta ++ ", " ++ angleLabel phi ++ ", " ++ angleLabel lam ++ ") " ++ qArg q ++ ";" ]
u3Circuit _ _ = error "u3Circuit: not a single qubit"

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
        | length qs == 1 -> Right (u3Circuit qs (matC mat))
        | otherwise -> Left (GateNotInDomain names "not diagonal, a permutation, or a single-qubit unitary")

-- ---------------------------------------------------------------------
-- new: clean preparation, or a non-basis temporary whose preparation is assumed.
-- ---------------------------------------------------------------------

basisIndexOfExact :: StateV Cyclo -> Maybe Int
basisIndexOfExact psi = case [ i | (i, c) <- zip [0 ..] psi, c /= 0 ] of
  [i] | psi !! i == 1 -> Just i
  _                   -> Nothing

compileNew :: Name -> Int -> StateV Cyclo -> [Int] -> [String]
compileNew x d psi qs = case basisIndexOfExact psi of
  Just i0 ->
    let k = ilog2 d
        bits = bitsOfIndex k i0
    in [ "x " ++ qArg q ++ ";" | (q, b) <- zip qs bits, b == 1 ]
  Nothing ->
    [ "// temporary " ++ x ++ ", preparation of psi assumed (not emitted): (" ++ intercalate ", " (map showC psi) ++ ")" ]
  where showC c = show (toC c)

-- | A loan: an input register with no declared state at all (unlike
-- 'compileNew's non-basis case, which at least names psi), so nothing is
-- emitted to prepare it -- the circuit's own qubit register is exactly
-- where the loan lands, whatever state that is (Drop.Lang.Interp's "Loans"
-- section: it joins the input context the same way a visible register
-- does).
compileLoan :: Name -> [String]
compileLoan x = [ "// input register " ++ x ++ ", a loan: arrives in a state this program does not know" ]

-- ---------------------------------------------------------------------
-- lift: the direct single-qubit rule, or the block form.
-- ---------------------------------------------------------------------

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

-- ---------------------------------------------------------------------
-- if/else: a boolean over lift-bound bits to an OpenQASM 3 condition.
-- ---------------------------------------------------------------------

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

indent :: [String] -> [String]
indent = map ("  " ++)

-- ---------------------------------------------------------------------
-- drop: the reclaiming gate on a safe record, nothing on an unsafe one.
-- ---------------------------------------------------------------------

kron :: Num a => [a] -> [a] -> [a]
kron xs ys = [ x * y | x <- xs, y <- ys ]

compileDrop :: LayoutInfo -> SafetyInfo -> [(Name, Int)] -> SiteId -> [Name] -> Either CompileError [String]
-- @drop ()@: a block of dimension one, safe with the unit scalar as its
-- certificate (the site definition's clause (1)) and nothing to reclaim -- the reclaiming gate
-- is the identity on no qubit.
compileDrop _ _ _ _ [] = Right [ "// drop (): nothing to reclaim" ]
compileDrop layout safety fixedBits site names = do
  qs <- Right (concatMap (\n -> Map.findWithDefault [] n (liWireQ layout)) names)
  -- A loan has no allocation vector (it arrives in whatever state the
  -- caller holds), so it contributes the scalar 1: 'psi' is the allocation
  -- state of the block's temporaries, in the drop's order.
  psi <- Right (foldr kron [1] [ Map.findWithDefault [1] n (liWireAlloc layout) | n <- names ])
  -- A register without an allocation vector is a loan or an input not
  -- marked loan; 'fragmentSafety' has refused every safe site naming the
  -- latter, so at a site that emits a gate it is a loan.
  let isLoan n = not (Map.member n (liWireAlloc layout))
      kinds  = [ (Map.findWithDefault 1 n (liWireDim layout), isLoan n) | n <- names ]
      qsLoan = concat [ Map.findWithDefault [] n (liWireQ layout) | n <- names, isLoan n ]
      qsTemp = concat [ Map.findWithDefault [] n (liWireQ layout) | n <- names, not (isLoan n) ]
      depth = Map.findWithDefault 0 site (liSiteDepth layout)
      siteMap = Map.findWithDefault Map.empty site safety
      fixedNames = map fst fixedBits
      consistentWith prefix = all (\(n, v) -> lookup n prefix == Just v) fixedBits
      openOf prefix = [ nb | nb@(n, _) <- prefix, n `notElem` fixedNames ]
      relevant = [ (openOf prefix, outcome)
                 | (prefix, outcome) <- Map.toList siteMap
                 , length prefix == depth, consistentWith prefix ]
      label = intercalate "," names
  case relevant of
    [] -> Right [ "// drop " ++ label ++ ": unreachable on this record" ]
    _  ->
      let outcomes = nub (map snd relevant)
      in case outcomes of
           [SafeCert cert] -> emitReclaim label qs psi cert
           [SafeIso bMat]            -> emitReclaimIso label qs qsLoan qsTemp kinds psi bMat
           [UnsafeOutcome]           -> Right [ "// " ++ label ++ " dropped unsafe: stays live" ]
           [UnreachableOutcome]      -> Right [ "// drop " ++ label ++ ": unreachable on this record" ]
           _ -> fmap concat (mapM (emitGroup label qs qsLoan qsTemp kinds psi) relevant)
  where
    emitGroup label qs qsLoan qsTemp kinds psi (openBits, outcome) = case outcome of
      UnreachableOutcome -> Right []
      UnsafeOutcome -> Right [ "// " ++ label ++ " dropped unsafe on record "
                                ++ show openBits ++ ": stays live" ]
      SafeIso bMat -> do
        body <- emitReclaimIso label qs qsLoan qsTemp kinds psi bMat
        if null body then Right [] else
          let cond = intercalate " && "
                       [ "c[" ++ show idx ++ "] == " ++ show (if b == 1 then sv else 1 - sv)
                       | (n, b) <- openBits
                       , let (idx, sv) = Map.findWithDefault (0, 1) n (liLiftInfo layout) ]
          in Right (["if (" ++ (if null cond then "true" else cond) ++ ") {"] ++ indent body ++ ["}"])
      SafeCert cert -> do
        body <- emitReclaim label qs psi cert
        if null body then Right [] else
          -- 'b' is the record's "1 = survived" flag (Drop.Lang.Machine's own
          -- convention, cfgBits); 'sv' is the *raw* qasm-measured value
          -- that means "survived" for this lift (liLiftInfo). The two
          -- share {0,1} but are not the same bit: translate, do not compare.
          let cond = intercalate " && "
                       [ "c[" ++ show idx ++ "] == " ++ show (if b == 1 then sv else 1 - sv)
                       | (n, b) <- openBits
                       , let (idx, sv) = Map.findWithDefault (0, 1) n (liLiftInfo layout) ]
          in Right (["if (" ++ (if null cond then "true" else cond) ++ ") {"] ++ indent body ++ ["}"])

    emitReclaim _label qs psi cert =
      let gRaw = map toC cert
          -- 'cert' is Drop.Lang.QState.canonicalLine's representative of the
          -- certificate ray (first nonzero coordinate scaled to 1), not a
          -- unit vector; 'reflectionR' needs a unit g.  That representative is
          -- NOT the one the gate is built from: 'reflectionR' re-phases g
          -- against psi itself (gTildeAndW multiplies by e^-i*arg<psi,g>, so
          -- <psi,g~> is real and nonnegative, with the first-nonzero tie-break
          -- only when <psi,g> = 0).  That is the paper's convention, sec 3.6.
          -- Which representative reaches this line therefore does not matter;
          -- only the ray does.
          gNorm = sqrt (sum [ magnitude z ** 2 | z <- gRaw ])
          g = if gNorm < 1e-12 then gRaw else map (/ (gNorm :+ 0)) gRaw
          r = reflectionR psi g
      in if length qs == 1
           then Right (u3Circuit qs r)
           else case (basisIndexOfC psi, basisIndexOfC g) of
                  (Just i, Just j)
                    | i == j    -> Right []
                    | otherwise -> Right (transpositionLines qs (i, j))
                  _ | proportionalTo psi g -> Right []
                    | otherwise -> Right (map renderOp
                        (fromMaybe (emitGeneralReflectionOps qs psi g)
                                   (emitTwoSupportReflectionOps qs psi g)))

    -- | A block holding a loan reclaims with B^dagger directly: unlike a
    -- temporary, there is no known psi to reflect from, so the reclaiming proposition's
    -- Householder construction does not apply -- the block factor B of
    -- the site definition's clause (3) already is the map the drop needs undone. B is
    -- fixed only up to a positive scale by the factorization
    -- (Drop.Lang.Interp.loanResultS), so it is normalised before any angle is
    -- read off it ('normaliseSquareIso').
    --
    -- A square B (the block is its loans and nothing else) is emitted in
    -- three shapes and no other ('squareFactorEmittable'): B the identity
    -- (nothing to undo), B on one qubit (a U(theta,phi,lambda)), and B a
    -- permutation of the basis states (the inverse permutation, through the
    -- same transposition circuit the temporary path uses). A rectangular B
    -- -- the block holds temporaries beside its loans, so H_block is bigger
    -- than H_loan -- is emitted when it is a product B' (x) g~ of a square
    -- factor on the loans of one of those three shapes and a certificate on
    -- the temporaries ('splitMixedFactor'): B'^dagger on
    -- the loan qubits, then the reclaiming reflection through psi - g~ on
    -- the temporary qubits, the two acting on disjoint registers
    -- and therefore commuting. Every other
    -- B -- a square factor on several qubits, or a rectangular one that
    -- entangles the loans with the temporaries -- leaves the block live
    -- with a "not emitted" comment: this compiler synthesises no general
    -- isometry, and it emits a block whole or not at all.
    emitReclaimIso label qs qsLoan qsTemp kinds psi bMat
      | square = squareIso qs bN
      | Just (bPrime, gT) <- splitMixedFactor kinds bMat
      , let bPN = normaliseSquareIso (matC bPrime)
      , squareFactorEmittable bPN = do
          loanLines <- squareIso qsLoan bPN
          tempLines <- emitReclaim label qsTemp psi gT
          Right (loanLines ++ tempLines)
      | Just _ <- splitMixedFactor kinds bMat =
          Right [ "// reclaim of " ++ label ++ " not emitted: the loan factor of \
                  \B = B' (x) g is on more than one qubit" ]
      | otherwise =
          Right [ "// reclaim of " ++ label ++ " not emitted: B : H_loan -> H_block \
                  \entangles the loans with the temporaries beside them" ]
      where
        bC     = matC bMat
        n      = length bC
        square = not (null bC) && all ((== n) . length) bC
        bN     = normaliseSquareIso bC
        -- the three square shapes, on the given qubits; @m@ normalised
        squareIso qsq m
          | isApproxIdentity m = Right []
          | length qsq == 1 = Right (u3Circuit qsq (daggerC m))
          | Just imgs <- permOfMatC m =
              Right (concatMap (concatMap (transpositionLines qsq) . cycleToTranspositions)
                               (cyclesOf (inversePerm imgs)))
          | otherwise = Right [ "// reclaim of " ++ label ++ " not emitted: the loan's B is on more than one qubit" ]

-- ---------------------------------------------------------------------
-- Structural recursion, emission.
-- ---------------------------------------------------------------------

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
    rest <- compileTerm layout safety atReturn fixedBits m
    Right (compileNew nm d psi qs ++ rest)
  Do (StLoan nm _) m -> do
    rest <- compileTerm layout safety atReturn fixedBits m
    Right (compileLoan nm ++ rest)
  Do (StDrop site v) m -> do
    dl <- compileDrop layout safety fixedBits site (valueNames v)
    rest <- compileTerm layout safety atReturn fixedBits m
    Right (dl ++ rest)
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

-- ---------------------------------------------------------------------
-- Top level.
-- ---------------------------------------------------------------------

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
  ]
  ++ [ "gate diff a, b { h a; h b; x a; x b; cz a, b; x a; x b; h a; h b; }   // Grover diffusion, up to global phase"
     | usesDiff ]
  ++ [ "qubit[" ++ show (liTotalQubits layout) ++ "] q;" ]
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

wireQubits :: LayoutInfo -> Name -> [Int]
wireQubits layout n = Map.findWithDefault [] n (liWireQ layout)

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

-- | The value each leaf of a term returns, left to right.
returnsOf :: Term a -> [Value]
returnsOf (Return v)   = [v]
returnsOf (Do _ m)     = returnsOf m
returnsOf (If _ m1 m2) = returnsOf m1 ++ returnsOf m2

-- | Every lift's classical bit index and the qasm-measured value that means
-- "the block survived" -- exported so a checker can translate
-- Drop.Lang.Machine's (paramName, 1=survived) records into the raw c[k]
-- values the emitted circuit actually produces, without re-deriving the
-- direct-vs-block-form and polarity decisions 'layoutProgram' already made.
liftInfoOf :: Program Cyclo -> Either CompileError [(Name, Int, Int)]
liftInfoOf prog = do
  layout <- layoutProgram prog
  Right [ (n, idx, sv) | (n, (idx, sv)) <- Map.toList (liLiftInfo layout) ]

-- | Every 'new'-allocated wire's physical qubits and its allocation vector
-- psi -- so a checker can seed a non-basis temporary's qubits at psi
-- directly, since (by the domain's own rule) 'compile' emits no
-- preparation gates for it. A wire whose psi is a computational basis
-- state needs no such seeding: its qubits already start at the qubit
-- register's hardware |0..0> and 'compile' emits the X gates that reach
-- psi from there.
wireAllocOf :: Program Cyclo -> Either CompileError [(Name, [Int], [Complex Double])]
wireAllocOf prog = do
  layout <- layoutProgram prog
  Right [ (n, Map.findWithDefault [] n (liWireQ layout), psi) | (n, psi) <- Map.toList (liWireAlloc layout) ]

-- | Every block-lift's indicator ancilla qubit: a
-- physical qubit Drop.Lang.Machine's own leaf state has no wire for at all,
-- since the derived form is not in the source program -- a checker needs
-- this to marginalise the ancilla (always back at |0>, by the lemma's own
-- proof) out of the emitted circuit's state before comparing it to a leaf.
liftAncillaOf :: Program Cyclo -> Either CompileError [(Name, Int)]
liftAncillaOf prog = do
  layout <- layoutProgram prog
  Right (Map.toList (liLiftAncilla layout))

-- | The physical qubits of every visible (input) wire, in 'progCtx' order.
visQubitsOf :: Program Cyclo -> Either CompileError [(Name, [Int])]
visQubitsOf prog = do
  layout <- layoutProgram prog
  Right [ (n, Map.findWithDefault [] n (liWireQ layout)) | (n, _) <- progCtx prog ]

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
expectedFinalState :: LayoutInfo -> SafetyInfo -> Config Cyclo -> [Complex Double]
expectedFinalState layout safety leaf = foldl applyReclaim (map toC (cfgAmp leaf)) (cfgSites leaf)
  where
    dimsC = cfgDims leaf
    namesC = cfgNames leaf
    applyReclaim amp rec_ =
      let depth = Map.findWithDefault 0 (srSite rec_) (liSiteDepth layout)
          prefix = take depth (cfgBits leaf)
          outcome = Map.findWithDefault UnreachableOutcome prefix
                      (Map.findWithDefault Map.empty (srSite rec_) safety)
      in case outcome of
           -- @drop ()@: no register, no gate (compileDrop's first clause).
           _ | null (srHidden rec_) -> amp
           SafeCert cert ->
             let hiddenNames = srHidden rec_
                 psi = foldr kron [1] [ Map.findWithDefault [1] n (liWireAlloc layout) | n <- hiddenNames ]
                 gRaw = map toC cert
                 gNorm = sqrt (sum [ magnitude z ** 2 | z <- gRaw ])
                 g = if gNorm < 1e-12 then gRaw else map (/ (gNorm :+ 0)) gRaw
                 r = reflectionR psi g
                 -- the block's positions in the drop's order, the order the
                 -- certificate ('probeOutcome'), 'psi' and the emitted qubit
                 -- list share; 'applyGate' reads its targets in the order given
                 positions = [ i | n <- hiddenNames, (i, nm) <- zip [0 ..] namesC, nm == n ]
                 -- The theorem's target is the branch map with the reclaiming
                 -- gate at every site the emitter has a clause for
                 -- (the per-record compilation theorem: "each emittable with its certificate").
                 -- Every SafeCert site is now emittable: the one-qubit clause,
                 -- the basis-state transposition, the proportional (R = I)
                 -- clause, and the general k-qubit reclaiming
                 -- reflection of 'emitGeneralReflectionOps' between them cover
                 -- every k >= 1 (bell-pair.s is the corpus instance that
                 -- needs the general clause).
             in applyGate dimsC r positions amp
           SafeIso bMat ->
             let hiddenNames = srHidden rec_
                 bC = matC bMat
                 n  = length bC
                 square = not (null bC) && all ((== n) . length) bC
                 bN = normaliseSquareIso bC
                 positions = [ i | n' <- hiddenNames, (i, nm) <- zip [0 ..] namesC, nm == n' ]
                 isLoan nm = not (Map.member nm (liWireAlloc layout))
                 kinds = [ (dimsC !! i, isLoan nm) | (nm, i) <- zip hiddenNames positions ]
                 loanPositions = [ i | (i, (_, True)) <- zip positions kinds ]
                 tempPositions = [ i | (i, (_, False)) <- zip positions kinds ]
                 psiTemp = foldr kron [1] [ Map.findWithDefault [1] nm (liWireAlloc layout)
                                          | nm <- hiddenNames, not (isLoan nm) ]
                 unitOf v = let vn = sqrt (sum [ magnitude z ** 2 | z <- v ])
                            in if vn < 1e-12 then v else map (/ (vn :+ 0)) v
                 -- Mirrors 'emitReclaimIso' clause for clause: a square B is
                 -- undone by B^dagger exactly when it is the identity, on one
                 -- qubit, or a permutation of the basis states; a rectangular
                 -- B = B' (x) g~ is undone by B'^dagger on the loans and the
                 -- reflection through psi - g~ on the temporaries exactly
                 -- when B' has one of those three shapes; nothing otherwise.
             in if square
                  then (if squareFactorEmittable bN then applyGate dimsC (daggerC bN) positions amp else amp)
                  else case splitMixedFactor kinds bMat of
                    Just (bPrime, gT)
                      | let bPN = normaliseSquareIso (matC bPrime)
                      , squareFactorEmittable bPN ->
                          let amp1 = applyGate dimsC (daggerC bPN) loanPositions amp
                              r    = reflectionR psiTemp (unitOf (map toC gT))
                          in applyGate dimsC r tempPositions amp1
                    _ -> amp
           _ -> amp

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
      -- safety claim (which Drop.Lang.Interp's loan criterion already decides
      -- for every possible incoming state).
      loanEnv0 = [ (n, ket [d] [0]) | (n, d) <- loanBindersOf core ]
      leaves = run (initConfigL (progCtx prog) inp loanEnv0 core)
  Right [ (leaf, expectedFinalState layout safety leaf) | leaf <- leaves ]

-- | The circuit, ending in the measurement of what the program returns. When
-- every branch returns the same value -- every program the parser reads,
-- since a surface branch returns exactly the registers it was handed -- the
-- output measurements follow the whole body once. When the branches return
-- different values, each branch measures its own at its @return@. Either way
-- @result[i]@ holds the i-th qubit of the value returned on the run taken;
-- a loan is never returned (Drop.Lang.Check.loanDiscipline), so never measured.
compile :: Program Cyclo -> Either CompileError String
compile prog = do
  layout <- layoutProgram prog
  let core = toTerm (progTerm prog)
  safety <- fragmentSafety prog core layout
  let visNames = map fst (progCtx prog)
      rets = returnsOf core
      widthOf v = length (concatMap (wireQubits layout) (valueNames v))
      width = case rets of { (v : _) -> widthOf v; [] -> 0 }
      uniform = case rets of { (v : vs) -> all (== v) vs; [] -> True }
      measure = outputMeasureLines layout visNames
  if all ((== width) . widthOf) rets then Right ()
    else Left (Other "Drop.Lang.Compile: the branches return values of different sizes (not a typed program)")
  body <- compileTerm layout safety (if uniform then const [] else measure) [] core
  let final = case rets of
        (v : _) | uniform, not (null (measure v)) -> "" : measure v
        _ -> []
  Right (unlines (buildHeader layout visNames width body ++ body ++ final))

-- | The physical qubits of every register the layout names -- inputs,
-- allocations and loans -- so a checker can map a returned value's names
-- to the qubits its @result@ bits must read.
wireQubitsOf :: Program Cyclo -> Either CompileError [(Name, [Int])]
wireQubitsOf prog = do
  layout <- layoutProgram prog
  Right (Map.toList (liWireQ layout))
