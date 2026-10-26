-- Drop.Lang.Programs.QPE: phase estimation with three counting qubits.
--
-- Question: Is the eigenstate temporary of phase estimation safe to drop, though it does not
--           return to |0>?
-- Answer:   The temporary psi is put on |1>, the eigenvector of the T gate, and every gate that
--           touches it is a controlled phase, so psi stays on [|1>] at every input and the drop
--           is safe: parked at (0, 1), not at the |0> it was allocated in. The static pass of
--           Drop.Lang.Pass admits it at depth 0. The counting register is exact. For the phase
--           1/8 (qpeT), which three bits hold exactly, the final state is |001> tensor |1> and
--           that is an equality, not a peak. For the phase 1/16 (qpe16), which they do not hold,
--           the probability of each outcome equals a closed form exactly (closed16), the eight sum
--           to 1, and 0 and 1 tie, both beating every other outcome, decided by the exact sign of
--           the difference.
-- Paper:    sec:lang:algorithms (the listing of qpe.s), app:corpus.
-- Shapes:   visQPE         the visible registers: c1, c2, c3, two levels each, c1 most significant.
--           qpeF z         the program for the controlled phase z: new psi, X, H on each counter,
--                          the ladder (z^4 from c1, z^2 from c2, z from c3), the inverse Fourier
--                          transform, drop psi.
--           qpeT, qpe16    qpeF at the primitive 8th and 16th roots of unity.
--           finalState p   the state at the end of p, from |000>.
-- Corpus file: programs/qpe.s holds qpeT; the check "programs/qpe.s is the module's program as
--           syntax" pairs them, and "qpe.s verdicts agree with ExQPE at the drop of psi" compares
--           verdicts.

module Drop.Lang.Programs.QPE where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass
import Drop.Lang.Programs.QFT (invQftC)

visQPE :: VisSpec
visQPE = [("c1", 2), ("c2", 2), ("c3", 2)]

-- >>> visQPE
-- [("c1",2),("c2",2),("c3",2)]

-- | Counting registers c1 c2 c3, c1 most significant, and the eigenstate
-- temporary psi.  The controlled-power ladder pairs c1 with U^4, c2 with
-- U^2 and c3 with U.
qpeF :: Cyclo -> Prog Cyclo
qpeF z =
  [ New "psi" 2
  , Gate gX ["psi"]                    -- the eigenvector |1>
  , Gate gHC ["c1"]
  , Gate gHC ["c2"]
  , Gate gHC ["c3"]
  , Gate (gCPhase (z * z * z * z)) ["c1", "psi"]
  , Gate (gCPhase (z * z))         ["c2", "psi"]
  , Gate (gCPhase z)               ["c3", "psi"]
  ]
  ++ invQftC ["c1", "c2", "c3"]
  ++ [ Drop ["psi"] ]

qpeT, qpe16 :: Prog Cyclo
qpeT  = qpeF (zetaC 3)   -- phase 1/8, exactly representable in 3 bits
qpe16 = qpeF (zetaC 4)   -- phase 1/16, not representable in 3 bits

-- Phase 1/8 as text: the eigenstate, the ladder, the inverse transform written out, the drop.
-- >>> :m + Drop.Lang.Render Drop.Lang.Parser
-- >>> mapM_ (putStrLn . renderCmd) qpeT
-- new psi : [2] @ |0>;
-- X psi;
-- H c1;
-- H c2;
-- H c3;
-- diag c1 psi (1, 1, 1, -1);
-- diag c2 psi (1, 1, 1, i);
-- diag c3 psi (1, 1, 1, z8);
-- Swap c1 c3;
-- H c3;
-- diag c2 c3 (1, 1, 1, -i);
-- H c2;
-- diag c1 c3 (1, 1, 1, -z8^3);
-- diag c1 c2 (1, 1, 1, -i);
-- H c1;
-- drop psi;

-- It is the text of programs/qpe.s, parsed.
-- >>> readFile "programs/qpe.s" >>= \src -> print (fmap (== (visQPE, qpeT)) (parseProgram src))
-- Right True

-- Safe at the drop of psi for both phases; no lift, so one verdict.
-- >>> verdict visQPE qpeT
-- [DropReport {drSite = ["psi"], drRows = [([],Safe)]}]

-- >>> verdict visQPE qpe16
-- [DropReport {drSite = ["psi"], drRows = [([],Safe)]}]

-- psi is left on the line (0, 1), the eigenvector, and the static pass admits it.
-- >>> probeResult visQPE qpeT "psi" [] (ket [2, 2, 2] [0, 0, 0]) == PLine [0, 1]
-- True

-- >>> map reVerdict (rTable (residualCheck visQPE qpeT "psi"))
-- [Admit]

finalState :: Prog Cyclo -> StateV Cyclo
finalState p = mAmp (runStmts (initMach visQPE (ket [2,2,2] [0,0,0])) p [] Nothing)

-- Phase 1/8: the counting register reads 001 exactly, with psi on |1>.
-- >>> finalState qpeT == ket [2, 2, 2, 2] [0, 0, 1, 1]
-- True

-- | Pr(y).  The eigenstate is unentangled by kickback, so the probability of
-- a counting outcome is the sum over its basis states.
probY :: StateV Cyclo -> Int -> Cyclo
probY st y = sum [ normSq (st !! (2 * y + b)) | b <- [0, 1] ]  -- impossible: y is below 8, so 2 * y + b is below the 16 amplitudes

-- The probabilities of the eight outcomes for phase 1/8: all on outcome 1.
-- >>> map (showAmp . probY (finalState qpeT)) [0 .. 7]
-- ["0","1","0","0","0","0","0","0"]

-- | The closed form for phase 1/16, with w = zeta_16^{1-2y}.
closed16 :: Int -> Cyclo
closed16 y = (2 - w ^ (8 :: Int) - conj w ^ (8 :: Int))
             / (64 * (2 - w - conj w))
  where w = zetaP 4 (fromIntegral (1 - 2 * y))

-- Phase 1/16 spreads: outcomes 0 and 1 tie, and both beat every other outcome by an exact sign.
-- >>> probY (finalState qpe16) 0 == probY (finalState qpe16) 1
-- True

-- >>> all (\y -> realSign (probY (finalState qpe16) 0 - probY (finalState qpe16) y) == 1) [2 .. 7]
-- True

-- Each probability equals the closed form exactly, and the eight sum to 1.
-- >>> [ probY (finalState qpe16) y == closed16 y | y <- [0 .. 7] ]
-- [True,True,True,True,True,True,True,True]

-- >>> sum [ probY (finalState qpe16) y | y <- [0 .. 7] ] == 1
-- True

-- The suite's claims ------------------------------------------------------------------

checks :: [(String, Bool)]
checks = concat
  [ [ ("QPE(T): the counting register is |001> exactly, not a peak"
      , finalState qpeT == ket [2, 2, 2, 2] [0, 0, 1, 1]) ]
  , [ ("QPE(T): drop psi safe, runtime check depth 0, admit"
      , semanticVerdict visQPE qpeT "psi" [] == Safe
        && probeResult visQPE qpeT "psi" [] (ket [2,2,2] [0,0,0]) == PLine [0, 1]
        && let r = residualCheck visQPE qpeT "psi"
           in rDepth r == 0 && map reVerdict (rTable r) == [Admit]
              && all snd (rHyps r)) ]
  , [ ("QPE(1/16): Pr(" ++ show y ++ ") equals the closed form exactly"
      , probY (finalState qpe16) y == closed16 y)
    | y <- [0 .. 7] ]
  , [ ("QPE(1/16): the eight probabilities sum to 1 exactly"
      , sum [ probY (finalState qpe16) y | y <- [0 .. 7] ] == 1) ]
  , -- 1/16 sits exactly between the 3-bit values 0/8 and 1/8, so the two
    -- outcomes tie and both beat the rest; decided by the exact real sign
    [ ("QPE(1/16): Pr(0) = Pr(1) exactly, and both beat every other outcome"
      , let st = finalState qpe16
        in probY st 0 == probY st 1
           && all (\y -> realSign (probY st 0 - probY st y) == 1) [2 .. 7]) ]
  , [ ("QPE(1/16): drop psi still safe, kickback being phase-only"
      , semanticVerdict visQPE qpe16 "psi" [] == Safe) ]
  ]

-- >>> length checks
-- 13

-- >>> map fst (take 1 checks)
-- ["QPE(T): the counting register is |001> exactly, not a peak"]
