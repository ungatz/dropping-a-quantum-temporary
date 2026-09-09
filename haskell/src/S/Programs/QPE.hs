-- QPE.hs: phase estimation, three counting qubits, one of the eight algorithms.
--
-- The eigenstate is the temporary; every gate touching it is a controlled
-- phase, so it stays on [|1>] and the drop is safe. Phase 1/8 is exact in
-- three bits (an equality, not a peak); phase 1/16 is not, and spreads,
-- checked against a closed form with ties broken by exact sign.

module S.Programs.QPE where

import S.Lang.Ring
import S.Lang.Cyclo
import S.Lang.QState
import S.Lang.Gates
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass
import S.Programs.QFT (invQftC)

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
  ++ [ Drop "psi" ]

visQPE :: VisSpec
visQPE = [("c1", 2), ("c2", 2), ("c3", 2)]

qpeT, qpe16 :: Prog Cyclo
qpeT  = qpeF (zetaC 3)   -- phase 1/8, exactly representable in 3 bits
qpe16 = qpeF (zetaC 4)   -- phase 1/16, not representable in 3 bits

finalState :: Prog Cyclo -> StateV Cyclo
finalState p = mAmp (runStmts (initMach visQPE (ket [2,2,2] [0,0,0])) p [] Nothing)

-- | Pr(y).  The eigenstate is unentangled by kickback, so the probability of
-- a counting outcome is the sum over its basis states.
probY :: StateV Cyclo -> Int -> Cyclo
probY st y = sum [ normSq (st !! (2 * y + b)) | b <- [0, 1] ]

-- | The closed form for phase 1/16, with w = zeta_16^{1-2y}.
closed16 :: Int -> Cyclo
closed16 y = (2 - w ^ (8 :: Int) - conj w ^ (8 :: Int))
             / (64 * (2 - w - conj w))
  where w = zetaP 4 (fromIntegral (1 - 2 * y))

checks :: [(String, Bool)]
checks = concat
  [ [ ("QPE(T): the counting register is |001> exactly, not a peak"
      , finalState qpeT == ket [2, 2, 2, 2] [0, 0, 1, 1]) ]
  , [ ("QPE(T): drop psi admissible, runtime check depth 0, admit"
      , semanticVerdict visQPE qpeT "psi" [] == Admissible
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
  , [ ("QPE(1/16): drop psi still admissible, kickback being phase-only"
      , semanticVerdict visQPE qpe16 "psi" [] == Admissible) ]
  ]
