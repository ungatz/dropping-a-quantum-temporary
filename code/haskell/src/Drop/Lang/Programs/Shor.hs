-- Drop.Lang.Programs.Shor: the order-finding core of Shor's algorithm, N = 15, a = 7.
--
-- Question: Is the residue register of order finding safe to drop, before and after the textbook
--           measurement of it?
-- Answer:   Three counting qubits c1, c2, c3 and a temporary w of dimension 16 that holds a
--           residue mod 15, started at 1. Controlled modular multiplications by 7^4, 7^2 and 7
--           entangle w with the counting register, so dropping w unmeasured is unsafe (shorProg).
--           The textbook "measure the second register" step is a lift of w against {7}
--           (shorMeasured). Then the drop is safe on the record that keeps {7}, with w parked on
--           the basis vector |7>, and unsafe on the complement: opposite verdicts on one program
--           text. From |000> the counting outcome has probability exactly 1/4 on each even y and 0
--           on each odd y, since the order of 7 mod 15 is 4. The static pass of Drop.Lang.Pass
--           declines on shorMeasured, since the prefix entangles w with the counting register.
-- Paper:    sec:meas:leaf (the paragraph on shor.s), app:corpus (the row for shor.s).
-- Shapes:   visShor       the visible registers: c1, c2, c3, two levels each.
--           shorCore      new w, w to |1>, H on each counter, the three controlled
--                         multiplications, the inverse Fourier transform.
--           shorProg      shorCore, then drop w.
--           shorMeasured  shorCore, then a lift of w against {7}, then drop w.
-- Corpus file: programs/shor.s holds shorMeasured; the check "programs/shor.s is the module's
--           program as syntax" pairs them, and "shor.s verdicts agree with the Shor module,
--           opposite verdicts on the two records" compares verdicts.

module Drop.Lang.Programs.Shor where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass
import Drop.Lang.Programs.QFT (invQftC)

visShor :: VisSpec
visShor = [("c1", 2), ("c2", 2), ("c3", 2)]

-- >>> visShor
-- [("c1",2),("c2",2),("c3",2)]

-- | w starts at |0>; this swap lands it on |1>.
swap01 :: Int -> Int
swap01 0 = 1
swap01 1 = 0
swap01 w = w

-- >>> map swap01 [0, 1, 2]
-- [1,0,2]

-- | Controlled multiplication by @a@ mod 15 on (c, w), control most
-- significant: fixed unless the control is 1 and w holds a nonzero residue.
cMulPerm :: Int -> Int -> Int
cMulPerm a j =
  let c = j `div` 16
      w = j `mod` 16
  in if c == 1 && w >= 1 && w <= 14 then c * 16 + (a * w) `mod` 15 else j

-- With the control off nothing moves; with it on, w goes to 7 w mod 15, and w = 0 stays.
-- >>> [ cMulPerm 7 j | j <- [3, 16, 17, 18] ]
-- [3,16,23,30]

-- | Everything through the inverse QFT: c1 with U^4 (7^4 = 1 mod 15), c2
-- with U^2 (7^2 = 4), c3 with U (7), as in the ladder of Drop.Lang.Programs.QPE.
shorCore :: Prog Cyclo
shorCore =
  [ New "w" 16
  , Gate (permGate 16 swap01) ["w"]
  , Gate gHC ["c1"]
  , Gate gHC ["c2"]
  , Gate gHC ["c3"]
  -- 7^4 = 1 mod 15, so this is the identity permutation; it stays because
  -- the algorithm calls for it regardless of what a simplifies to.
  , Gate (permGate 32 (cMulPerm 1)) ["c1", "w"]
  , Gate (permGate 32 (cMulPerm 4)) ["c2", "w"]
  , Gate (permGate 32 (cMulPerm 7)) ["c3", "w"]
  ] ++ invQftC ["c1", "c2", "c3"]

-- >>> length shorCore
-- 15

shorProg :: Prog Cyclo
shorProg = shorCore ++ [Drop ["w"]]

-- Dropped unmeasured, w is entangled with the counting register: unsafe, no lift to choose a record.
-- >>> verdict visShor shorProg
-- [DropReport {drSite = ["w"], drRows = [([],Unsafe)]}]

-- | The textbook "measure the second register" step: w survives restricted
-- to whether it fell in the block {7}.
shorMeasured :: Prog Cyclo
shorMeasured = shorCore ++ [Lift "s" "w" [7], Drop ["w"]]

-- It is the text of programs/shor.s, parsed.
-- >>> :m + Drop.Lang.Parser
-- >>> readFile "programs/shor.s" >>= \src -> print (fmap (== (visShor, shorMeasured)) (parseProgram src))
-- Right True

-- One lift, two records, opposite verdicts: safe on the block {7}, unsafe on its complement.
-- >>> verdict visShor shorMeasured
-- [DropReport {drSite = ["w"], drRows = [([SIn],Safe),([SOut],Unsafe)]}]

-- | The state at the end of the program, run from the all-zero input.
finalState :: Prog Cyclo -> StateV Cyclo
finalState p = mAmp (runStmts (initMach visShor (ket [2, 2, 2] [0, 0, 0])) p [] Nothing)

-- The state has 8 * 16 = 128 amplitudes, one for each counting outcome and level of w.
-- >>> length (finalState shorProg)
-- 128

-- | Pr(y), summing over the levels of w at counting outcome y.
probY :: StateV Cyclo -> Int -> Cyclo
probY st y = sum [ normSq (st !! (16 * y + w)) | w <- [0 .. 15] ]  -- impossible: y is below 8 and w below 16, so 16 * y + w is below the 128 amplitudes

-- Exactly one quarter on each even outcome and nothing on the odd ones: the order of 7 mod 15 is 4.
-- >>> map (showAmp . probY (finalState shorProg)) [0 .. 7]
-- ["1/4","0","1/4","0","1/4","0","1/4","0"]

basisW :: Int -> StateV Cyclo
basisW l = [ if i == l then 1 else 0 | i <- [0 .. 15] ]

-- >>> length (basisW 7)
-- 16

-- On the record that keeps {7} the drop is safe and w is left on |7>.
-- >>> fmap (== basisW 7) (semanticParked visShor shorMeasured "w" [SIn])
-- Just True

-- The static pass declines on both records: its prefix entangles w with the counting register.
-- >>> let table = residualCheck visShor shorMeasured "w"
-- >>> (rDepth table, lookup "prefix-parks" (rHyps table), map reVerdict (rTable table))
-- (1,Just False,[HypothesesFail,HypothesesFail])

-- The suite's claims ------------------------------------------------------------------

checks :: [(String, Bool)]
checks = concat
  [ [ ( "shorProg: drop w unsafe, entangled with the counting register"
      , semanticVerdict visShor shorProg "w" [] == Unsafe ) ]
  , [ ( "shorMeasured: drop w safe on the block {7}, parked on its basis vector"
      , semanticVerdict visShor shorMeasured "w" [SIn] == Safe
        && semanticParked visShor shorMeasured "w" [SIn] == Just (basisW 7) ) ]
  , [ ( "shorMeasured: drop w unsafe on the complement of {7}"
      , semanticVerdict visShor shorMeasured "w" [SOut] == Unsafe ) ]
  , [ ( "shorMeasured: opposite verdicts on one program text, one lift"
      , liftDepthBefore shorMeasured "w" == 1 ) ]
  , [ ( "shorProg from |000>: exact 1/4 on y in {0,2,4,6}, exact 0 on odd y "
        ++ "-- the order of 7 mod 15 is 4"
      , let st = finalState shorProg
        in and [ probY st y == (if even y then 1 / 4 else 0) | y <- [0 .. 7] ] ) ]
  , -- the controlled multiplication entangles w with the counting register
    -- before the lift, so the runtime check's pre-lift parking hypothesis
    -- fails and it declines on both records rather than deciding them: the
    -- semantic criterion still does, from the state the interpreter reaches.
    [ ( "shorMeasured: runtime check declines on both records, prefix-parks false"
      , let r = residualCheck visShor shorMeasured "w"
        in rDepth r == 1
           && lookup "prefix-parks" (rHyps r) == Just False
           && map reVerdict (rTable r) == [HypothesesFail, HypothesesFail] ) ]
  ]

-- >>> length checks
-- 6

-- >>> map fst (take 1 checks)
-- ["shorProg: drop w unsafe, entangled with the counting register"]
