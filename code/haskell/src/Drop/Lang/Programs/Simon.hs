-- Drop.Lang.Programs.Simon: Simon's problem on two bits, hidden string s = 11.
--
-- Question: Is the work register of Simon's algorithm safe to drop, before and after it is measured?
-- Answer:   The oracle |x1 x2>|w> -> |x1 x2>|w xor f(x1,x2)> is a permutation, not a phase gate,
--           so it entangles the work register w with the visible ones: dropping w unmeasured is
--           unsafe (simonProg). Measuring w first (simonMeasured, a lift of w against {0}) is
--           safe on both records, but on different lines: w only ever holds level 0 or level 1,
--           so keeping {0} leaves it on |0> and keeping the complement leaves it on |1>. The
--           visible state is the coset of the hidden string: proportional to |00> + |11> on the
--           first record and to |01> + |10> on the second, from |00>. The static pass of
--           Drop.Lang.Pass declines on both records, since the oracle entangles w before the lift.
-- Paper:    app:corpus (the row for simon.s).
-- Shapes:   visSimon        the visible registers: x1 and x2, two levels each.
--           simonCore       new w (four levels), H on x1 and x2, the oracle.
--           simonProg       simonCore, then drop w.
--           simonMeasured   simonCore, then a lift of w against {0}, then drop w.
-- Corpus file: programs/simon.s holds simonMeasured; the check "programs/simon.s is the module's
--           program as syntax" pairs them, and "simon.s verdicts agree with ExSimon, both records
--           safe on different lines" compares verdicts.

module Drop.Lang.Programs.Simon where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass

visSimon :: VisSpec
visSimon = [("x1", 2), ("x2", 2)]

-- >>> visSimon
-- [("x1",2),("x2",2)]

-- | Simon's oracle for s = 11: f(00) = f(11) = 0, f(01) = f(10) = 1, values
-- as levels of the two-bit register w.  Xor by f is xor by its low bit.
simonOraclePerm :: Int -> Int
simonOraclePerm j =
  let x1 = j `div` 8
      x2 = (j `div` 4) `mod` 2
      w  = j `mod` 4
  in x1 * 8 + x2 * 4 + (if x1 /= x2 then flipLow w else w)
  where flipLow k = if even k then k + 1 else k - 1

-- The oracle moves a level only when x1 and x2 differ, and then flips the low bit of w.
-- Levels are numbered x1 * 8 + x2 * 4 + w, so 4 (x1 = 0, x2 = 1, w = 0) goes to 5 and 8 goes to 9.
-- >>> map simonOraclePerm [0, 4, 8, 12]
-- [0,5,9,12]

simonCore :: Prog Cyclo
simonCore =
  [ New "w" 4
  , Gate gHC ["x1"]
  , Gate gHC ["x2"]
  , Gate (permGate 16 simonOraclePerm) ["x1", "x2", "w"]
  ]

-- >>> length simonCore
-- 4

simonProg :: Prog Cyclo
simonProg = simonCore ++ [Drop ["w"]]

-- Dropped unmeasured, w is entangled with x1 and x2: unsafe.
-- >>> verdict visSimon simonProg
-- [DropReport {drSite = ["w"], drRows = [([],Unsafe)]}]

simonMeasured :: Prog Cyclo
simonMeasured = simonCore ++ [Lift "s" "w" [0], Drop ["w"]]

-- It is the text of programs/simon.s, parsed.
-- >>> :m + Drop.Lang.Parser
-- >>> readFile "programs/simon.s" >>= \src -> print (fmap (== (visSimon, simonMeasured)) (parseProgram src))
-- Right True

-- One lift, two records, both safe.
-- >>> verdict visSimon simonMeasured
-- [DropReport {drSite = ["w"], drRows = [([SIn],Safe),([SOut],Safe)]}]

basisW :: Int -> StateV Cyclo
basisW l = [ if i == l then 1 else 0 | i <- [0 .. 3] ]

-- >>> map showAmp (basisW 1)
-- ["0","1","0","0"]

-- On different lines: |0> on the record that keeps {0}, |1> on the other.
-- >>> map (\sel -> fmap (== basisW (fromEnum (sel == [SOut]))) (semanticParked visSimon simonMeasured "w" sel)) [[SIn], [SOut]]
-- [Just True,Just True]

-- | The visible factor at the end of the program, run from the given input.
visibleAfter :: Prog Cyclo -> [Sel] -> StateV Cyclo -> Maybe (StateV Cyclo)
visibleAfter prog sel inp =
  let m = runStmts (initMach visSimon inp) prog sel Nothing
  in fmap fst (factorSplit (mDims m) [0, 1] (mAmp m))

-- The visible state is the coset of s = 11 that the measured value of w names.
-- >>> :m + Drop.Lang.State
-- >>> fmap (\v -> stateProportional v (addS (ket [2, 2] [0, 0]) (ket [2, 2] [1, 1]))) (visibleAfter simonMeasured [SIn] (ket [2, 2] [0, 0]))
-- Just True

-- >>> fmap (\v -> stateProportional v (addS (ket [2, 2] [0, 1]) (ket [2, 2] [1, 0]))) (visibleAfter simonMeasured [SOut] (ket [2, 2] [0, 0]))
-- Just True

-- The static pass declines on both records.
-- >>> let table = residualCheck visSimon simonMeasured "w"
-- >>> (rDepth table, lookup "prefix-parks" (rHyps table), map reVerdict (rTable table))
-- (1,Just False,[HypothesesFail,HypothesesFail])

-- The suite's claims ------------------------------------------------------------------

checks :: [(String, Bool)]
checks = concat
  [ [ ( "simonProg: drop w unsafe, entangled with x1 x2"
      , semanticVerdict visSimon simonProg "w" [] == Unsafe ) ]
  , [ ( "simonMeasured: drop w safe on both records, parked on different lines"
      , semanticVerdict visSimon simonMeasured "w" [SIn]  == Safe
        && semanticVerdict visSimon simonMeasured "w" [SOut] == Safe
        && semanticParked visSimon simonMeasured "w" [SIn]  == Just (basisW 0)
        && semanticParked visSimon simonMeasured "w" [SOut] == Just (basisW 1) ) ]
  , [ ( "simonMeasured from |00>, block {0}: visible state proportional to |00> + |11>, the coset of s"
      , case visibleAfter simonMeasured [SIn] (ket [2, 2] [0, 0]) of
          Just v  -> stateProportional v (addS (ket [2, 2] [0, 0]) (ket [2, 2] [1, 1]))
          Nothing -> False ) ]
  , [ ( "simonMeasured from |00>, complement of {0}: visible state proportional to |01> + |10>"
      , case visibleAfter simonMeasured [SOut] (ket [2, 2] [0, 0]) of
          Just v  -> stateProportional v (addS (ket [2, 2] [0, 1]) (ket [2, 2] [1, 0]))
          Nothing -> False ) ]
  , -- the oracle entangles w with x1 x2 before the lift, the same
    -- entanglement that refuses simonProg's unmeasured drop, so the runtime
    -- check's pre-lift parking hypothesis fails and it declines on both
    -- records rather than deciding them.
    [ ( "simonMeasured: runtime check declines on both records, prefix-parks false"
      , let r = residualCheck visSimon simonMeasured "w"
        in rDepth r == 1
           && lookup "prefix-parks" (rHyps r) == Just False
           && map reVerdict (rTable r) == [HypothesesFail, HypothesesFail] ) ]
  ]

-- >>> length checks
-- 5

-- >>> map fst (take 1 checks)
-- ["simonProg: drop w unsafe, entangled with x1 x2"]
