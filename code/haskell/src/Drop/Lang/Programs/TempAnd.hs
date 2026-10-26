-- Drop.Lang.Programs.TempAnd: a temporary AND, uncomputed by measurement.
--
-- Question: Is the temporary of an AND safe to drop when a measurement uncomputes it, not gates?
-- Answer:   A Toffoli writes x AND y into a temporary a. Dropped right after, a is entangled with x
--           and y on a superposed input, so the drop is unsafe (andComputed). The measurement form
--           (as in "Halving the cost of quantum addition", Quantum 2, 74 (2018)) applies H to a,
--           lifts a against the block {1}, and applies a CZ on x, y when the bit is 1
--           (andUncomputedByMeasurement). Then the drop is safe on both records, on opposite
--           lines: |1> under bit 1, |0> under bit 0. Without the CZ (andNoCorrection) the drop is
--           still safe on both records, but the visible register is left with a sign on |11>: the
--           phase the correction cancels. The static pass of Drop.Lang.Pass declines on the
--           measurement form, since its prefix entangles a with x and y before the lift.
-- Paper:    app:corpus (the corpus, site by site; the row for temp-and.s), sec:eval:corpus.
-- Shapes:   visXY                         the visible registers: x and y, two levels each.
--           andComputed                   new a, a Toffoli, drop a: no lift.
--           andUncomputedByMeasurement    the same, then H, a lift of a against {1}, the CZ under
--                                         that bit, and the drop.
--           andNoCorrection               the same without the CZ.
--           basisXY                       the four basis inputs of (x, y), named by their bits.
-- Corpus file: programs/temp-and.s holds andUncomputedByMeasurement; the check
--           "programs/temp-and.s is the module's program as syntax" pairs them, and "temp-and.s
--           verdicts agree with ExTempAnd, both records safe on different lines" compares verdicts.

module Drop.Lang.Programs.TempAnd where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass

-- The registers --------------------------------------------------------------

visXY :: VisSpec
visXY = [("x", 2), ("y", 2)]

-- >>> visXY
-- [("x",2),("y",2)]

cz :: Matrix Cyclo
cz = gCPhase (-1)

-- Controlled-Z is the identity except for a sign on |11>.
-- >>> map (map showAmp) cz
-- [["1","0","0","0"],["0","1","0","0"],["0","0","1","0"],["0","0","0","-1"]]

-- The three programs, smallest first -------------------------------------------

andComputed :: Prog Cyclo
andComputed =
  [ New "a" 2
  , Gate gCCX ["x", "y", "a"]
  , Drop ["a"]
  ]

-- The program as text, and its one site: unsafe, with no lift to choose a record.
-- >>> :m + Drop.Lang.Render Drop.Lang.Parser
-- >>> let listing = mapM_ (putStrLn . renderCmd)
-- >>> listing andComputed
-- new a : [2] @ |0>;
-- CCX x y a;
-- drop a;

-- >>> verdict visXY andComputed
-- [DropReport {drSite = ["a"], drRows = [([],Unsafe)]}]

andUncomputedByMeasurement :: Prog Cyclo
andUncomputedByMeasurement =
  [ New "a" 2
  , Gate gCCX ["x", "y", "a"]
  , Gate gHC ["a"]
  , Lift "m" "a" [1]
  , IfBit (GParam "m") [Gate cz ["x", "y"]] []
  , Drop ["a"]
  ]

-- The same program with a measurement: safe on both records.
-- >>> listing andUncomputedByMeasurement
-- new a : [2] @ |0>;
-- CCX x y a;
-- H a;
-- m = lift[{1}] a;
-- if m { diag x y (1, 1, 1, -1); } else { }
-- drop a;

-- >>> verdict visXY andUncomputedByMeasurement
-- [DropReport {drSite = ["a"], drRows = [([SIn],Safe),([SOut],Safe)]}]

-- It is the text of programs/temp-and.s, parsed (the paper's program is the example).
-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap (== (visXY, andUncomputedByMeasurement)) (parseProgram src))
-- Right True

-- The two records park the temporary on opposite lines: |1> under bit 1, |0> under bit 0.
-- >>> map (fmap (map showAmp) . semanticParked visXY andUncomputedByMeasurement "a") [[SIn], [SOut]]
-- [Just ["0","1"],Just ["1","0"]]

-- | The same, without the correction: the phase kicked back by the
-- measurement is left uncancelled.
andNoCorrection :: Prog Cyclo
andNoCorrection =
  [ New "a" 2
  , Gate gCCX ["x", "y", "a"]
  , Gate gHC ["a"]
  , Lift "m" "a" [1]
  , Drop ["a"]
  ]

-- Still safe on both records: the correction is about the visible register, not the drop.
-- >>> verdict visXY andNoCorrection
-- [DropReport {drSite = ["a"], drRows = [([SIn],Safe),([SOut],Safe)]}]

basisXY :: [(String, StateV Cyclo)]
basisXY =
  [ ("00", ket [2, 2] [0, 0]), ("01", ket [2, 2] [0, 1])
  , ("10", ket [2, 2] [1, 0]), ("11", ket [2, 2] [1, 1]) ]

-- >>> map fst basisXY
-- ["00","01","10","11"]

-- | The visible (x, y) factor at the end of the program, run from the given
-- basis input.
visibleFactor :: Prog Cyclo -> [Sel] -> StateV Cyclo -> Maybe (StateV Cyclo)
visibleFactor prog sel inp =
  let m = runStmts (initMach visXY inp) prog sel Nothing
  in fmap fst (factorSplit (mDims m) [0, 1] (mAmp m))

-- From |11> under bit 1 the correction restores the input, up to the factor 1/sqrt2 ...
-- >>> visibleFactor andUncomputedByMeasurement [SIn] (ket [2, 2] [1, 1]) == Just (scaleS invSqrt2C (ket [2, 2] [1, 1]))
-- True

-- ... and without the correction the same run carries a minus sign.
-- >>> visibleFactor andNoCorrection [SIn] (ket [2, 2] [1, 1]) == Just (scaleS (negate invSqrt2C) (ket [2, 2] [1, 1]))
-- True

-- The suite's claims -----------------------------------------------------------

checks :: [(String, Bool)]
checks = concat
  [ [ ( "andComputed: drop a unsafe for a superposed input"
      , semanticVerdict visXY andComputed "a" [] == Unsafe ) ]
  , [ ( "andUncomputedByMeasurement: drop a safe on both records, opposite parked lines"
      , semanticVerdict visXY andUncomputedByMeasurement "a" [SIn]  == Safe
        && semanticVerdict visXY andUncomputedByMeasurement "a" [SOut] == Safe
        && semanticParked visXY andUncomputedByMeasurement "a" [SIn]  == Just [0, 1]
        && semanticParked visXY andUncomputedByMeasurement "a" [SOut] == Just [1, 0] ) ]
  , [ ( "andUncomputedByMeasurement from |" ++ nm ++ ">, block {1}: visible factor is "
        ++ "1/sqrt2 times the input, and the CZ correction restores the identity"
      , visibleFactor andUncomputedByMeasurement [SIn] inp == Just (scaleS invSqrt2C inp) )
    | (nm, inp) <- basisXY ]
  , [ ( "andUncomputedByMeasurement from |" ++ nm ++ ">, complement of {1}: visible factor "
        ++ "is 1/sqrt2 times the input"
      , visibleFactor andUncomputedByMeasurement [SOut] inp == Just (scaleS invSqrt2C inp) )
    | (nm, inp) <- basisXY ]
  , [ ( "andNoCorrection from |" ++ nm ++ ">, block {1}: no phase when x and y are not both 1"
      , visibleFactor andNoCorrection [SIn] inp == Just (scaleS invSqrt2C inp) )
    | (nm, inp) <- take 3 basisXY ]
  , [ ( "andNoCorrection from |11>, block {1}: visible factor is -1/sqrt2 times |11>, "
        ++ "the phase the correction cancels"
      , visibleFactor andNoCorrection [SIn] (ket [2, 2] [1, 1])
          == Just (scaleS (negate invSqrt2C) (ket [2, 2] [1, 1])) ) ]
  , -- the Toffoli entangles a with x, y before the lift (that is why
    -- andComputed's unmeasured drop is refused above), so the runtime
    -- check's pre-lift parking hypothesis fails and it declines on both
    -- records rather than deciding them.
    [ ( "andUncomputedByMeasurement: runtime check declines on both records, prefix-parks false"
      , let r = residualCheck visXY andUncomputedByMeasurement "a"
        in rDepth r == 1
           && lookup "prefix-parks" (rHyps r) == Just False
           && map reVerdict (rTable r) == [HypothesesFail, HypothesesFail] ) ]
  ]

-- Fifteen claims; the first is the unsafe Toffoli.
-- >>> length checks
-- 15

-- >>> map fst (take 1 checks)
-- ["andComputed: drop a unsafe for a superposed input"]
