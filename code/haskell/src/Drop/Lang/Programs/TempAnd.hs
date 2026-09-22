-- TempAnd.hs: a temporary computed by a Toffoli, uncomputed by measurement,
-- as in Gidney, "Halving the cost of quantum addition", Quantum 2, 74 (2018).
--
-- The Toffoli entangles a with x, y on a superposed input, so dropping a
-- right after it is refused; H, then a measurement of a corrected by a CZ
-- on x, y when the outcome is 1, drops it safely on both records instead.

module Drop.Lang.Programs.TempAnd where

import Drop.Lang.Cyclo
import Drop.Lang.QState
import Drop.Lang.Gates
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Pass

visXY :: VisSpec
visXY = [("x", 2), ("y", 2)]

cz :: Matrix Cyclo
cz = gCPhase (-1)

andComputed :: Prog Cyclo
andComputed =
  [ New "a" 2
  , Gate gCCX ["x", "y", "a"]
  , Drop ["a"]
  ]

andUncomputedByMeasurement :: Prog Cyclo
andUncomputedByMeasurement =
  [ New "a" 2
  , Gate gCCX ["x", "y", "a"]
  , Gate gHC ["a"]
  , Lift "m" "a" [1]
  , IfBit (GParam "m") [Gate cz ["x", "y"]] []
  , Drop ["a"]
  ]

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

basisXY :: [(String, StateV Cyclo)]
basisXY =
  [ ("00", ket [2, 2] [0, 0]), ("01", ket [2, 2] [0, 1])
  , ("10", ket [2, 2] [1, 0]), ("11", ket [2, 2] [1, 1]) ]

-- | The visible (x, y) factor at the end of the program, run from the given
-- basis input.
visibleFactor :: Prog Cyclo -> [Sel] -> StateV Cyclo -> Maybe (StateV Cyclo)
visibleFactor prog sel inp =
  let m = runStmts (initMach visXY inp) prog sel Nothing
  in fmap fst (factorSplit (mDims m) [0, 1] (mAmp m))

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
