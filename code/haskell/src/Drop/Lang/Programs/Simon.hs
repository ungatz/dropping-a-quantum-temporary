-- Simon.hs: Simon's problem on two bits, hidden string s = 11.
--
-- The oracle |x1 x2>|w> -> |x1 x2>|w xor f(x1,x2)> is a permutation, not a
-- phase gate, so it entangles the work register with the visible one:
-- dropping w unmeasured is refused. Measuring w first is safe on both
-- branches, but on different lines: {0} and its complement are singletons.

module Drop.Lang.Programs.Simon where

import Drop.Lang.Cyclo
import Drop.Lang.QState
import Drop.Lang.Gates
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Pass

visSimon :: VisSpec
visSimon = [("x1", 2), ("x2", 2)]

-- | Simon's oracle for s = 11: f(00) = f(11) = 0, f(01) = f(10) = 1, values
-- as levels of the two-bit register w.  Xor by f is xor by its low bit.
simonOraclePerm :: Int -> Int
simonOraclePerm j =
  let x1 = j `div` 8
      x2 = (j `div` 4) `mod` 2
      w  = j `mod` 4
  in x1 * 8 + x2 * 4 + (if x1 /= x2 then flipLow w else w)
  where flipLow k = if even k then k + 1 else k - 1

simonCore :: Prog Cyclo
simonCore =
  [ New "w" 4
  , Gate gHC ["x1"]
  , Gate gHC ["x2"]
  , Gate (permGate 16 simonOraclePerm) ["x1", "x2", "w"]
  ]

simonProg :: Prog Cyclo
simonProg = simonCore ++ [Drop ["w"]]

simonMeasured :: Prog Cyclo
simonMeasured = simonCore ++ [Lift "s" "w" [0], Drop ["w"]]

basisW :: Int -> StateV Cyclo
basisW l = [ if i == l then 1 else 0 | i <- [0 .. 3] ]

-- | The visible factor at the end of the program, run from the given input.
visibleAfter :: Prog Cyclo -> [Sel] -> StateV Cyclo -> Maybe (StateV Cyclo)
visibleAfter prog sel inp =
  let m = runStmts (initMach visSimon inp) prog sel Nothing
  in fmap fst (factorSplit (mDims m) [0, 1] (mAmp m))

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
