-- Superdense.hs: superdense coding, one of the eight algorithms (the implementation section).
--
-- Bob's qubit b is visible; Alice's qubit a is the temporary. They share a
-- Bell pair; Alice encodes two bits into her half alone; Bob decodes and
-- both halves are measured. The drop of a is safe and outcome-independent
-- on every trace, unlike the boundary program of the section on why the record matters.

module Drop.Lang.Programs.Superdense where

import Drop.Lang.Ring
import Drop.Lang.QState
import Drop.Lang.Gates
import Drop.Lang.Syntax
import Drop.Lang.Interp

visSD :: VisSpec
visSD = [("b", 2)]

-- | The four classical messages, as (b0, b1).
bitPairs :: [(Int, Int)]
bitPairs = [ (b0, b1) | b0 <- [0, 1], b1 <- [0, 1] ]

-- | Bell pair, Alice's encoding on a alone, Bob's decoding, then both
-- outcomes lifted and Alice's half dropped.
superdenseF :: (Int, Int) -> Prog QS2
superdenseF (b0, b1) =
  [ New "a" 2
  , Gate gH ["a"]
  , Gate gCX ["a", "b"]           -- the shared Bell pair
  ]
  ++ [ Gate gX ["a"] | b1 == 1 ]   -- Alice encodes, on her half only
  ++ [ Gate gZ ["a"] | b0 == 1 ]
  ++ [ Gate gCX ["a", "b"]        -- Bob decodes
     , Gate gH ["a"]
     , Lift "p0" "a" [0]
     , Lift "p1" "b" [0]
     , Drop ["a"]
     ]

superdenseProg :: (Int, Int) -> Prog QS2
superdenseProg = superdenseF

-- | The lift convention is that the bit is 1 when the measured block {0}
-- survives, so outcome 0 is the selection SIn.
selOfOutcome :: Int -> Sel
selOfOutcome 0 = SIn
selOfOutcome _ = SOut

-- | The trace on which the pair (b0, b1) is read back.
selOfPair :: (Int, Int) -> [Sel]
selOfPair (b0, b1) = [selOfOutcome b0, selOfOutcome b1]

verdicts :: (Int, Int) -> [Verdict]
verdicts p = [ semanticVerdict visSD (superdenseProg p) "a" sel
             | sel <- allSelections 2 ]

-- | The exact weight of one trace, run from the intended visible input |0>.
traceWeight :: (Int, Int) -> [Sel] -> QS2
traceWeight p sel =
  norm2S (mAmp (runStmts (initMach visSD (ket [2] [0])) (superdenseProg p) sel Nothing))

checks :: [(String, Bool)]
checks = concat
  [ [ ("superdense " ++ nm p ++ ": drop a safe on every reachable trace"
      , all (/= Unsafe) (verdicts p)
        && any (== Safe) (verdicts p))
    | p <- bitPairs ]
  , [ ("superdense " ++ nm p ++ ": the verdict does not depend on the outcome"
      , allEqual [ v | v <- verdicts p, v /= Unreachable ])
    | p <- bitPairs ]
  , [ ("superdense " ++ nm p ++ ": the measured pair is the encoded pair,"
       ++ " weight 1, the other traces unreachable"
      , traceWeight p (selOfPair p) == 1
        && and [ traceWeight p sel == 0
               | sel <- allSelections 2, sel /= selOfPair p ])
    | p <- bitPairs ]
  ]
  where nm (b0, b1) = show b0 ++ show b1
