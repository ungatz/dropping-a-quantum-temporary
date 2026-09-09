-- Grover.hs: one Grover iteration on two qubits with an oracle ancilla,
-- one of the eight algorithms.
--
-- The oracle marks |11> by a Toffoli, a Z, and a Toffoli back.  After the
-- uncompute the ancilla sits on [|0>] and the drop is safe; omitting it
-- correlates the ancilla with the visible register, and the drop is unsafe.

module S.Programs.Grover where

import S.Lang.Ring
import S.Lang.QState
import S.Lang.Gates
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass

visG :: VisSpec
visG = [("x1", 2), ("x2", 2)]

-- | One Grover iteration, with the uncompute step present or absent.
groverF :: Bool -> Prog QS2
groverF uncompute =
  [ Gate gH ["x1"]
  , Gate gH ["x2"]
  , New "t" 2
  , Gate gCCX ["x1", "x2", "t"]
  , Gate gZ ["t"]
  ]
  ++ [ Gate gCCX ["x1", "x2", "t"] | uncompute ]
  ++ [ Drop "t"
     , Gate gDiff ["x1", "x2"]
     ]

groverProg, groverBroken :: Prog QS2
groverProg   = groverF True
groverBroken = groverF False

checks :: [(String, Bool)]
checks =
  [ ( "Grover oracle after the uncompute: admissible, parked [|0>]"
    , semanticVerdict visG groverProg "t" [] == Admissible
      && probeResult visG groverProg "t" [] (ket [2,2] [0,0]) == PLine [1, 0] )
  , ( "Grover oracle before the uncompute: inadmissible"
    , semanticVerdict visG groverBroken "t" [] == Inadmissible )
  , ( "Grover runtime check depth 0, table 1, admit"
    , let r = residualCheck visG groverProg "t"
      in rDepth r == 0 && map reVerdict (rTable r) == [Admit] )
  , ( "Grover without the uncompute: the runtime check refuses"
    , map reVerdict (rTable (residualCheck visG groverBroken "t")) == [Refuse] )
  , ( "one iteration from |00> lands exactly on the marked item |11>"
    , let m = runStmts (initMach visG (ket [2,2] [0,0])) groverProg [] Nothing
      in stateProportional (mAmp m) (ket (mDims m) [1, 1, 0]) )
  ]
