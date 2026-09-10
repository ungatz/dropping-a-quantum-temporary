-- DJ.hs: Deutsch-Jozsa, one of the suite's algorithms.
--
-- Ancilla on |-> gives phase kickback: the temporary stays on [|->] for
-- every input, so the drop is safe for constant and balanced f alike, with
-- no uncompute. Two variants: t at |0> with f(x) written in separates
-- constant from balanced, and a second oracle application restores safety.

module S.Programs.DJ where

import S.Lang.Ring
import S.Lang.QState
import S.Lang.Gates
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass

fConst0, fConst1, fId, fNot :: Int -> Int
fConst0 _ = 0
fConst1 _ = 1
fId x     = x
fNot x    = 1 - x

oracles :: [(String, Int -> Int)]
oracles = [("f=0", fConst0), ("f=1", fConst1), ("f=x", fId), ("f=1-x", fNot)]

visDJ :: VisSpec
visDJ = [("x", 2)]

-- | The textbook program: |-> ancilla, kickback, drop, then the lift of x.
djProg :: (Int -> Int) -> Prog QS2
djProg f =
  [ New "t" 2
  , Gate gX ["t"]
  , Gate gH ["t"]
  , Gate gH ["x"]
  , Gate (gUf f) ["x", "t"]
  , Gate gH ["x"]
  , Drop "t"
  , Lift "r" "x" [0]
  ]

-- | t at |0>, f(x) written into it and not uncomputed.
djNoUncompute :: (Int -> Int) -> Prog QS2
djNoUncompute f =
  [ New "t" 2, Gate gH ["x"], Gate (gUf f) ["x", "t"], Drop "t" ]

-- | The same, uncomputed: the oracle is an involution.
djUncomputed :: (Int -> Int) -> Prog QS2
djUncomputed f =
  [ New "t" 2, Gate gH ["x"], Gate (gUf f) ["x", "t"]
  , Gate (gUf f) ["x", "t"], Drop "t" ]

minusLine :: StateV QS2
minusLine = [1, -1]                    -- the canonical form of [|->]

checks :: [(String, Bool)]
checks = concat
  [ -- the textbook program: safe on all four oracles, leaves the temporary constant on [|->]
    [ ("DJ " ++ nm ++ " admissible, parked [|->]"
      , semanticVerdict visDJ (djProg f) "t" [] == Admissible
        && probeResult visDJ (djProg f) "t" [] [1, 0] == PLine minusLine)
    | (nm, f) <- oracles ]
  , -- the runtime check at depth 0: a one-entry table that accepts
    [ ("DJ " ++ nm ++ " runtime check depth 0, table 1, admit"
      , let r = residualCheck visDJ (djProg f) "t"
        in rDepth r == 0 && map reVerdict (rTable r) == [Admit]
           && all snd (rHyps r))
    | (nm, f) <- oracles ]
  , -- the decision itself: on the intended input |0>, selecting the block
    -- {0} of x carries weight 1 for constant f and 0 for balanced f
    [ ("DJ " ++ nm ++ " reads " ++ (if cst then "0" else "1") ++ " on |0>"
      , let m = runStmts (initMach visDJ (ket [2] [0])) (djProg f) [SIn] Nothing
        in norm2S (mAmp m) == (if cst then 1 else 0))
    | ((nm, f), cst) <- zip oracles [True, True, False, False] ]
  , -- the |0>-ancilla variant without the uncompute: safe iff constant
    [ ("DJ-noUC " ++ nm ++ " " ++ (if cst then "admissible" else "inadmissible")
      , semanticVerdict visDJ (djNoUncompute f) "t" []
          == (if cst then Admissible else Inadmissible))
    | ((nm, f), cst) <- zip oracles [True, True, False, False] ]
  , -- the uncomputed variant: safe for every f, leaves the temporary constant again on [|0>]
    [ ("DJ-UC " ++ nm ++ " admissible, parked [|0>]"
      , semanticVerdict visDJ (djUncomputed f) "t" [] == Admissible
        && probeResult visDJ (djUncomputed f) "t" [] [1, 0] == PLine [1, 0])
    | (nm, f) <- oracles ]
  ]
