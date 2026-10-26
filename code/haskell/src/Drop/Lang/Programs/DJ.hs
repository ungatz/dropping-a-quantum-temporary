-- Drop.Lang.Programs.DJ: Deutsch-Jozsa, and what happens to its temporary.
--
-- Question: Is the temporary of Deutsch-Jozsa safe to drop without uncomputing it?
-- Answer:   The ancilla t is prepared on |-> (X, then H). The oracle gate on x and t kicks a phase
--           back into x and leaves t on the line [|->] for every input, so the drop is safe for
--           each of the four one-bit oracles (f = 0, f = 1, f = x, f = 1 - x), constant and
--           balanced alike, with no uncompute (djPaper; djProg adds the lift of x that reads the
--           answer off). Two variants start t at |0> and write f(x) into it. Left as it is
--           (djNoUncompute) the drop is safe exactly when f is constant. After a second
--           application of the oracle (djUncomputed) it is safe for every f, with t parked on
--           [|0>]. At depth 0 the static pass of Drop.Lang.Pass admits the |-> program on a table
--           of one row.
-- Paper:    sec:dj (worked: Deutsch-Jozsa), sec:lang:syntax (the listing of dj.s), app:corpus.
-- Shapes:   visDJ         the visible register: x, two levels.
--           oracles       the four one-bit functions, named by their formulas.
--           djPaper f     the |-> program: new t, X, H, H x, oracle f, H x, drop t.
--           djProg f      djPaper f, then a lift of x against {0}.
--           djNoUncompute f, djUncomputed f
--                         the |0> variants, without and with the second oracle application.
-- Corpus file: programs/dj.s holds djPaper fId (the oracle f(x) = x, as CX x t); the check
--           "programs/dj.s is the module's program as syntax" pairs them, and "dj.s verdicts agree
--           with the DJ module (f=x), parked [|->]" compares verdicts.

module Drop.Lang.Programs.DJ where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass

-- The oracles and the register ----------------------------------------------------

fConst0, fConst1, fId, fNot :: Int -> Int
fConst0 _ = 0
fConst1 _ = 1
fId x     = x
fNot x    = 1 - x

-- Each function as its two values, on 0 and on 1.
-- >>> [ (f 0, f 1) | f <- [fConst0, fConst1, fId, fNot] ]
-- [(0,0),(1,1),(0,1),(1,0)]

oracles :: [(String, Int -> Int)]
oracles = [("f=0", fConst0), ("f=1", fConst1), ("f=x", fId), ("f=1-x", fNot)]

-- >>> map fst oracles
-- ["f=0","f=1","f=x","f=1-x"]

visDJ :: VisSpec
visDJ = [("x", 2)]

-- >>> visDJ
-- [("x",2)]

-- The programs, smallest first -----------------------------------------------------

-- | The program of the paper's syntax subsection, and the corpus file dj.s:
-- |-> temporary, kickback, drop, and return.
djPaper :: (Int -> Int) -> Prog QS2
djPaper f =
  [ New "t" 2
  , Gate gX ["t"]
  , Gate gH ["t"]
  , Gate gH ["x"]
  , Gate (gUf f) ["x", "t"]
  , Gate gH ["x"]
  , Drop ["t"]
  ]

-- The paper's program as text, for the oracle f(x) = x.
-- >>> :m + Drop.Lang.Render Drop.Lang.Parser
-- >>> let listing = mapM_ (putStrLn . renderCmd) . mapProg embedQS2
-- >>> listing (djPaper fId)
-- new t : [2] @ |0>;
-- X t;
-- H t;
-- H x;
-- CX x t;
-- H x;
-- drop t;

-- It is the text of programs/dj.s, parsed.
-- >>> readFile "programs/dj.s" >>= \src -> print (fmap (== (visDJ, mapProg embedQS2 (djPaper fId))) (parseProgram src))
-- Right True

-- Safe for each of the four oracles, constant or balanced: one site, no lift, one verdict.
-- >>> [ (n, map drRows (verdict visDJ (djPaper f))) | (n, f) <- oracles ]
-- [("f=0",[[([],Safe)]]),("f=1",[[([],Safe)]]),("f=x",[[([],Safe)]]),("f=1-x",[[([],Safe)]])]

-- | The same, with the lift of x that reads the answer off. The drop is
-- before the lift, so no site sees it; the lift is what makes the
-- decision readable, and the checks below use it.
djProg :: (Int -> Int) -> Prog QS2
djProg f = djPaper f ++ [ Lift "r" "x" [0] ]

-- >>> drop 7 (djProg fId)
-- [Lift "r" "x" [0]]

-- >>> verdict visDJ (djProg fId)
-- [DropReport {drSite = ["t"], drRows = [([],Safe)]}]

-- | t at |0>, f(x) written into it and not uncomputed.
djNoUncompute :: (Int -> Int) -> Prog QS2
djNoUncompute f =
  [ New "t" 2, Gate gH ["x"], Gate (gUf f) ["x", "t"], Drop ["t"] ]

-- Safe exactly when f is constant: for f = x and f = 1 - x the written value correlates t with x.
-- >>> [ (n, map drRows (verdict visDJ (djNoUncompute f))) | (n, f) <- oracles ]
-- [("f=0",[[([],Safe)]]),("f=1",[[([],Safe)]]),("f=x",[[([],Unsafe)]]),("f=1-x",[[([],Unsafe)]])]

-- | The same, uncomputed: the oracle is an involution.
djUncomputed :: (Int -> Int) -> Prog QS2
djUncomputed f =
  [ New "t" 2, Gate gH ["x"], Gate (gUf f) ["x", "t"]
  , Gate (gUf f) ["x", "t"], Drop ["t"] ]

-- A second oracle application undoes the first: safe for every f.
-- >>> [ (n, map drRows (verdict visDJ (djUncomputed f))) | (n, f) <- oracles ]
-- [("f=0",[[([],Safe)]]),("f=1",[[([],Safe)]]),("f=x",[[([],Safe)]]),("f=1-x",[[([],Safe)]])]

minusLine :: StateV QS2
minusLine = [1, -1]                    -- the canonical form of [|->]

-- >>> minusLine
-- [1,-1]

-- The |-> program leaves t on [|->]; the uncomputed variant leaves it on [|0>].
-- >>> probeResult visDJ (djPaper fId) "t" [] [1, 0] == PLine minusLine
-- True

-- >>> probeResult visDJ (djUncomputed fId) "t" [] [1, 0]
-- PLine [1,0]

-- The suite's claims ----------------------------------------------------------------

checks :: [(String, Bool)]
checks = concat
  [ -- the textbook program: safe on all four oracles, leaves the temporary constant on [|->]
    [ ("DJ " ++ nm ++ " safe, parked [|->]"
      , semanticVerdict visDJ (djProg f) "t" [] == Safe
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
    [ ("DJ-noUC " ++ nm ++ " " ++ (if cst then "safe" else "unsafe")
      , semanticVerdict visDJ (djNoUncompute f) "t" []
          == (if cst then Safe else Unsafe))
    | ((nm, f), cst) <- zip oracles [True, True, False, False] ]
  , -- the uncomputed variant: safe for every f, leaves the temporary constant again on [|0>]
    [ ("DJ-UC " ++ nm ++ " safe, parked [|0>]"
      , semanticVerdict visDJ (djUncomputed f) "t" [] == Safe
        && probeResult visDJ (djUncomputed f) "t" [] [1, 0] == PLine [1, 0])
    | (nm, f) <- oracles ]
  ]

-- Four oracles in each of five families of claims.
-- >>> length checks
-- 20

-- >>> map fst (take 1 checks)
-- ["DJ f=0 safe, parked [|->]"]
