-- Drop.Lang.Programs.Superdense: superdense coding of two bits.
--
-- Question: Is Alice's half of a superdense-coding exchange safe to drop once both qubits are
--           measured?
-- Answer:   Bob's qubit b is visible; Alice's qubit a is the temporary. They share a Bell pair.
--           Alice encodes the message (b0, b1) on her half alone, an X for b1 and a Z for b0;
--           Bob decodes with a CX and an H; both qubits are lifted; a is dropped. For each of the
--           four messages the drop is safe on every trace that is reachable, and the verdict does
--           not depend on the outcome, unlike program (c) of the paper, whose two records have
--           opposite verdicts. From the intended input |0>, the one trace that reads the encoded
--           pair back has weight 1 and the other three have weight 0. The lift convention is that
--           the bit is 1 when the measured block {0} survives, so outcome 0 is the selection SIn.
-- Paper:    app:corpus (the row for superdense.s), sec:meas:programs (program (c), the contrast).
-- Shapes:   visSD            the visible register: b, two levels.
--           bitPairs         the four messages, as (b0, b1).
--           superdenseF m    the program for the message m: new a, the Bell pair, Alice's encoding,
--                            Bob's decoding, the lifts p0 of a and p1 of b, drop a.
--           selOfPair m      the selection on which m is read back.
-- Corpus file: programs/superdense.s holds superdenseProg (1, 1); the check "programs/superdense.s
--           is the module's program as syntax" pairs them, and "superdense.s verdicts agree with
--           ExSuperdense at (1,1)" compares verdicts.

module Drop.Lang.Programs.Superdense where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion

visSD :: VisSpec
visSD = [("b", 2)]

-- >>> visSD
-- [("b",2)]

-- | The four classical messages, as (b0, b1).
bitPairs :: [(Int, Int)]
bitPairs = [ (b0, b1) | b0 <- [0, 1], b1 <- [0, 1] ]

-- >>> bitPairs
-- [(0,0),(0,1),(1,0),(1,1)]

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

-- The message (0, 0) encodes nothing: eight commands. The message (1, 1) adds the X and the Z.
-- >>> map (length . superdenseF) [(0, 0), (1, 1)]
-- [8,10]

-- The message (1, 1) as text, as in programs/superdense.s.
-- >>> :m + Drop.Lang.Render Drop.Lang.Parser Drop.Lang.Pass
-- >>> mapM_ (putStrLn . renderCmd) (mapProg embedQS2 (superdenseF (1, 1)))
-- new a : [2] @ |0>;
-- H a;
-- CX a b;
-- X a;
-- Z a;
-- CX a b;
-- H a;
-- p0 = lift[{0}] a;
-- p1 = lift[{0}] b;
-- drop a;

superdenseProg :: (Int, Int) -> Prog QS2
superdenseProg = superdenseF

-- >>> superdenseProg (1, 0) == superdenseF (1, 0)
-- True

-- It is the text of programs/superdense.s, parsed.
-- >>> readFile "programs/superdense.s" >>= \src -> print (fmap (== (visSD, mapProg embedQS2 (superdenseProg (1, 1)))) (parseProgram src))
-- Right True

-- | The lift convention is that the bit is 1 when the measured block {0}
-- survives, so outcome 0 is the selection SIn.
selOfOutcome :: Int -> Sel
selOfOutcome 0 = SIn
selOfOutcome _ = SOut

-- >>> map selOfOutcome [0, 1]
-- [SIn,SOut]

-- | The trace on which the pair (b0, b1) is read back.
selOfPair :: (Int, Int) -> [Sel]
selOfPair (b0, b1) = [selOfOutcome b0, selOfOutcome b1]

-- >>> map selOfPair bitPairs
-- [[SIn,SIn],[SIn,SOut],[SOut,SIn],[SOut,SOut]]

verdicts :: (Int, Int) -> [Verdict]
verdicts p = [ semanticVerdict visSD (superdenseProg p) "a" sel
             | sel <- allSelections 2 ]

-- The four traces, in the order SIn SIn, SIn SOut, SOut SIn, SOut SOut. The message (0, 0) is
-- read on the first; no trace is unsafe, and two are unreachable.
-- >>> verdicts (0, 0)
-- [Safe,Safe,Unreachable,Unreachable]

-- >>> verdicts (1, 1)
-- [Unreachable,Unreachable,Safe,Safe]

-- >>> verdict visSD (superdenseProg (1, 1))
-- [DropReport {drSite = ["a"], drRows = [([SIn,SIn],Unreachable),([SIn,SOut],Unreachable),([SOut,SIn],Safe),([SOut,SOut],Safe)]}]

-- The static pass agrees: it admits the reachable records and calls the others unreachable.
-- >>> map (\e -> (reBits e, reVerdict e)) (rTable (residualCheck visSD (superdenseProg (1, 1)) "a"))
-- [([1,1],RUnreachable),([1,0],RUnreachable),([0,1],Admit),([0,0],Admit)]

-- | The exact weight of one trace, run from the intended visible input |0>.
traceWeight :: (Int, Int) -> [Sel] -> QS2
traceWeight p sel =
  norm2S (mAmp (runStmts (initMach visSD (ket [2] [0])) (superdenseProg p) sel Nothing))

-- From |0>, the trace that reads the message back has weight 1; every other trace has weight 0.
-- >>> [ traceWeight (1, 1) sel == 1 | sel <- allSelections 2 ]
-- [False,False,False,True]

-- >>> and [ traceWeight p (selOfPair p) == 1 | p <- bitPairs ]
-- True

-- The suite's claims ------------------------------------------------------------------

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

-- Three claims for each of the four messages.
-- >>> length checks
-- 12

-- >>> map fst (take 1 checks)
-- ["superdense 00: drop a safe on every reachable trace"]
