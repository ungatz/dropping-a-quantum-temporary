-- Drop.Lang.Programs.Grover: one Grover iteration on two qubits, with an oracle temporary.
--
-- Question: Is the temporary of Grover's oracle safe to drop once its mark has been uncomputed?
-- Answer:   The oracle marks |11> by a Toffoli from x1, x2 into a temporary t, a Z on t, and a
--           Toffoli back. After the uncompute t sits on [|0>] for every input and the drop is
--           safe (groverProg); the static pass of Drop.Lang.Pass admits it at depth 0. Without the
--           second Toffoli (groverBroken) t is correlated with the visible registers and the
--           drop is unsafe; the pass refuses it. One iteration from |00> lands exactly on the
--           marked item |11>.
-- Paper:    sec:lang:algorithms (the listing of grover.s), app:corpus.
-- Shapes:   visG            the visible registers: x1 and x2, two levels each.
--           groverF b       one iteration, with the uncompute present (b = True) or absent.
--           groverProg, groverBroken
--                           groverF True and groverF False.
-- Corpus file: programs/grover.s holds groverProg; the check "programs/grover.s is the module's
--           program as syntax" pairs them, and "grover.s verdicts agree with ExGrover" compares
--           verdicts.

module Drop.Lang.Programs.Grover where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass

visG :: VisSpec
visG = [("x1", 2), ("x2", 2)]

-- >>> visG
-- [("x1",2),("x2",2)]

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
  ++ [ Drop ["t"]
     , Gate gDiff ["x1", "x2"]
     ]

-- Eight commands with the uncompute, seven without.
-- >>> map (length . groverF) [True, False]
-- [8,7]

groverProg, groverBroken :: Prog QS2
groverProg   = groverF True
groverBroken = groverF False

-- The iteration as text, and its one site.
-- >>> :m + Drop.Lang.Render Drop.Lang.Parser
-- >>> let listing = mapM_ (putStrLn . renderCmd) . mapProg embedQS2
-- >>> listing groverProg
-- H x1;
-- H x2;
-- new t : [2] @ |0>;
-- CCX x1 x2 t;
-- Z t;
-- CCX x1 x2 t;
-- drop t;
-- Diff x1 x2;

-- It is the text of programs/grover.s, parsed.
-- >>> readFile "programs/grover.s" >>= \src -> print (fmap (== (visG, mapProg embedQS2 groverProg)) (parseProgram src))
-- Right True

-- After the uncompute the drop is safe; without it the drop is unsafe.
-- >>> verdict visG groverProg
-- [DropReport {drSite = ["t"], drRows = [([],Safe)]}]

-- >>> verdict visG groverBroken
-- [DropReport {drSite = ["t"], drRows = [([],Unsafe)]}]

-- The temporary is left on [|0>], the basis line, from |00>.
-- >>> probeResult visG groverProg "t" [] (ket [2, 2] [0, 0])
-- PLine [1,0]

-- The static pass admits the first and refuses the second.
-- >>> map reVerdict (rTable (residualCheck visG groverProg "t"))
-- [Admit]

-- >>> map reVerdict (rTable (residualCheck visG groverBroken "t"))
-- [Refuse]

-- One iteration from |00> lands exactly on the marked item |11>, with t back on |0>.
-- >>> let m = runStmts (initMach visG (ket [2, 2] [0, 0])) groverProg [] Nothing
-- >>> stateProportional (mAmp m) (ket (mDims m) [1, 1, 0])
-- True

-- The suite's claims ------------------------------------------------------------------

checks :: [(String, Bool)]
checks =
  [ ( "Grover oracle after the uncompute: safe, parked [|0>]"
    , semanticVerdict visG groverProg "t" [] == Safe
      && probeResult visG groverProg "t" [] (ket [2,2] [0,0]) == PLine [1, 0] )
  , ( "Grover oracle before the uncompute: unsafe"
    , semanticVerdict visG groverBroken "t" [] == Unsafe )
  , ( "Grover runtime check depth 0, table 1, admit"
    , let r = residualCheck visG groverProg "t"
      in rDepth r == 0 && map reVerdict (rTable r) == [Admit] )
  , ( "Grover without the uncompute: the runtime check refuses"
    , map reVerdict (rTable (residualCheck visG groverBroken "t")) == [Refuse] )
  , ( "one iteration from |00> lands exactly on the marked item |11>"
    , let m = runStmts (initMach visG (ket [2,2] [0,0])) groverProg [] Nothing
      in stateProportional (mAmp m) (ket (mDims m) [1, 1, 0]) )
  ]

-- >>> length checks
-- 5

-- >>> map fst (take 1 checks)
-- ["Grover oracle after the uncompute: safe, parked [|0>]"]
