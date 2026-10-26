-- Drop.Lang.Programs.RUS: one repeat-until-success step, unrolled.
--
-- Question: Is the temporary of a repeat-until-success step safe to drop, when both branches of
--           its conditional run the same code?
-- Answer:   A three-level temporary t is tilted off |0> by a rational rotation, then lifted
--           against the block {0, 1}; the if runs the same joint gate on x and t in both
--           branches. What differs between the two records is only the state the lift
--           transferred. The drop is unsafe when the block {0, 1} survives and safe when its
--           complement {2} does, with t parked on the basis line |2>: one program text, opposite
--           verdicts. The static pass of Drop.Lang.Pass decides the two apart by the one
--           classical bit: it refuses on bit 1, admits on bit 0, and agrees with the criterion on
--           both rows. Everything runs over the rationals; no radical appears.
-- Paper:    app:corpus (the row for rus.s), sec:eval:corpus.
-- Shapes:   visR      the visible register: x, three levels.
--           rusProg   new t, the tilt, a lift of t against {0, 1}, the if, drop t.
-- Corpus file: programs/rus.s holds rusProg; the check "programs/rus.s is the module's program as
--           syntax" pairs them, and "rus.s verdicts agree with ExRUS" compares verdicts.

module Drop.Lang.Programs.RUS where

import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Criterion
import Drop.Lang.Pass

visR :: VisSpec
visR = [("x", 3)]

-- >>> visR
-- [("x",3)]

rusProg :: Prog Rational
rusProg =
  [ New "t" 3
  , Gate gTilt ["t"]
  , Lift "p" "t" [0, 1]
  , IfBit (GParam "p") [Gate gREAD3 ["x", "t"]]   -- success branch: read
              [Gate gREAD3 ["x", "t"]]   -- failure branch: same code
  , Drop ["t"]
  ]

-- The step as text: both branches read the same.
-- >>> :m + Drop.Lang.Render Drop.Lang.Parser Drop.Lang.Scalar
-- >>> mapM_ (putStrLn . renderCmd) (mapProg fromRational rusProg)
-- new t : [3] @ |0>;
-- tilt t;
-- p = lift[{0,1}] t;
-- if p { READ3 x t; } else { READ3 x t; }
-- drop t;

-- It is the text of programs/rus.s, parsed.
-- >>> readFile "programs/rus.s" >>= \src -> print (fmap (== (visR, mapProg fromRational rusProg)) (parseProgram src))
-- Right True

-- One lift before the drop, two records, opposite verdicts: unsafe when the block {0, 1} survives.
-- >>> verdict visR rusProg
-- [DropReport {drSite = ["t"], drRows = [([SIn],Unsafe),([SOut],Safe)]}]

-- Where the safe record parks t: on the basis line |2>.
-- >>> semanticParked visR rusProg "t" [SOut]
-- Just [0 % 1,0 % 1,1 % 1]

-- The static pass: bit 1 refuses, bit 0 admits, and the line the prefix parks t on is (1, 1, 1/2).
-- >>> let table = residualCheck visR rusProg "t"
-- >>> (map (\e -> (reBits e, reVerdict e)) (rTable table), rParked table)
-- ([([1],Refuse),([0],Admit)],Just [1 % 1,1 % 1,1 % 2])

-- It agrees with the criterion on both rows.
-- >>> map (\e -> agreeRC (reVerdict e) (semanticVerdict visR rusProg "t" (reSel e))) (rTable table)
-- [Agree,Agree]

-- The suite's claims ------------------------------------------------------------------

checks :: [(String, Bool)]
checks =
  let r    = residualCheck visR rusProg "t"
      ent b = case [ e | e <- rTable r, reBits e == b ] of
                (e : _) -> Just e
                []      -> Nothing
  in
  [ ( "RUS verdicts differ across the two selections"
    , semanticVerdict visR rusProg "t" [SIn]  == Unsafe
      && semanticVerdict visR rusProg "t" [SOut] == Safe )
  , ( "RUS runtime check depth 1, table 2, every hypothesis holds"
    , rDepth r == 1 && length (rTable r) == 2 && all snd (rHyps r) )
  , ( "RUS runtime check: bit 1 refuses, bit 0 admits"
    , fmap reVerdict (ent [1]) == Just Refuse
      && fmap reVerdict (ent [0]) == Just Admit )
  , ( "RUS parked line (1,1,1/2); transferred states (1,1,0) and (0,0,1)"
    , rParked r == Just [1, 1, 1/2]
      && case (ent [1] >>= reTransferred, ent [0] >>= reTransferred) of
           (Just t1, Just t0) ->
             stateProportional t1 [1, 1, 0] && stateProportional t0 [0, 0, 1]
           _ -> False )
  , ( "RUS runtime check agrees with the criterion on both entries"
    , all (\e -> agreeRC (reVerdict e)
                   (semanticVerdict visR rusProg "t" (reSel e)) == Agree)
          (rTable r) )
  ]

-- >>> length checks
-- 5

-- >>> map fst (take 1 checks)
-- ["RUS verdicts differ across the two selections"]
