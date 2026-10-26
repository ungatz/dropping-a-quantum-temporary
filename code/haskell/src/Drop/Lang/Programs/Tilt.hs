-- Drop.Lang.Programs.Tilt: the tilt family, a qutrit whose drop verdict depends on the record.
--
-- Question: Can one program text have a safe drop on one record and an unsafe drop on the other?
-- Answer:   Yes. A three-level temporary t is rotated off |0> by a rational "tilt", lifted against
--           the block {0, 1}, read by a joint gate with x, and dropped. The tilt gTilt takes |0>
--           to (2/3, 2/3, 1/3), which has a foot inside the measured block and a foot on |2>.
--           Keeping the block {0, 1} leaves t correlated with x, so the drop is unsafe; keeping
--           the complement leaves the basis line |2>, so it is safe. The two selections
--           disagree, so no verdict that ignores the record is right on both. The family has two
--           members, gTilt and gTilt2, and both run over the rationals: no radical appears. For
--           gTilt, from |0>, the two records have weights 8/9 and 1/9, and the static pass of
--           Drop.Lang.Pass parks t on (1, 1, 1/2), refuses bit 1 and admits bit 0. The paper
--           prints this statement on a qubit (program (c), thm:notext); the qutrit family is the
--           artifact's own witness.
-- Paper:    sec:boundary (why the record matters), thm:notext (the qubit version).
-- Shapes:   visTilt          the visible register: x, three levels.
--           tiltF u          new t, the tilt u, a lift of t against {0, 1}, the joint read of x
--                            and t, drop t.
--           tiltProg, tilt2Prog
--                            tiltF at the two members of the family.
--           member u name    the six checks shared by one member.
-- Corpus file: none; this program is the module's own. programs/rus.s is its neighbour, with an
--           if between the lift and the drop.

module Drop.Lang.Programs.Tilt where

import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Criterion
import Drop.Lang.Pass

visTilt :: VisSpec
visTilt = [("x", 3)]

-- >>> visTilt
-- [("x",3)]

tiltF :: Matrix Rational -> Prog Rational
tiltF u =
  [ New "t" 3
  , Gate u ["t"]
  , Lift "p" "t" [0, 1]
  , Gate gREAD3 ["x", "t"]
  , Drop ["t"]
  ]

-- Five commands, whatever the tilt.
-- >>> length (tiltF gTilt)
-- 5

tiltProgOf :: Matrix Rational -> Prog Rational
tiltProgOf = tiltF

tiltProg, tilt2Prog :: Prog Rational
tiltProg  = tiltProgOf gTilt
tilt2Prog = tiltProgOf gTilt2

-- The two members tilt |0> to different states.
-- >>> map (\u -> applyGate [3] u [0] (ket [3] [0] :: [Rational])) [gTilt, gTilt2]
-- [[2 % 3,2 % 3,1 % 3],[3 % 5,12 % 25,16 % 25]]

-- One lift before the drop, two records, opposite verdicts; the same for both members.
-- >>> verdict visTilt tiltProg
-- [DropReport {drSite = ["t"], drRows = [([SIn],Unsafe),([SOut],Safe)]}]

-- >>> verdict visTilt tilt2Prog
-- [DropReport {drSite = ["t"], drRows = [([SIn],Unsafe),([SOut],Safe)]}]

-- For gTilt the static pass parks t on (1, 1, 1/2), refuses bit 1 and admits bit 0.
-- >>> let table = residualCheck visTilt tiltProg "t"
-- >>> (rParked table, map (\e -> (reBits e, reVerdict e)) (rTable table))
-- (Just [1 % 1,1 % 1,1 % 2],[([1],Refuse),([0],Admit)])

-- Under the block {0, 1} the three basis inputs leave t entangled and only the all-ones input
-- factors; under the complement every input leaves t on |2>.
-- >>> [ probeResult visTilt tiltProg "t" [SIn] inp | inp <- [ket [3] [0], ket [3] [1], ket [3] [2], [1, 1, 1]] ]
-- [PFail,PFail,PFail,PLine [1 % 1,1 % 1,0 % 1]]

-- >>> [ probeResult visTilt tiltProg "t" [SOut] inp | inp <- [ket [3] [0], ket [3] [1], ket [3] [2], [1, 1, 1]] ]
-- [PLine [0 % 1,0 % 1,1 % 1],PLine [0 % 1,0 % 1,1 % 1],PLine [0 % 1,0 % 1,1 % 1],PLine [0 % 1,0 % 1,1 % 1]]

-- For gTilt, from |0>, the two records have weights 8/9 and 1/9, which sum to 1.
-- >>> map (\sel -> branchWeight visTilt tiltProg "t" sel (ket [3] [0])) [[SIn], [SOut]]
-- [8 % 9,1 % 9]

-- | The shared checks for one member of the family.
member :: Matrix Rational -> String -> [(String, Bool)]
member u nm =
  let p   = tiltProgOf u
      r   = residualCheck visTilt p "t"
      ent b = case [ e | e <- rTable r, reBits e == b ] of
                (e : _) -> Just e
                []      -> Nothing
  in
  [ ( nm ++ " selection {0,1}: unsafe"
    , semanticVerdict visTilt p "t" [SIn] == Unsafe )
  , ( nm ++ " selection {2}: safe"
    , semanticVerdict visTilt p "t" [SOut] == Safe )
  , ( nm ++ " the two selections disagree, so no text-level verdict exists"
    , semanticVerdict visTilt p "t" [SIn] /= semanticVerdict visTilt p "t" [SOut] )
  , ( nm ++ " runtime check depth 1, table 2, all hypotheses hold"
    , rDepth r == 1 && length (rTable r) == 2 && all snd (rHyps r) )
  , ( nm ++ " runtime check: bit 1 refuses, bit 0 admits"
    , fmap reVerdict (ent [1]) == Just Refuse
      && fmap reVerdict (ent [0]) == Just Admit )
  , ( nm ++ " transferred states are the parked line met with the block"
    , case (rParked r, ent [1] >>= reTransferred, ent [0] >>= reTransferred) of
        (Just g, Just t1, Just t0) ->
          -- impossible: g is the parked line of a three-level temporary, so it has entries 0, 1 and 2
          t1 == [g !! 0, g !! 1, 0] && t0 == [0, 0, g !! 2]
        _ -> False )
  ]

-- Six checks for each member of the family.
-- >>> map (length . uncurry member) [(gTilt, "tilt(1/3)"), (gTilt2, "tilt(3/5-4/5)")]
-- [6,6]

-- >>> map fst (take 2 (member gTilt "tilt(1/3)"))
-- ["tilt(1/3) selection {0,1}: unsafe","tilt(1/3) selection {2}: safe"]

-- The suite's claims ------------------------------------------------------------------

checks :: [(String, Bool)]
checks = concat
  [ member gTilt  "tilt(1/3)"
  , member gTilt2 "tilt(3/5-4/5)"
  , [ ( "tilt branch weights 8/9 (the block) and 1/9 (its complement)"
      , branchWeight visTilt tiltProg "t" [SIn]  (ket [3] [0]) == 8/9
        && branchWeight visTilt tiltProg "t" [SOut] (ket [3] [0]) == 1/9 )
    , ( "tilt parked line is exactly (1,1,1/2)"
      , rParked (residualCheck visTilt tiltProg "t") == Just [1, 1, 1/2] )
    , ( "tilt selection {0,1}: basis probes fail but the all-ones probe factors"
      , let pr inp = probeResult visTilt tiltProg "t" [SIn] inp
            isFail PFail = True
            isFail _     = False
            isLine (PLine _) = True
            isLine _         = False
        in all (isFail . pr) [ket [3] [j] | j <- [0..2]]
           && isLine (pr [1, 1, 1]) )
    ]
  ]

-- >>> length checks
-- 15
