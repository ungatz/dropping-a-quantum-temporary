-- Tilt.hs: the tilt family, the program the boundary result is
-- proved with. It runs entirely over the rationals; no radical appears.
--
-- tilt|0> = (2/3, 2/3, 1/3) has a foot inside the measured block {0,1} and
-- a foot on |2>: the block selection leaves a correlated superposition and
-- an unsafe drop, the complement leaves the basis line |2> and a safe drop.

module S.Programs.Tilt where

import S.Lang.QState
import S.Lang.Gates
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass

visTilt :: VisSpec
visTilt = [("x", 3)]

tiltF :: Matrix Rational -> Prog Rational
tiltF u =
  [ New "t" 3
  , Gate u ["t"]
  , Lift "p" "t" [0, 1]
  , Gate gREAD3 ["x", "t"]
  , Drop "t"
  ]

tiltProgOf :: Matrix Rational -> Prog Rational
tiltProgOf = tiltF

tiltProg, tilt2Prog :: Prog Rational
tiltProg  = tiltProgOf gTilt
tilt2Prog = tiltProgOf gTilt2

-- | The shared checks for one member of the family.
member :: Matrix Rational -> String -> [(String, Bool)]
member u nm =
  let p   = tiltProgOf u
      r   = residualCheck visTilt p "t"
      ent b = case [ e | e <- rTable r, reBits e == b ] of
                (e : _) -> Just e
                []      -> Nothing
  in
  [ ( nm ++ " selection {0,1}: inadmissible"
    , semanticVerdict visTilt p "t" [SIn] == Inadmissible )
  , ( nm ++ " selection {2}: admissible"
    , semanticVerdict visTilt p "t" [SOut] == Admissible )
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
          t1 == [g !! 0, g !! 1, 0] && t0 == [0, 0, g !! 2]
        _ -> False )
  ]

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
