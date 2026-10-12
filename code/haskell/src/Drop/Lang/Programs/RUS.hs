-- RUS.hs: one repeat-until-success iteration, unrolled (Sections 6, 9.2).
--
-- Both branches of the conditional run the same code; what differs is the
-- state the selection transferred. The drop is refused when the block
-- {0,1} survives and accepted when its complement does, so the runtime
-- check decides the two apart by one classical bit.

module Drop.Lang.Programs.RUS where

import Drop.Lang.QState
import Drop.Lang.Gates
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Pass

visR :: VisSpec
visR = [("x", 3)]

rusProg :: Prog Rational
rusProg =
  [ New "t" 3
  , Gate gTilt ["t"]
  , Lift "p" "t" [0, 1]
  , IfBit (GParam "p") [Gate gREAD3 ["x", "t"]]   -- success branch: read
              [Gate gREAD3 ["x", "t"]]   -- failure branch: same code
  , Drop ["t"]
  ]

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
