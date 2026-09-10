-- Shor.hs: order-finding core of Shor's algorithm, N = 15, a = 7, three counting qubits.
--
-- The temporary w holds the residue mod 15 (dimension 16, level 15 unused).
-- Controlled modular multiplication entangles w with the counting register,
-- the textbook "measure the second register" step: dropping w unmeasured is
-- refused; with the measurement first, admissible on the branch selected, refused on its complement.

module S.Programs.Shor where

import S.Lang.Ring
import S.Lang.Cyclo
import S.Lang.QState
import S.Lang.Gates
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass
import S.Programs.QFT (invQftC)

visShor :: VisSpec
visShor = [("c1", 2), ("c2", 2), ("c3", 2)]

-- | w starts at |0>; this swap lands it on |1>.
swap01 :: Int -> Int
swap01 0 = 1
swap01 1 = 0
swap01 w = w

-- | Controlled multiplication by @a@ mod 15 on (c, w), control most
-- significant: fixed unless the control is 1 and w holds a nonzero residue.
cMulPerm :: Int -> Int -> Int
cMulPerm a j =
  let c = j `div` 16
      w = j `mod` 16
  in if c == 1 && w >= 1 && w <= 14 then c * 16 + (a * w) `mod` 15 else j

-- | Everything through the inverse QFT: c1 with U^4 (7^4 = 1 mod 15), c2
-- with U^2 (7^2 = 4), c3 with U (7), as in ExQPE's ladder.
shorCore :: Prog Cyclo
shorCore =
  [ New "w" 16
  , Gate (permGate 16 swap01) ["w"]
  , Gate gHC ["c1"]
  , Gate gHC ["c2"]
  , Gate gHC ["c3"]
  -- 7^4 = 1 mod 15, so this is the identity permutation; it stays because
  -- the algorithm calls for it regardless of what a simplifies to.
  , Gate (permGate 32 (cMulPerm 1)) ["c1", "w"]
  , Gate (permGate 32 (cMulPerm 4)) ["c2", "w"]
  , Gate (permGate 32 (cMulPerm 7)) ["c3", "w"]
  ] ++ invQftC ["c1", "c2", "c3"]

shorProg :: Prog Cyclo
shorProg = shorCore ++ [Drop "w"]

-- | The textbook "measure the second register" step: w survives restricted
-- to whether it fell in the block {7}.
shorMeasured :: Prog Cyclo
shorMeasured = shorCore ++ [Lift "s" "w" [7], Drop "w"]

-- | The state at the end of the program, run from the all-zero input.
finalState :: Prog Cyclo -> StateV Cyclo
finalState p = mAmp (runStmts (initMach visShor (ket [2, 2, 2] [0, 0, 0])) p [] Nothing)

-- | Pr(y), summing over the levels of w at counting outcome y.
probY :: StateV Cyclo -> Int -> Cyclo
probY st y = sum [ normSq (st !! (16 * y + w)) | w <- [0 .. 15] ]

basisW :: Int -> StateV Cyclo
basisW l = [ if i == l then 1 else 0 | i <- [0 .. 15] ]

checks :: [(String, Bool)]
checks = concat
  [ [ ( "shorProg: drop w inadmissible, entangled with the counting register"
      , semanticVerdict visShor shorProg "w" [] == Inadmissible ) ]
  , [ ( "shorMeasured: drop w admissible on the block {7}, parked on its basis vector"
      , semanticVerdict visShor shorMeasured "w" [SIn] == Admissible
        && semanticParked visShor shorMeasured "w" [SIn] == Just (basisW 7) ) ]
  , [ ( "shorMeasured: drop w inadmissible on the complement of {7}"
      , semanticVerdict visShor shorMeasured "w" [SOut] == Inadmissible ) ]
  , [ ( "shorMeasured: opposite verdicts on one program text, one lift"
      , liftDepthBefore shorMeasured "w" == 1 ) ]
  , [ ( "shorProg from |000>: exact 1/4 on y in {0,2,4,6}, exact 0 on odd y "
        ++ "-- the order of 7 mod 15 is 4"
      , let st = finalState shorProg
        in and [ probY st y == (if even y then 1 / 4 else 0) | y <- [0 .. 7] ] ) ]
  , -- the controlled multiplication entangles w with the counting register
    -- before the lift, so the runtime check's pre-lift parking hypothesis
    -- fails and it declines on both records rather than deciding them: the
    -- semantic criterion still does, from the state the interpreter reaches.
    [ ( "shorMeasured: runtime check declines on both records, prefix-parks false"
      , let r = residualCheck visShor shorMeasured "w"
        in rDepth r == 1
           && lookup "prefix-parks" (rHyps r) == Just False
           && map reVerdict (rTable r) == [HypothesesFail, HypothesesFail] ) ]
  ]
