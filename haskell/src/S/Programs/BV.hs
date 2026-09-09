-- BV.hs: Bernstein-Vazirani, hidden string s = (s1, s2), one of the eight algorithms.
--
-- The ancilla pattern is Deutsch-Jozsa's: t on |->, so the oracle kicks
-- back a phase and leaves the temporary constant on [|->] at every input.
-- The drop is safe for every hidden string, with no uncompute, and the
-- visible action is exactly X^s.

module S.Programs.BV where

import S.Lang.Ring
import S.Lang.QState
import S.Lang.Gates
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass

visBV :: VisSpec
visBV = [("x1", 2), ("x2", 2)]

bvProg :: Int -> Int -> Prog QS2
bvProg s1 s2 =
  [ New "t" 2
  , Gate gX ["t"]
  , Gate gH ["t"]
  , Gate gH ["x1"]
  , Gate gH ["x2"]
  , Gate (gUs s1 s2) ["x1", "x2", "t"]
  , Gate gH ["x1"]
  , Gate gH ["x2"]
  , Drop "t"
  , Lift "p1" "x1" [0]
  , Lift "p2" "x2" [0]
  ]

strings :: [(Int, Int)]
strings = [ (s1, s2) | s1 <- [0, 1], s2 <- [0, 1] ]

minusLine :: StateV QS2
minusLine = [1, -1]

-- | The visible factor of basis test input j at the drop site.
visFactor :: Int -> Int -> Int -> StateV QS2
visFactor s1 s2 j =
  let inp = [ if k == j then 1 else 0 | k <- [0 .. 3] ]
      m   = runStmts (initMach visBV inp) (bvProg s1 s2) [] (Just "t")
  in case factorSplit (mDims m) [regPos m "t"] (mAmp m) of
       Just (_, vB) -> vB
       Nothing      -> error "BV: basis probe did not factor"

checks :: [(String, Bool)]
checks = concat
  [ [ ("BV s=" ++ show s1 ++ show s2 ++ " admissible, parked [|->]"
      , semanticVerdict visBV (bvProg s1 s2) "t" [] == Admissible
        && probeResult visBV (bvProg s1 s2) "t" [] (ket [2,2] [0,0])
             == PLine minusLine)
    | (s1, s2) <- strings ]
  , -- W = X^s: basis test input j's visible factor is on the line of e_{j xor s}
    [ ("BV s=" ++ show s1 ++ show s2 ++ " visible action is X^s"
      , and [ stateProportional (visFactor s1 s2 j)
                                (ket [4] [j `xor2` (2 * s1 + s2)])
            | j <- [0 .. 3] ])
    | (s1, s2) <- strings ]
  , [ ("BV s=" ++ show s1 ++ show s2 ++ " runtime check depth 0, admit"
      , let r = residualCheck visBV (bvProg s1 s2) "t"
        in rDepth r == 0 && map reVerdict (rTable r) == [Admit])
    | (s1, s2) <- strings ]
  ]
  where
    xor2 :: Int -> Int -> Int
    xor2 a b = (if a `div` 2 /= b `div` 2 then 2 else 0)
             + (if a `mod` 2 /= b `mod` 2 then 1 else 0)
