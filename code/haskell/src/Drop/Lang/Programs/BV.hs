-- Drop.Lang.Programs.BV: Bernstein-Vazirani, on a hidden string of two bits.
--
-- Question: Is the temporary of Bernstein-Vazirani safe to drop without uncomputing it, whatever
--           the hidden string?
-- Answer:   The ancilla pattern is Deutsch-Jozsa's: t on |-> (X, then H), so the oracle for the
--           string s = (s1, s2) kicks a phase back and leaves the temporary on [|->] at every
--           input. The drop is safe for each of the four strings, with no uncompute, and the
--           visible action is exactly X^s: a basis input j comes out on the line of j xor s.
--           The lifts of x1 and x2 come after the drop, so they read the string off without
--           touching the site. At depth 0 the static pass of Drop.Lang.Pass admits each program.
-- Paper:    sec:dj (the same kickback), app:corpus (names Bernstein-Vazirani as not in the corpus).
-- Shapes:   visBV        the visible registers: x1 and x2, two levels each.
--           strings      the four hidden strings, as pairs of bits.
--           bvProg s1 s2 the program for the string (s1, s2): new t, X, H, H on x1 and x2, the
--                        oracle, H on x1 and x2, drop t, then a lift of each against {0}.
--           visFactor s1 s2 j
--                        the factor on x1, x2 of the state at the drop, from basis input j.
-- Corpus file: none; this program is the module's own.

module Drop.Lang.Programs.BV where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass

visBV :: VisSpec
visBV = [("x1", 2), ("x2", 2)]

-- >>> visBV
-- [("x1",2),("x2",2)]

strings :: [(Int, Int)]
strings = [ (s1, s2) | s1 <- [0, 1], s2 <- [0, 1] ]

-- >>> strings
-- [(0,0),(0,1),(1,0),(1,1)]

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
  , Drop ["t"]
  , Lift "p1" "x1" [0]
  , Lift "p2" "x2" [0]
  ]

-- The program for the string (1, 0): eleven commands, one drop.
-- >>> length (bvProg 1 0)
-- 11

-- >>> dropSites (bvProg 1 0)
-- [["t"]]

-- Safe for each of the four hidden strings: one site, the lifts come after it.
-- >>> [ ((s1, s2), map drRows (verdict visBV (bvProg s1 s2))) | (s1, s2) <- strings ]
-- [((0,0),[[([],Safe)]]),((0,1),[[([],Safe)]]),((1,0),[[([],Safe)]]),((1,1),[[([],Safe)]])]

minusLine :: StateV QS2
minusLine = [1, -1]

-- >>> minusLine
-- [1,-1]

-- The temporary is left on [|->] from |00>, whatever the string.
-- >>> [ probeResult visBV (bvProg s1 s2) "t" [] (ket [2, 2] [0, 0]) == PLine minusLine | (s1, s2) <- strings ]
-- [True,True,True,True]

-- | The visible factor of basis test input j at the drop site.
visFactor :: Int -> Int -> Int -> StateV QS2
visFactor s1 s2 j =
  let inp = [ if k == j then 1 else 0 | k <- [0 .. 3] ]
      m   = runStmts (initMach visBV inp) (bvProg s1 s2) [] (Just ["t"])
  in case factorSplit (mDims m) [regPos m "t"] (mAmp m) of
       Just (_, vB) -> vB
       -- impossible: the oracle only kicks a phase back, so t is left on [|->] and always factors
       Nothing      -> error "BV: basis probe did not factor"

-- The visible action is X^s. For s = (1, 0) the input |00> (j = 0) comes out on the line of
-- |10> (j xor 2 = 2), and the input |11> (j = 3) on the line of |01> (j = 1).
-- >>> [ stateProportional (visFactor 1 0 j) (ket [4] [j2]) | (j, j2) <- [(0, 2), (3, 1)] ]
-- [True,True]

-- >>> visFactor 1 0 0
-- [0,0,1,0]

-- The suite's claims ------------------------------------------------------------------

checks :: [(String, Bool)]
checks = concat
  [ [ ("BV s=" ++ show s1 ++ show s2 ++ " safe, parked [|->]"
      , semanticVerdict visBV (bvProg s1 s2) "t" [] == Safe
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

-- Three claims for each of the four strings.
-- >>> length checks
-- 12

-- >>> map fst (take 1 checks)
-- ["BV s=00 safe, parked [|->]"]
