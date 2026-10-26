-- Drop.Lang.Checks.Exhaustive: the theory checked on everything of a bounded shape, not only on the example programs.
--
-- Question: Do the laws the paper relies on hold on every case of a small, closed shape, and not only on the programs it prints?
-- Answer:   Three lists of named checks, which checks concatenates in this order. algebraChecks: on a
--           fixed set of elements of the cyclotomic tower, + and * are associative, * commutes and
--           distributes, conj is a ring involution, normSq is multiplicative, recip inverts every
--           nonzero element, and embedQS2 is a ring homomorphism. gateChecks: each gate matrix in
--           gatesQS2 and gatesCyclo is exactly unitary. programChecks: every program of one shape
--           (allProgs: new t, a prefix, optionally a lift of t against {1}, a suffix, drop t, where
--           the prefix and the suffix are each empty or one or two commands from pool) is run on
--           two inputs under every selection, and four invariants are checked: the selection
--           weights sum to 1; dropping is the runtime identity; the runtime check of
--           Drop.Lang.Pass never disagrees with the criterion; and a visible unitary appended
--           after the drop moves no verdict. Every check is a closed enumeration, so a red line
--           names the case.
-- Paper:    sec:residual (the runtime check against the criterion), sec:lang:dynamics (what a drop does
--           at run time); the enumeration itself is the artifact's own.
-- Shapes:   elems         the elements of the tower the algebra checks range over.
--           gatesQS2, gatesCyclo
--                         (name, matrix): the gates checked for unitarity, over Q[sqrt2] and over
--                         the tower.
--           pool          the commands a prefix or suffix is made of.
--           segments      the prefixes and suffixes: the empty one, each single command, each pair.
--           allProgs      every program of the shape, over the visible register x (visX).
--           inputs        the two test inputs each program is run on.

module Drop.Lang.Checks.Exhaustive where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass

-- 1. Algebra

elems :: [Cyclo]
elems = [ 0, 1, -1, fromRational (1/2), fromRational (-3/5)
        , iC, zetaC 3, zetaC 4, invSqrt2C, zetaC 3 + 1 ]

-- Ten elements: 0, 1, -1, two rationals, i, the primitive 8th and 16th roots of unity, 1/sqrt2, and one sum.
-- >>> length elems
-- 10
-- >>> map showAmp (take 5 elems)
-- ["0","1","-1","1/2","-3/5"]

algebraChecks :: [(String, Bool)]
algebraChecks =
  [ ("cyclo: + and * associative, * commutative and distributing"
    , and [ (a + b) + c == a + (b + c)
            && (a * b) * c == a * (b * c)
            && a * b == b * a
            && a * (b + c) == a * b + a * c
          | a <- elems, b <- elems, c <- elems ])
  , ("cyclo: conj is a ring involution on all pairs"
    , and [ conj (a + b) == conj a + conj b
            && conj (a * b) == conj a * conj b
            && conj (conj a) == a
          | a <- elems, b <- elems ])
  , ("cyclo: normSq multiplicative on all pairs"
    , and [ normSq (a * b) == normSq a * normSq b
          | a <- elems, b <- elems ])
  , ("cyclo: recip total and correct on the nonzero elements"
    , and [ a * recip a == 1 | a <- elems, a /= 0 ])
  , ("cyclo: embedQS2 is a ring homomorphism"
    , let qs = [ QS2 1 0, QS2 0 1, QS2 (1/2) (-1/3), QS2 (-2) (3/4) ]
      in and [ embedQS2 (x * y) == embedQS2 x * embedQS2 y
               && embedQS2 (x + y) == embedQS2 x + embedQS2 y
             | x <- qs, y <- qs ])
  ]

-- >>> map fst (take 2 algebraChecks)
-- ["cyclo: + and * associative, * commutative and distributing","cyclo: conj is a ring involution on all pairs"]
-- >>> all snd algebraChecks
-- True
-- >>> length algebraChecks
-- 5

-- 2. Gates

matMulM :: Num a => Matrix a -> Matrix a -> Matrix a
matMulM _ []            = []
matMulM a b@(row0 : _)  = [ [ sum (zipWith (*) row col) | col <- colsB ] | row <- a ]
  -- impossible: every row of a matrix has the length of the first, so j is in range
  where colsB = [ [ r !! j | r <- b ] | j <- [0 .. length row0 - 1] ]

-- A product of two small matrices, and the empty matrix.
-- >>> matMulM [[1, 2], [3, 4]] [[0, 1], [1, 0]] :: [[Int]]
-- [[2,1],[4,3]]
-- >>> matMulM [] [[1]] :: [[Int]]
-- []

isIdM :: (Eq a, Num a) => Matrix a -> Bool
isIdM m = m == [ [ if i == j then 1 else 0 | j <- [0 .. n - 1] ]
               | i <- [0 .. n - 1] ]
  where n = length m

-- >>> isIdM ([[1, 0], [0, 1]] :: [[Int]])
-- True
-- >>> isIdM ([[1, 1], [0, 1]] :: [[Int]])
-- False

unitary :: (Eq a, Num a, Conj a) => Matrix a -> Bool
unitary m = isIdM (daggerM m `matMulM` m)

-- The controlled-X gate is unitary; a shear is not.
-- >>> unitary (gCX :: Matrix QS2)
-- True
-- >>> unitary ([[1, 1], [0, 1]] :: Matrix QS2)
-- False

gatesQS2 :: [(String, Matrix QS2)]
gatesQS2 =
  [ ("H", gH), ("X", gX), ("CX", gCX), ("CCX", gCCX), ("Swap", gSwap)
  , ("tilt", gTilt), ("tilt2", gTilt2), ("READ3", gREAD3), ("Diff", gDiff) ]

-- >>> map fst gatesQS2
-- ["H","X","CX","CCX","Swap","tilt","tilt2","READ3","Diff"]

gatesCyclo :: [(String, Matrix Cyclo)]
gatesCyclo =
  [ ("HC", gHC), ("T", gT), ("S", gS)
  , ("phase z8", gPhase (zetaC 3)), ("cphase z16", gCPhase (zetaC 4)) ]

-- >>> map fst gatesCyclo
-- ["HC","T","S","phase z8","cphase z16"]

gateChecks :: [(String, Bool)]
gateChecks =
  [ ("all " ++ show (length gatesQS2) ++ " Q[sqrt2] gates exactly unitary"
    , all (unitary . snd) gatesQS2)
  , ("all " ++ show (length gatesCyclo) ++ " tower gates exactly unitary"
    , all (unitary . snd) gatesCyclo)
  ]

-- >>> map fst gateChecks
-- ["all 9 Q[sqrt2] gates exactly unitary","all 5 tower gates exactly unitary"]
-- >>> all snd gateChecks
-- True

-- 3. Bounded Program Enumeration

visX :: VisSpec
visX = [("x", 2)]

-- >>> visX
-- [("x",2)]

pool :: [Cmd QS2]
pool = [ Gate gH ["t"], Gate gH ["x"], Gate gX ["t"]
       , Gate gCX ["x", "t"], Gate gCX ["t", "x"] ]

-- Five commands: two Hadamards, an X, and the controlled X in both directions.
-- >>> length pool
-- 5

segments :: [[Cmd QS2]]
segments = [[]] ++ [ [g] | g <- pool ] ++ [ [g1, g2] | g1 <- pool, g2 <- pool ]

-- One empty prefix, five single commands, twenty-five pairs.
-- >>> [ length (filter ((== n) . length) segments) | n <- [0, 1, 2] ]
-- [1,5,25]

allProgs :: [Prog QS2]
allProgs = [ [New "t" 2] ++ pre ++ mid ++ post ++ [Drop ["t"]]
           | pre <- segments, mid <- [[], [Lift "p" "t" [1]]], post <- segments ]

-- Thirty-one prefixes, with and without the lift, thirty-one suffixes. The smallest program is new and drop.
-- >>> length allProgs
-- 1922
-- >>> map length (take 3 allProgs)
-- [2,3,3]

inputs :: [StateV QS2]
inputs = [ ket [2] [0], scaleS invSqrt2 (addS (ket [2] [0]) (ket [2] [1])) ]

-- >>> map (map showAmp) inputs
-- [["1","0"],["1/2*r2","1/2*r2"]]

selsOf :: Prog QS2 -> [[Sel]]
selsOf p = allSelections (liftDepthBefore p "t")

-- A program without a lift has one selection; with one, two.
-- >>> [ length (selsOf (allProgs !! i)) | i <- [0, 31] ]
-- [1,2]

-- | Selection weights sum to 1 on every input.
weightsOK :: Prog QS2 -> Bool
weightsOK p = and
  [ sum [ norm2S (mAmp (runStmts (initMach visX v) p sel Nothing))
        | sel <- selsOf p ] == 1
  | v <- inputs ]

-- The program new t, H t, a lift of t against {1}, CX t x, drop t; and the smallest one, new t and drop t.
-- >>> weightsOK (allProgs !! 98)
-- True
-- >>> weightsOK (allProgs !! 0)
-- True

-- | Drop is the runtime identity.
dropIdOK :: Prog QS2 -> Bool
dropIdOK p = and
  [ mAmp (runStmts (initMach visX v) p sel Nothing)
      == mAmp (runStmts (initMach visX v) (filter notDrop p) sel Nothing)
  | v <- inputs, sel <- selsOf p ]
  where notDrop (Drop _) = False
        notDrop _        = True

-- The program new t, H t, a lift of t against {1}, CX t x, drop t; and the smallest one, new t and drop t.
-- >>> dropIdOK (allProgs !! 98)
-- True
-- >>> dropIdOK (allProgs !! 0)
-- True

-- | The runtime check never disagrees with the criterion.
noDisagreeOK :: Prog QS2 -> Bool
noDisagreeOK p = and
  [ agreeRC (reVerdict e) sv /= Disagree
  | let rep = residualCheck visX p "t"
  , (e, sel) <- zip (rTable rep) (selsOf p)
  , let sv = semanticVerdict visX p "t" sel ]

-- The program new t, H t, a lift of t against {1}, CX t x, drop t; and the smallest one, new t and drop t.
-- >>> noDisagreeOK (allProgs !! 98)
-- True
-- >>> noDisagreeOK (allProgs !! 0)
-- True

-- | A visible-only unitary appended after the drop moves no verdict.
vgateBlindOK :: Prog QS2 -> Bool
vgateBlindOK p = and
  [ semanticVerdict visX (p ++ [Gate gH ["x"]]) "t" sel
      == semanticVerdict visX p "t" sel
  | sel <- selsOf p ]

-- The program new t, H t, a lift of t against {1}, CX t x, drop t; and the smallest one, new t and drop t.
-- >>> vgateBlindOK (allProgs !! 98)
-- True
-- >>> vgateBlindOK (allProgs !! 0)
-- True

programChecks :: [(String, Bool)]
programChecks =
  [ (show n ++ " programs: selection weights sum to 1 on two inputs each"
    , all weightsOK allProgs)
  , (show n ++ " programs: Drop is the runtime identity"
    , all dropIdOK allProgs)
  , (show n ++ " programs: the runtime check never disagrees with the criterion"
    , all noDisagreeOK allProgs)
  , (show n ++ " programs: an appended visible unitary moves no verdict"
    , all vgateBlindOK allProgs)
  ]
  where n = length allProgs

-- >>> map fst programChecks
-- ["1922 programs: selection weights sum to 1 on two inputs each","1922 programs: Drop is the runtime identity","1922 programs: the runtime check never disagrees with the criterion","1922 programs: an appended visible unitary moves no verdict"]

checks :: [(String, Bool)]
checks = algebraChecks ++ gateChecks ++ programChecks

-- >>> length checks
-- 11
