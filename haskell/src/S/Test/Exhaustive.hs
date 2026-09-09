-- Exhaustive.hs: the theory checked on everything of a bounded shape, not only the example programs.
--
-- The algebra layer checks the cyclotomic tower's field and ring laws on an
-- enumerated set of elements; the gate layer checks every gate matrix is
-- exactly unitary; the program layer enumerates every program of a bounded
-- shape and checks four invariants, each documented at its own check.

module S.Test.Exhaustive where

import S.Lang.Ring
import S.Lang.Cyclo
import S.Lang.QState
import S.Lang.Gates
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass

-- 1. Algebra

elems :: [Cyclo]
elems = [ 0, 1, -1, fromRational (1/2), fromRational (-3/5)
        , iC, zetaC 3, zetaC 4, invSqrt2C, zetaC 3 + 1 ]

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

-- 2. Gates

matMulM :: Num a => Matrix a -> Matrix a -> Matrix a
matMulM _ []            = []
matMulM a b@(row0 : _)  = [ [ sum (zipWith (*) row col) | col <- colsB ] | row <- a ]
  where colsB = [ [ r !! j | r <- b ] | j <- [0 .. length row0 - 1] ]

isIdM :: (Eq a, Num a) => Matrix a -> Bool
isIdM m = m == [ [ if i == j then 1 else 0 | j <- [0 .. n - 1] ]
               | i <- [0 .. n - 1] ]
  where n = length m

unitary :: (Eq a, Num a, Conj a) => Matrix a -> Bool
unitary m = isIdM (daggerM m `matMulM` m)

gatesQS2 :: [(String, Matrix QS2)]
gatesQS2 =
  [ ("H", gH), ("X", gX), ("CX", gCX), ("CCX", gCCX), ("Swap", gSwap)
  , ("tilt", gTilt), ("tilt2", gTilt2), ("READ3", gREAD3), ("Diff", gDiff) ]

gatesCyclo :: [(String, Matrix Cyclo)]
gatesCyclo =
  [ ("HC", gHC), ("T", gT), ("S", gS)
  , ("phase z8", gPhase (zetaC 3)), ("cphase z16", gCPhase (zetaC 4)) ]

gateChecks :: [(String, Bool)]
gateChecks =
  [ ("all " ++ show (length gatesQS2) ++ " Q[sqrt2] gates exactly unitary"
    , all (unitary . snd) gatesQS2)
  , ("all " ++ show (length gatesCyclo) ++ " tower gates exactly unitary"
    , all (unitary . snd) gatesCyclo)
  ]

-- 3. Bounded Program Enumeration

visX :: VisSpec
visX = [("x", 2)]

pool :: [Cmd QS2]
pool = [ Gate gH ["t"], Gate gH ["x"], Gate gX ["t"]
       , Gate gCX ["x", "t"], Gate gCX ["t", "x"] ]

segments :: [[Cmd QS2]]
segments = [[]] ++ [ [g] | g <- pool ] ++ [ [g1, g2] | g1 <- pool, g2 <- pool ]

allProgs :: [Prog QS2]
allProgs = [ [New "t" 2] ++ pre ++ mid ++ post ++ [Drop "t"]
           | pre <- segments, mid <- [[], [Lift "p" "t" [1]]], post <- segments ]

inputs :: [StateV QS2]
inputs = [ ket [2] [0], scaleS invSqrt2 (addS (ket [2] [0]) (ket [2] [1])) ]

selsOf :: Prog QS2 -> [[Sel]]
selsOf p = allSelections (liftDepthBefore p "t")

-- | Selection weights sum to 1 on every input.
weightsOK :: Prog QS2 -> Bool
weightsOK p = and
  [ sum [ norm2S (mAmp (runStmts (initMach visX v) p sel Nothing))
        | sel <- selsOf p ] == 1
  | v <- inputs ]

-- | Drop is the runtime identity.
dropIdOK :: Prog QS2 -> Bool
dropIdOK p = and
  [ mAmp (runStmts (initMach visX v) p sel Nothing)
      == mAmp (runStmts (initMach visX v) (filter notDrop p) sel Nothing)
  | v <- inputs, sel <- selsOf p ]
  where notDrop (Drop _) = False
        notDrop _        = True

-- | The runtime check never disagrees with the criterion.
noDisagreeOK :: Prog QS2 -> Bool
noDisagreeOK p = and
  [ agreeRC (reVerdict e) sv /= Disagree
  | let rep = residualCheck visX p "t"
  , (e, sel) <- zip (rTable rep) (selsOf p)
  , let sv = semanticVerdict visX p "t" sel ]

-- | A visible-only unitary appended after the drop moves no verdict.
vgateBlindOK :: Prog QS2 -> Bool
vgateBlindOK p = and
  [ semanticVerdict visX (p ++ [Gate gH ["x"]]) "t" sel
      == semanticVerdict visX p "t" sel
  | sel <- selsOf p ]

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

checks :: [(String, Bool)]
checks = algebraChecks ++ gateChecks ++ programChecks
