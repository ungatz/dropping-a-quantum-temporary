-- Drop.Lang.Gates: the gate matrices the corpus programs use.
--
-- Question: Which unitaries may a program apply, and over which field does each live?
-- Answer:   Permutation gates and rational rotations over any field; the Hadamard over Q[sqrt2]
--           (gH) and over the tower (gHC); phase gates over the tower. A joint gate reads its
--           registers in the order the Gate statement names them, first most significant.
-- Paper:    fig:syntax (the gate set is a parameter of the language), sec:lang:denotation.
-- Shapes:   Matrix a, square, of side the product of its registers' dimensions; isUnitary
--           checks the unitarity exactly, with no tolerance.

module Drop.Lang.Gates where

import Drop.Lang.Scalar
import Drop.Lang.State

permGate :: Num a => Int -> (Int -> Int) -> Matrix a
permGate d perm =
  [ [ if i == perm j then 1 else 0 | j <- [0 .. d - 1] ] | i <- [0 .. d - 1] ]

-- >>> permGate 2 id :: [[Int]]
-- [[1,0],[0,1]]
-- >>> permGate 2 (\j -> 1 - j) :: [[Int]]
-- [[0,1],[1,0]]
-- >>> permGate 3 (\j -> (j + 1) `mod` 3) :: [[Int]]
-- [[0,0,1],[1,0,0],[0,1,0]]

gX, gZ :: Num a => Matrix a
gX = [[0, 1], [1, 0]]
gZ = [[1, 0], [0, -1]]

-- >>> gX :: [[Int]]
-- [[0,1],[1,0]]
-- >>> gZ :: [[Int]]
-- [[1,0],[0,-1]]
-- >>> matMul gX gX == (permGate 2 id :: [[Rational]])
-- True

-- | H = (1/sqrt2) [[1,1],[1,-1]], exact over Q[sqrt2].
gH :: Matrix QS2
gH = map (map (* invSqrt2)) [[1, 1], [1, -1]]

-- >>> map (map showAmp) gH
-- [["1/2*r2","1/2*r2"],["1/2*r2","-1/2*r2"]]
-- >>> map showAmp (applyGate [2] gH [0] (ket [2] [0]))
-- ["1/2*r2","1/2*r2"]
-- >>> isUnitary gH
-- True

-- | CX with the control first: |c t> -> |c, t + c>.
gCX :: Num a => Matrix a
gCX = permGate 4 (\j -> let c = j `div` 2; t = j `mod` 2
                        in 2 * c + (if c == 1 then 1 - t else t))

-- >>> applyGate [2,2] gCX [0,1] (ket [2,2] [1,0])
-- [0,0,0,1]
-- >>> applyGate [2,2] gCX [0,1] (ket [2,2] [0,1])
-- [0,1,0,0]
-- >>> isUnitary (gCX :: [[Rational]])
-- True

-- | Toffoli on (c1 c2 t).
gCCX :: Num a => Matrix a
gCCX = permGate 8 (\j -> let c1 = j `div` 4; c2 = (j `div` 2) `mod` 2; t = j `mod` 2
                         in 4 * c1 + 2 * c2 +
                            (if c1 == 1 && c2 == 1 then 1 - t else t))

-- >>> applyGate [2,2,2] gCCX [0,1,2] (ket [2,2,2] [1,1,0])
-- [0,0,0,0,0,0,0,1]
-- >>> applyGate [2,2,2] gCCX [0,1,2] (ket [2,2,2] [1,0,0])
-- [0,0,0,0,1,0,0,0]

-- | Oracle |x t> -> |x, t + f(x)> on one qubit x.
gUf :: Num a => (Int -> Int) -> Matrix a
gUf f = permGate 4 (\j -> let x = j `div` 2; t = j `mod` 2
                          in 2 * x + (if f x == 1 then 1 - t else t))

-- >>> applyGate [2,2] (gUf id) [0,1] (ket [2,2] [1,0])
-- [0,0,0,1]
-- >>> applyGate [2,2] (gUf (const 0)) [0,1] (ket [2,2] [1,0])
-- [0,0,1,0]

-- | Bernstein-Vazirani oracle |x1 x2 t> -> |x1 x2, t + s.x>.
gUs :: Num a => Int -> Int -> Matrix a
gUs s1 s2 = permGate 8 (\j ->
  let x1 = j `div` 4; x2 = (j `div` 2) `mod` 2; t = j `mod` 2
      b  = (s1 * x1 + s2 * x2) `mod` 2
  in 4 * x1 + 2 * x2 + (if b == 1 then 1 - t else t))

-- >>> applyGate [2,2,2] (gUs 1 1) [0,1,2] (ket [2,2,2] [1,0,0])
-- [0,0,0,0,0,1,0,0]
-- >>> applyGate [2,2,2] (gUs 1 1) [0,1,2] (ket [2,2,2] [1,1,0])
-- [0,0,0,0,0,0,1,0]

-- | tilt = (1/3) [[2,2,1],[2,-1,-2],[1,-2,2]], the qutrit rotation of the
-- boundary program (the section on why the record matters).
gTilt :: Fractional a => Matrix a
gTilt = map (map (/ 3)) [[2, 2, 1], [2, -1, -2], [1, -2, 2]]

-- >>> map (map showRat) gTilt
-- [["2/3","2/3","1/3"],["2/3","-1/3","-2/3"],["1/3","-2/3","2/3"]]
-- >>> isUnitary (gTilt :: [[Rational]])
-- True

-- | The 3/5-4/5 member of the same family: two plane rotations by the
-- (3,4,5) angle.  tilt2|0> = (3/5, 12/25, 16/25) has a foot inside the
-- measured block {0,1} and a foot on |2>, the same geometry in fifths.
gTilt2 :: Fractional a => Matrix a
gTilt2 = matMul r12 r01
  where r01 = [[3/5, -4/5, 0], [4/5, 3/5, 0], [0, 0, 1]]
        r12 = [[1, 0, 0], [0, 3/5, -4/5], [0, 4/5, 3/5]]

-- >>> applyGate [3] gTilt2 [0] (ket [3] [0] :: [Rational])
-- [3 % 5,12 % 25,16 % 25]
-- >>> isUnitary (gTilt2 :: [[Rational]])
-- True

-- | The correlating read on two qutrits: |x t> -> |x + t mod 3, t>.
gREAD3 :: Num a => Matrix a
gREAD3 = permGate 9 (\j -> let x = j `div` 3; t = j `mod` 3
                           in 3 * ((x + t) `mod` 3) + t)

-- >>> applyGate [3,3] gREAD3 [0,1] (ket [3,3] [1,2])
-- [0,0,1,0,0,0,0,0,0]
-- >>> isUnitary (gREAD3 :: [[Rational]])
-- True

-- | Grover diffusion on two qubits, 2|s><s| - I.
gDiff :: Fractional a => Matrix a
gDiff = [ [ (if i == j then -1 else 0) + 1/2 | j <- [0 .. 3 :: Int] ]
        | i <- [0 .. 3 :: Int] ]

-- >>> map (map showRat) gDiff
-- [["-1/2","1/2","1/2","1/2"],["1/2","-1/2","1/2","1/2"],["1/2","1/2","-1/2","1/2"],["1/2","1/2","1/2","-1/2"]]
-- >>> isUnitary (gDiff :: [[Rational]])
-- True

-- Gates over the cyclotomic tower

-- | H over Q(zeta_8), where 1/sqrt2 = (zeta_8 + zeta_8^{-1})/2.
gHC :: Matrix Cyclo
gHC = map (map (* invSqrt2C)) [[1, 1], [1, -1]]

-- >>> map (map showAmp) gHC
-- [["1/2*z8+-1/2*z8^3","1/2*z8+-1/2*z8^3"],["1/2*z8+-1/2*z8^3","-1/2*z8+1/2*z8^3"]]
-- >>> map showAmp (applyGate [2] gHC [0] (ket [2] [1]))
-- ["1/2*z8+-1/2*z8^3","-1/2*z8+1/2*z8^3"]
-- >>> isUnitary gHC
-- True

-- | The phase gate diag(1, z); T is phase zeta_8 and S is phase i.
gPhase :: Num a => a -> Matrix a
gPhase z = [[1, 0], [0, z]]

-- >>> gPhase 5 :: [[Int]]
-- [[1,0],[0,5]]
-- >>> map (map showAmp) (gPhase iC)
-- [["1","0"],["0","1*z4"]]

gT, gS :: Matrix Cyclo
gT = gPhase (zetaC 3)
gS = gPhase iC

-- >>> map (map showAmp) gS
-- [["1","0"],["0","1*z4"]]
-- >>> map (map showAmp) gT
-- [["1","0"],["0","1*z8"]]
-- >>> matMul gT gT == gS
-- True
-- >>> isUnitary gT
-- True

-- | Controlled phase diag(1,1,1,z), symmetric in its two registers.
gCPhase :: Num a => a -> Matrix a
gCPhase z = [ [ if i == j then (if i == 3 then z else 1) else 0
              | j <- [0 .. 3 :: Int] ] | i <- [0 .. 3 :: Int] ]

-- >>> gCPhase 7 :: [[Int]]
-- [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,7]]
-- >>> map (map showAmp) (gCPhase iC)
-- [["1","0","0","0"],["0","1","0","0"],["0","0","1","0"],["0","0","0","1*z4"]]

gSwap :: Num a => Matrix a
gSwap = permGate 4 (\j -> 2 * (j `mod` 2) + j `div` 2)

-- >>> applyGate [2,2] gSwap [0,1] (ket [2,2] [1,0])
-- [0,1,0,0]
-- >>> matMul gSwap gSwap == (permGate 4 id :: [[Rational]])
-- True

conjM :: Conj a => Matrix a -> Matrix a
conjM = map (map conj)

-- >>> map (map showAmp) (conjM gT)
-- [["1","0"],["0","-1*z8^3"]]
-- >>> conjM gH == gH
-- True

-- | The adjoint of an exact unitary: the conjugate transpose.
daggerM :: Conj a => Matrix a -> Matrix a
daggerM = transposeM . conjM

-- >>> daggerM gT == gPhase (conj (zetaC 3))
-- True
-- >>> daggerM gH == gH
-- True
-- >>> matMul gT (daggerM gT) == (permGate 2 id :: [[Cyclo]])
-- True
-- >>> daggerM [[1,2],[3,4 :: Rational]] == [[1,3],[2,4]]
-- True
