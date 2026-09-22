-- Gates.hs: the exact gate matrices the example programs use.
--
-- Permutation gates and rational rotations are polymorphic over any
-- Fractional scalar; the Hadamard needs 1/sqrt2, fixed at Q[sqrt2] with a
-- second copy over the cyclotomic tower for the complex programs. Register
-- order in a joint gate is the name list in the Gate command, first most significant.

module Drop.Lang.Gates where

import Drop.Lang.Ring
import Drop.Lang.Cyclo
import Drop.Lang.QState

permGate :: Num a => Int -> (Int -> Int) -> Matrix a
permGate d perm =
  [ [ if i == perm j then 1 else 0 | j <- [0 .. d - 1] ] | i <- [0 .. d - 1] ]

gX, gZ :: Num a => Matrix a
gX = [[0, 1], [1, 0]]
gZ = [[1, 0], [0, -1]]

-- | H = (1/sqrt2) [[1,1],[1,-1]], exact over Q[sqrt2].
gH :: Matrix QS2
gH = map (map (* invSqrt2)) [[1, 1], [1, -1]]

-- | CX with the control first: |c t> -> |c, t + c>.
gCX :: Num a => Matrix a
gCX = permGate 4 (\j -> let c = j `div` 2; t = j `mod` 2
                        in 2 * c + (if c == 1 then 1 - t else t))

-- | Toffoli on (c1 c2 t).
gCCX :: Num a => Matrix a
gCCX = permGate 8 (\j -> let c1 = j `div` 4; c2 = (j `div` 2) `mod` 2; t = j `mod` 2
                         in 4 * c1 + 2 * c2 +
                            (if c1 == 1 && c2 == 1 then 1 - t else t))

-- | Oracle |x t> -> |x, t + f(x)> on one qubit x.
gUf :: Num a => (Int -> Int) -> Matrix a
gUf f = permGate 4 (\j -> let x = j `div` 2; t = j `mod` 2
                          in 2 * x + (if f x == 1 then 1 - t else t))

-- | Bernstein-Vazirani oracle |x1 x2 t> -> |x1 x2, t + s.x>.
gUs :: Num a => Int -> Int -> Matrix a
gUs s1 s2 = permGate 8 (\j ->
  let x1 = j `div` 4; x2 = (j `div` 2) `mod` 2; t = j `mod` 2
      b  = (s1 * x1 + s2 * x2) `mod` 2
  in 4 * x1 + 2 * x2 + (if b == 1 then 1 - t else t))

-- | tilt = (1/3) [[2,2,1],[2,-1,-2],[1,-2,2]], the qutrit rotation of the
-- boundary program (the section on why the record matters).
gTilt :: Fractional a => Matrix a
gTilt = map (map (/ 3)) [[2, 2, 1], [2, -1, -2], [1, -2, 2]]

-- | The 3/5-4/5 member of the same family: two plane rotations by the
-- (3,4,5) angle.  tilt2|0> = (3/5, 12/25, 16/25) has a foot inside the
-- measured block {0,1} and a foot on |2>, the same geometry in fifths.
gTilt2 :: Fractional a => Matrix a
gTilt2 = matMul r12 r01
  where r01 = [[3/5, -4/5, 0], [4/5, 3/5, 0], [0, 0, 1]]
        r12 = [[1, 0, 0], [0, 3/5, -4/5], [0, 4/5, 3/5]]

-- | The correlating read on two qutrits: |x t> -> |x + t mod 3, t>.
gREAD3 :: Num a => Matrix a
gREAD3 = permGate 9 (\j -> let x = j `div` 3; t = j `mod` 3
                           in 3 * ((x + t) `mod` 3) + t)

-- | Grover diffusion on two qubits, 2|s><s| - I.
gDiff :: Fractional a => Matrix a
gDiff = [ [ (if i == j then -1 else 0) + 1/2 | j <- [0 .. 3 :: Int] ]
        | i <- [0 .. 3 :: Int] ]

-- Gates over the cyclotomic tower

-- | H over Q(zeta_8), where 1/sqrt2 = (zeta_8 + zeta_8^{-1})/2.
gHC :: Matrix Cyclo
gHC = map (map (* invSqrt2C)) [[1, 1], [1, -1]]

-- | The phase gate diag(1, z); T is phase zeta_8 and S is phase i.
gPhase :: Num a => a -> Matrix a
gPhase z = [[1, 0], [0, z]]

gT, gS :: Matrix Cyclo
gT = gPhase (zetaC 3)
gS = gPhase iC

-- | Controlled phase diag(1,1,1,z), symmetric in its two registers.
gCPhase :: Num a => a -> Matrix a
gCPhase z = [ [ if i == j then (if i == 3 then z else 1) else 0
              | j <- [0 .. 3 :: Int] ] | i <- [0 .. 3 :: Int] ]

gSwap :: Num a => Matrix a
gSwap = permGate 4 (\j -> 2 * (j `mod` 2) + j `div` 2)

conjM :: Conj a => Matrix a -> Matrix a
conjM = map (map conj)

-- | The adjoint of an exact unitary: the conjugate transpose.
daggerM :: Conj a => Matrix a -> Matrix a
daggerM = transposeM . conjM
