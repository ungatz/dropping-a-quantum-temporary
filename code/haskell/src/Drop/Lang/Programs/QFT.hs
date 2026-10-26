-- Drop.Lang.Programs.QFT: the exact quantum Fourier transform, as a circuit.
--
-- Question: What is the quantum Fourier transform on n registers, written as gates over exact scalars?
-- Answer:   The standard construction: for each register in turn a Hadamard, then a controlled
--           rotation from each later register, then swaps that reverse the order of the
--           registers. The inverse is the reversed circuit with every gate replaced by its
--           adjoint. Phase estimation consumes the inverse; this module defines no temporary and
--           no drop, so it has no verdict of its own. A rotation reaches diag(1, 1, 1, zeta_{2^n})
--           for n registers, so the scalar field grows with n, which is why the scalar tower of
--           Drop.Lang.Scalar is indexed rather than fixed.
-- Paper:    sec:lang:algorithms (the inverse Fourier transform in the listing of qpe.s).
-- Shapes:   qftSteps ws   the named gates of the circuit on the registers ws, in run order: a name,
--                         a matrix and the registers it acts on.
--           qftC, invQftC the transform and its inverse, as programs.
-- Corpus file: none; this program is the module's own. programs/qpe.s writes the three-register
--           inverse transform out gate by gate, and the check "programs/qpe.s is the module's
--           program as syntax" (see Drop.Lang.Programs.QPE) pairs it with invQftC.

module Drop.Lang.Programs.QFT where

import Drop.Lang.Scalar
import Drop.Lang.State (Matrix)
import Drop.Lang.Gates
import Drop.Lang.Flat

-- | The named gates of the circuit on the given registers, in run order.
qftSteps :: [String] -> [(String, Matrix Cyclo, [String])]
qftSteps ws =
  concat
    [ ("H", gHC, [ws !! j])  -- impossible: j < n = length ws
      : [ ("R" ++ show m, gCPhase (zetaC m), [ws !! j, ws !! k])  -- impossible: j < k < n = length ws
        | k <- [j + 1 .. n - 1], let m = k - j + 1 ]
    | j <- [0 .. n - 1] ]
  ++ [ ("SWAP", gSwap, [ws !! i, ws !! (n - 1 - i)])  -- impossible: i < n div 2, so both positions are below n
     | i <- [0 .. n `div` 2 - 1] ]
  where n = length ws

-- One register is a Hadamard and nothing else; two add a rotation R2 and a swap.
-- >>> [ (name, regs) | (name, _, regs) <- qftSteps ["a"] ]
-- [("H",["a"])]

-- >>> [ (name, regs) | (name, _, regs) <- qftSteps ["a", "b"] ]
-- [("H",["a"]),("R2",["a","b"]),("H",["b"]),("SWAP",["a","b"])]

-- Three registers: a Hadamard on each, the rotations R2 and R3 from the later registers, one swap.
-- >>> [ (name, regs) | (name, _, regs) <- qftSteps ["a", "b", "c"] ]
-- [("H",["a"]),("R2",["a","b"]),("R3",["a","c"]),("H",["b"]),("R2",["b","c"]),("H",["c"]),("SWAP",["a","c"])]

-- | The transform and its inverse, the latter being the reversed circuit
-- with each gate replaced by its adjoint.
qftC, invQftC :: [String] -> Prog Cyclo
qftC ws    = [ Gate g xs | (_, g, xs) <- qftSteps ws ]
invQftC ws = [ Gate (daggerM g) xs | (_, g, xs) <- reverse (qftSteps ws) ]

-- The transform of |00> is the uniform superposition, with amplitude one half on each of four levels.
-- >>> :m + Drop.Lang.Interp Drop.Lang.State
-- >>> let runOn prog inp = mAmp (runStmts (initMach [("a", 2), ("b", 2)] inp) prog [] Nothing)
-- >>> map showAmp (runOn (qftC ["a", "b"]) (ket [2, 2] [0, 0]))
-- ["1/2","1/2","1/2","1/2"]

-- The inverse undoes it, on every basis input.
-- >>> [ runOn (qftC ["a", "b"] ++ invQftC ["a", "b"]) (ket [2, 2] [i, j]) == ket [2, 2] [i, j] | i <- [0, 1], j <- [0, 1] ]
-- [True,True,True,True]

-- The scalar field grows: the largest rotation of three registers is a primitive 8th root of unity.
-- >>> map showAmp [zetaC 2, zetaC 3]
-- ["1*z4","1*z8"]
