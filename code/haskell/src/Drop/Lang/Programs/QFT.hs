-- QFT.hs: the exact quantum Fourier transform as a circuit.
--
-- Standard construction (Hadamard + controlled rotations + bit-reversal
-- swaps), consumed in reverse by phase estimation; defines no temporary or
-- drop. Rotations reach diag(1,1,1,zeta_{2^n}), so the scalar field grows
-- with n, which is why Drop.Lang.Cyclo's tower is indexed rather than fixed.

module Drop.Lang.Programs.QFT where

import Drop.Lang.Cyclo
import Drop.Lang.QState (Matrix)
import Drop.Lang.Gates
import Drop.Lang.Syntax

-- | The named gates of the circuit on the given registers, in run order.
qftSteps :: [String] -> [(String, Matrix Cyclo, [String])]
qftSteps ws =
  concat
    [ ("H", gHC, [ws !! j])
      : [ ("R" ++ show m, gCPhase (zetaC m), [ws !! j, ws !! k])
        | k <- [j + 1 .. n - 1], let m = k - j + 1 ]
    | j <- [0 .. n - 1] ]
  ++ [ ("SWAP", gSwap, [ws !! i, ws !! (n - 1 - i)])
     | i <- [0 .. n `div` 2 - 1] ]
  where n = length ws

-- | The transform and its inverse, the latter being the reversed circuit
-- with each gate replaced by its adjoint.
qftC, invQftC :: [String] -> Prog Cyclo
qftC ws    = [ Gate g xs | (_, g, xs) <- qftSteps ws ]
invQftC ws = [ Gate (daggerM g) xs | (_, g, xs) <- reverse (qftSteps ws) ]
