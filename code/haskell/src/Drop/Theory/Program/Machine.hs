-- |
-- Module      : Drop.Theory.Program.Machine
--
-- The operational semantics: a configuration carrying live and latent
-- register names and an unnormalised state vector.  @drop t@ leaves the
-- amplitude vector untouched; 'runTerm' permutes to the denotation's order.
module Drop.Theory.Program.Machine
  ( -- * Configurations
    Config(..)
  , initConfig
    -- * Running
  , stepTerm
  , runTermRaw
  , runTerm
  ) where

import Drop.Theory.Algebra.Linear
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing (TypedProgram(..))

-- | A machine configuration for the measurement-free calculus.
data Config = Config
  { cfgNames   :: [Name]   -- ^ live and latent registers, in tensor order
  , cfgDims    :: [Int]
  , cfgDropped :: [Name]   -- ^ latent: dropped, still in the tensor
  , cfgAmp     :: Vec
  }

initConfig :: Name -> Int -> Vec -> Config
initConfig v m psi = Config [v] [m] [] psi

-- | One step per term former.  There is no stuck state: every well-typed term
-- either is a value or steps.
--
-- 'stepTerm' takes a term that need not have met the checker, and a dropped
-- register stays in the tensor, so a gate or a second drop on it would go
-- through; it is refused by name instead.
stepTerm :: Config -> Term -> Config
stepTerm c e
  | (x : _) <- [ x | x <- named e, x `elem` cfgDropped c ] =
      error ("Drop.Theory.Program.Machine: register " ++ x ++ " has been dropped")
  where
    named (Act _ _ (t, v) _) = [t, v]
    named (Drop t _)         = [t]
    named _                  = []
stepTerm c (Ret _)    = c
stepTerm c (Pair _ _) = c

stepTerm c (New t d i0 e) =
  stepTerm c { cfgNames = cfgNames c ++ [t]
             , cfgDims  = cfgDims c ++ [d]
             , cfgAmp   = tensorV (cfgAmp c) (vbasis d i0) } e

stepTerm c (Act (t',v') u (t,v) e) =
  stepTerm c { cfgNames = map ren (cfgNames c)
             , cfgAmp   = matVec (applyGateAt (cfgDims c) (gateMat u) [pt,pv])
                                 (cfgAmp c) } e
  where
    pt = pos t
    pv = pos v
    pos x = maybe (error ("Drop.Theory.Program.Machine: no register " ++ x))
                  id (lookup x (zip (cfgNames c) [0 ..]))
    ren x | x == t    = t'
          | x == v    = v'
          | otherwise = x

-- The whole of the drop rule.  The amplitude vector is untouched.
stepTerm c (Drop t e) =
  stepTerm c { cfgDropped = cfgDropped c ++ [t] } e

-- | Run a typed program's term on a visible input, in the machine's own tensor
-- order.  Returns the final configuration, with the latent factor sitting
-- where it was allocated.
runTermRaw :: TypedProgram -> Vec -> Config
runTermRaw tp psi =
  stepTerm (initConfig (progVis (tpProgram tp)) (tpVisDim tp) psi)
           (progTerm (tpProgram tp))

-- | Run a typed program's term on a visible input and return the result in the
-- denotation's convention: dropped registers first, then the rest.
runTerm :: TypedProgram -> Vec -> Vec
runTerm tp psi = matVec (reorder (cfgDims c) order) (cfgAmp c)
  where
    c      = runTermRaw tp psi
    idxOf x = maybe (error ("Drop.Theory.Program.Machine.runTerm: no register " ++ x))
                    id (lookup x (zip (cfgNames c) [0 ..]))
    dropIx = map idxOf (cfgDropped c)
    order  = dropIx ++ [ i | i <- [0 .. length (cfgDims c) - 1], i `notElem` dropIx ]
