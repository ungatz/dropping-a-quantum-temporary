-- Drop.Theory.Program.Machine: running a term on a state.
--
-- Question: What does a run of a term do to the state?
-- Answer:   A configuration holds the registers' names and dimensions in tensor order, the names
--           dropped so far, and an amplitude vector. stepTerm runs a term to its end, one case for
--           each form: New appends a register in a basis state, a gate acts on the two registers it
--           names (applyGateAt), and Drop only adds the name to the dropped list, leaving the
--           amplitude vector untouched. A term that names a dropped register is refused.
--           runTermRaw returns the final configuration, with the dropped registers where they were
--           allocated. runTerm permutes them to the front, the order of the denotation.
-- Paper:    sec:lang:dynamics, fig:machine.
-- Shapes:   Config   register names, dimensions, dropped names and the amplitude vector.

module Drop.Theory.Program.Machine
  ( -- * Configurations
    Config(..)
  , initConfig
    -- * Running
  , stepTerm
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

-- Before any step: one visible register and its input.
-- >>> :m + Drop.Theory.Program.Typing Drop.Theory.Corpus.Examples
-- >>> let c0 = initConfig "v" 2 (vbasis 2 1)
-- >>> (cfgNames c0, cfgDims c0, cfgDropped c0, cfgAmp c0)
-- (["v"],[2],[],[0,1])

initConfig :: Name -> Int -> Vec -> Config
initConfig v m psi = Config [v] [m] [] psi

-- >>> cfgAmp (initConfig "v" 3 (vbasis 3 2))
-- [0,0,1]
-- >>> cfgNames (initConfig "x" 2 (vAllOnes 2))
-- ["x"]

-- | Run a term to its end, one case for each term former.
--
-- 'stepTerm' takes a term that need not have met the checker, and a dropped
-- register stays in the tensor, so a gate or a second drop on it would go
-- through; it is refused by name instead.
stepTerm :: Config -> Term -> Config
stepTerm c e
  | (x : _) <- [ x | x <- named e, x `elem` cfgDropped c ] =
      -- refusal: a gate or a drop on a register already dropped
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
    -- refusal: a name that is not in the configuration (a term that was not type checked)
    pos x = maybe (error ("Drop.Theory.Program.Machine: no register " ++ x))
                  id (lookup x (zip (cfgNames c) [0 ..]))
    ren x | x == t    = t'
          | x == v    = v'
          | otherwise = x

-- The whole of the drop rule.  The amplitude vector is untouched.
stepTerm c (Drop t e) =
  stepTerm c { cfgDropped = cfgDropped c ++ [t] } e

-- Spread and park on the input |1>: the temporary joins as the second register, the gate acts, and the drop only names it dropped.
-- >>> let c1 = stepTerm c0 (progTerm spreadAndPark)
-- >>> (cfgNames c1, cfgDims c1, cfgDropped c1)
-- (["v1","t1"],[2,2],["t1"])
-- >>> cfgAmp c1
-- [0,0,sqrt2/2,sqrt2/2]
-- >>> cfgAmp (stepTerm c0 (Ret "v")) == cfgAmp c0
-- True

-- | Run a typed program's term on a visible input, in the machine's own tensor
-- order.  Returns the final configuration, with the latent factor sitting
-- where it was allocated.
runTermRaw :: TypedProgram -> Vec -> Config
runTermRaw tp psi =
  stepTerm (initConfig (progVis (tpProgram tp)) (tpVisDim tp) psi)
           (progTerm (tpProgram tp))

-- The raw tensor order puts the visible register first and the temporary after it.
-- >>> fmap (\tp -> cfgAmp (runTermRaw tp (vbasis 2 0))) (checkProgram spreadAndRead)
-- Right [sqrt2/2,0,0,sqrt2/2]
-- >>> fmap (\tp -> cfgDropped (runTermRaw tp (vbasis 2 0))) (checkProgram spreadAndRead)
-- Right ["t2"]

-- | Run a typed program's term on a visible input and return the result in the
-- denotation's convention: dropped registers first, then the rest.
runTerm :: TypedProgram -> Vec -> Vec
runTerm tp psi = matVec (reorder (cfgDims c) order) (cfgAmp c)
  where
    c      = runTermRaw tp psi
    -- impossible: every dropped name was a register of the configuration
    idxOf x = maybe (error ("Drop.Theory.Program.Machine.runTerm: no register " ++ x))
                    id (lookup x (zip (cfgNames c) [0 ..]))
    dropIx = map idxOf (cfgDropped c)
    order  = dropIx ++ [ i | i <- [0 .. length (cfgDims c) - 1], i `notElem` dropIx ]

-- runTerm puts the dropped register first. On the input |1> the read correlates the two registers.
-- >>> fmap (\tp -> runTerm tp (vbasis 2 1)) (checkProgram spreadAndRead)
-- Right [0,sqrt2/2,sqrt2/2,0]
-- >>> fmap (\tp -> runTerm tp (vbasis 2 1)) (checkProgram spreadAndReadTwice)
-- Right [0,sqrt2/2,0,sqrt2/2]
-- >>> fmap (\tp -> runTerm tp (vbasis 2 0)) (checkProgram twoGateSilq)
-- Right [1,0,0,0]
