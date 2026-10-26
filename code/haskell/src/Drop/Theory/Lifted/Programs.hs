-- Drop.Theory.Lifted.Programs: the programs with lifts that the measurement section discusses.
--
-- Question: Which programs with lifts show that the verdict of a drop depends on the measurement record?
-- Answer:   liftedWitness tilts a trit, lifts the block {0,1}, reads under a conditional whose two arms are
--           the same, and drops: its record In (weight 8/9) is unsafe and its record Out (weight 1/9) is
--           safe. liftedWitnessNoRead deletes the read and is safe on both records.
--           classicalCoreNaiveEncoding is the leaking classical program written with equal amplitudes,
--           and is safe on both. qubitSplitAfterJointGate has a qubit temporary and a joint gate after the
--           lift: safe on In, unsafe on Out, each of weight 1/2. sameChannelSafe and sameChannelUnsafe
--           are two programs with one summed channel and equal weights, safe on both records and unsafe
--           on both.
-- Paper:    sec:boundary (why the record matters), sec:channel (what the summed channel forgets).
-- Shapes:   LProgram   a label, the visible register and its dimension, and a lifted term (Drop.Theory.Lifted).

module Drop.Theory.Lifted.Programs
  ( liftedWitness
  , liftedWitnessNoRead
  , classicalCoreNaiveEncoding
  , qubitSplitAfterJointGate
  , sameChannelSafe
  , sameChannelUnsafe
  ) where

import Drop.Theory.Program.Gates
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Program.Syntax
import Drop.Theory.Lifted

-- | The witness that no record-oblivious verdict serves: identical branches under a
-- lift, so the conditional computes nothing.
--
-- > let t = new |0> in
-- >   t := tilt t;
-- >   let p = lift (meas t in {0,1}) in
-- >   if p then (v := v + t) else (v := v + t);
-- >   drop t; v
--
-- @In@ (weight 8\/9): the temporary is correlated with @v@, drop refused.
-- @Out@ (weight 1\/9): the temporary is a basis state, drop accepted.
liftedWitness :: LProgram
liftedWitness = LProgram
  { lLabel  = "the witness: tilt, lift {0,1}, read under a vacuous conditional, drop"
  , lVis    = "v"
  , lVisDim = 3
  , lTerm   =
      LNew "t" 3 0 $
        LAct ("t1","v1") (gTiltT 3) ("t","v") $
          LLift "p" "t1" [0,1] $
            LIf "p" (readThenDrop "t1" "v1") (readThenDrop "t1" "v1")
  }
  where
    readThenDrop t v =
      LAct ("t2","v2") (gRead 3) (t, v) (LDrop "t2" (LRet "v2"))

-- Each program: its depth, and the weight and ruling of each record.
-- >>> fmap (map (\v -> (tvTrace v, tvWeight v, admissible (tvVerdict v))) . verdictProfile) (checkLProgram liftedWitness)
-- Right [([In],Just 8/9,False),([Out],Just 1/9,True)]
-- >>> fmap ltDepth (checkLProgram liftedWitness)
-- Right 1

-- | The witness with the read deleted: tilt, lift, drop. Safe under both
-- traces, since the impossibility begins at the read, not the measurement.
liftedWitnessNoRead :: LProgram
liftedWitnessNoRead = LProgram
  { lLabel  = "the witness with the read deleted: tilt, lift, drop"
  , lVis    = "v"
  , lVisDim = 3
  , lTerm   =
      LNew "t" 3 0 $
        LAct ("t1","v1") (gTiltT 3) ("t","v") $
          LLift "p" "t1" [0,1] $
            LDrop "t1" (LRet "v1")
  }

-- >>> fmap (map (\v -> (tvTrace v, tvWeight v, admissible (tvVerdict v))) . verdictProfile) (checkLProgram liftedWitnessNoRead)
-- Right [([In],Just 8/9,True),([Out],Just 1/9,True)]

-- | The classical witness transcribed naively: spread the trit, apply
--
-- > pi(v, t) = (v, t (+) v)  when t in {0,1};   (v, 2)  when t = 2,
--
-- read block @{0,1}@, drop. The classical machine leaks here; the quantum
-- encoding does not, since the surviving state is a superposition and the
-- permutation swaps two equal amplitudes. The classical statement lives in
-- "Drop.Theory.Corpus.Classical".
classicalCoreNaiveEncoding :: LProgram
classicalCoreNaiveEncoding = LProgram
  { lLabel  = "the trap: the classical core encoded as equal amplitudes, not split"
  , lVis    = "v"
  , lVisDim = 2
  , lTerm   =
      LNew "t" 3 0 $
        -- spread the trit over all three levels (weights 4/9, 4/9, 1/9)
        LAct ("t1","v1") (onTmp "fair3" fair3 2) ("t","v") $
          LAct ("t2","v2") (joint "pi" 3 2 piMat) ("t1","v1") $
            LLift "p" "t2" [0,1] $
              LDrop "t2" (LRet "v2")
  }
  where
    fair3 = mTilt   -- tilt|0> = (2,2,1)/3: three nonzero amplitudes, all reachable
    piMat = permMat 6 (\k -> let t = k `div` 2
                                 v = k `mod` 2
                             in if t <= 1 then ((t + v) `mod` 2) * 2 + v
                                          else 2 * 2 + v)

-- >>> fmap (map (\v -> (tvTrace v, tvWeight v, admissible (tvVerdict v))) . verdictProfile) (checkLProgram classicalCoreNaiveEncoding)
-- Right [([In],Just 8/9,True),([Out],Just 1/9,True)]
-- >>> fmap oracleSplit (checkLProgram classicalCoreNaiveEncoding)
-- Right False

-- | A temporary qubit whose verdict depends on the outcome. It needs a joint gate after
-- the lift, since a measurement alone leaves singleton blocks in dimension two.
--
-- @H@ on @v@, @CX@ (v controls), @lift (meas t in {0})@, then the real
-- orthogonal @V@,
--
-- > |00> -> |00>,  |01> -> (|01> - |10>)/sqrt2,  |10> -> |11>,  |11> -> (|01> + |10>)/sqrt2
--
-- then drop. Surviving block: basis state, drop safe. Other block: @V@
-- sends @|11>@ to a Bell state, Kraus rank two, drop refused. Both traces
-- carry weight 1\/2.
qubitSplitAfterJointGate :: LProgram
qubitSplitAfterJointGate = LProgram
  { lLabel  = "a scratch qubit, oracle-split by a joint gate after the lift"
  , lVis    = "v"
  , lVisDim = 2
  , lTerm   =
      LNew "t" 2 0 $
        LAct ("t0","v0") (onVis "H" 2 mH) ("t","v") $
          LAct ("t1","v1") (joint "CX(v->t)" 2 2 mCXvt) ("t0","v0") $
            LLift "p" "t1" [0] $
              LAct ("t2","v2") (joint "V" 2 2 mVent) ("t1","v1") $
                LDrop "t2" (LRet "v2")
  }
  where
    r2  = kinvsqrt2
    nr2 = kneg kinvsqrt2
    z   = kzero
    o   = kone
    -- |t,v>, temporary most significant: |t,v> -> |t xor v, v>
    mCXvt = [ [o,z,z,z], [z,z,z,o], [z,z,o,z], [z,o,z,z] ]
    mVent = [ [o, z,   z, z ]
            , [z, r2,  z, r2]
            , [z, nr2, z, r2]
            , [z, z,   o, z ] ]

-- >>> fmap (map (\v -> (tvTrace v, tvWeight v, admissible (tvVerdict v))) . verdictProfile) (checkLProgram qubitSplitAfterJointGate)
-- Right [([In],Just 1/2,True),([Out],Just 1/2,False)]
-- >>> fmap oracleSplit (checkLProgram qubitSplitAfterJointGate)
-- Right True

-- | One half of the instrument-adequacy pair: two commands can denote the
-- same channel, with the same branch weights, and opposite drop verdicts.
--
-- @H@, @CZ@, lift @{0}@, drop. Each branch has one Kraus operator
-- (@I\/sqrt2@ on @In@, @Z\/sqrt2@ on @Out@); both safe, summing to the
-- dephasing channel at weight 1\/2 each.
sameChannelSafe :: LProgram
sameChannelSafe = LProgram
  { lLabel  = "same channel, both branches safe: H, CZ, lift {0}, drop"
  , lVis    = "v"
  , lVisDim = 2
  , lTerm   =
      LNew "t" 2 0 $
        LAct ("t1","v1") (gHt 2) ("t","v") $
          LAct ("t2","v2") gCZ ("t1","v1") $
            LLift "p" "t2" [0] $
              LDrop "t2" (LRet "v2")
  }

-- >>> fmap (map (\v -> (tvTrace v, tvWeight v, admissible (tvVerdict v))) . verdictProfile) (checkLProgram sameChannelSafe)
-- Right [([In],Just 1/2,True),([Out],Just 1/2,True)]

-- | The other half: same spread, but the joint gate runs after the lift:
-- @H@, lift @{0}@, @t := t (+) v@, drop.
--
-- Each branch has two non-proportional Kraus operators, rank two, both
-- refused. The branch maps still sum to the same dephasing channel at the
-- same weights: same channel, opposite verdicts on every branch.
sameChannelUnsafe :: LProgram
sameChannelUnsafe = LProgram
  { lLabel  = "same channel, both branches unsafe: H, lift {0}, compute, drop"
  , lVis    = "v"
  , lVisDim = 2
  , lTerm   =
      LNew "t" 2 0 $
        LAct ("t1","v1") (gHt 2) ("t","v") $
          LLift "p" "t1" [0] $
            LAct ("t2","v2") gCompute ("t1","v1") $
              LDrop "t2" (LRet "v2")
  }

-- >>> fmap (map (\v -> (tvTrace v, tvWeight v, admissible (tvVerdict v))) . verdictProfile) (checkLProgram sameChannelUnsafe)
-- Right [([In],Just 1/2,False),([Out],Just 1/2,False)]
-- >>> fmap (map (tvWeights) . verdictProfile) (checkLProgram sameChannelUnsafe)
-- Right [[1/2,1/2],[1/2,1/2]]
