-- |
-- Module      : Drop.Theory.Lifted.Programs
--
-- The lifted programs the paper discusses: the witness no static analysis
-- can serve, the same text with the read deleted, the qubit that splits
-- after a joint gate, and the pair of programs with one channel and two
-- verdicts. Values of the syntax in "Drop.Theory.Lifted".
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

-- | The witness no static analysis can serve: identical branches under a
-- lift, so the conditional computes nothing.
--
-- > let t = new |0> in
-- >   t := tilt t;
-- >   let p = lift (meas t in {0,1}) in
-- >   if p then (v := v + t) else (v := v + t);
-- >   drop t; v
--
-- @In@ (weight 8\/9): temporary correlated with @v@, drop refused.
-- @Out@ (weight 1\/9): temporary a basis state, drop accepted.
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
        -- spread the trit uniformly: the classical "fair three-way coin"
        LAct ("t1","v1") (onTmp "fair3" fair3 2) ("t","v") $
          LAct ("t2","v2") (joint "pi" 3 2 piMat) ("t1","v1") $
            LLift "p" "t2" [0,1] $
              LDrop "t2" (LRet "v2")
  }
  where
    -- Any orthogonal matrix whose first column is (1,1,1)/sqrt3 works; the
    -- entries below are exact in this field.
    fair3 = mTilt   -- tilt|0> = (2,2,1)/3: three nonzero weights, all reachable
    piMat = permMat 6 (\k -> let t = k `div` 2
                                 v = k `mod` 2
                             in if t <= 1 then ((t + v) `mod` 2) * 2 + v
                                          else 2 * 2 + v)

-- | A temporary qubit that is outcome-dependent, the reason the obstruction
-- does not appear at temporary dimension two: it needs a joint gate after
-- the lift, since a measurement alone leaves singleton blocks there.
--
-- @H@ on @v@, @CX@ (v controls), @lift (meas t in {0})@, then the real
-- orthogonal @V@,
--
-- > |00> -> |00>,  |01> -> (|01> - |10>)/sqrt2,  |10> -> |11>,  |11> -> (|01> + |10>)/sqrt2
--
-- then drop. Surviving block: basis state, drop safe. Other block: @V@
-- sends @|11>@ to a Bell state, Kraus rank two, drop refused. Both traces
-- carry weight 1\/2, so this does not depend on restricting to reachable
-- traces.
--
-- Restricted statement: with no joint gate after the lift, a dimension-two
-- temporary cannot split; three is the first dimension that fails.
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

-- | The other half: same spread, but the joint gate runs after the lift:
-- @H@, lift @{0}@, @t := t (+) v@, drop.
--
-- Each branch now has two non-proportional Kraus operators, rank two, both
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
