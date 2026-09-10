-- |
-- Module      : DQT.Lifted.Programs
--
-- The lifted programs of the boundary result: the witness no static analysis can
-- serve, the same text with the read deleted, and the family where every
-- lift bit is load-bearing. Values of the syntax in "DQT.Lifted".
module DQT.Lifted.Programs
  ( liftedWitness
  , liftedWitnessNoRead
  , classicalCoreNaiveEncoding
  , qubitSplitAfterJointGate
  , depthTwoEveryBitLoadBearing
  , liveTradeRespread
  , sameChannelSafe
  , sameChannelUnsafe
  ) where

import DQT.Calculus.Gates
import DQT.Algebra.Linear
import DQT.Algebra.Scalar
import DQT.Calculus.Syntax
import DQT.Lifted

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
-- "DQT.Corpus.Classical".
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

-- | The tightness family of the lift-trace bound, at @k = 2@: a gate-free
-- chain of @k@ measurements needs temporary dimension @2^k@ to keep every
-- trace alive and @2^k + 1@ to refuse one of them.
--
-- Basis states 0..2^k-1 labelled by bit strings, plus @bot@. Spread the
-- allocated state over all of them, then apply @X@ to @v@ at @bot@ only.
-- Measurement @j@ selects
--
-- > S_j  =  { states whose j-th label bit is 0 }  u  { bot }
--
-- so state @s@ survives trace @s@ and @bot@ survives the all-@In@ trace;
-- every other trace has Kraus rank one, the all-@In@ trace rank two. At
-- all-@In@, flipping any bit flips the verdict: tightness and attainment
-- both at @2^k + 1@.
--
-- At @k = 2@: five basis states, spread by the Householder reflection
-- carrying @e_0@ to @(1\/2, 1\/2, 1\/2, 1\/(2 sqrt 2), 1\/(2 sqrt 2))@. The
-- four traces carry weights @3\/8@, @1\/4@, @1\/4@, @1\/8@, all nonzero.
depthTwoEveryBitLoadBearing :: LProgram
depthTwoEveryBitLoadBearing = LProgram
  { lLabel  = "the tight family at k=2: a five-level temporary on which both lift bits are load-bearing"
  , lVis    = "v"
  , lVisDim = 2
  , lTerm   =
      LNew "t" 5 0 $
        LAct ("t1","v1") (onTmp "spread5" spread5 2) ("t","v") $
          LAct ("t2","v2") (joint "markBot" 5 2 markBot) ("t1","v1") $
            LLift "p" "t2" [0,1,4] $
              LLift "q" "t2" [0,2,4] $
                LDrop "t2" (LRet "v2")
  }
  where
    h  = kdiv kone (fromInt 2)              -- 1/2
    r  = kdiv kinvsqrt2 (fromInt 2)         -- 1/(2 sqrt 2)
    nh = kneg h
    nr = kneg r
    t3 = kdiv (fromInt 3) (fromInt 4)       -- 3/4
    q1 = kdiv kone (fromInt 4)              -- 1/4
    nq = kneg q1
    -- Householder reflection @I - 2ww^T@, @w = e_0 - v@,
    -- @v = (1/2, 1/2, 1/2, 1/(2 sqrt 2), 1/(2 sqrt 2))@. @||w||^2 = 1@
    -- exactly since @v_0 = 1/2@, so no division is needed. First column is @v@.
    spread5 = [ [ h,  h,  h,  r,  r]
              , [ h,  h, nh, nr, nr]
              , [ h, nh,  h, nr, nr]
              , [ r, nr, nr, t3, nq]
              , [ r, nr, nr, nq, t3] ]
    -- Identity on the visible register at basis states 0..3, @X@ at basis state 4.
    markBot = permMat 10 (\k -> if k < 8 then k else 17 - k)

-- | The liveness trade: two load-bearing bits with no dead branch, in
-- temporary dimension three, using one re-spreading gate between the two
-- measurements.
--
-- Tilt, measure @{0,1}@, re-spread, measure @{0,1}@ again, read, drop.
-- Plain @tilt@ as the re-spreading gate would make the verdict a function
-- of the second bit alone; @tilt@ composed with the cyclic relabelling
-- @|0> -> |2> -> |1> -> |0>@ is used instead,
--
-- > respread  =  (1/3) * [ [ 1,  2,  2]
-- >                      , [-2,  2, -1]
-- >                      , [ 2,  1, -2] ]
--
-- giving traces of weight @4\/9@, @4\/9@, @5\/81@, @4\/81@ and verdicts
-- safe, safe, unsafe, safe: neither bit alone decides it, both are
-- load-bearing.
--
-- Against 'depthTwoEveryBitLoadBearing': one re-spread buys two live bits
-- at dimension three, where the gate-free route needs @5@.
liveTradeRespread :: LProgram
liveTradeRespread = LProgram
  { lLabel  = "the liveness trade: tilt, lift {0,1}, re-spread, lift {0,1}, read, drop"
  , lVis    = "v"
  , lVisDim = 3
  , lTerm   =
      LNew "t" 3 0 $
        LAct ("t1","v1") (gTiltT 3) ("t","v") $
          LLift "p" "t1" [0,1] $
            LAct ("t2","v2") (onTmp "respread" respread 3) ("t1","v1") $
              LLift "q" "t2" [0,1] $
                LAct ("t3","v3") (gRead 3) ("t2","v2") $
                  LDrop "t3" (LRet "v3")
  }
  where
    -- tilt after the cyclic relabelling |0> -> |2> -> |1> -> |0>
    respread = matMul mTilt (permMat 3 (\k -> [2,0,1] !! k))

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
