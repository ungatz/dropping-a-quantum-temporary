-- |
-- Module      : DQT.Many.Nested
--
-- A nested witness prepares each temporary of a program with its own gate;
-- a composite witness instead needs one temporary of dimension
-- @d_1 * ... * d_n@, not a program of the surface language.
module DQT.Many.Nested
  ( -- * The constant state and its factors
    parkedState
  , parkedFactors
    -- * The nested witness
  , NestedWitness(..)
  , NestedReason(..)
    -- * Gate rings and the norm condition
  , GateRing(..)
  , zHalf, qOmega
  , rayCarriesUnitVector
  , nestedWitness
  , checkNestedWitness
  , bundledWitnessExists
    -- * The drop-order lemma, mechanised
  , truncateAtDrop
  , wireSafeAtDropSite
  , dropOrderIsIrrelevant
    -- * The trichotomy, inhabited
  , irreduciblyJoint
  , reduciblyJoint
  , phaseBuysTheRoot
  , usesAfterDrop, gatesBeforeAlloc, resurrectsAName
  , interleavedDrops
    -- * The separating pair for the per-lifetime negative
  , projectionToWire
  , shuffleSafe, shuffleUnsafe
  , projectionsAgree
    -- * Reporting
  , nestedReport
  ) where

import qualified Data.Ratio
import Data.Bits ((.&.))

import DQT.Criterion (safeByRank)
import DQT.Pretty (wrapAt)
import DQT.Calculus.Elaborate (coreMap)
import DQT.Calculus.Gates (mCX, mH)
import DQT.Algebra.Linear
import DQT.Many.Multi
import DQT.Algebra.Scalar
import DQT.Criterion.Split (Split (..), factorSplit)
import DQT.Calculus.Syntax
import DQT.Calculus.Typing
import DQT.Criterion.Witness (Reason (..), householder, synthesize)

-- The Constant State

-- | The constant state of a multi-temporary program: the vector the composite temporary is
-- left on, when it is left on a fixed ray at all.
--
-- Returns @Nothing@ when the composite drop is unsafe: level 1 of the
-- trichotomy, where there is no state to factor.
parkedState :: MProgram -> Either BundleError (Maybe Vec)
parkedState p = do
  b <- bundle p
  case checkProgram b of
    Left e   -> error ("DQT.Many.Nested.parkedState: bundled program ill-typed: "
                       ++ show e)
    Right tp
      | not (safeByRank tp) -> pure Nothing
      | otherwise ->
          -- Jointly safe means K = g (x) W.  Read g off the first column:
          -- K e_0 = g (x) (W e_0), and split across {bundle} | {visible}.
          let m    = progVisDim (tpProgram tp)
              dims = [tpTmpDim tp, m]
              col  = matVec (coreMap tp) (vbasis m 0)
          in pure (splitLeft <$> factorSplit dims [0] col)

-- | The per-temporary factors of the constant state, when it is a full
-- product across the partition of temporaries.
--
-- @Nothing@ covers levels 1 and 2 together (unsafe or safe-but-entangled);
-- 'parkedState' tells them apart. Each factor is normalised to a @1@ in
-- its first nonzero coordinate, a canonical ray representative.
parkedFactors :: MProgram -> Either BundleError (Maybe [Vec])
parkedFactors p = do
  mg <- parkedState p
  case mg of
    Nothing -> pure Nothing
    Just g  ->
      let dims = [ d | (_, d, _) <- mTemporaries p ]
      in pure (peel dims g)
  where
    -- Split off one temporary at a time; each split must succeed or the state is
    -- entangled across that cut.
    peel :: [Int] -> Vec -> Maybe [Vec]
    peel []       _ = Just []
    peel [_]      v = Just [v]
    peel (d : ds) v = do
      s  <- factorSplit (d : [dimProduct ds]) [0] v
      rest <- peel ds (splitRight s)
      pure (splitLeft s : rest)

-- Gate Rings And The Norm Condition

-- | A gate ring, for the one question this module asks: given a ray, does
-- it carry a unit vector with entries in the ring?
--
-- Not a square root of the squared norm: a unit vector on @[g]@ needs
-- @1/||g||^2@ to be a norm @lambda lambda-bar@ from the ring, not a
-- square. With enough phase the two can differ ('phaseBuysTheRoot').
data GateRing = GateRing
  { ringName      :: String
  , ringHas       :: K -> Bool
      -- ^ is this scalar in the ring?
  , ringUnitOnRay :: Vec -> Maybe Vec
      -- ^ a unit vector over the ring on the given ray, if there is one
  }

-- | @Z[1/2]@: real, dyadic, no @i@ and no @sqrt2@. A unit vector on @[g]@
-- needs real @lambda@ with @lambda^2 ||g||^2 = 1@: here, and only here,
-- the condition is a square root of a dyadic rational.
zHalf :: GateRing
zHalf = GateRing "Z[1/2]" inZHalf f
  where
    f g = do
      let n2 = vnorm2 g
      r <- kToRational n2
      lam <- ratSqrt (1 / r)
      if isDyadic lam && all (maybe False isDyadic . kToRational)
                             (map (kmul (fromRat lam)) g)
        then Just (map (kmul (fromRat lam)) g) else Nothing
    isDyadic q = let d = Data.Ratio.denominator q in d > 0 && (d .&. (d - 1)) == 0
    inZHalf k = maybe False isDyadic (kToRational k)

-- | @Q(w)@, the field this package computes in. A phase is available, so
-- the condition is the norm equation, settled by a bounded search over
-- small ring elements: a witness finder, not a decision procedure, but
-- enough for every ray that occurs here.
qOmega :: GateRing
qOmega = GateRing "Q(w)" (const True) f
  where
    f g =
      let n2 = vnorm2 g
      in case [ lam | lam <- candidates
                    , kmul (kmul lam (kconj lam)) n2 == kone ] of
           (lam : _) -> Just (map (kmul lam) g)
           []        -> Nothing
    -- lambda = (a + b w + c w^2 + d w^3) / e, small height
    candidates =
      [ kdiv (K (toRational a) (toRational b) (toRational c) (toRational d))
             (fromInt (fromIntegral e))
      | e <- [1 .. 6 :: Int]
      , a <- rng, b <- rng, c <- rng, d <- rng
      , (a, b, c, d) /= (0, 0, 0, 0) ]
    rng = [-2 .. 2 :: Int]

-- | Does the ray through @g@ carry a unit vector over the ring?
rayCarriesUnitVector :: GateRing -> Vec -> Maybe Vec
rayCarriesUnitVector = ringUnitOnRay

-- The Nested Witness

-- | A witness in the nested shape: one preparation gate per temporary, and one
-- gate on the visible register.
data NestedWitness = NestedWitness
  { nwFactors :: [Vec]  -- ^ @g_1 .. g_n@, each a unit vector over @K@
  , nwPrepare :: [Mat]  -- ^ @R_1 .. R_n@, each a gate on that temporary alone
  , nwVisible :: Mat    -- ^ @W@
  }

-- | Why no nested witness exists.  Each constructor is a level of the
-- trichotomy or a hypothesis failing out loud.
data NestedReason
  = NestedBundleError BundleError
  | NotJointlySafe
      -- ^ level 1: the composite drop is unsafe.
  | ParkedIsEntangled
      -- ^ level 2: the composite temporary is on a fixed ray that does not
      -- factor across the partition of temporaries.
  | FactorRayCarriesNoUnitVector Int String K
      -- ^ level 3: temporary @k@'s factor ray carries no unit vector in
      -- the named gate ring, since @1/||g_k||^2@ is not a norm there
      -- (semantically safe to drop, arithmetically unpreparable).
  | FactorPreparationNotOverRing Int String
      -- ^ the ray carries an @A@-valued unit vector, but its preparing
      -- reflection is not over @A@: the Householder divides by
      -- @||e_i0 - u||^2@, not always invertible outside a field. Example
      -- over @Z[1/2]@: @(1,3,2,1,1)/4@ has @||w||^2 = 3/2@, an entry @2/3@.
  | FactorPreparationNotReal Int
      -- ^ the ring carries a unit vector on temporary @k@'s ray, but it
      -- is not real, and 'DQT.Criterion.Witness.householder' builds real
      -- reflections only: a limit of this construction, not "no witness".
  | FactorReflectionFailed Int Reason
      -- ^ the per-temporary Householder construction failed for temporary @k@.
  deriving (Show)

-- | Build the nested witness, or say which level of the trichotomy the
-- program sits at.
--
-- The one-temporary Direction 2 applied @n@ times independently: when it
-- works, the nested program is @n@ separate one-temporary programs side
-- by side.
nestedWitness :: GateRing -> MProgram -> Either NestedReason NestedWitness
nestedWitness ring p = do
  mfs <- either (Left . NestedBundleError) Right (parkedFactors p)
  mg  <- either (Left . NestedBundleError) Right (parkedState p)
  case (mg, mfs) of
    (Nothing, _)      -> Left NotJointlySafe
    (Just _, Nothing) -> Left ParkedIsEntangled
    (Just _, Just fs) -> do
      let tmps = mTemporaries p
      rs <- mapM prepare (zip3 [0 ..] tmps fs)
      pure NestedWitness { nwFactors = [ u | (u, _) <- rs ]
                         , nwPrepare = [ r | (_, r) <- rs ]
                         , nwVisible = matId (mVisDim p) }
  where
    -- Normalise one factor to a unit vector over K, then reflect e_{i0} onto
    -- it.  The normalisation is where level 3 fails, and it fails with the
    -- factor's own squared norm in hand.
    prepare (k, (_, d, i0), gk) =
      case rayCarriesUnitVector ring gk of
        Nothing -> Left (FactorRayCarriesNoUnitVector k (ringName ring)
                                                      (vnorm2 gk))
        Just u
          | not (all kIsReal u) -> Left (FactorPreparationNotReal k)
          | otherwise -> case householder d i0 u of
              Left r  -> Left (FactorReflectionFailed k r)
              Right m
                | not (all (all (ringHas ring)) m) ->
                    Left (FactorPreparationNotOverRing k (ringName ring))
                | otherwise -> Right (u, m)

-- | Independent re-check: every preparation gate is unitary, and applying it to
-- its own allocation basis vector reproduces that temporary's factor.
checkNestedWitness :: MProgram -> NestedWitness -> Bool
checkNestedWitness p w =
  let allocs = [ i0 | (_, _, i0) <- mTemporaries p ]
      dims   = [ d  | (_, d, _)  <- mTemporaries p ]
  in length (nwPrepare w) == length allocs
     && and [ matIsUnitary r | r <- nwPrepare w ]
     && and [ matVec r (vbasis d i0) == u
            | (r, d, i0, u) <- zip4 (nwPrepare w) dims allocs (nwFactors w) ]
  where
    zip4 (a:as) (b:bs) (c:cs) (d:ds) = (a,b,c,d) : zip4 as bs cs ds
    zip4 _ _ _ _ = []

-- | Does the composite witness exist?  This is 'DQT.Criterion.Witness.synthesize' on
-- the composite program; at level 3 it is 'True' while 'nestedWitness'
-- fails.
bundledWitnessExists :: MProgram -> Either BundleError Bool
bundledWitnessExists p = do
  b <- bundle p
  case checkProgram b of
    Left e   -> error ("DQT.Many.Nested.bundledWitnessExists: " ++ show e)
    Right tp -> pure (either (const False) (const True) (synthesize tp))

-- The Drop-Order Lemma, Made Executable

-- | Truncate a program at the drop of @t@: keep every statement up to and
-- including @drop t@, then drop whatever else is still live.
--
-- The trailing drops are what make the result a program 'bundle' will accept;
-- they do not change @t@'s own verdict.
truncateAtDrop :: MProgram -> Name -> Maybe MProgram
truncateAtDrop p t =
  case break isDropT (mStmts p) of
    (_, [])            -> Nothing          -- t is never dropped
    (before, d : _) ->
      let kept    = before ++ [d]
          allocd  = [ nm | MNew nm _ _ <- kept ]
          dropped = [ nm | MDrop nm    <- kept ]
          live    = [ nm | nm <- allocd, nm `notElem` dropped ]
      in Just p { mLabel = mLabel p ++ "  [truncated at drop " ++ t ++ "]"
                , mStmts = kept ++ map MDrop live }
  where
    isDropT (MDrop x) = x == t
    isDropT _         = False

-- | The per-temporary verdict for @t@ computed at its own drop site, by truncating
-- the program there.
wireSafeAtDropSite :: MProgram -> Name -> Either BundleError Bool
wireSafeAtDropSite p t = case truncateAtDrop p t of
  Nothing -> Left (NotAllDropped [t])
  Just q  -> wireSafe q t

-- | The drop-order lemma, checked rather than argued: for every temporary,
-- the verdict at its own drop site agrees with the verdict at the end.
--
-- Not vacuous: 'bundle' ignores where a drop stands, so the two sides come
-- from different programs (truncated vs. whole); the affine discipline is
-- what forces agreement.
dropOrderIsIrrelevant :: MProgram -> Bool
dropOrderIsIrrelevant p =
  and [ wireSafeAtDropSite p t == wireSafe p t | (t, _, _) <- mTemporaries p ]

-- The Inhabitants

-- | The all-ones ray in dimension @d@, as a unit vector when it is one.
allOnesPrep :: Int -> Mat
allOnesPrep d =
  case ksqrtReal (fromInt (fromIntegral d)) of
    Just c  -> case householder d 0 (map (`kdiv` c) (vAllOnes d)) of
                 Right m -> m
                 Left _  -> matId d
    Nothing -> matId d

-- | Two 3-dimensional temporaries prepared jointly on the all-ones ray of
-- @H_9@: a square-root test gives the wrong answer here.
--
-- Squared norm @1/3@, @sqrt 3@ not in @Q(w)@, yet the ray carries a field
-- unit vector since @|1 + sqrt2 i|^2 = 3@. Not level-3 over @Q(w)@; over
-- @Z[1/2]@ (no @i@, no @sqrt2@), it is.
phaseBuysTheRoot :: MProgram
phaseBuysTheRoot = MProgram
  { mLabel  = "two 3-level wires on the all-ones ray of H_9, where the phase pays"
  , mVis    = "v"
  , mVisDim = 2
  , mStmts  =
      [ MNew "a" 3 0
      , MNew "b" 3 0
      , MApply "R9" (allOnesPrep 9) ["a", "b"]
      , MDrop "a"
      , MDrop "b" ]
  }

-- | Level 3, over @Z[1/2]@: two qubits, each put on the all-ones ray by
-- its own Hadamard, visible register untouched.
--
-- * composite drop __safe__, every temporary __separately fixed__: ray
--   @(1,1) (x) (1,1)@;
-- * __bundle__ preparable over @Z[1/2]@: @(1,1,1,1)@ carries
--   @(1/2)(1,1,1,1)@, reflection entries @+-1/2@;
-- * __neither temporary is__: @(1,1)@ needs @lambda^2 = 1/2@, i.e.
--   @sqrt2@ in @Z[1/2]@ (the necessary half of the criterion).
--
-- Four is a square, two is not: an arithmetic obstruction, though neither
-- temporary is entangled and neither drop is unsafe.
irreduciblyJoint :: MProgram
irreduciblyJoint = MProgram
  { mLabel  = "two qubits, one joint gate over Z[1/2]: bundle preparable, neither wire"
  , mVis    = "v"
  , mVisDim = 2
  , mStmts  =
      [ MNew "a" 2 0
      , MNew "b" 2 0
      -- One joint gate: no gate over Z[1/2] puts a single qubit on the
      -- all-ones ray (needs 1/sqrt2, and H is not over Z[1/2]; an earlier
      -- version wrongly used two Hadamards). The 4x4 all-ones Householder
      -- is over Z[1/2]: ||w||^2 = 1, every entry +-1/2.
      , MApply "R4" (allOnesPrep 4) ["a", "b"]
      , MDrop "a"
      , MDrop "b" ]
  }

-- | The control: the same construction one dimension up, two 4-dimensional
-- temporaries each on the all-ones ray.
--
-- The factor ray @(1,1,1,1)@ carries @(1/2)(1,1,1,1)@ over @Z[1/2]@, so the
-- nested witness exists: the obstruction in 'irreduciblyJoint' is that @2@
-- is not a square and @4@ is, not nesting itself.
reduciblyJoint :: MProgram
reduciblyJoint = MProgram
  { mLabel  = "two 4-level wires on the all-ones ray: the control, a nested witness exists"
  , mVis    = "v"
  , mVisDim = 2
  , mStmts  =
      [ MNew "a" 4 0
      , MApply "P4" (allOnesPrep 4) ["a"]
      , MNew "b" 4 0
      , MApply "P4" (allOnesPrep 4) ["b"]
      , MDrop "a"
      , MDrop "b" ]
  }


-- | A program whose drops are interleaved with the rest of the work: @a@
-- is allocated, used and dropped before @b@ is ever allocated.
--
-- Makes 'dropOrderIsIrrelevant' say something: with drops all at the end,
-- truncation is nearly the whole program; here truncating at @a@'s drop
-- discards half the program, yet @a@'s verdict still has to match.
interleavedDrops :: MProgram
interleavedDrops = MProgram
  { mLabel  = "drops interleaved: a is allocated, used and dropped before b exists"
  , mVis    = "v"
  , mVisDim = 2
  , mStmts  =
      [ MNew "a" 2 0
      , MApply "H" mH ["a"]
      , MDrop "a"
      , MNew "b" 2 0
      , MApply "CX" mCX ["b", "v"]
      , MApply "CX" mCX ["b", "v"]
      , MDrop "b" ]
  }

-- | The ordered list of windows naming a given register: the
-- per-temporary projection, exactly the input a per-lifetime analysis
-- has. Order-preserving within the temporary, recording nothing about
-- other temporaries' windows.
--
-- Equal exactly when the temporary ran the same gates on the same
-- registers in the same order.
projectionToWire :: MProgram -> Name -> [(String, [Name])]
projectionToWire p t =
  [ (nm, xs) | MApply nm _ xs <- mStmts p, t `elem` xs ]

-- | Do two programs have literally equal projections at every temporary, and
-- the same temporaries?  This is the hypothesis of the negative, checked
-- rather than asserted.
projectionsAgree :: MProgram -> MProgram -> Bool
projectionsAgree p q =
     names p == names q
  && and [ projectionToWire p t == projectionToWire q t | t <- names p ]
  where names r = [ t | (t,_,_) <- mTemporaries r ]

-- | The separating pair, half one: @a@ copies @v@ then uncopies it; @b@ is
-- put in superposition and writes into @v@ /after/ both of @a@'s windows,
-- so the uncompute cancels correctly and @a@ returns to its allocation
-- state: dropping @a@ is safe.
shuffleSafe :: MProgram
shuffleSafe = MProgram
  { mLabel  = "compute/uncompute on a, with b's write after both windows"
  , mVis    = "v"
  , mVisDim = 2
  , mStmts  =
      [ MNew "a" 2 0
      , MNew "b" 2 0
      , MApply "H"  mH  ["b"]
      , MApply "CX" mCX ["v", "a"]
      , MApply "CX" mCX ["v", "a"]
      , MApply "CX" mCX ["b", "v"]
      , MDrop "a"
      , MDrop "b" ]
  }

-- | The separating pair, half two: the same windows on each temporary in
-- the same order, only the /interleaving/ differs: @b@'s write moves
-- between @a@'s two windows, so the second @CX v a@ reads a changed @v@,
-- the uncompute misses, and @a@ is left correlated. Dropping @a@ is unsafe.
--
-- 'projectionsAgree' checks the hypothesis, 'wireSafe' the conclusion.
shuffleUnsafe :: MProgram
shuffleUnsafe = MProgram
  { mLabel  = "the same windows on every wire, with b's write moved inside a's pair"
  , mVis    = "v"
  , mVisDim = 2
  , mStmts  =
      [ MNew "a" 2 0
      , MNew "b" 2 0
      , MApply "H"  mH  ["b"]
      , MApply "CX" mCX ["v", "a"]
      , MApply "CX" mCX ["b", "v"]
      , MApply "CX" mCX ["v", "a"]
      , MDrop "a"
      , MDrop "b" ]
  }

-- | A name allocated again after being dropped.
--
-- The calculus permits this, @new@ being the only resurrection, but composition
-- gives every allocation its own tensor factor, so two allocations of one name
-- would be two temporaries sharing a name and 'DQT.Many.Multi.liftGate' would
-- resolve gates to the wrong one.  It is refused with an instruction to rename.
resurrectsAName :: MProgram
resurrectsAName = MProgram
  { mLabel = "probe: a name allocated again after it was dropped"
  , mVis = "v", mVisDim = 2
  , mStmts = [ MNew "a" 2 0, MDrop "a", MNew "a" 2 0, MDrop "a" ] }

-- | A gate applied to a temporary that was already dropped.
usesAfterDrop :: MProgram
usesAfterDrop = MProgram
  { mLabel = "probe: gate on a wire after it was dropped"
  , mVis = "v", mVisDim = 2
  , mStmts = [ MNew "a" 2 0, MDrop "a", MApply "H" mH ["a"] ] }

-- | A gate applied to a temporary before it is allocated.
gatesBeforeAlloc :: MProgram
gatesBeforeAlloc = MProgram
  { mLabel = "probe: gate on a wire before it is allocated"
  , mVis = "v", mVisDim = 2
  , mStmts = [ MApply "H" mH ["a"], MNew "a" 2 0, MDrop "a" ] }

-- Reporting

-- | The trichotomy, printed over the module's own examples plus the ones
-- "DQT.Many.Multi" supplies, showing all three levels inhabited at once.
nestedReport :: String
nestedReport = unlines $
  [ "nested allocation: does the witness survive the nesting?"
  , ""
  , "  The bundle settles the verdict, not the witness: a bundled witness has"
  , "  one temporary of dimension d_1 * ... * d_n, which is not a program of"
  , "  the surface language. A nested witness prepares each wire with its own"
  , "  gate. When does one exist?"
  , ""
  ] ++ concatMap block progs
  where
    progs = [ irreduciblyJoint, reduciblyJoint, phaseBuysTheRoot, bellPair,
              nestedThree
            , interleavedDrops, usesAfterDrop, gatesBeforeAlloc
            , resurrectsAName ]
    block p =
      [ replicate 72 '='
      , "  " ++ mLabel p
      , "    joint verdict         : " ++ shw (jointSafe p)
      , "    every wire fixed      : " ++ shw (everyWireSafe p)
      , "    parked state factors  : " ++ either (const "?") (maybe "no" (const "yes"))
                                            (parkedFactors p)
      , "    bundled witness       : " ++ either (const "?") yn (bundledWitnessExists p)
      ]
      ++ row "nested witness /Q(w)  " (verdictOf qOmega p)
      ++ row "nested witness /Z[1/2]" (verdictOf zHalf p)
      ++ [ "" ]
    row lbl s = case wrapAt 50 s of
      []       -> [ "    " ++ lbl ++ ": " ]
      (l : ls) -> ("    " ++ lbl ++ ": " ++ l)
                    : [ replicate 28 ' ' ++ l' | l' <- ls ]
    shw = either (const "?") show
    yn b = if b then "exists" else "none"
    verdictOf ring p = case nestedWitness ring p of
      Right w -> "exists, " ++ show (length (nwPrepare w))
                 ++ " preparation gate(s); re-checked: "
                 ++ show (checkNestedWitness p w)
      Left NotJointlySafe            -> "none: level 1, the drop is unsafe"
      Left ParkedIsEntangled         -> "none: level 2, the parked ray is entangled"
      Left (FactorRayCarriesNoUnitVector k rn n2) ->
        "none: level 3, wire " ++ show k ++ " has ||g_k||^2 = " ++ showK n2
        ++ ", and its ray carries no unit vector over " ++ rn
      Left (FactorPreparationNotOverRing k rn) ->
        "none: wire " ++ show k ++ "'s ray carries a unit vector over " ++ rn
        ++ ", but the reflection preparing it does not lie in " ++ rn
      Left (FactorPreparationNotReal k) ->
        "the ring carries a unit vector on wire " ++ show k
        ++ "'s ray, but it is not real; this construction builds real"
        ++ " reflections only, so no verdict"
      Left (NestedBundleError e)     -> "none: " ++ show e
      Left r                         -> "none: " ++ show r
