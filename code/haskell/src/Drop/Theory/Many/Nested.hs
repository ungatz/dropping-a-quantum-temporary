-- Drop.Theory.Many.Nested: when a safe bundle can be prepared one temporary at a time.
--
-- Question: A program with several temporaries is safe as a bundle. Is each temporary prepared by a gate
--           of its own, and over which ring of scalars?
-- Answer:   parkedState reads off the vector g the bundle is left on (Nothing when the bundle is unsafe:
--           level 1). parkedFactors splits g into one vector for each temporary, one cut at a time
--           (Nothing when g is entangled across them: level 2). nestedWitness takes a gate ring (zHalf, or
--           qOmega, the field this package computes in) and, for each factor, asks whether its ray carries
--           a unit vector over the ring (rayCarriesUnitVector) and builds the real reflection that carries
--           the temporary's allocation state to it; a ray with no such vector over the ring is level 3. A
--           failure is a NestedReason. checkNestedWitness checks the gates are unitary and prepare
--           the factors. bundledWitnessExists asks whether one gate on the whole bundle does the same.
--           truncateAtDrop, wireSafeAtDropSite and dropOrderIsIrrelevant check that a wire's verdict does not
--           depend on where its drop stands. bellPair (level 2), irreduciblyJoint (level 3) and
--           reduciblyJoint (a witness exists) are one program for each outcome; nestedReport prints them.
-- Paper:    sec:factor (a tuple drop is one site); the paper does not state the gate rings.
-- Shapes:   GateRing        a name, membership in the ring, and a unit vector on a ray over the ring if there is one.
--           NestedWitness   a unit vector, a gate preparing it and a visible matrix, for each temporary.
--           NestedReason    why there is no nested witness: a level of the trichotomy, or a failing hypothesis.

module Drop.Theory.Many.Nested
  ( -- * The nested witness
    NestedWitness(..)
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
  , dropOrderIsIrrelevant
    -- * The trichotomy, inhabited
  , irreduciblyJoint
  , reduciblyJoint
  , phaseBuysTheRoot
  , usesAfterDrop, gatesBeforeAlloc, resurrectsAName
  , interleavedDrops
    -- * Reporting
  , nestedReport
  ) where

import qualified Data.Ratio
import Data.Bits ((.&.))

import Drop.Theory.Criterion (safeByRank)
import Drop.Theory.Pretty (wrapAt)
import Drop.Theory.Program.Elaborate (coreMap)
import Drop.Theory.Program.Gates (mCX, mH)
import Drop.Theory.Algebra.Linear
import Drop.Theory.Many.Multi
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Criterion.Split (Split (..), factorSplit)
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing
import Drop.Theory.Criterion.Witness (Reason (..), householder, synthesize)

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
    -- impossible: bundle has already run scopeCheck, which states the premises the core checker needs
    Left e   -> error ("Drop.Theory.Many.Nested.parkedState: bundled program ill-typed: "
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

-- The bundle of the Bell pair is left on the Bell state; an unsafe bundle has no state.
-- >>> let hh = MProgram "two Hadamards" "v" 2 [MNew "a" 2 0, MNew "b" 2 0, MApply "H" mH ["a"], MApply "H" mH ["b"], MDrop "a", MDrop "b"]
-- >>> parkedState bellPair
-- Right (Just [sqrt2/2,0,0,sqrt2/2])
-- >>> parkedState hh
-- Right (Just [1/2,1/2,1/2,1/2])
-- >>> parkedState (MProgram "p" "v" 2 [MNew "a" 2 0, MApply "H" mH ["a"], MApply "CX" mCX ["a", "v"], MDrop "a"])
-- Right Nothing

-- | The per-temporary factors of the constant state, when it is a full
-- product across the partition of temporaries.
--
-- @Nothing@ covers levels 1 and 2 together (unsafe or safe-but-entangled);
-- 'parkedState' tells them apart. Each factor is on its own ray, as the split
-- returns it (a column of a coefficient matrix), so it is not scaled.
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

-- The Bell state does not factor across its two qubits; two Hadamards leave a product.
-- >>> let hh = MProgram "two Hadamards" "v" 2 [MNew "a" 2 0, MNew "b" 2 0, MApply "H" mH ["a"], MApply "H" mH ["b"], MDrop "a", MDrop "b"]
-- >>> parkedFactors bellPair
-- Right Nothing
-- >>> parkedFactors hh
-- Right (Just [[1/2,1/2],[1,1]])
-- >>> parkedFactors (MProgram "p" "v" 2 [MNew "a" 2 0, MApply "H" mH ["a"], MApply "CX" mCX ["a", "v"], MDrop "a"])
-- Right Nothing

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

-- >>> (ringName zHalf, ringHas zHalf kone, ringHas zHalf kimag)
-- ("Z[1/2]",True,False)
-- >>> (ringName qOmega, ringHas qOmega kimag)
-- ("Q(w)",True)

-- | @Z[1/2]@: real, dyadic, no @i@ and no @sqrt2@. A unit vector on @[g]@
-- needs a real @lambda@ with @lambda^2 ||g||^2 = 1@, a square root of a
-- dyadic rational.
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

-- One half is in Z[1/2]; one third and i are not.
-- >>> map (ringHas zHalf) [kdiv kone ktwo, kdiv kone (fromInt 3), kimag]
-- [True,False,False]
-- >>> rayCarriesUnitVector zHalf [kone, kone, kone, kone]
-- Just [1/2,1/2,1/2,1/2]
-- >>> rayCarriesUnitVector zHalf [kone, kone]
-- Nothing

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

-- Every scalar of Q(w) is in the ring; the ray (1,1) carries a unit vector there.
-- >>> map (ringHas qOmega) [kdiv kone ktwo, kimag]
-- [True,True]
-- >>> rayCarriesUnitVector qOmega [kone, kone]
-- Just [(-1/2 + -1/2w^2),(-1/2 + -1/2w^2)]
-- >>> rayCarriesUnitVector qOmega [kone, kzero]
-- Just [-1,0]

-- | Does the ray through @g@ carry a unit vector over the ring?
rayCarriesUnitVector :: GateRing -> Vec -> Maybe Vec
rayCarriesUnitVector = ringUnitOnRay

-- The ray (1,1,1) needs a phase: its unit vector has entries (-1 - w - w^3)/3.
-- >>> rayCarriesUnitVector zHalf [kone, kone]
-- Nothing
-- >>> fmap vnorm2 (rayCarriesUnitVector qOmega [kone, kone, kone])
-- Just 1
-- >>> fmap (map (kmul (fromInt 3))) (rayCarriesUnitVector qOmega [kone, kone, kone])
-- Just [(-1 + -1w + -1w^3),(-1 + -1w + -1w^3),(-1 + -1w + -1w^3)]

-- The Nested Witness

-- | A witness in the nested shape: one preparation gate per temporary, and one
-- gate on the visible register.
data NestedWitness = NestedWitness
  { nwFactors :: [Vec]  -- ^ @g_1 .. g_n@, each a unit vector over @K@
  , nwPrepare :: [Mat]  -- ^ @R_1 .. R_n@, each a gate on that temporary alone
  , nwVisible :: Mat    -- ^ @W@
  }

-- >>> :m + Drop.Theory.Program.Gates
-- >>> let xx = MProgram "two flips" "v" 2 [MNew "a" 2 0, MNew "b" 2 0, MApply "X" mX ["a"], MApply "X" mX ["b"], MDrop "a", MDrop "b"]
-- >>> either (const ([], [], [])) (\w -> (nwFactors w, nwPrepare w, nwVisible w)) (nestedWitness zHalf xx)
-- ([[0,1],[0,1]],[[[0,1],[1,0]],[[0,1],[1,0]]],[[1,0],[0,1]])

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
      -- is not real, and 'Drop.Theory.Criterion.Witness.householder' builds real
      -- reflections only: a limit of this construction, not "no witness".
  | FactorReflectionFailed Int Reason
      -- ^ the per-temporary Householder construction failed for temporary @k@.
  deriving (Show)

-- The reasons print as constructors. The last failure: a unit vector over Z[1/2] whose preparing reflection leaves the ring.
-- >>> let u = map (\n -> kdiv (fromInt n) (fromInt 4)) [1, 3, 2, 1, 1]
-- >>> NotJointlySafe
-- NotJointlySafe
-- >>> ParkedIsEntangled
-- ParkedIsEntangled
-- >>> FactorRayCarriesNoUnitVector 0 "Z[1/2]" kone
-- FactorRayCarriesNoUnitVector 0 "Z[1/2]" 1
-- >>> FactorPreparationNotReal 1
-- FactorPreparationNotReal 1
-- >>> (all (ringHas zHalf) u, vnorm2 u)
-- (True,1)
-- >>> fmap (filter (not . ringHas zHalf) . concat) (householder 5 0 u)
-- Right [2/3,-1/6,-1/6,-1/6,11/12,-1/12,-1/6,-1/12,11/12]

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

-- The three outcomes over Z[1/2] on the smallest programs: no bundle state, an entangled one, a ray with no unit vector; and a witness for two flipped qubits.
-- >>> :m + Drop.Theory.Program.Gates
-- >>> let xx = MProgram "two flips" "v" 2 [MNew "a" 2 0, MNew "b" 2 0, MApply "X" mX ["a"], MApply "X" mX ["b"], MDrop "a", MDrop "b"]
-- >>> let hh = MProgram "two Hadamards" "v" 2 [MNew "a" 2 0, MNew "b" 2 0, MApply "H" mH ["a"], MApply "H" mH ["b"], MDrop "a", MDrop "b"]
-- >>> either show (const "witness") (nestedWitness zHalf (MProgram "p" "v" 2 [MNew "a" 2 0, MApply "H" mH ["a"], MApply "CX" mCX ["a", "v"], MDrop "a"]))
-- "NotJointlySafe"
-- >>> either show (const "witness") (nestedWitness zHalf bellPair)
-- "ParkedIsEntangled"
-- >>> either show (const "witness") (nestedWitness zHalf irreduciblyJoint)
-- "FactorRayCarriesNoUnitVector 0 \"Z[1/2]\" 1/2"
-- >>> either show (const "witness") (nestedWitness zHalf xx)
-- "witness"
-- >>> either show (const "witness") (nestedWitness qOmega hh)
-- "FactorPreparationNotReal 0"

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

-- The witness for two flipped qubits passes; the same gates do not prepare a program of another shape.
-- >>> :m + Drop.Theory.Program.Gates
-- >>> let xx = MProgram "two flips" "v" 2 [MNew "a" 2 0, MNew "b" 2 0, MApply "X" mX ["a"], MApply "X" mX ["b"], MDrop "a", MDrop "b"]
-- >>> either (const False) (checkNestedWitness xx) (nestedWitness zHalf xx)
-- True
-- >>> either (const False) (checkNestedWitness (MProgram "p" "v" 2 [MNew "a" 2 0, MDrop "a"])) (nestedWitness zHalf xx)
-- False

-- | Does the composite witness exist?  This is 'Drop.Theory.Criterion.Witness.synthesize' on
-- the composite program; at level 3 it is 'True' while 'nestedWitness'
-- fails.
bundledWitnessExists :: MProgram -> Either BundleError Bool
bundledWitnessExists p = do
  b <- bundle p
  case checkProgram b of
    -- impossible: bundle has already run scopeCheck, which states the premises the core checker needs
    Left e   -> error ("Drop.Theory.Many.Nested.bundledWitnessExists: " ++ show e)
    Right tp -> pure (either (const False) (const True) (synthesize tp))

-- A bundle can have a witness although its temporaries cannot be prepared one by one.
-- >>> bundledWitnessExists irreduciblyJoint
-- Right True
-- >>> bundledWitnessExists bellPair
-- Right True

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

-- >>> fmap (length . mStmts) (truncateAtDrop interleavedDrops "a")
-- Just 3
-- >>> fmap mLabel (truncateAtDrop interleavedDrops "a")
-- Just "drops interleaved: a is allocated, used and dropped before b exists  [truncated at drop a]"
-- >>> fmap (length . mStmts) (truncateAtDrop interleavedDrops "z")
-- Nothing

-- | The per-temporary verdict for @t@ computed at its own drop site, by truncating
-- the program there.
wireSafeAtDropSite :: MProgram -> Name -> Either BundleError Bool
wireSafeAtDropSite p t = case truncateAtDrop p t of
  Nothing -> Left (NotAllDropped [t])
  Just q  -> wireSafe q t

-- >>> wireSafeAtDropSite interleavedDrops "a"
-- Right True
-- >>> wireSafeAtDropSite bellPair "a"
-- Right False
-- >>> wireSafeAtDropSite bellPair "z"
-- Left these temporaries are never dropped, so the program does not have the visible result type: ["z"]

-- | The drop-order lemma, checked rather than argued: for every temporary,
-- the verdict at its own drop site agrees with the verdict at the end.
--
-- The comparison is not trivial: 'bundle' ignores where a drop stands, so the
-- two sides come from different programs (truncated and whole); the affine
-- discipline is what forces agreement.
dropOrderIsIrrelevant :: MProgram -> Bool
dropOrderIsIrrelevant p =
  -- refusal: a program that fails scopeCheck has no drop order to compare
  either (error . ("dropOrderIsIrrelevant: " ++) . show) (const True) (scopeCheck p) &&
  and [ wireSafeAtDropSite p t == wireSafe p t | (t, _, _) <- mTemporaries p ]

-- >>> dropOrderIsIrrelevant interleavedDrops
-- True
-- >>> dropOrderIsIrrelevant bellPair
-- True

-- The Inhabitants

-- | The all-ones ray in dimension @d@, as a unit vector when it is one.
allOnesPrep :: Int -> Mat
allOnesPrep d =
  case ksqrtReal (fromInt (fromIntegral d)) of
    Just c  -> case householder d 0 (map (`kdiv` c) (vAllOnes d)) of
                 Right m -> m
                 Left _  -> matId d
    Nothing -> matId d

-- The Householder reflection onto the all-ones ray; in dimension 3 the root of 3 is missing, so the identity stands in.
-- >>> matColumn (allOnesPrep 4) 0
-- [1/2,1/2,1/2,1/2]
-- >>> matIsUnitary (allOnesPrep 4)
-- True
-- >>> allOnesPrep 3 == matId 3
-- True

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

-- >>> (mLabel phaseBuysTheRoot, mTemporaries phaseBuysTheRoot)
-- ("two 3-level wires on the all-ones ray of H_9, where the phase pays",[("a",3,0),("b",3,0)])

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
      -- all-ones ray (it needs 1/sqrt2, and H is not over Z[1/2]). The 4x4
      -- all-ones Householder is over Z[1/2]: ||w||^2 = 1, every entry +-1/2.
      , MApply "R4" (allOnesPrep 4) ["a", "b"]
      , MDrop "a"
      , MDrop "b" ]
  }

-- Over Z[1/2]: safe as a bundle, and the first wire's ray needs a root of 2.
-- >>> (mLabel irreduciblyJoint, mTemporaries irreduciblyJoint)
-- ("two qubits, one joint gate over Z[1/2]: bundle preparable, neither wire",[("a",2,0),("b",2,0)])
-- >>> parkedFactors irreduciblyJoint
-- Right (Just [[1/2,1/2],[1,1]])
-- >>> jointSafe irreduciblyJoint
-- Right True

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

-- >>> (mLabel reduciblyJoint, mTemporaries reduciblyJoint)
-- ("two 4-level wires on the all-ones ray: the control, a nested witness exists",[("a",4,0),("b",4,0)])


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

-- >>> map (\s -> case s of { MNew {} -> "new"; MApply {} -> "apply"; MDrop {} -> "drop" }) (mStmts interleavedDrops)
-- ["new","apply","drop","new","apply","apply","drop"]
-- >>> jointSafe interleavedDrops
-- Right True

-- | A name allocated again after being dropped.
--
-- The calculus permits this, @new@ being the only resurrection, but composition
-- gives every allocation its own tensor factor, so two allocations of one name
-- would be two temporaries sharing a name and 'Drop.Theory.Many.Multi.liftGate' would
-- resolve gates to the wrong one.  It is refused with an instruction to rename.
resurrectsAName :: MProgram
resurrectsAName = MProgram
  { mLabel = "probe: a name allocated again after it was dropped"
  , mVis = "v", mVisDim = 2
  , mStmts = [ MNew "a" 2 0, MDrop "a", MNew "a" 2 0, MDrop "a" ] }

-- >>> either show (const "ok") (scopeCheck resurrectsAName)
-- "the name \"a\" is allocated again after being dropped; bundling gives each allocation its own factor, so rename the second one (alpha-conversion) and bundle again"

-- | A gate applied to a temporary that was already dropped.
usesAfterDrop :: MProgram
usesAfterDrop = MProgram
  { mLabel = "probe: gate on a wire after it was dropped"
  , mVis = "v", mVisDim = 2
  , mStmts = [ MNew "a" 2 0, MDrop "a", MApply "H" mH ["a"] ] }

-- >>> either show (const "ok") (scopeCheck usesAfterDrop)
-- "gate H names the temporary \"a\", which has already been dropped, and a dropped name is untouchable"

-- | A gate applied to a temporary before it is allocated.
gatesBeforeAlloc :: MProgram
gatesBeforeAlloc = MProgram
  { mLabel = "probe: gate on a wire before it is allocated"
  , mVis = "v", mVisDim = 2
  , mStmts = [ MApply "H" mH ["a"], MNew "a" 2 0, MDrop "a" ] }

-- >>> either show (const "ok") (scopeCheck gatesBeforeAlloc)
-- "gate H names the temporary \"a\" before it is allocated"

-- Reporting

-- | The trichotomy, printed over the module's own examples plus the ones
-- "Drop.Theory.Many.Multi" supplies, showing all three levels inhabited at once.
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

-- The first lines of the report, shown as strings.
-- >>> mapM_ print (take 4 (lines nestedReport))
-- "nested allocation: does the witness survive the nesting?"
-- ""
-- "  The bundle settles the verdict, not the witness: a bundled witness has"
-- "  one temporary of dimension d_1 * ... * d_n, which is not a program of"
