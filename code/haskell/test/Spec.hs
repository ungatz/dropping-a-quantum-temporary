-- |
-- The check suite lists the library's claims, each paired with the code that
-- decides it, so a red line names a claim, not a function. It is not a
-- property-based sweep: one check per claim, on the programs of the
-- catalogue. The last three checks gate the package: no inexact
-- arithmetic, every dirty ancilla on a unit state, the language suite green.
module Main (main) where

import Control.Monad (filterM, unless)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import Data.List (isInfixOf)
import System.Exit (exitFailure)

import DQT.Bridge
import DQT.Corpus.Classical
import DQT.Criterion.Context
import DQT.Criterion
import DQT.Calculus.Elaborate
import DQT.Corpus.Examples
import DQT.Calculus.Gates
import DQT.Criterion.Gram
import DQT.Lifted
import DQT.Lifted.Programs
import DQT.Algebra.Linear
import DQT.Calculus.Metatheory
import DQT.Many.Multi
import DQT.Many.Nested
import DQT.Corpus.Producer
import DQT.Corpus.Isolable (isolableIsSound, isolableIncompletenessWitnesses, r3Count)
import DQT.Many.Release
import DQT.Residual
import DQT.Algebra.Scalar
import DQT.Calculus.Syntax
import DQT.Calculus.Typing
import DQT.Criterion.Witness

import S.Lang.Cyclo (Cyclo)
import qualified S.Lang.Interp as SI
import S.Lang.Parser (parseProgram)
import S.Lang.QState (norm2S)
import qualified S.Report.Run as SRun
import qualified S.Suite as SSuite
import qualified S.Lang.Syntax as S

data Check = Check
  { chName  :: String   -- ^ the statement
  , chClaim :: String   -- ^ what it asserts, in one line
  , chOK    :: Bool
  }

main :: IO ()
main = do
  floats <- floatCheck
  dirty  <- newdirtyUnitCheck
  mcx    <- mcxChecks
  putStrLn "  --- the language layer, in full ---"
  sfails <- SSuite.suiteRun
  putStrLn "  --- end of the language layer ---"
  let sCheck = Check "the-language-suite-passes"
                     ("the language layer's own " ++ show SSuite.suiteCheckCount
                       ++ " checks, over " ++ show (length SSuite.suiteAlgorithms)
                       ++ " algorithms")
                     (sfails == 0)
      results = checks ++ mcx ++ [floats, dirty, sCheck]
  mapM_ report results
  let bad = [ c | c <- results, not (chOK c) ]
  putStrLn ""
  putStrLn ("  " ++ show (length results - length bad) ++ " / "
            ++ show (length results) ++ " statements hold")
  putStrLn ("  the language layer: " ++ show SSuite.suiteCheckCount
            ++ " checks in " ++ show (length SSuite.suiteGroups)
            ++ " groups, over " ++ show (length SSuite.suiteAlgorithms)
            ++ " algorithms")
  unless (null bad) $ do
    putStrLn ("  FAILED: " ++ show (map chName bad))
    exitFailure

report :: Check -> IO ()
report c = do
  putStrLn ((if chOK c then "  PASS  " else "  FAIL  ") ++ chName c)
  putStrLn ("        " ++ chClaim c)

-- Typed programs of the catalogue, once

typedCatalogue :: [(String, TypedProgram)]
typedCatalogue = [ (n, tp) | (n, p) <- catalogue, Right tp <- [checkProgram p] ]

allTyped :: Bool
allTyped = length typedCatalogue == length catalogue

isSafe :: TypedProgram -> Bool
isSafe tp = case verdict tp of
  Safe _ -> True
  _      -> False

-- | The verdict every catalogue entry must receive: the one table in the
-- package written by hand rather than computed, so a change in the
-- arithmetic cannot quietly change a verdict. Each entry is justified by the
-- header on its program in "DQT.Corpus.Examples".
expectedVerdicts :: [(String, Bool)]
expectedVerdicts =
  [ ("example-A",     True)   -- both reads are no-ops: the control is |0>
  , ("example-B",     False)  -- H then one read: Kraus operators I/sqrt2 and X/sqrt2
  , ("example-C",     True)   -- two reads compose to the identity on v
  , ("park",          True)   -- nothing touches the visible register
  , ("silq-two-gate", True)   -- H H = 1
  , ("tilt-read",     False)  -- three-dimensional, three independent Kraus operators
  , ("in-shape",      True)   -- it is the shape
  , ("dj-constant",   True)   -- phase kickback leaves the ancilla alone
  , ("dj-balanced",   True)
  , ("bv-0",          True)
  , ("bv-1",          True)
  , ("grover-oracle", True)   -- compute, mark, uncompute
  , ("kickback",      False)  -- cZ after H entangles
  , ("copy-copy",     True)   -- copy twice is the identity
  , ("cz-copy",       False)
  , ("compute-alone", False)  -- it copies the visible register into the temporary
  , ("do-nothing",    True)
  ]

checks :: [Check]
checks =
  [ Check "gate-classicality-alone-is-an-unsound-discard-rule"
      "a permutation can move visible data into the temporary; compute-alone is the witness"
      (not qfreeIsSound && qfreeUnsoundnessWitnesses == ["compute-alone"])

  , Check "a-producer-discipline-is-sound-and-strictly-incomplete"
      "with the dataflow clause restored it accepts no unsafe drop, and refuses ten safe ones"
      (producerIsSound && length producerIncompletenessWitnesses == 10)

  , Check "the-producer-table-totals-are-the-published-ones"
      ("the totals the catalogue reports: R1 accepts four, "
       ++ "R2 accepts two, the criterion admits twelve")
      (r1Count == 4 && r2Count == 2 && safeCount == 12)

  , Check "output-isolability-is-sound-and-strictly-incomplete"
      ("output-isolability as Faro, Marino and Messina write Definition 5, "
       ++ "run at the drop site: "
       ++ "it accepts no unsafe drop, and refuses two safe ones")
      (isolableIsSound && isolableIncompletenessWitnesses == ["dj-balanced", "bv-1"])

  , Check "the-isolability-count-on-the-strict-reading"
      "R3, on the strict reading, accepts ten of the seventeen catalogue programs"
      (r3Count == 10)

  , Check "the-scalar-field-is-a-field"
      "every nonzero element of the scalar field has an inverse, computed exactly"
      (and [ kmul x (kinv x) == kone | x <- fieldSamples ]
       && ksqrtReal (fromInt 2) == Just ksqrt2
       && ksqrtReal khalf == Just kinvsqrt2)

  , Check "every-catalogue-program-types"
      "the catalogue is well typed; a program that fails typing is not a program"
      allTyped

  , Check "allocFree-is-the-single-scope-premise"
      "a second allocation inside an allocation body is rejected, and only that"
      (case checkProgram nestedAlloc of
         Left e -> e == AllocInBody
         _      -> False
       && either (const False) (const True) (checkProgram flatAlloc))

  , Check "typing-forces-the-core-map-to-be-an-isometry"
      "K^dagger K = 1 on every typed program: this is why W comes out unitary"
      (and [ matMul (matConjTranspose (coreMap tp)) (coreMap tp)
               == matId (tpVisDim tp)
           | (_, tp) <- typedCatalogue ])

  , Check "the-denotation-agrees-with-the-machine"
      "the compositional semantics and the operational one give the same matrix"
      (and [ agreesWithMachine tp | (_, tp) <- typedCatalogue ])

  , Check "drop-moves-a-factor-it-does-not-erase-one"
      "after the drop the temporary is still there, as a latent tensor factor"
      (and [ droppedDims tp == [tpTmpDim tp]
             && length (coreMap tp) == tpTmpDim tp * tpVisDim tp
           | (_, tp) <- typedCatalogue ])

  , Check "the-two-routes-to-the-criterion-agree"
      "vanishing cut minors and slice rank <= 1 decide every program alike"
      (and [ routesAgree tp | (_, tp) <- typedCatalogue ])

  , Check "slice-Gram-and-Choi-ranks-agree"
      "the three matrices of the splitting section have one rank between them"
      (and [ ranksAgree (tpTmpDim tp) (tpVisDim tp) (coreMap tp)
           | (_, tp) <- typedCatalogue ])

  , Check "the-Gram-identity-decides-the-criterion"
      "G^2 = tr(G) G exactly when the slices are collinear, on every program and every lifted trace"
      (and [ gramIsRankAtMostOne d m k == slicesAreCollinear d m k
           | (d, m, k) <- coreMapsEverywhere ])

  , Check "the-Gram-matrix-carries-the-certificate-ray"
      "on every safe program G^T / tr(G) is the projector onto the parked line"
      (and [ case (certificateOf tp, parkedProjector (tpTmpDim tp) (tpVisDim tp) (coreMap tp)) of
               (Just c, Just p) -> p == rayProjector (certParked c)
               _                -> False
           | (_, tp) <- typedCatalogue, isSafe tp ])

  , Check "the-verdicts-are-the-expected-ones"
      "every catalogue program receives the verdict claimed for it"
      (and [ maybe False (\tp -> isSafe tp == want) (lookup n typedCatalogue)
           | (n, want) <- expectedVerdicts ]
       && length expectedVerdicts == length catalogue)

  , Check "direction-1-a-program-of-the-shape-is-safe"
      "elaborating sep(R,W) gives (R e_i0) (x) W, hence rank one, for every R, W"
      (and [ forwardDirection m d i0 r w == Right True
           | (d, m, i0, r, w) <- forwardSamples ])

  , Check "direction-2-a-safe-program-is-source-weakenable"
      "every safe program yields a program of the shape with the same denotation"
      (and [ case synthesize tp of
               Left  _ -> False
               Right w -> checkWitness tp w && inSepShape (wProgram w)
           | (_, tp) <- typedCatalogue, isSafe tp ])

  , Check "direction-2-refuses-exactly-the-unsafe-programs"
      "synthesis fails on an unsafe program, and reports the rank that beat it"
      (and [ case synthesize tp of
               Left (DoesNotFactor r _) -> r >= 2
               _                        -> False
           | (_, tp) <- typedCatalogue, not (isSafe tp) ])

  , Check "the-shape-is-a-denotational-property-not-a-syntactic-one"
      "example-C is safe and is not in the shape; its witness deletes both reads"
      (maybe False (not . inSepShape) (byName "example-C")
       && maybe False inSepShape (byName "in-shape")
       && witnessDeletesTheReads)

  , Check "a-client-sees-exactly-the-Choi-matrix"
      "observational equality under the standard clients = equal channels"
      (and [ observationsDetermineChannel a b
           | (_, a) <- typedCatalogue, (_, b) <- typedCatalogue ])

  , Check "the-identity-client-alone-is-too-weak"
      "compute-alone and do-nothing are separated only by a mixing continuation"
      (case (checkProgram computeAlone, checkProgram doNothing) of
         (Right a, Right b) -> identityOnlyIsNotEnough a b
         _                  -> False)

  , Check "bundling-preserves-the-denotation"
      "many temporaries compile to one of dimension prod d_i, with the same map"
      (all bundlePreservesDenotation [bellPair, wideVisible, nestedThree])

  , Check "joint-safety-is-strictly-coarser-than-per-wire-safety"
      "the Bell pair is jointly safe while neither wire is safe on its own"
      (jointSafe bellPair == Right True
       && everyWireSafe bellPair == Right False)

  , Check "one-text-can-have-two-verdicts"
      "the lifted witness is oracle-split; deleting its read makes it constant"
      (case (checkLProgram liftedWitness, checkLProgram liftedWitnessNoRead) of
         (Right a, Right b) -> oracleSplit a
                               && everySoundStaticDisciplineRejects a
                               && constantProfile b && not (oracleSplit b)
         _                  -> False)

  , Check "the-naive-quantum-encoding-of-the-classical-core-does-not-split"
      "equal amplitudes turn the leaking permutation into an invisible swap"
      (case checkLProgram classicalCoreNaiveEncoding of
         Right a -> not (oracleSplit a)
         Left  _ -> False)

  , Check "the-residual-table-agrees-with-the-semantic-criterion"
      "at every measurement record, the emitted table rules as the criterion does"
      (and [ residualAgrees tp == Just []
           | p <- [liftedWitness, liftedWitnessNoRead]
           , Right tp <- [checkLProgram p] ])

  , Check "a-scratch-bit-is-never-underdetermined"
      "no permutation of V x {0,1} splits; the trit of the boundary section does"
      (all twoLevelsNeverSplit [2, 3, 4] && threeLevelsCanSplit)

  , Check "the-two-engines-agree"
      "theory engine (build K, take a rank) = language engine (probe, compare lines)"
      (null bridgeDisagreements)

  , Check "the-residual-pass-is-exhaustive-and-agrees"
      "every measurement record has a table entry, and every entry matches the criterion"
      (and [ a && b | (_, a, b) <- residualCheckedTwice ])

  , Check "gate-output-binders-must-be-distinct"
          "the Gate rule needs t' /= v' as Pair needs v1 /= v2; reusing a consumed input name stays legal"
          (checkProgram collidingOutputs `failsWith` "t' /= v'"
           && isRight (checkProgram shadowingIsFine))

  , Check "a-register-dimension-must-be-positive"
          "checkProgram rejects a visible dimension of 0 and of -1"
          (all (isLeft . checkProgram . visibleOfDim) [0, -1, -2])

  , Check "a-ragged-matrix-is-refused-not-elaborated"
          "checkGate rejects a gate whose rows have unequal length, which would otherwise reach coreMap and crash"
          raggedIsRefused

  , Check "a-dropped-wire-is-untouchable"
      "a gate on a wire already dropped, or on one not yet allocated, is rejected"
      (case (bundle usesAfterDrop, bundle gatesBeforeAlloc,
             bundle resurrectsAName) of
         (Left (GateOnDeadRegister _ "a"), Left (GateBeforeAllocation _ "a"),
          Left (ReallocatedAfterDrop "a")) -> True
         _                                 -> False)

  , Check "the-drop-order-lemma-holds-where-it-could-fail"
      "each wire's verdict at its own drop site equals its verdict at the end, on a program where truncating removes half the gates"
      (all dropOrderIsIrrelevant
        [ interleavedDrops, bellPair, nestedThree, irreduciblyJoint
        , reduciblyJoint, phaseBuysTheRoot ]
       -- and the check certifies its own non-vacuity: truncating
       -- interleavedDrops at a's drop really does throw most of it away
       && (case truncateAtDrop interleavedDrops "a" of
             Just q  -> length (mStmts q) * 2 < length (mStmts interleavedDrops)
             Nothing -> False))

  , Check "the-nested-witness-trichotomy-is-inhabited"
      "all three levels occur: an entangled ray, a product ray with no witness over Z[1/2], and a witness where the arithmetic allows one"
      (case (nestedWitness zHalf bellPair, nestedWitness zHalf irreduciblyJoint,
             nestedWitness zHalf reduciblyJoint) of
         (Left ParkedIsEntangled, Left (FactorRayCarriesNoUnitVector _ _ _), Right w)
           -> checkNestedWitness reduciblyJoint w
         _ -> False)

  , Check "a-phase-can-supply-what-a-square-root-cannot"
      "the ray (1,1,1) carries a unit vector although sqrt 3 is not in the field, since |1 + sqrt2 i|^2 = 3"
      (let lam  = kadd kone (kmul ksqrt2 kimag)          -- 1 + sqrt2 i
           n    = kmul lam (kconj lam)
           ray  = [kone, kone, kone]
       in n == fromInt 3
          && ksqrtReal (fromInt 3) == Nothing            -- sqrt 3 is NOT in K
          && (case rayCarriesUnitVector qOmega ray of    -- yet the ray carries one
                Just u  -> vnorm2 u == kone
                Nothing -> False))

  , Check "a-scratch-qubit-splits-once-a-joint-gate-follows-the-lift"
      "a joint gate after the lift splits a qubit temporary: both records at weight 1/2, one safe, one unsafe"
      (case checkLProgram qubitSplitAfterJointGate of
         Left _   -> False
         Right tp ->
           let vs = verdictProfile tp
           in ltDepth tp == 1
              && length vs == 2
              && oracleSplit tp
              && not (constantProfile tp)
              && all ((== Just (kdiv kone (fromInt 2))) . tvWeight) vs)

  , Check "the-summed-channel-does-not-decide-the-drop"
      "H then CZ then lift against H then lift then compute: equal Choi matrices, equal branch weights, opposite verdicts"
      (case (checkLProgram sameChannelSafe, checkLProgram sameChannelUnsafe) of
         (Right a, Right b) ->
           let prof tp = [ (isSafeV (tvVerdict v), tvWeight v)
                         | v <- verdictProfile tp ]
               half     = Just (kdiv kone (fromInt 2))
           in sumChoiOf a == sumChoiOf b
              && prof a == [(True,  half), (True,  half)]
              && prof b == [(False, half), (False, half)]
         _ -> False)

  , Check "gate-classicality-fails-at-every-dimension"
      "computeAloneAt d for d = 2 to 8: one permutation gate, accepted by classicality, refused by the criterion at rank d"
      (and [ qfreeAccepts p && rankOf p == Just d
           | d <- [2 .. 8 :: Int]
           , let p = computeAloneAt d ])

  , Check "every-bit-of-a-depth-two-trace-is-load-bearing"
      "k = 2: five levels, four live records, only the all-In record refused, so either bit flips the verdict"
      (case checkLProgram depthTwoEveryBitLoadBearing of
         Left _   -> False
         Right tp ->
           let vs   = verdictProfile tp
               safe = [ isSafeV (tvVerdict v) | v <- vs ]
               ws   = [ tvWeight v | v <- vs ]
           in ltDepth tp == 2
              && length vs == 4
              && oracleSplit tp
              -- [In,In] refuses; its three neighbours all accept
              && safe == [False, True, True, True]
              -- every branch is live: no verdict rides on a dead trace
              && all (\w -> w /= Nothing && w /= Just kzero) ws)

  , Check "one-respreading-gate-buys-two-live-bits-on-three-levels"
      "tilt after the cyclic relabelling: three levels, four live branches, the verdict a function of neither bit alone"
      (case checkLProgram liveTradeRespread of
         Left _   -> False
         Right tp ->
           let vs   = verdictProfile tp
               safe = [ isSafeV (tvVerdict v) | v <- vs ]
               ws   = [ tvWeight v | v <- vs ]
           in ltDepth tp == 2
              && length vs == 4
              && oracleSplit tp
              && all (\w -> w /= Nothing && w /= Just kzero) ws
              -- not a function of the first bit, not a function of the second
              && not (safe !! 0 == safe !! 1 && safe !! 2 == safe !! 3)
              && not (safe !! 0 == safe !! 2 && safe !! 1 == safe !! 3))

  , Check "the-per-lifetime-negative-has-a-separating-pair"
      "shuffleSafe and shuffleUnsafe have equal per-wire projections and opposite drop verdicts"
      (projectionsAgree shuffleSafe shuffleUnsafe
       && wireSafe shuffleSafe   "a" == Right True
       && wireSafe shuffleUnsafe "a" == Right False)

  , Check "carrying-a-unit-vector-is-necessary-not-sufficient"
      "over Z[1/2] the ray carries a unit vector and the reflection preparing it is still not over the ring"
      (let u  = [ kdiv (fromInt n) (fromInt 4) | n <- [1,3,2,1,1] ]
       in vnorm2 u == kone                                  -- a unit vector
          && all (ringHas zHalf) u                          -- over Z[1/2]
          && (case householder 5 0 u of                     -- yet its reflection
                Right m -> not (all (all (ringHas zHalf)) m)   -- is not
                Left _  -> False))

  , Check "per-wire-release-can-cost-a-square-root"
      "jointly safe with every wire fixed, and no nested witness over Z[1/2], where the ray (1,1) carries no unit vector"
      (jointSafe irreduciblyJoint == Right True
       && everyWireSafe irreduciblyJoint == Right True
       && bundledWitnessExists irreduciblyJoint == Right True
       && (case nestedWitness zHalf irreduciblyJoint of
             Left (FactorRayCarriesNoUnitVector _ _ _) -> True
             _                                         -> False))

  , Check "the-obstruction-is-that-two-is-not-a-square"
      "two 4-level wires on the same ray do have a nested witness over Z[1/2]: four is a square and two is not"
      (case nestedWitness zHalf reduciblyJoint of
         Right w -> length (nwPrepare w) == 2 && checkNestedWitness reduciblyJoint w
         Left _  -> False)

  , Check "every-wire-fixed-implies-jointly-safe"
      ("the per-wire reading is strictly stronger: a product of fixed rays is a "
       ++ "fixed ray, and bellPair witnesses the strictness")
      (all (\q -> everyWireSafe q /= Right True || jointSafe q == Right True)
           [ bellPair, nestedThree, irreduciblyJoint, reduciblyJoint
           , phaseBuysTheRoot ]
       && everyWireSafe bellPair == Right False
       && jointSafe bellPair == Right True)

  , Check "the-restoration-gap-is-eight-of-twelve"
          "the catalogue admits 12 drops and the restoration rule refuses 8 of them"
          (restorationGap == (12, 8))

  , Check "the-restoration-rule-is-sound-but-not-complete"
      "restoring to the allocation ray refuses safe drops, including DJ and BV"
      (restorationRuleIsSufficient
       && all (`elem` restorationRuleIsNotNecessary)
              ["example-C", "dj-constant", "dj-balanced", "bv-0", "bv-1"])

  , Check "the-calculus-is-well-defined"
      "typing total, progress, final dimensions and adequacy over the canonical-chain family"
      (boundedTypingTotality && boundedProgress && boundedFinalDimensionCheck
       && machineIsAFunction && boundedAdequacy && resultTypeIsHonest
       && typingForcesAnIsometry)

  , Check "the-structural-rules-are-the-affine-ones"
      "contraction rejected, implicit weakening rejected, allocFree enforced"
      (contractionIsRejected && implicitWeakeningIsRejected && allocFreeIsEnforced)

  , Check "the-read-family-minimax"
      "the two numbers the read family turns on are 1/2 and 4/9, exactly"
      (readFamilyMinimaxSquared uPlus == khalf
       && productReplacementErrorSquared uPlus 0 == khalf
       && readFamilyMinimaxSquared uTiltIn == fromRat (4/9)
       && productReplacementErrorSquared uTiltIn 0 == fromRat (4/9))
  ]

-- Fixtures the checks need

fieldSamples :: [K]
fieldSamples =
  [ kone, ktwo, khalf, ksqrt2, komega, kimag
  , kadd kone ksqrt2, ksub ksqrt2 kimag, kadd komega kone
  , kadd (fromRat (3/5)) (kmul ktwo komega) ]

-- | @(d, m, i0, R, W)@ for the easy direction.  Every combination is legal
-- source: @R@ acts on the temporary, @W@ on the visible register.
forwardSamples :: [(Int, Int, Int, Mat, Mat)]
forwardSamples =
  [ (2, 2, 0, mId 2,   mId 2)
  , (2, 2, 0, mH,      mId 2)
  , (2, 2, 0, mH,      mX)
  , (2, 2, 1, mX,      mZ)
  , (2, 2, 0, mId 2,   mH)
  , (3, 3, 0, mTilt,   mId 3)
  , (3, 3, 0, mShift 3, mShift 3)
  , (3, 2, 2, mShift 3, mH)
  ]

-- | @example-C@ is @H; READ; READ@, and its witness is @sep(H, 1)@: the two
-- reads are gone.
witnessDeletesTheReads :: Bool
witnessDeletesTheReads =
  case checkProgram spreadAndReadTwice of
    Left  _  -> False
    Right tp -> case synthesize tp of
      Left  _ -> False
      Right w -> wPrepare w == mH
                 && matIsIdentity (wVisible w)
                 && length (gatesIn (progTerm (wProgram w))) == 2
                 && length (gatesIn (progTerm spreadAndReadTwice)) == 3

uPlus :: Vec
uPlus = [kinvsqrt2, kinvsqrt2]

-- | The tilt vector restricted to the block the measurement keeps.
uTiltIn :: Vec
uTiltIn = [fromRat (2/3), fromRat (2/3), kzero]

nestedAlloc :: Program
nestedAlloc = Program "two allocations, one inside the other" "v" 2
  (New "t" 2 0 (New "s" 2 0 (Drop "s" (Drop "t" (Ret "v")))))

flatAlloc :: Program
flatAlloc = Program "one allocation" "v" 2 (New "t" 2 0 (Drop "t" (Ret "v")))

-- The borrowed dirty ancilla, through the surface language

-- | The C3X row of the table of algorithms, run end to end through the
-- concrete syntax, not a hand-built term: Gidney's four-Toffoli
-- three-controlled X on one borrowed ancilla. The loan on @|0>@ must come
-- back on its own ray, the loan on @|+>@ must come back on its own ray, and
-- the text with the fourth Toffoli deleted must be refused.
mcxChecks :: IO [Check]
mcxChecks = mapM one
  [ ( "the-borrowed-ancilla-returns-on-the-loans-own-ray"
    , "programs/mcx-dirty.s"
    , "the drop is admitted and the temporary is left on the line (1,0)"
    , Just [1, 0] )
  , ( "the-borrowed-ancilla-verdict-does-not-depend-on-the-loan"
    , "programs/mcx-dirty-plus.s"
    , "the same text with the loan on |+> is admitted, on the line (1,1)"
    , Just [1, 1] )
  , ( "deleting-the-restoring-toffoli-is-refused"
    , "programs/mcx-dirty-half.s"
    , "with the fourth Toffoli gone the ancilla still holds the and of q1 and q2, and the drop is refused"
    , Nothing )
  ]
  where
    one (nm, path, claim, want) = do
      there <- doesFileExist path
      if not there
        then pure (Check nm (claim ++ "  [MISSING: " ++ path ++ "]") False)
        else do
          src <- readFile path
          pure (Check nm claim (agrees want (SRun.runText src)))

    agrees want (Right rep) = case SRun.rpSites rep of
      [site] -> case SRun.srRows site of
        [row] -> case want of
          Just ln -> SRun.trVerdict row == SI.Admissible
                     && SRun.trLine row == Just (ln :: [Cyclo])
          Nothing -> SRun.trVerdict row == SI.Inadmissible
        _     -> False
      _      -> False
    agrees _ (Left _) = False

-- No inexact arithmetic anywhere

-- | One inexact number would turn an exact zero into a tolerance question.
-- This walks the source directories, strips the comments, and searches what
-- is left for an inexact type name. The walk covers a module added later;
-- the two type names are assembled from halves below because this file is
-- one of the files it reads.
floatCheck :: IO Check
floatCheck = do
  dirs    <- filterM doesDirectoryExist sourceDirs
  files   <- concat <$> mapM haskellFilesIn dirs
  srcs    <- mapM readFile files
  let code    = unlines [ l | s <- srcs, l <- lines s, not (isComment l) ]
      missing = [ d | d <- sourceDirs, d `notElem` dirs ]
      found   = [ n | n <- inexactTypeNames, n `isInfixOf` code ]
  pure (Check "no-floating-point-anywhere"
              ("no inexact numeric type occurs in any expression in the "
               ++ show (length files) ++ " source files of the package"
               ++ (if null missing then "" else "  [MISSING: " ++ show missing ++ "]")
               ++ (if null found then "" else "  [FOUND: " ++ show found ++ "]"))
              (null missing && not (null files) && null found))
  where
    isComment l = case dropWhile (== ' ') l of
      '-' : '-' : _ -> True
      _             -> False

sourceDirs :: [FilePath]
sourceDirs = ["src", "app", "test"]

-- | The two names, assembled rather than written, for the reason above.
inexactTypeNames :: [String]
inexactTypeNames = ["Dou" ++ "ble", "Flo" ++ "at"]

-- | Every Haskell file under a directory, at any depth: the modules sit in
-- subdirectories, and a walk one level deep would read almost none of them
-- while still reporting a pass.
haskellFilesIn :: FilePath -> IO [FilePath]
haskellFilesIn d = do
  names <- listDirectory d
  fmap concat . mapM (one . ((d ++ "/") ++)) $ names
  where
    one p = do
      isDir <- doesDirectoryExist p
      if isDir then haskellFilesIn p
               else pure [ p | ".hs" `isSuffixOfStr` p ]

-- Every dirty ancilla arrives on a unit state

-- | Every @newdirty@ must write a unit vector: @||psi|| = 1@ is the side
-- condition on the rule. A non-unit state carries the wrong weight, and can
-- pick a ray with no unit representative in the scalar tower. The scan is over
-- the directory, so a program added later is covered.
newdirtyUnitCheck :: IO Check
newdirtyUnitCheck = do
  there <- doesDirectoryExist "programs"
  if not there
    then pure (Check "every-newdirty-writes-a-unit-vector"
                     "programs/ not reachable from the working directory"
                     False)
    else do
      names <- listDirectory "programs"
      let ss = [ "programs/" ++ n | n <- names, ".s" `isSuffixOfStr` n ]
      srcs <- mapM readFile ss
      let bad = [ f ++ ": " ++ x ++ " at norm^2 " ++ show (norm2S psi)
                | (f, src) <- zip ss srcs
                , Right (_, prog) <- [parseProgram src]
                , S.NewDirty x _ psi <- prog
                , norm2S psi /= 1 ]
          unparsed = [ f | (f, src) <- zip ss srcs
                         , Left _ <- [parseProgram src] ]
      pure (Check "every-newdirty-writes-a-unit-vector"
                  ("none of the " ++ show (length ss)
                   ++ " shipped programs writes a non-unit state by hand"
                   ++ (if null bad then "" else "  [" ++ show bad ++ "]")
                   ++ (if null unparsed then "" else "  [UNPARSED: "
                        ++ show unparsed ++ "]"))
                  (null bad && null unparsed && not (null ss)))

isSuffixOfStr :: String -> String -> Bool
isSuffixOfStr suf xs = reverse suf `isPrefixOfStr` reverse xs
  where isPrefixOfStr [] _ = True
        isPrefixOfStr _ [] = False
        isPrefixOfStr (a:as) (b:bs) = a == b && isPrefixOfStr as bs

-- | Does this rejection name the premise it is about?  Checking only that a
-- program is refused is too weak: @collidingOutputs@ is also refused for an
-- incidental reason (its body mentions a name the Drop removed), so a bare
-- @isLeft@ passes without the premise existing at all.
failsWith :: Show e => Either e a -> String -> Bool
failsWith (Left e) s = s `isInfixOf` show e
failsWith (Right _) _ = False

isLeft, isRight :: Either a b -> Bool
isLeft  = either (const True)  (const False)
isRight = either (const False) (const True)

-- | @let (t1,t1) = I(t,v) in ...@: one binder name for both outputs.
collidingOutputs :: Program
collidingOutputs =
  Program "colliding" "v" 2 $
    New "t" 2 0 $
      Act ("x","x") (gIdent 2 2) ("t","v") $
        Drop "x" (Ret "x")

-- | @let (t,v) = I(t,v) in ...@: outputs reuse the consumed inputs, ordinary
-- shadowing that must stay legal.
shadowingIsFine :: Program
shadowingIsFine =
  Program "shadowing" "v" 2 $
    New "t" 2 0 $
      Act ("t","v") (gIdent 2 2) ("t","v") $
        Drop "t" (Ret "v")

visibleOfDim :: Int -> Program
visibleOfDim m = Program ("vis" ++ show m) "v" m $ New "t" 2 0 $ Drop "t" (Ret "v")

-- | The witness: a 4x4-shaped gate whose rows are 4, 3, 2 and 1 wide.
-- @matRows = 4@ and @matCols = 4@ (the first row), so a shape test reading
-- the first row alone passes it.
raggedMat :: Mat
raggedMat =
  [ [kzero, kzero, kzero, kneg kone]
  , [kzero, kzero, kneg kone]
  , [kzero, kneg kone]
  , [kneg kone] ]

raggedIsRefused :: Bool
raggedIsRefused =
  case checkProgram raggedProgram of
    Left _  -> True
    Right _ -> False

raggedProgram :: Program
raggedProgram =
  Program "ragged" "v" 2 $
    New "t" 2 0 $
      Act ("t1","v1") (joint "RAGGED" 2 2 raggedMat) ("t","v") $
        Drop "t1" (Ret "v1")

-- | The drop verdict as a boolean.  'DQT.Lifted.admissible' is local to that
-- module, and the trace checks need the profile as a bit vector.
isSafeV :: Verdict -> Bool
isSafeV (Safe _) = True
isSafeV _        = False

-- | The Kraus rank a refused drop reports, or 'Nothing' when it is accepted.
rankOf :: Program -> Maybe Int
rankOf p = case checkProgram p of
  Left _   -> Nothing
  Right tp -> case verdict tp of
    Unsafe _ r -> Just r
    _          -> Nothing

-- | Every denotation the suite knows: the catalogue, and the selected denotation
-- of every lifted example along every measurement record.  Zero maps (unreachable
-- traces) are included on purpose: both tests must call them safe.
coreMapsEverywhere :: [(Int, Int, Mat)]
coreMapsEverywhere =
  [ (tpTmpDim tp, tpVisDim tp, coreMap tp) | (_, tp) <- typedCatalogue ]
  ++ [ (ltTmpDim tp, ltVisDim tp, coreMapAt tp tr)
     | p <- liftedExamples, Right tp <- [checkLProgram p]
     , tr <- allTraces (ltDepth tp) ]

-- | The lifted examples of "DQT.Lifted".
liftedExamples :: [LProgram]
liftedExamples =
  [ liftedWitness, liftedWitnessNoRead, classicalCoreNaiveEncoding
  , qubitSplitAfterJointGate, depthTwoEveryBitLoadBearing, liveTradeRespread
  , sameChannelSafe, sameChannelUnsafe ]

-- | The orthogonal projector @g g^dagger / ||g||^2@ onto the line of @g@.
rayProjector :: Vec -> Mat
rayProjector g = [ [ kdiv (kmul a (kconj b)) n | b <- g ] | a <- g ]
  where n = vnorm2 g

-- | The Choi matrix of a lifted program's summed channel: the branch
-- channels added up, what a continuation that cannot see the measurement
-- record observes.
sumChoiOf :: LTypedProgram -> Mat
sumChoiOf tp = foldr1 (zipWith (zipWith kadd))
  [ choiMatrix (ltTmpDim tp) (ltVisDim tp) (coreMapAt tp tr)
  | tr <- allTraces (ltDepth tp) ]
