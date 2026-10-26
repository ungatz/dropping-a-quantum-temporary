-- Spec: the paper's named statements, each paired with the code that decides it.
--
-- Question: Does each claim of the paper hold of the package's two checkers,
--           on the programs the paper discusses?
-- Answer:   The suite lists 44 statements, each with a name, a one-line
--           claim and the code that decides it, so a red line names a
--           theorem, not a function. It is not a property-based sweep: one
--           statement per claim, on the catalogue of Drop.Theory.Corpus.Examples
--           and the lifted examples. Thirty-eight are decided by the theory
--           layer, or by Drop.Bridge against the language layer (typing, the
--           denotation, the verdicts, the two directions of the criterion,
--           bundling, lifts, the boundary, nested witnesses, square roots);
--           three run the borrowed-loan programs through the report; the last
--           three gate the package: no inexact numeric type occurs in any
--           source file, every state a shipped program writes by hand is a unit
--           vector, and the language layer's own suite passes. It prints each
--           statement with its claim, then "n / 44 statements hold".
-- Paper:    thm:criterion, prop:gram, prop:composite, prop:channel,
--           cor:nostatic, sec:boundary, sec:residual, thm:loancriterion
-- Shapes:   Check   a named statement: its name, its claim in one line, and
--                   whether it holds

module Main (main) where

import Control.Monad (filterM, unless)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import Data.Either (isLeft, isRight)
import Data.List (isInfixOf, isSuffixOf)
import System.Exit (exitFailure)

import Drop.Bridge
import Drop.Theory.Corpus.Classical
import Drop.Theory.Criterion.Context
import Drop.Theory.Criterion
import Drop.Theory.Program.Elaborate
import Drop.Theory.Corpus.Examples
import Drop.Theory.Program.Gates
import Drop.Theory.Criterion.Gram
import Drop.Theory.Lifted
import Drop.Theory.Lifted.Programs
import Drop.Theory.Algebra.Linear
import Drop.Theory.Many.Multi
import Drop.Theory.Many.Nested
import Drop.Theory.Residual
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing
import Drop.Theory.Criterion.Witness

import Drop.Lang.Scalar (Cyclo)
import qualified Drop.Lang.Criterion as SC
import Drop.Lang.Parser (parseProgram)
import Drop.Lang.State (norm2S)
import qualified Drop.Lang.Report.Run as SRun
import qualified Drop.Lang.Suite as SSuite
import Drop.Lang.Checks.Parser (readCorpus)
import qualified Drop.Lang.Flat as S

data Check = Check
  { chName  :: String   -- ^ the statement
  , chClaim :: String   -- ^ what it asserts, in one line
  , chOK    :: Bool
  }

main :: IO ()
main = do
  corpus <- readCorpus
  floats <- floatCheck
  dirty  <- loanUnitCheck
  mcx    <- mcxChecks
  putStrLn "  --- the language layer, in full ---"
  sfails <- SSuite.suiteRun
  putStrLn "  --- end of the language layer ---"
  let sCheck = Check "the-language-suite-passes"
                     ("the language layer's own " ++ show (SSuite.suiteCheckCount corpus)
                       ++ " checks, over " ++ show (length SSuite.suiteAlgorithms)
                       ++ " algorithms")
                     (sfails == 0)
      results = checks ++ mcx ++ [floats, dirty, sCheck]
  mapM_ report results
  let bad = [ c | c <- results, not (chOK c) ]
  putStrLn ""
  putStrLn ("  " ++ show (length results - length bad) ++ " / "
            ++ show (length results) ++ " statements hold")
  putStrLn ("  the language layer: " ++ show (SSuite.suiteCheckCount corpus)
            ++ " checks in " ++ show (length (SSuite.suiteGroups corpus))
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
-- arithmetic cannot quietly change a verdict. The comment beside an entry
-- says why.
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

-- | The statements of the paper that this suite decides, in ten groups.
checks :: [Check]
checks =
  typingStatements ++ denotationStatements ++ verdictStatements
  ++ bundlingStatements ++ liftedProgramStatements ++ boundaryStatements
  ++ premiseStatements ++ nestedWitnessStatements ++ liftedSplitStatements ++ squareRootStatements

-- The scalar field, and typing: the catalogue types, the scope premise.
typingStatements :: [Check]
typingStatements =
  [ Check "the-scalar-field-is-a-field"
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
  ]

-- The denotation: an isometry, the machine's matrix, a latent factor, and the criterion by its routes.
denotationStatements :: [Check]
denotationStatements =
  [ Check "typing-forces-the-core-map-to-be-an-isometry"
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
  ]

-- Verdicts: the expected ones, the two directions of the criterion, the shape, and what a client sees.
verdictStatements :: [Check]
verdictStatements =
  [ Check "the-verdicts-are-the-expected-ones"
      "every catalogue program receives the verdict the paper claims for it"
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
  ]

-- Bundling many temporaries into one.
bundlingStatements :: [Check]
bundlingStatements =
  [ Check "bundling-preserves-the-denotation"
      "many temporaries compile to one of dimension prod d_i, with the same map"
      (all bundlePreservesDenotation [bellPair, wideVisible, nestedThree])

  , Check "joint-safety-is-strictly-coarser-than-per-wire-safety"
      "the Bell pair is jointly safe while neither wire is safe on its own"
      (jointSafe bellPair == Right True
       && everyWireSafe bellPair == Right False)
  ]

-- Programs with a lift: one text, two verdicts; the classical core; the residual table.
liftedProgramStatements :: [Check]
liftedProgramStatements =
  [ Check "one-text-can-have-two-verdicts"
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
  ]

-- The boundary, the two engines, and the exhaustive table.
boundaryStatements :: [Check]
boundaryStatements =
  [ Check "a-scratch-bit-is-never-underdetermined"
      "no permutation of V x {0,1} splits; the trit of the boundary section does"
      (all twoLevelsNeverSplit [2, 3, 4] && threeLevelsCanSplit)

  , Check "the-two-engines-agree"
      "theory engine (build K, take a rank) = language engine (probe, compare lines)"
      (null bridgeDisagreements)

  , Check "the-residual-table-is-exhaustive-and-agrees-with-its-criterion"
      "every measurement record has a table entry, and every entry matches the criterion"
      (and [ a && b | (_, a, b) <- residualAgreesWithItsCriterion ])
  ]

-- Premises the typing rules refuse: binders, dimensions, ragged gates, dropped wires.
premiseStatements :: [Check]
premiseStatements =
  [ Check "gate-output-binders-must-be-distinct"
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
  ]

-- Nested witnesses: the drop order, the trichotomy, and a phase that supplies a root.
nestedWitnessStatements :: [Check]
nestedWitnessStatements =
  [ Check "the-drop-order-lemma-holds-where-it-could-fail"
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
  ]

-- A joint gate after a lift splits a qubit, and the summed channel does not decide.
liftedSplitStatements :: [Check]
liftedSplitStatements =
  [ Check "a-scratch-qubit-splits-once-a-joint-gate-follows-the-lift"
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
  ]

-- Rays, reflections and square roots: when a joint witness exists and when each wire has one.
squareRootStatements :: [Check]
squareRootStatements =
  [ Check "carrying-a-unit-vector-is-necessary-not-sufficient"
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

nestedAlloc :: Program
nestedAlloc = Program "two allocations, one inside the other" "v" 2
  (New "t" 2 0 (New "s" 2 0 (Drop "s" (Drop "t" (Ret "v")))))

flatAlloc :: Program
flatAlloc = Program "one allocation" "v" 2 (New "t" 2 0 (Drop "t" (Ret "v")))

-- The borrowed dirty ancilla, through the surface language

-- | The C3X row of the table of algorithms, run end to end through the
-- concrete syntax, not a hand-built term: the four-Toffoli three-controlled
-- X on one borrowed ancilla (programs/mcx-dirty.s). The loan must come back
-- reclaimed with B = I, the text with one extra flip on the loan with B = X,
-- and the text with the fourth Toffoli deleted must be refused. The wanted
-- result is 'Nothing' for an expected refusal, 'Just (Left line)' for a
-- temporary's expected parked line, 'Just (Right b)' for a loan's expected
-- reclaiming gate B.
mcxChecks :: IO [Check]
mcxChecks = mapM one
  [ ( "the-borrowed-loan-returns-via-a-fixed-gate"
    , "programs/mcx-dirty.s"
    , "the drop is admitted and the loan is reclaimed with B = I"
    , Just (Right [[1, 0], [0, 1]]) )
  , ( "the-borrowed-loan-verdict-does-not-depend-on-an-extra-flip"
    , "programs/mcx-dirty-x.s"
    , "the same text with one extra X on the loan is admitted, reclaimed with B = X"
    , Just (Right [[0, 1], [1, 0]]) )
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
          Just (Left ln) -> SRun.trVerdict row == SC.Safe
                             && SRun.trLine row == Just (ln :: [Cyclo])
          Just (Right b) -> SRun.trVerdict row == SC.Safe
                             && SRun.trCert row == Just (b :: [[Cyclo]])
          Nothing        -> SRun.trVerdict row == SC.Unsafe
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
  files0  <- concat <$> mapM haskellFilesIn dirs
  -- The OpenQASM 3 emitter and its test are exempt. The emitter is the module
  -- Drop/Lang/Compile/Emit.hs alone: the layout, the safety decision and the
  -- reuse decision (Compile/Layout.hs, Safety.hs, Reuse.hs) and the entry
  -- Compile.hs are scanned like every other module, because the verdict and
  -- the certificate it emits on are computed exactly by Drop.Lang.Machine and
  -- Drop.Lang.State; the emitter only PRINTS an angle (U(theta,phi,lambda),
  -- p(theta)) as a decimal when it is not a multiple of pi/8, which OpenQASM
  -- requires. Nothing it prints feeds a verdict. An exemption that names no
  -- file the walk found is stale, and fails the check.
  let files   = [ f | f <- files0, not (any (`isSuffixOf` f) emitterFiles) ]
      absent  = [ e | e <- emitterFiles, not (any (e `isSuffixOf`) files0) ]
  srcs    <- mapM readFile files
  let code    = unlines [ l | s <- srcs, l <- lines s, not (isComment l) ]
      missing = [ d | d <- sourceDirs, d `notElem` dirs ]
      found   = [ n | n <- inexactTypeNames, n `isInfixOf` code ]
  pure (Check "no-floating-point-anywhere"
              ("no inexact numeric type occurs in any expression in "
               ++ show (length files) ++ " of the package's "
               ++ show (length files0) ++ " source files (the OpenQASM emitter "
               ++ "and its test print decimal angles, and are exempt)"
               ++ (if null missing then "" else "  [MISSING: " ++ show missing ++ "]")
               ++ (if null found then "" else "  [FOUND: " ++ show found ++ "]")
               ++ (if null absent then "" else "  [EXEMPT BUT ABSENT: " ++ show absent ++ "]"))
              (null missing && not (null files) && null found && null absent))
  where
    isComment l = case dropWhile (== ' ') l of
      '-' : '-' : _ -> True
      _             -> False

sourceDirs :: [FilePath]
sourceDirs = ["src", "app", "test"]

emitterFiles :: [FilePath]
emitterFiles = ["Drop/Lang/Compile/Emit.hs", "CompileSpec.hs"]

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
               else pure [ p | ".hs" `isSuffixOf` p ]

-- Every dirty ancilla arrives on a unit state

-- | Every @new ... \@ psi@ must write a unit vector: @||psi|| = 1@ is the
-- printed rule. A non-unit state carries the wrong weight, and can pick a
-- ray with no unit representative in the scalar tower. A loan
-- (a header @loan@) has no state to check by construction: it declares none.
-- The scan is over the directory, so a program added later is covered.
loanUnitCheck :: IO Check
loanUnitCheck = do
  there <- doesDirectoryExist "programs"
  if not there
    then pure (Check "every-declared-state-is-a-unit-vector"
                     "programs/ not reachable from the working directory"
                     False)
    else do
      names <- listDirectory "programs"
      let ss = [ "programs/" ++ n | n <- names, ".s" `isSuffixOf` n ]
      srcs <- mapM readFile ss
      let bad = [ f ++ ": " ++ x ++ " at norm^2 " ++ show (norm2S psi)
                | (f, src) <- zip ss srcs
                , Right (_, prog) <- [parseProgram src]
                , S.NewState x _ psi <- prog
                , norm2S psi /= 1 ]
          unparsed = [ f | (f, src) <- zip ss srcs
                         , Left _ <- [parseProgram src] ]
      pure (Check "every-declared-state-is-a-unit-vector"
                  ("none of the " ++ show (length ss)
                   ++ " shipped programs writes a non-unit state by hand"
                   ++ (if null bad then "" else "  [" ++ show bad ++ "]")
                   ++ (if null unparsed then "" else "  [UNPARSED: "
                        ++ show unparsed ++ "]"))
                  (null bad && null unparsed && not (null ss)))

-- | Does this rejection name the premise it is about?  Checking only that a
-- program is refused is too weak: @collidingOutputs@ is also refused for an
-- incidental reason (its body mentions a name the Drop removed), so a bare
-- @isLeft@ passes without the premise existing at all.
failsWith :: Show e => Either e a -> String -> Bool
failsWith (Left e) s = s `isInfixOf` show e
failsWith (Right _) _ = False

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

-- | The drop verdict as a boolean.  'Drop.Theory.Lifted.admissible' is local to that
-- module, and the trace checks need the profile as a bit vector.
isSafeV :: Verdict -> Bool
isSafeV (Safe _) = True
isSafeV _        = False

-- | Every denotation the suite knows: the catalogue, and the selected denotation
-- of every lifted example along every measurement record.  Zero maps (unreachable
-- traces) are included on purpose: both tests must call them safe.
coreMapsEverywhere :: [(Int, Int, Mat)]
coreMapsEverywhere =
  [ (tpTmpDim tp, tpVisDim tp, coreMap tp) | (_, tp) <- typedCatalogue ]
  ++ [ (ltTmpDim tp, ltVisDim tp, coreMapAt tp tr)
     | p <- liftedExamples, Right tp <- [checkLProgram p]
     , tr <- allTraces (ltDepth tp) ]

-- | The lifted examples of "Drop.Theory.Lifted", every one the paper discusses.
liftedExamples :: [LProgram]
liftedExamples =
  [ liftedWitness, liftedWitnessNoRead, classicalCoreNaiveEncoding
  , qubitSplitAfterJointGate, sameChannelSafe, sameChannelUnsafe ]

-- | The orthogonal projector @g g^dagger / ||g||^2@ onto the line of @g@.
rayProjector :: Vec -> Mat
rayProjector g = [ [ kdiv (kmul a (kconj b)) n | b <- g ] | a <- g ]
  where n = vnorm2 g

-- | The Choi matrix of a lifted program's summed channel: the branch
-- channels added up, what a continuation that cannot see the measurement
-- record observes.
sumChoiOf :: LTypedProgram -> Mat
sumChoiOf tp = foldr1 (zipWith (zipWith kadd))  -- impossible: allTraces gives at least one trace
  [ choiMatrix (ltTmpDim tp) (ltVisDim tp) (coreMapAt tp tr)
  | tr <- allTraces (ltDepth tp) ]
