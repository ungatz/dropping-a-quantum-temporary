-- TypedSpec.hs: checks for the typed surface language -- Drop.Lang.Typed,
-- Drop.Lang.Check, Drop.Lang.Machine, Drop.Lang.Elab -- in its own test-suite
-- stanza, so it can be run alone.
--
-- Sections:
--   (a) every programs/*.s corpus program, converted to the typed syntax
--       via Drop.Lang.Elab.flatToProgram, typechecks;
--   (b) the three shapes a naive semantics gets stuck on run to a value;
--   (c) a random stuck-state search: >= 2000 small well-typed core terms,
--       each checked for progress, preservation and the termination
--       measure;
--   (d) machine = denotation: every corpus program, and the (c) terms,
--       agree between Drop.Lang.Machine and Drop.Lang.Elab + Drop.Lang.Interp;
--   (e) the desugaring lemma, on a handful of hand-built surface terms;
--   (n) Step-New's second side condition: the machine refuses a name that
--       is bound later in the term, which would clone a register;
--   (o) the type-safety theorem's termination bound: the number of
--       statements along the longest branch, an `if` counting as one;
--   (p) the hidden-register invariant: along every run of every corpus program, the
--       term's context is the allocated registers minus the dropped ones;
--   (q) the desugaring lemma on the corpus: expanding a block changes no state at
--       any site, hence no verdict;
--   (g) the site definition adversarially: loans, tuple blocks, unreachable records;
--   (j) the site definition's clause (4) at a block of several registers;
--   (l) the loan discipline: every loan dropped exactly once, never
--       returned (Drop.Lang.Check.loanDiscipline).
--
-- No external test framework and no 'random' package (offline build): a
-- tiny deterministic linear congruential generator supplies the ">= 2000
-- random terms" of (c), so a failing run is exactly reproducible by its
-- printed seed.

module Main (main) where

import Control.Monad (forM, unless)
import Data.IORef
import Data.List (isInfixOf, nub, (\\))
import System.Exit (exitFailure)

import Drop.Lang.Cyclo (Cyclo)
import Drop.Lang.Check
import Drop.Lang.Elab
import Drop.Lang.Gates
import Drop.Lang.Machine
import Drop.Lang.QState
import Drop.Lang.Ring (Conj (..))
import Drop.Lang.Syntax (VisSpec, Prog, Sel (..), Cmd (..), Guard (..))
import Drop.Lang.Parser (SFile (..), parseProgram, renderProgram, sfVis)
import Drop.Lang.Typed
import qualified Data.Map.Strict as Map
import qualified Drop.Lang.Interp as I
import qualified Drop.Lang.Report.Run as RR
import Drop.Lang.Report.Run (runText, showSite)
import qualified Drop.Lang.Checks.Parser as TP

-- A tiny counting/assertion harness -----------------------------------

data Counters = Counters { cPass :: IORef Int, cFail :: IORef Int }

newCounters :: IO Counters
newCounters = Counters <$> newIORef 0 <*> newIORef 0

check1 :: Counters -> String -> Bool -> IO ()
check1 c name ok = do
  if ok then modifyIORef' (cPass c) (+ 1) else modifyIORef' (cFail c) (+ 1)
  putStrLn ((if ok then "  PASS  " else "  FAIL  ") ++ name)

report :: Counters -> IO ()
report c = do
  p <- readIORef (cPass c)
  f <- readIORef (cFail c)
  putStrLn ""
  putStrLn (show (p + f) ++ " checks, " ++ show p ++ " passed, " ++ show f ++ " failed")
  unless (f == 0) exitFailure

-- (a) The corpus, typechecked -------------------------------------------

corpusFiles :: [FilePath]
corpusFiles = TP.progFiles

parsedCorpus :: [(FilePath, VisSpec, Prog Cyclo)]
parsedCorpus =
  [ (f, vis, prog) | f <- corpusFiles, Right (vis, prog) <- [TP.parsed f] ]

-- | Every corpus file, as the parser reads it whole: header, body and the
-- value its `return` names.
parsedFiles :: [(FilePath, SFile)]
parsedFiles = [ (f, sf) | f <- corpusFiles, Right sf <- [TP.parsedFile f] ]

corpusChecks :: Counters -> IO ()
corpusChecks c = do
  putStrLn ("(a) corpus typechecking: " ++ show (length parsedCorpus) ++ " of "
            ++ show (length corpusFiles) ++ " files parsed")
  check1 c "every listed corpus file parsed" (length parsedCorpus == length corpusFiles)
  n <- newIORef (0 :: Int)
  mapM_ (\(f, sf) -> do
            let prog' = flatToProgramR (sfVis sf) (sfReturn sf) (sfBody sf)
                want  = sfResult sf
            case check prog' of
              Right ty | ty == want -> modifyIORef' n (+ 1)
              Right ty -> putStrLn ("    " ++ f ++ ": typechecked at " ++ show ty
                                     ++ ", expected " ++ show want)
              Left e -> putStrLn ("    " ++ f ++ ": " ++ showTypeError e)
        ) parsedFiles
  ok <- readIORef n
  check1 c ("all " ++ show (length parsedFiles)
            ++ " corpus programs typecheck at the result type their header declares")
         (ok == length parsedFiles)

-- (d) machine = denotation, on the corpus --------------------------------

-- | Every basis assignment of a program's loans, jointly (the empty
-- environment for a loan-free program): a spread of concrete inputs to
-- check the two engines against, not a re-derivation of Drop.Lang.Interp's
-- own (exhaustive) loan criterion, which decides safety separately.
loanEnvCombos :: [(String, Int)] -> [[(String, StateV Cyclo)]]
loanEnvCombos [] = [[]]
loanEnvCombos ((x, d) : rest) =
  [ (x, ket [d] [k]) : env | k <- [0 .. d - 1], env <- loanEnvCombos rest ]

corpusMachineAgrees :: Counters -> IO ()
corpusMachineAgrees c = machineAgreesOn c "the corpus"
  "Drop.Lang.Machine agrees exactly with Drop.Lang.Elab + Drop.Lang.Interp on every corpus leaf"
  parsedCorpus

-- | The same comparison over any list of parsed programs: run each on every
-- (visible probe, loan arrival) pair and require Drop.Lang.Machine's leaf and
-- Drop.Lang.Elab + Drop.Lang.Interp's to be the same state on the same wires.
machineAgreesOn :: Counters -> String -> String
                -> [(FilePath, VisSpec, Prog Cyclo)] -> IO ()
machineAgreesOn c label claim corpus = do
  leavesTotal <- newIORef (0 :: Int)
  okRef <- newIORef (0 :: Int)
  totalRef <- newIORef (0 :: Int)
  mapM_ (\(_f, vis, prog) -> do
            let core   = fst (splitProg vis prog)
                probes = I.probesFor vis :: [(String, StateV Cyclo)]
                loans  = [ (x, d) | Loan x d <- prog ]
                loanEnvs = loanEnvCombos loans
            mapM_ (\(_, inp) ->
              mapM_ (\loanEnv -> do
                      let cfg0   = initConfigL vis inp loanEnv core
                          leaves = run cfg0
                      modifyIORef' leavesTotal (+ length leaves)
                      mapM_ (\leaf -> do
                                modifyIORef' totalRef (+ 1)
                                let sel = [ if b == 1 then SIn else SOut | (_, b) <- cfgBits leaf ]
                                    mch = I.runStmts (I.initMachL vis inp loanEnv) prog sel Nothing
                                    agree = cfgAmp leaf == I.mAmp mch
                                            && cfgNames leaf == I.mNames mch
                                            && cfgDims leaf == I.mDims mch
                                if agree then modifyIORef' okRef (+ 1)
                                  else putStrLn ("    disagreement on " ++ _f ++ " selection " ++ show sel)
                            ) leaves
                    ) loanEnvs
              ) probes
        ) corpus
  total <- readIORef totalRef
  ok <- readIORef okRef
  lt <- readIORef leavesTotal
  putStrLn ("(d) machine = denotation on " ++ label ++ ": " ++ show lt
            ++ " (probe, leaf) pairs checked")
  check1 c claim (total > 0 && ok == total)
  where
    splitProg vis prog = (flatToCoreForTest vis prog, ())

-- The program as the expanded term the statics and the machine read: the
-- surface form Drop.Lang.Elab builds (which carries an 'SBlock' wherever the
-- file has a non-tail `if`), with its blocks discharged by the sequencing
-- operator.
flatToCoreForTest :: Num a => VisSpec -> Prog a -> Term a
flatToCoreForTest vis prog = toTerm (progTerm (flatToProgram vis prog))

-- | The same program as the SURFACE term, blocks and all.
flatToSurfaceForTest :: Num a => VisSpec -> Prog a -> Surface a
flatToSurfaceForTest vis prog = progTerm (flatToProgram vis prog)

-- (b) The three shapes a naive semantics gets stuck on ---------------------

runsToValue :: (Eq a, Num a) => [(Name, Int)] -> StateV a -> Term a -> Bool
runsToValue vis inp core = not (null leaves) && all isFinal leaves
  where leaves = run (initConfig vis inp core)

stuckShapeChecks :: Counters -> IO ()
stuckShapeChecks c = do
  putStrLn "(b) the three shapes a naive semantics gets stuck on"
  -- (i) a bare operation in tail position via sugar: `H x; return x`.
  let core1 :: Term Cyclo
      core1 = Do (StGate gHC (VVar "x")) (Return (VVar "x"))
      vis1  = [("x", 2)]
  check1 c "(i) bare operation in tail position typechecks"
         (checkTerm core1 (ctxFromList vis1) == Right (TReg 2))
  check1 c "(i) bare operation in tail position runs to a value"
         (runsToValue vis1 [1, 0] core1)

  -- (ii) a lift inside a block: `q = { b = lift[{0}] x; return x }; return q`,
  -- expanded via seqTerm/toTerm. 'b' is a classical parameter, not a
  -- register, so the block returns the register alone and the bit is read off
  -- cfgBits after running, exactly as the corpus does.
  let inner' :: Surface Cyclo
      inner' = SDo (StLift "b" [0] "x") (SReturn (VVar "x"))
      outer :: Surface Cyclo
      outer = SBlock (VVar "q") inner' (SReturn (VVar "q"))
      core2 = toTerm outer
      vis2  = [("x", 2)]
  check1 c "(ii) a lift inside a block typechecks"
         (checkSurface outer (ctxFromList vis2) == Right (TReg 2))
  check1 c "(ii) a lift inside a block runs to a value on every leaf"
         (runsToValue vis2 [1, 0] core2)

  -- (iii) a tail if: `if p then return v1 else return v2`, p bound by a
  -- preceding lift.
  let core3 :: Term Cyclo
      core3 = Do (StLift "p" [0] "x") (If (BParam "p") (Return (VVar "x")) (Return (VVar "x")))
      vis3  = [("x", 2)]
  check1 c "(iii) a tail if typechecks"
         (checkTerm core3 (ctxFromList vis3) == Right (TReg 2))
  check1 c "(iii) a tail if runs to a value on every leaf"
         (runsToValue vis3 [1, 0] core3)

-- A tiny deterministic PRNG ----------------------------------------------

newtype Seed = Seed Integer

seed0 :: Int -> Seed
seed0 n = Seed (fromIntegral n * 2654435761 + 12345)

next :: Seed -> (Integer, Seed)
next (Seed s) = let s' = (s * 6364136223846793005 + 1442695040888963407) `mod` (2 ^ (61 :: Int))
                in (s', Seed s')

rollN :: Seed -> Int -> (Int, Seed)
rollN s n = let (v, s') = next s in (fromInteger (v `mod` fromIntegral n), s')

-- | @rollBool s chance@ is true with probability @chance / 10000@ -- an
-- exact integer rate, so this generator (like every other numeric type in
-- the package) uses no inexact scalar.
rollBool :: Seed -> Int -> (Bool, Seed)
rollBool s chance = let (v, s') = rollN s 10000 in (v < chance, s')

pick :: Seed -> [a] -> (a, Seed)
pick s xs = let (i, s') = rollN s (length xs) in (xs !! i, s')

-- Random well-typed core-term generation ---------------------------------

data GenSt = GenSt
  { gLive   :: [(Name, Int)]  -- live wires, in allocation order
  , gFresh  :: Int
  , gOps    :: Int            -- lets + lifts so far
  , gLifts  :: Int
  , gIfUsed :: Bool
  , gSite   :: Int
  , gBits   :: [Name]         -- lift-bound parameters in scope
  }

gen0 :: GenSt
gen0 = GenSt [("w0", 2)] 1 0 0 False 0 []

dim2Pool, dim3Pool :: [Matrix Cyclo]
dim2Pool = [gX, gZ, gHC, gS, gT]
dim3Pool = [permGate 3 (\j -> (j + 1) `mod` 3), permGate 3 (\j -> (j + 2) `mod` 3)]

twoWirePool :: [Matrix Cyclo]
twoWirePool = [gCX, gSwap]

maxOps, maxWires, maxLifts :: Int
maxOps = 6
maxWires = 4
maxLifts = 2

-- | Generate a random well-typed core term against 'gen0''s starting
-- context (a single dimension-2 wire "w0"), returning the term and the
-- final seed. The term is well typed by construction: every action reads
-- only currently-live wires and updates 'gLive' exactly as the statics
-- would, so a 'checkCore' pass is a genuine independent check, not a
-- tautology (the check re-derives typing from scratch off the term text).
genRandomCore :: Seed -> GenSt -> (Term Cyclo, Seed)
genRandomCore seed gs
  | gOps gs >= maxOps = (finish, seed)
  | otherwise =
      let (stop, seed1) = rollBool seed (if gOps gs < 1 then 0 else 1500)
      in if stop then (finish, seed1) else
         let (choice, seed2) = pick seed1 (actionsAvailable gs)
         in case choice of
              ANew  -> genNew seed2
              AGate -> genGate seed2
              ADrop -> genDrop seed2
              ALift -> genLift seed2
              AIf   -> genIf seed2
  where
    finish = Return (tupleValT (map fst (gLive gs)))

    genNew s =
      let (d, s1) = pick s [2, 3]
          x = "g" ++ show (gFresh gs)
          gs' = gs { gLive = gLive gs ++ [(x, d)], gFresh = gFresh gs + 1, gOps = gOps gs + 1 }
          (rest, s2) = genRandomCore s1 gs'
      in (Do (StNew x d (ket [d] [0])) rest, s2)

    genGate s =
      let live2 = [ x | (x, d) <- gLive gs, d == 2 ]
          (useTwo, s0) = if length live2 >= 2 then rollBool s 3000 else (False, s)
      in if useTwo
           then let (pr, s1) = pickPair s0 live2
                    (g, s2)  = pick s1 twoWirePool
                    v = VPair (VVar (fst pr)) (VVar (snd pr))
                    (rest, s3) = genRandomCore s2 (gs { gOps = gOps gs + 1 })
                in (Do (StGate g v) rest, s3)
           else let ((x, d), s1) = pick s0 (gLive gs)
                    (g, s2) = pick s1 (if d == 2 then dim2Pool else dim3Pool)
                    (rest, s3) = genRandomCore s2 (gs { gOps = gOps gs + 1 })
                in (Do (StGate g (VVar x)) rest, s3)
      where
        pickPair s' xs =
          let (a, sA) = pick s' xs
              others  = filter (/= a) xs
              (b, sB) = pick sA others
          in ((a, b), sB)

    genDrop s =
      let ((x, _), s1) = pick s (gLive gs)
          gs' = gs { gLive = filter ((/= x) . fst) (gLive gs), gOps = gOps gs + 1, gSite = gSite gs + 1 }
          (rest, s2) = genRandomCore s1 gs'
      in (Do (StDrop (gSite gs) (VVar x)) rest, s2)

    genLift s =
      let ((x, d), s1) = pick s (gLive gs)
          (blkK, s2) = rollN s1 (d - 1)
          block = [0 .. blkK]
          p = "p" ++ show (gFresh gs)
          gs' = gs { gFresh = gFresh gs + 1
                   , gOps = gOps gs + 1, gLifts = gLifts gs + 1, gBits = gBits gs ++ [p] }
          (rest, s3) = genRandomCore s2 gs'
      in (Do (StLift p block x) rest, s3)

    genIf s =
      let (p, s1) = pick s (gBits gs)
          -- Branches bind nothing (as the shipped .s corpus requires),
          -- so both continue from the same live context; each may apply
          -- its own short run of gates before rejoining.
          (m1, s2) = genBranchGates s1 (2 :: Int) (gLive gs)
          (m2, s3) = genBranchGates s2 (2 :: Int) (gLive gs)
          gs' = gs { gOps = gOps gs + 1, gIfUsed = True }
          (cont, s4) = genRandomCore s3 gs'
          patch branch = spliceTerm branch cont
      in (If (BParam p) (patch m1) (patch m2), s4)

    genBranchGates s 0 _ = (Return VUnit, s)  -- placeholder root; spliced away by 'spliceTerm'
    genBranchGates s k live =
      let (doIt, s1) = rollBool s 6000
      in if not doIt || null live then (Return VUnit, s1)
         else
           let ((x, d), s2) = pick s1 live
               (g, s3) = pick s2 (if d == 2 then dim2Pool else dim3Pool)
               (rest, s4) = genBranchGates s3 (k - 1) live
           in (Do (StGate g (VVar x)) rest, s4)

    -- Replace the placeholder 'Return VUnit' leaf of a branch skeleton by
    -- the shared continuation.
    spliceTerm (Return VUnit) k = k
    spliceTerm (Do st m) k      = Do st (spliceTerm m k)
    spliceTerm other _          = other  -- (a lift or an `if` never occurs here)

data Action = ANew | AGate | ADrop | ALift | AIf

actionsAvailable :: GenSt -> [Action]
actionsAvailable gs =
  concat
    [ [ ANew  | length (gLive gs) < maxWires ]
    , [ AGate | not (null (gLive gs)) ]
    , [ ADrop | not (null (gLive gs)) ]
    , [ ALift | not (null (gLive gs)) && gLifts gs < maxLifts ]
    , [ AIf   | not (gIfUsed gs) && not (null (gBits gs)) ]
    ]

tupleValT :: [Name] -> Value
tupleValT []       = VUnit
tupleValT [x]      = VVar x
tupleValT (x : xs) = VPair (VVar x) (tupleValT xs)

-- (c) The random stuck-state search --------------------------------------

randomTermCount :: Int
randomTermCount = 2000

-- | Structural, machine-independent step count along the path an
-- environment picks -- an independent re-derivation of 'run''s own count,
-- used as the termination-measure cross-check.
staticSteps :: Term a -> (Name -> Bool) -> Int
staticSteps (Return _) _      = 0
staticSteps (Do _ m) env      = 1 + staticSteps m env
staticSteps (If e m1 m2) env  = 1 + staticSteps (if evalB env e then m1 else m2) env

runCounting :: Num a => Config a -> [(Config a, Int)]
runCounting cfg0 = go cfg0 0
  where
    go cfg n = case step cfg of
      []    -> [(cfg, n)]
      succs -> concatMap (\c -> go c (n + 1)) succs

randomStuckSearch :: Counters -> IO ()
randomStuckSearch c = do
  putStrLn ("(c) random stuck-state search: " ++ show randomTermCount ++ " terms")
  progressRef <- newIORef (0 :: Int)
  preserveRef <- newIORef (0 :: Int)
  termRef     <- newIORef (0 :: Int)
  leafRef     <- newIORef (0 :: Int)
  covRef      <- newIORef ([] :: [String])
  _ <- forM [0 .. randomTermCount - 1] $ \i -> do
    let (core, _seed) = genRandomCore (seed0 i) gen0
        vis0 = [("w0", 2)]
    -- Well-typedness by construction, re-checked from scratch:
    case checkTerm core (ctxFromList vis0) of
      Left e -> putStrLn ("    term " ++ show i ++ ": FAILED TO TYPECHECK: " ++ showTypeError e)
      Right ty0 -> do
        modifyIORef' covRef (nubAppend (constructorsOf core))
        let inp = replicate 2 1  -- the (1,1) unnormalized probe: nonzero on every branch it can reach
            cfg0 = initConfig vis0 inp core
            leafPairs = runCounting cfg0
        modifyIORef' leafRef (+ length leafPairs)
        -- Progress: every leaf is final (run terminated via 'step' = []
        -- rather than a pattern-match failure, i.e. this line was reached).
        okProg <- pure (all (isFinal . fst) leafPairs && not (null leafPairs))
        if okProg then modifyIORef' progressRef (+ 1)
          else putStrLn ("    term " ++ show i ++ ": progress failed")
        -- Preservation: after every step on every path, the reconstructed
        -- (term, live context) re-typechecks at the same type.
        let preserved = and
              [ case checkTerm (cfgTerm leaf) (liveCtxOf leaf) of
                  Right ty -> ty == ty0
                  Left _   -> False
              | (leaf, _) <- leafPairs ]
        if preserved then modifyIORef' preserveRef (+ 1)
          else putStrLn ("    term " ++ show i ++ ": preservation failed")
        -- Termination measure: run's own step count equals the
        -- independent structural count on the same leaf's bit record.
        let termOk = and
              [ n == staticSteps core (\p -> lookup p (cfgBits leaf) == Just 1)
              | (leaf, n) <- leafPairs ]
        if termOk then modifyIORef' termRef (+ 1)
          else putStrLn ("    term " ++ show i ++ ": termination-measure mismatch")
  progressN <- readIORef progressRef
  preserveN <- readIORef preserveRef
  termN <- readIORef termRef
  leaves <- readIORef leafRef
  cov <- readIORef covRef
  putStrLn ("    " ++ show leaves ++ " leaves reached across " ++ show randomTermCount ++ " terms")
  putStrLn ("    constructs exercised: " ++ show cov)
  check1 c "progress: every random term's every leaf is a final configuration"
         (progressN == randomTermCount)
  check1 c "preservation: every intermediate configuration re-typechecks at the same type"
         (preserveN == randomTermCount)
  check1 c "termination measure: step count equals the independent structural count"
         (termN == randomTermCount)
  where
    nubAppend new old = old ++ filter (`notElem` old) new
    -- The configuration's own context: the allocated registers the term
    -- still names, which the hidden-register invariant says are the allocated ones
    -- minus the dropped ones. (p) below checks that reading against the
    -- drops the run actually crossed.
    liveCtxOf leaf = ctxFromList (ctxOf leaf)

constructorsOf :: Term a -> [String]
constructorsOf (Return _)  = ["return"]
constructorsOf (Do st m)   = stmtName st : constructorsOf m
  where stmtName (StGate _ _) = "gate"; stmtName (StNew {})  = "new"
        stmtName (StLoan {})  = "loan"; stmtName (StDrop _ _) = "drop"
        stmtName (StLift {})  = "lift"
constructorsOf (If _ m1 m2) = "if" : (constructorsOf m1 ++ constructorsOf m2)

-- (d, continued) machine = denotation on a sample of the random terms ----

randomMachineAgrees :: Counters -> IO ()
randomMachineAgrees c = do
  let sampleCount = 200
      terms = [ fst (genRandomCore (seed0 (i + 900000)) gen0) | i <- [0 .. sampleCount - 1] ]
      vis0 = [("w0", 2)]
  agreeRef <- newIORef (0 :: Int)
  totalRef <- newIORef (0 :: Int)
  -- Every term of this language elaborates: the shapes that would force a
  -- refusal -- a gate or a lift that renames -- do not exist, since neither binds.
  mapM_ (\core -> case elabE core of
            Left e -> putStrLn ("    a random term did not elaborate: " ++ e)
            Right prog -> do
              let inp = [1, 0] :: StateV Cyclo
                  cfg0 = initConfig vis0 inp core
                  leaves = run cfg0
              mapM_ (\leaf -> do
                        modifyIORef' totalRef (+ 1)
                        let sel = [ if b == 1 then SIn else SOut | (_, b) <- cfgBits leaf ]
                            mch = denote vis0 prog sel inp
                        if cfgAmp leaf == I.mAmp mch
                          then modifyIORef' agreeRef (+ 1)
                          else putStrLn "    disagreement on a random term"
                    ) leaves
        ) terms
  total <- readIORef totalRef
  agree <- readIORef agreeRef
  putStrLn ("(d, continued) machine = denotation on " ++ show total
            ++ " random-term leaves (of " ++ show sampleCount
            ++ " sampled terms, every one of which elaborates by Lemma E)")
  check1 c "Drop.Lang.Machine agrees with Drop.Lang.Elab + Drop.Lang.Interp on every sampled random term"
         (total > 0 && agree == total)

-- (e) The desugaring lemma, hand-built ------------------------------------

desugaringChecks :: Counters -> IO ()
desugaringChecks c = do
  putStrLn "(e) the desugaring lemma"
  -- M1 = `H x; return x`, ybar = x, M2 = `X x; return x`.
  -- checkSurface (SBlock ...) should agree with typing M1 alone into
  -- Omega_ybar, then M2 under (rest, Omega_ybar); and the denotation should
  -- compose: running M1 to its value and feeding it to M2 equals running the
  -- expanded whole.
  let m1 :: Surface Cyclo
      m1 = SDo (StGate gHC (VVar "x")) (SReturn (VVar "x"))
      m2 :: Surface Cyclo
      m2 = SDo (StGate gX (VVar "x")) (SReturn (VVar "x"))
      whole = SBlock (VVar "x") m1 m2
      vis = [("x", 2)]
      core = toTerm whole
  tM1 <- pure (checkSurface m1 (ctxFromList vis))
  tWhole <- pure (checkSurface whole (ctxFromList vis))
  check1 c "type of M1 (+)_ybar M2 matches checking M1 then M2 in sequence"
         (tM1 == Right (TReg 2) && tWhole == Right (TReg 2))
  let inp = [1, 0] :: StateV Cyclo
      leavesWhole = run (initConfig vis inp core)
      leavesM1 = run (initConfig vis inp (toTerm m1))
      composed = concatMap (\l1 -> run (initConfig vis (cfgAmp l1) (toTerm m2))) leavesM1
  check1 c "denotation composes: running the expanded whole equals running M1 then M2"
         (map cfgAmp leavesWhole == map cfgAmp composed)

  -- A second instance nesting a lift, to exercise the statement case of
  -- (+)_ybar on a binder (the operator has ONE clause for all statements,
  -- and this is the one that binds).
  let m1L :: Surface Cyclo
      m1L = SDo (StLift "b" [0] "x") (SReturn (VVar "x"))
      m2L :: Surface Cyclo
      m2L = SDo (StGate gZ (VVar "x")) (SReturn (VVar "x"))
      wholeL = SBlock (VVar "x") m1L m2L
      coreL = toTerm wholeL
  check1 c "the lift case of (+)_ybar typechecks the same way"
         (checkSurface wholeL (ctxFromList vis) == Right (TReg 2))
  let leavesWholeL = run (initConfig vis inp coreL)
      leavesM1L = run (initConfig vis inp (toTerm m1L))
      composedL = concatMap (\l1 -> run (initConfig vis (cfgAmp l1) (toTerm m2L))) leavesM1L
  check1 c "denotation composes through a nested lift"
         (map cfgAmp leavesWholeL == map cfgAmp composedL)

-- (f) trace preservation: Sigma_o E_o^dagger E_o = I -----------------------
--
-- Every corpus program, read as a computation from its visible input alone
-- (the temporary's allocation state is fixed, not part of the input), is a
-- family of exact linear maps E_o, one per measurement record o -- the
-- 'cfgBits' label of a Drop.Lang.Machine leaf. A gate step is unitary, an
-- allocation step tensors with a fixed unit vector (an isometry), and a
-- lift step splits into two orthogonal projections that sum to the
-- identity; composed, this is exactly the statement that the whole family
-- is trace preserving: Sigma_o E_o^dagger E_o = I on the visible input's
-- own space, entry by entry, in the exact field (Data.List.nub, sum, conj
-- and (*) only -- no floating point, so this needs no tolerance and the
-- no-floating-point-anywhere gate in this file stays green).
--
-- The columns of E_o come from running the machine on every computational
-- basis vector of the visible input ('Drop.Lang.Interp.probesFor', taking its
-- first 'dv' probes and dropping the trailing all-ones "sum" probe, which
-- exists for a different check and is not a basis vector); the row space is
-- whatever the leaf's own joint register happens to be, which the identity
-- being checked never has to name.

-- | Every (basis index, record, leaf amplitude) triple reached from every
-- visible computational basis vector. A loan is pinned at the given
-- (arbitrary) fixed state for this check: the identity being checked is
-- about the family indexed by the visible input alone, for whatever the
-- rest of the joint register is tensored in at, fixed or not -- gate and
-- lift steps do not care, and a loan tensors in exactly like a temporary
-- does once its value is fixed for the run. It is not itself the loan's own
-- theorem (Drop.Lang.Interp's loan criterion, which quantifies over every
-- loan value); see that module's "Loans" section.
recordLeaves :: (Eq a, Num a)
             => VisSpec -> [(String, StateV a)] -> Term a
             -> [(Int, [(Name, Int)], StateV a)]
recordLeaves vis loanEnv core =
  [ (j, cfgBits leaf, cfgAmp leaf)
  | (j, inp) <- zip [0 :: Int ..] basisInputs
  , leaf <- run (initConfigL vis inp loanEnv core)
  ]
  where
    dv          = product (map snd vis)
    basisInputs = take dv (map snd (I.probesFor vis))

-- | Sigma_o E_o^dagger E_o, as a (dv x dv) matrix over the visible input's
-- computational basis: entry (j,k) is the sum, over every record reached,
-- of the exact inner product between the j-th and k-th basis vectors' leaf
-- amplitudes at that record. 'error' fires only if two basis inputs
-- disagree on which records are reachable, which would itself mean the
-- machine is not a well-formed family of leaves over a shared input space.
traceMatrix :: (Eq a, Num a, Conj a) => VisSpec -> [(String, StateV a)] -> Term a -> Matrix a
traceMatrix vis loanEnv core =
  [ [ sum [ innerProd (lookupAmp j r) (lookupAmp k r) | r <- records ]
    | k <- [0 .. dv - 1] ]
  | j <- [0 .. dv - 1] ]
  where
    dv      = product (map snd vis)
    leaves  = recordLeaves vis loanEnv core
    records = nub [ r | (_, r, _) <- leaves ]
    byKey   = Map.fromList [ ((j, r), amp) | (j, r, amp) <- leaves ]
    lookupAmp j r = Map.findWithDefault
      (error "traceMatrix: a record reached from one basis input is missing from another")
      (j, r) byKey
    innerProd u v = sum (zipWith (\a b -> conj a * b) u v)

identityMatrix :: Num a => Int -> Matrix a
identityMatrix n = [ [ if i == j then 1 else 0 | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]

traceIsPreserved :: (Eq a, Num a, Conj a) => VisSpec -> [(String, StateV a)] -> Term a -> Bool
traceIsPreserved vis loanEnv core =
  traceMatrix vis loanEnv core == identityMatrix (product (map snd vis))

traceChecks :: Counters -> IO ()
traceChecks c = do
  let results = [ (f, traceIsPreserved vis loanEnv0 (flatToCoreForTest vis prog))
                | (f, vis, prog) <- parsedCorpus
                , let loanEnv0 = [ (x, ket [d] [0]) | Loan x d <- prog ] ]
      bad     = [ f | (f, ok) <- results, not ok ]
  putStrLn ("(f) trace preservation: Sigma_o E_o^dagger E_o = I on the visible "
            ++ "input, exactly, checked on all " ++ show (length results)
            ++ " corpus programs")
  mapM_ (\f -> putStrLn ("    " ++ f ++ ": FAILS the completeness identity")) bad
  check1 c "every corpus program's Drop.Lang.Machine leaves satisfy Sigma_o E_o^dagger E_o = I exactly"
         (not (null results) && null bad)

-- Main --------------------------------------------------------------------

main :: IO ()
main = do
  c <- newCounters
  corpusChecks c
  stuckShapeChecks c
  randomStuckSearch c
  corpusMachineAgrees c
  randomMachineAgrees c
  desugaringChecks c
  traceChecks c
  siteChecks c
  stepNewCaptureChecks c
  terminationBoundChecks c
  hiddenRegisterChecks c
  corpusBlockChecks c
  report c

-- (g) the site and the criterion, adversarially -------------------------
--
-- The site definition read back as tests. Each case is a program text, run through
-- Drop.Lang.Report.Run.runText (parse, well-formedness, then the criterion at every
-- site on every record), and compared against the verdict the site definition dictates.
-- Cases (a1)-(a3), (b1)-(b3) and (d1)-(d2) exercise a loan the engine must
-- assign a probe state to; (a1) is the shape that separates the block-factor
-- test of clause 4 from a per-input product test.

-- | The verdict word at each site of a program text, in program order:
-- @Right [(site, [verdict per record])]@, or @Left@ the rejection message.
siteVerdicts :: String -> Either String [(String, [String])]
siteVerdicts src = case runText src of
  Left e  -> Left e
  Right r -> Right [ (showSite (RR.srSite s), map (show . RR.trVerdict) (RR.srRows s))
                   | s <- RR.rpSites r ]

-- | The whole report as the command line prints it, so a check can name
-- the certificate ("B = { 1, 0 ; 0, 1 }") in the paper's own spelling.
reportText :: String -> String
reportText src = either ("REJECTED: " ++) RR.renderReport (runText src)

siteChecks :: Counters -> IO ()
siteChecks c = do
  putStrLn "(g) the site and the criterion, adversarially (the site definition)"
  let eq name src want = check1 c name (siteVerdicts src == Right want)
      rejects name src frag = check1 c name $ case siteVerdicts src of
        Left e -> frag `isInfixOf` e
        _      -> False

  -- (a) a loan block that is a product at every input but not B (x) W.
  -- Swap moves the loan's whole state into a temporary and leaves |0> on
  -- the loan: the block IS constant, so a per-input product test (or the
  -- fixed-ray test a temporary gets) accepts; no fixed B on the loan alone
  -- reproduces the joint action, so clause 4 refuses.
  eq "(a1) a loan swapped into a temporary is UNSAFE, though its block is constant"
     progSwapLoan [("a", ["Unsafe"])]
  eq "(a2) the same program with the swap undone is SAFE"
     progSwapLoanBack [("a", ["Safe"])]
  eq "(a3) a loan hit with CZ against the input is UNSAFE (every basis label fixed)"
     progCZLoan [("t", ["Unsafe"])]

  -- (b) two live loans, dropped separately and as a tuple.
  eq "(b1) two loans, each restored, are SAFE at their own sites"
     progTwoLoans [("a", ["Safe"]), ("b", ["Safe"])]
  check1 c "(b1') each of the two loans is reclaimed with B = I"
    (count "B = { 1, 0 ; 0, 1 }" (reportText progTwoLoans) == 2)
  eq "(b2) two loans, only the first restored: SAFE then UNSAFE"
     progTwoLoansHalf [("a", ["Safe"]), ("b", ["Unsafe"])]
  -- (b3) HAND: the CCX pair cancels and b is never touched, so the site map
  -- is |i>_a |j>_b |q1> |q>  |->  itself. The site definition's clause (4) with
  -- H_loan = H_a (x) H_b reads off B = I_4 and W = I. Expect SAFE.
  eq "(b3) two loans dropped as ONE tuple: SAFE, block factor I_4"
     progTwoLoansTuple [("(a, b)", ["Safe"])]
  check1 c "(b3') the tuple block's certificate is the 4x4 identity"
    (count "B = { 1, 0, 0, 0 ; 0, 1, 0, 0 ; 0, 0, 1, 0 ; 0, 0, 0, 1 }"
           (reportText progTwoLoansTuple) == 1)

  -- (c) a loan measured by a lift, then dropped: its would-be block factor
  -- is a projector, which is not an isometry, so no record is safe.
  eq "(c1) a lifted loan is UNSAFE on every record"
     progLiftedLoan [("a", ["Unsafe", "Unsafe"])]

  -- (d) a block mixing a loan with a temporary: the site definition's clause (4) covers it with
  -- a RECTANGULAR block factor, and the engine decides it there.
  -- HAND: t is allocated at |0> and nothing is done, so the site map is
  -- |b>_a |v>_x  |->  |b>_a |0>_t (x) |v>_x. Writing H_block = H_a (x) H_t
  -- in the order the drop names them, B|0> = |00> = e_0 and B|1> = |10> =
  -- e_2, i.e. B = I (x) |0>, the 4x2 isometry with B^dagger B = I_2.
  -- Expect SAFE, B = { 1, 0 ; 0, 0 ; 0, 1 ; 0, 0 }.
  eq "(d1) a loan and a temporary in one tuple drop: SAFE, B rectangular"
     progLoanAndTemp [("(a, t)", ["Safe"])]
  check1 c "(d2) that block's factor is I (x) |0> : H_a -> H_a (x) H_t"
    (count "B = { 1, 0 ; 0, 0 ; 0, 1 ; 0, 0 }" (reportText progLoanAndTemp) == 1)

  -- (e) an input register is not special: dropping it is the copy-input
  -- leak whenever the program has read it, and d = 1 is not a register.
  eq "(e1) dropping an input the program has copied is UNSAFE"
     progDropInput [("x", ["Unsafe"])]
  rejects "(e2) a register of dimension 1 is not a register"
     "prog p (x : [1]) : 1 { drop x; return () }" "at least 2"

  -- (f) a closed program (no inputs): the Bell pair is safe jointly and
  -- unsafe wire by wire -- the composite-temporary proposition on a one-point domain.
  eq "(f1) a closed program's Bell pair is SAFE dropped as one block"
     progBellJoint [("(a, b)", ["Safe"])]
  eq "(f2) the same pair is UNSAFE at each wire dropped alone"
     progBellApart [("a", ["Unsafe"]), ("b", ["Unsafe"])]

  -- (g) an unreachable record: the site map is 0, and the site definition's clause (3) makes it
  -- safe by convention; the engine reports it, and does not divide by zero.
  eq "(g1) a lift whose block has probability 0 gives Unreachable, not a crash"
     progUnreachable [("t", ["Unreachable", "Safe"])]

  -- (h) a temporary in a program that also holds a loan. The site map's
  -- domain is the whole input context, loans included, so the loan is
  -- varied too; seeding it at |0> instead calls (h1) safe.
  eq "(h1) a temporary that copies a live loan is UNSAFE"
     progTempReadsLoan [("t", ["Unsafe"])]
  eq "(h2) the same temporary with the copy undone is SAFE"
     progTempReadsLoanBack [("t", ["Safe"])]
  eq "(h3) a temporary beside an untouched loan is SAFE, and the loan is too"
     progTempBesideLoan [("t", ["Safe"]), ("a", ["Safe"])]

  -- (i) an `if` branch binds nothing, and a block is spliced, so a block
  -- that shadows an outer name is a repeated binder. Both are refused with
  -- a line number rather than mis-run.
  rejects "(i1) an allocation inside an if branch is refused by name"
     progAllocInBranch "'new' inside an if branch"
  rejects "(i2) a block that shadows its own binder is refused by name"
     "prog p (x : [2]) : [2] * [2] { y = { new y : [2] @ |0>; return y }; return (x, y) }"
     "already exists"

  blockChecks c
  loanDisciplineChecks c

  -- (m) the elaboration agrees with the machine here too: the corpus has no
  -- tuple drop and no program with two loans, so (d) never sees either.
  machineAgreesOn c "the programs of (g)"
    "(m) Drop.Lang.Machine agrees with Drop.Lang.Elab + Drop.Lang.Interp on loans and tuple drops"
    adversarialParsed

  -- alpha-equivalence, the relation the desugaring lemma is stated up to:
  -- two cores differing only in a bound name are identified by 'alphaEq'
  -- and distinguished by '(==)', and a free name is still compared by name.
  check1 c "(g') alphaEq identifies a renamed binder, (==) does not"
    (alphaEq coreBindsT coreBindsU && coreBindsT /= coreBindsU)
  check1 c "(g'') alphaEq still distinguishes a different free name"
    (not (alphaEq (Return (VVar "x") :: Term Cyclo) (Return (VVar "y"))))

  -- (n) parse . render . parse is the identity on every program above, as
  -- Drop.Lang.Checks.Parser already checks it on every corpus file.
  check1 c ("(n) parse . render is the identity on all "
            ++ show (length adversarialPrograms) ++ " programs of (g)")
    (all renderRoundTrips adversarialPrograms)

  -- (o) `drop ()`, a site with no register under the site definition's clause (1): the parser admits
  -- it, it renders back as `drop ();`, its block has dimension one, and the
  -- site is safe with the unit scalar as certificate on every input.
  eq "(o) drop (): a site with no register, SAFE"
     progDropUnit [("()", ["Safe"])]
  check1 c "(o') drop () renders back as itself"
    (renderRoundTrips progDropUnit)

-- (j) the site definition's clause (4) at a block of SEVERAL registers ---------------
--
-- Clause (4) writes the input space as [[Omega]] = H_loan (x) [[Omega']],
-- where H_loan is the tensor product of the spaces of the loans IN THE
-- BLOCK, and asks that the site map factor as sigma_s = B (x) W with
-- B : H_loan -> H_block an isometry (rectangular when the block holds
-- temporaries beside its loans) and W : [[Omega']] -> H_rest linear.
--
-- Each case below carries the hand computation that fixes its expected
-- verdict and, where it is safe, its block factor B. H_block is indexed in
-- the order the `drop` names its registers, so for a block (a, t) the basis
-- index of |i>_a |j>_t is 2i + j.
blockChecks :: Counters -> IO ()
blockChecks c = do
  putStrLn "(j) the site definition's clause (4) at a block of several registers"
  let eq name src want = check1 c name (siteVerdicts src == Right want)
      cert name src b  = check1 c name (count ("B = " ++ b) (reportText src) == 1)

  -- (j-i) HAND: two loans, nothing done. sigma_s : |i>_a |j>_b (x) |v>_x
  -- |-> |i>_a |j>_b (x) |v>_x, so B = I_4 on H_a (x) H_b and W = I. SAFE.
  eq "(j-i) two loans, block (a,b), nothing done: SAFE"
     progBlockTwoLoansId [("(a, b)", ["Safe"])]
  cert "(j-i') its block factor is I_4"
     progBlockTwoLoansId "{ 1, 0, 0, 0 ; 0, 1, 0, 0 ; 0, 0, 1, 0 ; 0, 0, 0, 1 }"

  -- (j-ii) HAND: Swap a b then drop (a,b). sigma_s : |i>_a |j>_b |-> |j>_a
  -- |i>_b, which is B = SWAP on H_a (x) H_b, an isometry that is not the
  -- identity; SWAP^dagger = SWAP is the reclaiming gate. SAFE.
  eq "(j-ii) two loans, Swap then drop (a,b): SAFE"
     progBlockTwoLoansSwap [("(a, b)", ["Safe"])]
  cert "(j-ii') its block factor is SWAP, an isometry that is not I"
     progBlockTwoLoansSwap "{ 1, 0, 0, 0 ; 0, 0, 1, 0 ; 0, 1, 0, 0 ; 0, 0, 0, 1 }"

  -- (j-iii) HAND: loan a, temporary t at |0>, nothing done. sigma_s :
  -- |b>_a |-> |b>_a |0>_t, i.e. B = I (x) |0> : H_a -> H_a (x) H_t, the 4x2
  -- isometry with columns e_0 and e_2 and B^dagger B = I_2. SAFE.
  eq "(j-iii) loan a + temporary t at |0>, block (a,t): SAFE"
     progBlockLoanTemp [("(a, t)", ["Safe"])]
  cert "(j-iii') its block factor is the 4x2 isometry I (x) |0>"
     progBlockLoanTemp "{ 1, 0 ; 0, 0 ; 0, 1 ; 0, 0 }"

  -- (j-iv) HAND: `CX a t` with a the control and t at |0> copies the loan's
  -- basis label: |b>_a |0>_t |-> |b>_a |b>_t. So B|b> = |bb>, columns e_0
  -- and e_3, B^dagger B = I_2 -- an isometry (not a cloner: it is linear
  -- and copies the BASIS, which is what an isometry may do). SAFE.
  eq "(j-iv) loan a + temporary t, CX a t, block (a,t): SAFE"
     progBlockLoanCopy [("(a, t)", ["Safe"])]
  cert "(j-iv') its block factor is |b> |-> |b>|b>"
     progBlockLoanCopy "{ 1, 0 ; 0, 0 ; 0, 0 ; 0, 1 }"

  -- (j-v) HAND: `H t; CX t a` with t the control. Start |b>_a |0>_t;
  -- H t gives |b>(|0>+|1>)/sqrt2; CX t a leaves |b>|0> and sends |b>|1> to
  -- |b+1>|1>, so the joint map is
  --     |b>_a  |->  (|b>|0> + |b+1>|1>)/sqrt2
  -- which IS B|b> for B = (1/sqrt2) * { 1,0 ; 0,1 ; 0,1 ; 1,0 } (columns
  -- (|00>+|11>)/sqrt2 and (|01>+|10>)/sqrt2, orthonormal), so B^dagger B =
  -- I_2. a IS entangled with t, and the block holds both, so clause (4)
  -- still factors. SAFE.
  eq "(j-v) loan a + temporary t, H t; CX t a, block (a,t): SAFE"
     progBlockLoanEntangled [("(a, t)", ["Safe"])]
  -- 1/2*z8 + -1/2*z8^3 is 1/sqrt2: zeta_8 - zeta_8^3 = sqrt2.
  cert "(j-v') its block factor is (1/sqrt2) (|00>,|11>) , (|01>,|10>)"
     progBlockLoanEntangled
     "{ 1/2*z8+-1/2*z8^3, 0 ; 0, 1/2*z8+-1/2*z8^3 ; 0, 1/2*z8+-1/2*z8^3 ; \
     \1/2*z8+-1/2*z8^3, 0 }"

  -- (j-vi) HAND: t is allocated at |0>, so `CX t a` (t the control) acts as
  -- the identity; `H a` then sends |b>_a |0>_t to (H|b>)_a |0>_t. So
  -- B = H (x) |0>, the 4x2 isometry with columns (|00>+|10>)/sqrt2 and
  -- (|00>-|10>)/sqrt2; B^dagger B = I_2. SAFE.
  eq "(j-vi) loan a + temporary t at |0>, CX t a; H a, block (a,t): SAFE"
     progBlockLoanHadamard [("(a, t)", ["Safe"])]
  cert "(j-vi') its block factor is H (x) |0>"
     progBlockLoanHadamard
     "{ 1/2*z8+-1/2*z8^3, 1/2*z8+-1/2*z8^3 ; 0, 0 ; 1/2*z8+-1/2*z8^3, \
     \-1/2*z8+1/2*z8^3 ; 0, 0 }"

  -- (j-vii) HAND: `CX a x` writes the loan's basis label into the VISIBLE
  -- register, which the block does not hold. The site map's entry is
  --   [a_out = a_in] [x_out = x_in + a_in] [t_out = 0],
  -- and no B (x) W reproduces it: W would have to depend on a_in. Neither
  -- block sees a fixed B, so both are UNSAFE -- the block cannot be widened
  -- out of the obligation by taking the temporary in with it.
  eq "(j-vii) loan entangled with the visible input, block (a) alone: UNSAFE"
     progBlockLoanLeaksAlone [("a", ["Unsafe"])]
  eq "(j-vii') the same leak with block (a,t): still UNSAFE"
     progBlockLoanLeaksPair [("(a, t)", ["Unsafe"])]

  -- (j-viii) the fixture the compile suite and s_bench.py both gate on: CZ
  -- against the input keeps every basis label of t fixed, and the
  -- block/rest reshape does not factor at all. UNSAFE, as before.
  eq "(j-viii) cz-loan.s (test/fixtures) is still UNSAFE"
     czLoanFixture [("t", ["Unsafe"])]

progBlockTwoLoansId, progBlockTwoLoansSwap, progBlockLoanTemp,
  progBlockLoanCopy, progBlockLoanEntangled, progBlockLoanHadamard, progDropUnit,
  progBlockLoanLeaksAlone, progBlockLoanLeaksPair, czLoanFixture :: String

progBlockTwoLoansId =
  "prog block_two_loans_id (x : [2], loan a : [2], loan b : [2]) : [2] {\n\
  \    drop (a, b);\n\
  \    return x\n\
  \}"

progBlockTwoLoansSwap =
  "prog block_two_loans_swap (x : [2], loan a : [2], loan b : [2]) : [2] {\n\
  \    Swap a b;\n\
  \    drop (a, b);\n\
  \    return x\n\
  \}"

progBlockLoanTemp =
  "prog block_loan_temp (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"

progBlockLoanCopy =
  "prog block_loan_copy (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a t;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"

progDropUnit =
  "prog drop_unit (x : [2]) : [2] {\n\
  \    drop ();\n\
  \    return x\n\
  \}"

progBlockLoanEntangled =
  "prog block_loan_entangled (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    H t;\n\
  \    CX t a;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"

progBlockLoanHadamard =
  "prog block_loan_hadamard (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX t a;\n\
  \    H a;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"

progBlockLoanLeaksAlone =
  "prog block_loan_leaks_alone (x : [2], loan a : [2]) : [2] * [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a x;\n\
  \    drop a;\n\
  \    return (x, t)\n\
  \}"

progBlockLoanLeaksPair =
  "prog block_loan_leaks_pair (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a x;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"

-- | test/fixtures/cz-loan.s, inline: the (j-viii) check must not depend on
-- the file being readable from whatever directory the suite is run in.
czLoanFixture =
  "prog cz_loan (r : [2], loan t : [2]) : [2] {\n\
  \    diag t r (1, 1, 1, -1);\n\
  \    drop t;\n\
  \    return r\n\
  \}"

-- (l) the loan discipline ---------------------------------------------
--
-- The language definition: a loan is an input the caller lends and gets back at a
-- drop, so it is DROPPED, not returned, and every loan input is dropped
-- EXACTLY ONCE -- on every execution path, so a loan dropped in one branch
-- of an `if` and not the other is an error. Drop.Lang.Check.loanDiscipline
-- states this; it is NOT a typing rule (a loan types exactly like a `new`),
-- and 'checkProgram' calls it after 'check'.
--
-- Two of the four cases below go through 'loanDiscipline' directly rather
-- than through 'checkProgram'/'typecheckText': an undropped loan is also a
-- 'LeftoverWires' for the statics (and, in a .s file, the parser's own
-- line-numbered "neither dropped nor returned"), so calling checkProgram
-- would test which net is hit first, not the rule.
loanDisciplineChecks :: Counters -> IO ()
loanDisciplineChecks c = do
  putStrLn "(l) the loan discipline (the language definition, Drop.Lang.Check.loanDiscipline)"

  check1 c "(l1) mcx-dirty.s -- a loan dropped exactly once -- typechecks"
    (case TP.fileSrc "programs/mcx-dirty.s" of
       Left _    -> False
       Right src -> case RR.typecheckText src of
         Right ok -> ok == "mcx3 : [2] * [2] * [2] * [2]"
         Left _   -> False)

  check1 c "(l2) `return (x, a)` with `a` a loan is rejected, naming the rule"
    (case RR.typecheckText srcReturnsLoan of
       Left e  -> "a loan is dropped, not returned (the language definition)" `isInfixOf` e
       Right _ -> False)
  check1 c "(l2') and the rejection carries the line the `return` stands on"
    (case RR.typecheckText srcReturnsLoan of
       Left e  -> "line 3: " `isInfixOf` e
       Right _ -> False)

  -- (l3) a loan neither dropped nor returned. In a .s file the parser's own
  -- rule fires first, with a line; the discipline is what states it about
  -- the typed program, whoever built it.
  check1 c "(l3) a loan never dropped and never returned is rejected by the discipline"
    (loanDiscipline progLoanUndropped == Left (LoanNotDroppedOnce "a"))
  check1 c "(l3') the same text as a .s file is rejected with a line too"
    (case RR.typecheckText srcUndroppedLoan of
       Left e  -> "line 4: " `isInfixOf` e && "'a'" `isInfixOf` e
       Right _ -> False)

  -- (l4) dropped on one branch of an `if` only: not "exactly once on every
  -- path". Dropping on both branches is the same drop site copied by the
  -- desugaring, and is accepted -- by the discipline and by the statics.
  check1 c "(l4) a loan dropped in only one branch of an if is rejected"
    (loanDiscipline progLoanOneBranch == Left (LoanNotDroppedOnce "a"))
  check1 c "(l4') the same loan dropped on BOTH branches is accepted"
    (loanDiscipline progLoanBothBranches == Right ())
  check1 c "(l4'') and that program typechecks whole, discipline included"
    (checkProgram progLoanBothBranches == Right (TReg 2))

srcReturnsLoan, srcUndroppedLoan :: String
srcReturnsLoan =
  "prog ret_loan (x : [2], loan a : [2]) : [2] * [2] {\n\
  \    H x;\n\
  \    return (x, a)\n\
  \}"
srcUndroppedLoan =
  "prog undropped (x : [2], loan a : [2]) : [2] {\n\
  \    H x;\n\
  \    return x\n\
  \}"

-- | A loan bound and then neither dropped nor returned.
progLoanUndropped :: Program Cyclo
progLoanUndropped = Program [("x", 2)]
  (SDo (StLoan "a" 2) (SReturn (VVar "x")))

-- | A loan dropped on one branch of an `if` only, and on both.
progLoanOneBranch, progLoanBothBranches :: Program Cyclo
progLoanOneBranch = Program [("x", 2)]
  (SDo (StLoan "a" 2)
    (SDo (StLift "m" [0] "x")
      (SIf (BParam "m")
        (SDo (StDrop 0 (VVar "a")) (SReturn (VVar "x")))
        (SReturn (VVar "x")))))
progLoanBothBranches = Program [("x", 2)]
  (SDo (StLoan "a" 2)
    (SDo (StLift "m" [0] "x")
      (SIf (BParam "m")
        (SDo (StDrop 0 (VVar "a")) (SReturn (VVar "x")))
        (SDo (StDrop 0 (VVar "a")) (SReturn (VVar "x"))))))

-- | How many times a needle occurs in a haystack.
count :: String -> String -> Int
count needle hay = length [ () | t <- tails' hay, needle `isPrefixOf'` t ]
  where
    tails' []       = [[]]
    tails' l@(_:xs) = l : tails' xs
    isPrefixOf' p t = take (length p) t == p

renderRoundTrips :: String -> Bool
renderRoundTrips src = case parseProgram src of
  Left _ -> False
  Right (vis, prog) -> parseProgram (renderProgram vis prog) == Right (vis, prog)

-- | One core term and its alpha-variant: the same allocation bound to a
-- different name.
coreBindsT, coreBindsU :: Term Cyclo
coreBindsT = Do (StNew "t" 2 (ket [2] [0])) (Return (VVar "t"))
coreBindsU = Do (StNew "u" 2 (ket [2] [0])) (Return (VVar "u"))

-- | The (g) programs, parsed, for the machine/denotation comparison.
adversarialParsed :: [(FilePath, VisSpec, Prog Cyclo)]
adversarialParsed =
  [ ("(g) program " ++ show i, vis, prog)
  | (i, src) <- zip [(1 :: Int) ..] adversarialPrograms
  , Right (vis, prog) <- [parseProgram src] ]

adversarialPrograms :: [String]
adversarialPrograms =
  [ progSwapLoan, progSwapLoanBack, progCZLoan, progTwoLoans, progTwoLoansHalf
  , progTwoLoansTuple, progLiftedLoan, progLoanAndTemp, progDropInput
  , progBellJoint, progBellApart, progUnreachable, progTempReadsLoan
  , progTempReadsLoanBack, progTempBesideLoan
  , progBlockTwoLoansId, progBlockTwoLoansSwap, progBlockLoanTemp
  , progBlockLoanCopy, progBlockLoanEntangled, progBlockLoanHadamard
  , progBlockLoanLeaksAlone, progBlockLoanLeaksPair ]

progSwapLoan, progSwapLoanBack, progCZLoan, progTwoLoans, progTwoLoansHalf,
  progTwoLoansTuple, progLiftedLoan, progLoanAndTemp, progDropInput,
  progBellJoint, progBellApart, progUnreachable, progTempReadsLoan,
  progTempReadsLoanBack, progTempBesideLoan, progAllocInBranch :: String

progSwapLoan =
  "prog swap_loan (x : [2], loan a : [2]) : [2] * [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    Swap a t;\n\
  \    drop a;\n\
  \    return (x, t)\n\
  \}"

progSwapLoanBack =
  "prog swap_back (x : [2], loan a : [2]) : [2] * [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    Swap a t;\n\
  \    Swap a t;\n\
  \    drop a;\n\
  \    return (x, t)\n\
  \}"

progCZLoan =
  "prog cz_loan (r : [2], loan t : [2]) : [2] {\n\
  \    diag t r (1, 1, 1, -1);\n\
  \    drop t;\n\
  \    return r\n\
  \}"

progTwoLoans =
  "prog two_loans (q1 : [2], q : [2], loan a : [2], loan b : [2]) : [2] * [2] {\n\
  \    CCX q1 a q;  CCX q1 a q;\n\
  \    CCX q1 b q;  CCX q1 b q;\n\
  \    drop a;  drop b;\n\
  \    return (q1, q)\n\
  \}"

progTwoLoansHalf =
  "prog two_loans_half (q1 : [2], q : [2], loan a : [2], loan b : [2]) : [2] * [2] {\n\
  \    CCX q1 a q;  CCX q1 a q;\n\
  \    CCX q1 b q;\n\
  \    drop a;  drop b;\n\
  \    return (q1, q)\n\
  \}"

progTwoLoansTuple =
  "prog two_loans_tuple (q1 : [2], q : [2], loan a : [2], loan b : [2]) : [2] * [2] {\n\
  \    CCX q1 a q;  CCX q1 a q;\n\
  \    drop (a, b);\n\
  \    return (q1, q)\n\
  \}"

progLiftedLoan =
  "prog lifted_loan (x : [2], loan a : [2]) : [2] {\n\
  \    m = lift[{0}] a;\n\
  \    drop a;\n\
  \    return x\n\
  \}"

progLoanAndTemp =
  "prog loan_and_temp (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"

progDropInput =
  "prog drop_input (x : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX x t;\n\
  \    drop x;\n\
  \    return t\n\
  \}"

progBellJoint =
  "prog bell_joint () : 1 {\n\
  \    new a : [2] @ |0>;\n\
  \    new b : [2] @ |0>;\n\
  \    H a;  CX a b;\n\
  \    drop (a, b);\n\
  \    return ()\n\
  \}"

progBellApart =
  "prog bell_apart () : 1 {\n\
  \    new a : [2] @ |0>;\n\
  \    new b : [2] @ |0>;\n\
  \    H a;  CX a b;\n\
  \    drop a;  drop b;\n\
  \    return ()\n\
  \}"

progUnreachable =
  "prog unreachable (x : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    m = lift[{1}] t;\n\
  \    drop t;\n\
  \    return x\n\
  \}"

progTempReadsLoan =
  "prog temp_reads_loan (x : [2], loan a : [2]) : [2] * [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a t;\n\
  \    drop t;\n\
  \    return (x, a)\n\
  \}"

progTempReadsLoanBack =
  "prog temp_reads_loan_back (x : [2], loan a : [2]) : [2] * [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a t;  CX a t;\n\
  \    drop t;\n\
  \    return (x, a)\n\
  \}"

progTempBesideLoan =
  "prog temp_beside_loan (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    H t;  H t;\n\
  \    drop t;\n\
  \    drop a;\n\
  \    return x\n\
  \}"

progAllocInBranch =
  "prog alloc_in_branch (x : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    H t;\n\
  \    m = lift[{0}] t;\n\
  \    if m { new u : [2] @ |0>; drop u; } else { }\n\
  \    drop t;\n\
  \    return x\n\
  \}"


-- (n) Step-New's second side condition ------------------------------------
--
-- The machine figure's \textsc{Step-New} allocates a name w with w not in Delta AND
-- w NOT BOUND IN M. The second condition is the one that rules out capture:
-- the paper's own example is
--
--     new 5 : [2] @ |0>;  new 7 : [2] @ |0>;  return (5, 7)
--
-- where an allocator that took w = 7 at the FIRST allocation would continue
-- with M[7/5], whose `new 7` then rebinds a name already in Delta and whose
-- `return` names one register twice: the successor clones a register. The
-- machine here refuses that w ('stepNewAt' returns Nothing), and the witness
-- below shows what the refused successor would have been.

progFiveSeven :: Term Cyclo
progFiveSeven =
  Do (StNew "5" 2 (ket [2] [0]))
    (Do (StNew "7" 2 (ket [2] [0]))
      (Return (VPair (VVar "5") (VVar "7"))))

stepNewCaptureChecks :: Counters -> IO ()
stepNewCaptureChecks c = do
  putStrLn "(n) Step-New's capture side condition (the machine figure)"
  -- A CLOSED program, so its context is exactly what it allocates.
  let vis0 = [] :: [(Name, Int)]
      inp0 = [1] :: StateV Cyclo
      cfg0 = initConfig vis0 inp0 progFiveSeven
      cont = case progFiveSeven of Do _ m -> m; _ -> error "(n): not an allocation"

  check1 c "(n1) the program `new 5; new 7; return (5,7)` typechecks"
    (checkTerm progFiveSeven (ctxFromList vis0)
       == Right (TTensor (TReg 2) (TReg 2)))

  -- the second side condition: 7 is bound later in M, so the machine refuses it
  check1 c "(n2) Step-New refuses w = 7: it is bound in the continuation"
    (case stepNewAt "7" cfg0 of Nothing -> True; Just _ -> False)
  check1 c "(n2') and `7` really is bound in that continuation"
    ("7" `elem` boundIn cont)

  -- What the refused successor would have been: <Delta.7, sigma (x) psi ||
  -- M[7/5]>, whose own `new 7` then rebinds a name already in Delta. It is
  -- ill typed, which is the preservation failure the machine figure's caption names.
  check1 c "(n3) the successor Step-New refuses is ill typed: it clones a register"
    (checkTerm (renameTerm "5" "7" cont) (ctxFromList [("7", 2)])
       == Left (UsedTwice "7"))
  check1 c "(n3') and its `return` names one register twice"
    (freeTerm (renameTerm "5" "7" cont) == ["7"])

  -- the first side condition: a name already allocated
  let visX = [("x", 2)] :: [(Name, Int)]
      inpX = [1, 0] :: StateV Cyclo
      cfgX = initConfig visX inpX
               (Do (StNew "t" 2 (ket [2] [0])) (Return (VPair (VVar "x") (VVar "t")))
                  :: Term Cyclo)
  check1 c "(n4) Step-New refuses w = x: it is already in Delta"
    (case stepNewAt "x" cfgX of Nothing -> True; Just _ -> False)

  -- the name the program wrote is legal, and is the one the machine takes
  check1 c "(n5) Step-New accepts w = 5, the name the program wrote"
    (case stepNewAt "5" cfg0 of
       Just cfg -> cfgNames cfg == ["5"]
       Nothing  -> False)
  check1 c "(n5') and `step` takes exactly that name"
    (case step cfg0 of
       [cfg] -> cfgNames cfg == ["5"]
       _     -> False)

  -- the run ends with two DISTINCT registers, so nothing was cloned
  check1 c "(n6) the run allocates two distinct registers and ends at a value"
    (case run cfg0 of
       [leaf] -> cfgNames leaf == ["5", "7"] && isFinal leaf
       _      -> False)

  -- a term that DOES rebind the written name forces a fresh one, and the
  -- machine still runs it to a value with distinct registers.
  let shadowing :: Term Cyclo
      shadowing = Do (StNew "t" 2 (ket [2] [0]))
                    (Do (StDrop 0 (VVar "t"))
                      (Do (StNew "t" 2 (ket [2] [0]))
                        (Do (StDrop 1 (VVar "t")) (Return (VVar "x")))))
  check1 c "(n7) a term that rebinds `t` runs with two distinct registers"
    (case run (initConfig visX inpX shadowing) of
       [leaf] -> length (nub (cfgNames leaf)) == length (cfgNames leaf)
                 && length (cfgNames leaf) == 3 && isFinal leaf
       _      -> False)

-- (o) the termination bound, an `if` counting as one ----------------------
--
-- The type-safety theorem's termination bound: every run reaches a final configuration in at most
-- |M| steps, where |M| is the number of statements along the longest branch,
-- an `if` counting as ONE ('Drop.Lang.Typed.termSize').

-- | Every run's step count, one entry per leaf.
runLengths :: Num a => Config a -> [Int]
runLengths cfg0 = go cfg0 0
  where go cfg n = case step cfg of
          []    -> [n]
          succs -> concatMap (\c -> go c (n + 1)) succs

terminationBoundChecks :: Counters -> IO ()
terminationBoundChecks c = do
  putStrLn "(o) the termination bound |M|, an `if` counting as one"

  -- an `if` is ONE statement, not two: an empty `if` measures 1.
  check1 c "(o1) |if e {return ()} else {return ()}| = 1"
    (termSize (If (BParam "p") (Return VUnit) (Return VUnit) :: Term Cyclo) == 1)
  -- and the branches are measured by the LONGER of the two, not their sum
  check1 c "(o2) |M| takes the longest branch, not the sum"
    (termSize (If (BParam "p")
                 (Do (StGate gX (VVar "x")) (Return (VVar "x")))
                 (Return (VVar "x")) :: Term Cyclo) == 2)

  -- a lift then a branching `if`: |M| = 3, and the two runs take 3 and 2.
  let withIf :: Term Cyclo
      withIf = Do (StLift "p" [0] "x")
                 (If (BParam "p")
                    (Do (StGate gX (VVar "x")) (Return (VVar "x")))
                    (Return (VVar "x")))
      vis = [("x", 2)] :: [(Name, Int)]
      inp = [1, 1] :: StateV Cyclo
  check1 c "(o3) |lift; if p {X x; return x} else {return x}| = 3"
    (termSize withIf == 3)
  check1 c "(o3') its two runs take 3 and 2 steps, both within the bound"
    (runLengths (initConfig vis inp withIf) == [3, 2])

  -- every random term: every run is within its own bound
  let terms = [ fst (genRandomCore (seed0 i) gen0) | i <- [0 .. randomTermCount - 1] ]
      vis0 = [("w0", 2)] :: [(Name, Int)]
      inp0 = [1, 1] :: StateV Cyclo
      okRandom = and [ all (<= termSize t) (runLengths (initConfig vis0 inp0 t))
                     | t <- terms ]
      tight = or [ maximum (runLengths (initConfig vis0 inp0 t)) == termSize t
                 | t <- terms, hasIf t ]
  check1 c ("(o4) every run of all " ++ show randomTermCount
            ++ " random terms is within |M|") okRandom
  check1 c "(o4') and some random term with an `if` attains the bound" tight

  -- every corpus program: every run is within its own bound
  let corpusOk =
        [ (f, all (<= termSize core) (runLengths (initConfigL visC inpC loanEnv core)))
        | (f, visC, prog) <- parsedCorpus
        , let core = flatToCoreForTest visC prog
        , let loanEnv = [ (x, ket [d] [0]) | Loan x d <- prog ]
        , (_, inpC) <- I.probesFor visC :: [(String, StateV Cyclo)] ]
  check1 c ("(o5) every run of every corpus program is within |M| ("
            ++ show (length corpusOk) ++ " (program, probe) pairs)")
    (not (null corpusOk) && all snd corpusOk)

hasIf :: Term a -> Bool
hasIf (Return _)  = False
hasIf (Do _ m)    = hasIf m
hasIf (If _ _ _)  = True

-- (p) the hidden registers: allocated minus dropped ------------------------
--
-- The hidden-register invariant: along a run, the term's context is the allocated
-- registers MINUS the ones the run has dropped. There is no hidden set in
-- the configuration, so this is a claim relating two things that are both
-- read off it: 'ctxOf' (the allocated registers the term still names) and
-- the drops the path has crossed ('cfgSites').

-- | Every configuration visited, not only the leaves.
allConfigs :: (Eq a, Num a) => Config a -> [Config a]
allConfigs cfg = cfg : concatMap allConfigs (step cfg)

-- | The invariant at one configuration.
ctxIsAllocatedMinusDropped :: Config a -> Bool
ctxIsAllocatedMinusDropped cfg =
  map fst (ctxOf cfg) == (cfgNames cfg \\ dropped)
  && cfgHidden cfg == dropped'
  where
    dropped  = concatMap srHidden (cfgSites cfg)
    dropped' = [ x | x <- cfgNames cfg, x `elem` dropped ]

hiddenRegisterChecks :: Counters -> IO ()
hiddenRegisterChecks c = do
  putStrLn "(p) the hidden registers are the allocated ones the term no longer names"
  let cfgsOf (_, vis, prog) =
        [ cfg
        | (_, inp) <- I.probesFor vis :: [(String, StateV Cyclo)]
        , let loanEnv = [ (x, ket [d] [0]) | Loan x d <- prog ]
        , cfg <- allConfigs (initConfigL vis inp loanEnv (flatToCoreForTest vis prog)) ]
      perFile = [ (f, cfgsOf e) | e@(f, _, _) <- parsedCorpus ]
      bad = [ f | (f, cfgs) <- perFile, not (all ctxIsAllocatedMinusDropped cfgs) ]
      total = sum [ length cfgs | (_, cfgs) <- perFile ]
  mapM_ (\f -> putStrLn ("    " ++ f ++ ": the invariant fails somewhere on a run")) bad
  putStrLn ("    " ++ show total ++ " configurations visited across "
            ++ show (length perFile) ++ " corpus programs")
  check1 c "(p1) along every run of every corpus program, the context is the \
           \allocated registers minus the dropped ones"
    (total > 0 && null bad)
  -- the same on the random terms, where drops are generated freely
  let randomCfgs =
        [ cfg
        | i <- [0 .. 199 :: Int]
        , let t = fst (genRandomCore (seed0 i) gen0)
        , cfg <- allConfigs (initConfig [("w0", 2)] ([1, 1] :: StateV Cyclo) t) ]
  check1 c ("(p2) and at all " ++ show (length randomCfgs)
            ++ " configurations of 200 random terms")
    (not (null randomCfgs) && all ctxIsAllocatedMinusDropped randomCfgs)

-- (q) expanding a block changes no state at any site, hence no verdict -----
--
-- The desugaring lemma (2). Every corpus program with a non-tail `if` is read by
-- Drop.Lang.Elab as a BLOCK -- @(if e {M1} else {M2}) (+)_ybar M@ -- and the
-- statics and the machine see the expanded term, while Drop.Lang.Interp (the
-- engine that decides every verdict the paper prints) runs the UNEXPANDED
-- command list. So the two can be compared at the only place a verdict is
-- read: the state at a drop site.
--
-- The verdict at a site is a function of (the registers in tensor order,
-- their dimensions, the amplitude, the site's own registers) and of nothing
-- else -- 'Drop.Lang.Interp.probeResultL' takes exactly that -- so equal site
-- states are equal verdicts.

surfaceHasBlock :: Surface a -> Bool
surfaceHasBlock (SReturn _)     = False
surfaceHasBlock (SDo _ m)       = surfaceHasBlock m
surfaceHasBlock (SIf _ m1 m2)   = surfaceHasBlock m1 || surfaceHasBlock m2
surfaceHasBlock (SBlock _ _ _)  = True

-- | The expansion done the OTHER way: walking the flat command list and
-- copying the continuation into both branches by hand, with no sequencing
-- operator anywhere. An independent implementation, so that comparing it
-- with 'toTerm' tests the operator rather than restating it.
flatExpandDirect :: forall a. Num a => Value -> Prog a -> Term a
flatExpandDirect ret prog = fst (go 0 prog)
  where
    go :: Int -> Prog a -> (Term a, Int)
    go sid [] = (Return ret, sid)
    go sid (c : cs) = case c of
      New x d          -> wrap (StNew x d (ket [d] [0]))
      NewState x d psi -> wrap (StNew x d psi)
      Loan x d         -> wrap (StLoan x d)
      Gate g xs        -> wrap (StGate g (tupleValT xs))
      Lift p x blk     -> wrap (StLift p blk x)
      Drop xs          -> let (rest, sid') = go (sid + 1) cs
                          in (Do (StDrop sid (tupleValT xs)) rest, sid')
      IfBit g thn els  -> let (cont, sid') = go sid cs
                          in (If (gb g) (copyInto thn cont) (copyInto els cont), sid')
      where
        wrap st = let (rest, sid') = go sid cs in (Do st rest, sid')

    copyInto :: Prog a -> Term a -> Term a
    copyInto [] k = k
    copyInto (Gate g xs : rest) k = Do (StGate g (tupleValT xs)) (copyInto rest k)
    copyInto (IfBit g t e : rest) k =
      If (gb g) (copyInto t (copyInto rest k)) (copyInto e (copyInto rest k))
    copyInto (_ : _) _ = error "flatExpandDirect: an if-branch binds a wire"

    gb (GBit b)   = BLit b
    gb (GParam p) = BParam p
    gb (GNot e)   = BNot (gb e)
    gb (GAnd x y) = BAnd (gb x) (gb y)
    gb (GOr x y)  = BOr (gb x) (gb y)

-- | The value a corpus file's `return` names, as Drop.Lang.Elab computes it.
liveAtEnd :: VisSpec -> Prog a -> Value
liveAtEnd vis prog = tupleValT (map fst (foldl stepLive vis prog))
  where
    stepLive acc c = case c of
      New x d        -> acc ++ [(x, d)]
      NewState x d _ -> acc ++ [(x, d)]
      Loan x d       -> acc ++ [(x, d)]
      Drop xs        -> filter ((`notElem` xs) . fst) acc
      _              -> acc

corpusBlockChecks :: Counters -> IO ()
corpusBlockChecks c = do
  let withBlocks = [ e | e@(_, vis, prog) <- parsedCorpus
                       , surfaceHasBlock (flatToSurfaceForTest vis prog) ]
  putStrLn ("(q) expanding a block: " ++ show (length withBlocks)
            ++ " corpus programs use one -- "
            ++ unwords [ f | (f, _, _) <- withBlocks ])
  check1 c "(q0) at least one corpus program uses a block" (not (null withBlocks))

  -- (q1) the operator agrees with an independent hand expansion.
  let sameExpansion (_, vis, prog) =
        alphaEq (flatToCoreForTest vis prog) (flatExpandDirect (liveAtEnd vis prog) prog)
  check1 c "(q1) (+)_ybar agrees with copying the continuation into both \
           \branches by hand, on every corpus program that uses a block"
    (all sameExpansion withBlocks)

  -- (q2) the state at every site is the unexpanded engine's, so the verdict
  -- at every site on every record is unchanged.
  agreeRef <- newIORef (0 :: Int)
  totalRef <- newIORef (0 :: Int)
  mapM_ (\(f, vis, prog) -> do
          let core   = flatToCoreForTest vis prog
              loanEnv = [ (x, ket [d] [0]) | Loan x d <- prog ]
          mapM_ (\(_, inp) ->
            mapM_ (\leaf -> do
                     let sel = [ if b == 1 then SIn else SOut | (_, b) <- cfgBits leaf ]
                     mapM_ (\sr -> do
                              modifyIORef' totalRef (+ 1)
                              let m = I.runStmts (I.initMachL vis inp loanEnv) prog sel
                                        (Just (srHidden sr))
                                  ok = srNames sr == I.mNames m
                                       && srDims sr == I.mDims m
                                       && srAmp sr == I.mAmp m
                              if ok then modifyIORef' agreeRef (+ 1)
                                else putStrLn ("    " ++ f ++ ": site " ++ show (srHidden sr)
                                               ++ " differs on record " ++ show sel))
                           (cfgSites leaf))
                  (run (initConfigL vis inp loanEnv core)))
            (I.probesFor vis :: [(String, StateV Cyclo)]))
        withBlocks
  total <- readIORef totalRef
  agree <- readIORef agreeRef
  putStrLn ("    " ++ show total ++ " (site, record, probe) states compared")
  check1 c "(q2) the expanded term's state at every drop site is the \
           \unexpanded engine's, so no verdict changes"
    (total > 0 && agree == total)
