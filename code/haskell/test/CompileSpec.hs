-- CompileSpec.hs: checks for Drop.Lang.Compile, the OpenQASM 3 compiler of the
-- typed surface language. Its own test-suite stanza, so it can be run alone
-- and so its writes to ../qasm3/out-typed/ are the only ones a suite makes.
--
-- (a) every programs/*.s corpus program that is inside the compile domain
--     (a qubit-only program: every register a power-of-two dimension, and
--     every gate diagonal, a permutation, or a single-qubit unitary --
--     Drop.Lang.Compile's own table) compiles; the qutrit program rus.s is
--     refused with the dimension message, bell-block.s is refused because
--     its `mat` gate on the dimension-4 block t is none of the three the
--     compiler knows how to lower, and every other corpus program compiles;
-- (b) each compiled circuit is written to ../qasm3/out-typed/<name>.qasm;
-- (c) a JSON export of Drop.Lang.Machine's leaves (per program, per basis
--     probe of the visible input plus the all-ones probe, following every
--     lift branch) to ../qasm3/out-typed/<name>.leaves.json, for
--     qasm3/compile_check.py to compare against the emitted circuit,
--     numerically, outside this process;
-- (d) the Householder reflection R of the reclaiming proposition reproduces the stated
--     examples, and Drop.Lang.Compile.u3OfMatrix's U(theta,phi,lambda)
--     reproduces R up to a global phase.

module Main (main) where

import Control.Monad (forM_, unless)
import Data.Bits ((.&.), shiftL, shiftR, xor)
import Data.Complex
import Data.IORef
import Data.List (intercalate, isInfixOf, isSuffixOf)
import Data.Word (Word64)
import System.Directory (createDirectoryIfMissing)
import System.Exit (exitFailure)
import Text.Printf (printf)

import Drop.Lang.Cyclo (Cyclo)
import Drop.Lang.Syntax (Prog, VisSpec)
import Drop.Lang.Compile
import Drop.Lang.Elab (flatToProgram)
import Drop.Lang.Interp (probesFor)
import Drop.Lang.Machine
import Drop.Lang.QState (StateV, applyGate)
import Drop.Lang.Typed
import Drop.Lang.Parser (parseProgram)
import qualified Drop.Lang.Checks.Parser as TP

-- A tiny counting harness, as in TypedSpec.hs ------------------------------

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

-- The corpus ---------------------------------------------------------------

corpusFiles :: [FilePath]
corpusFiles = TP.progFiles

baseName :: FilePath -> String
baseName = reverse . takeWhile (/= '/') . reverse

stripDotS :: String -> String
stripDotS n = if ".s" `isSuffixOf` n then take (length n - 2) n else n

qutritFiles :: [String]
qutritFiles = ["rus.s"]

-- | Files refused for any reason: the qutrit register (rus.s) and the two
-- gates outside the compiler's table (bell-block.s's `mat` on a
-- dimension-4 block, and program (c)'s declared V on two qubits).
refusedFiles :: [String]
refusedFiles = qutritFiles ++ ["bell-block.s", "c.s"]

outDir :: FilePath
outDir = "../qasm3/out-typed"

-- (a)/(b): compile every corpus program, write the .qasm text ------------

compileCorpus :: Counters -> IO ()
compileCorpus c = do
  createDirectoryIfMissing True outDir
  putStrLn "(a)/(b) compiling the corpus"
  results <- mapM tryOne corpusFiles
  let compiled = [ n | (n, Right _) <- results ]
      refused  = [ (n, e) | (n, Left e) <- results ]
  putStrLn (show (length compiled) ++ " compiled, " ++ show (length refused) ++ " refused:")
  mapM_ (\(n, e) -> putStrLn ("    " ++ n ++ ": REFUSED: " ++ showCompileError e)) refused
  check1 c "every other corpus program compiles"
    (all (`elem` compiled) [ baseName f | f <- corpusFiles, baseName f `notElem` refusedFiles ])
  check1 c "rus.s is refused"
    (all (`elem` map fst refused) qutritFiles)
  check1 c "rus.s is refused with the dimension message (register x, dimension 3)"
    (all (\n -> case lookup n refused of
                  Just (NonPowerOfTwo _ 3) -> True
                  _ -> False) qutritFiles)
  check1 c "bell-block.s is refused: its `mat` on t is not diagonal, a permutation, or a single-qubit unitary"
    (case lookup "bell-block.s" refused of
       Just (GateNotInDomain ["t"] msg) ->
         msg == "not diagonal, a permutation, or a single-qubit unitary"
       _ -> False)
  check1 c "c.s is refused: the declared gate V on (t, q) is outside the emitter's table"
    (case lookup "c.s" refused of
       Just (GateNotInDomain ["t", "q"] msg) ->
         msg == "not diagonal, a permutation, or a single-qubit unitary"
       _ -> False)
  where
    tryOne f = case TP.parsed f of
      Left e -> do
        putStrLn ("    " ++ f ++ ": did not parse: " ++ e)
        return (baseName f, Left (Other e))
      Right (vis, prog) -> do
        let typed = flatToProgram vis prog
        case compile typed of
          Left e -> return (baseName f, Left e)
          Right txt -> do
            writeFile (outDir ++ "/" ++ stripDotS (baseName f) ++ ".qasm") txt
            return (baseName f, Right txt)

-- (c): JSON export of Drop.Lang.Machine's leaves ------------------------------

jStr :: String -> String
jStr s = "\"" ++ concatMap esc s ++ "\""
  where esc '"' = "\\\""; esc '\\' = "\\\\"; esc ch = [ch]

jNum :: Double -> String
jNum = printf "%.17g"

jArr :: [String] -> String
jArr xs = "[" ++ intercalate "," xs ++ "]"

jObj :: [(String, String)] -> String
jObj kvs = "{" ++ intercalate "," [ jStr k ++ ":" ++ v | (k, v) <- kvs ] ++ "}"

leafJson :: (Config Cyclo, [Complex Double]) -> String
leafJson (cfg, expected) = jObj
  [ ("names", jArr (map jStr (cfgNames cfg)))
  , ("dims", jArr (map (jNum . fromIntegral) (cfgDims cfg)))
  , ("hidden", jArr (map jStr (cfgHidden cfg)))
  , ("record", jArr [ jArr [jStr n, jNum (fromIntegral b)] | (n, b) <- cfgBits cfg ])
  , ("amp", jArr [ jArr [jNum (realPart z), jNum (imagPart z)] | a <- cfgAmp cfg, let z = toC a ])
  , ("expectedAmp", jArr [ jArr [jNum (realPart z), jNum (imagPart z)] | z <- expected ])
  ]

exportLeaves :: FilePath -> IO ()
exportLeaves f = case TP.parsed f of
  Left _ -> return ()
  Right (vis, prog) -> exportLeavesOf (stripDotS (baseName f)) vis prog

-- | The leaves export for a program given as its parsed form, under the
-- name compile_check.py pairs with @<name>.qasm@; the corpus goes through
-- 'exportLeaves', the source-string fixtures of (k) below through this.
exportLeavesOf :: String -> VisSpec -> Prog Cyclo -> IO ()
exportLeavesOf name vis prog = do
    let typed = flatToProgram vis prog
    case layoutOnly typed of
      Left _ -> return ()  -- refused programs (rus) have nothing to export
      Right () -> do
        let probes = probesFor vis :: [(String, StateV Cyclo)]
            perProbe = [ (i, either (const []) id (leavesWithExpected typed inp))
                       | (i, (_, inp)) <- zip [0 :: Int ..] probes ]
            liftInfo = either (const []) id (liftInfoOf typed)
            wireAlloc = either (const []) id (wireAllocOf typed)
            visQ = either (const []) id (visQubitsOf typed)
            liftAncilla = either (const []) id (liftAncillaOf typed)
            js = jObj
              [ ("visNames", jArr (map (jStr . fst) vis))
              , ("visDims", jArr (map (jNum . fromIntegral . snd) vis))
              , ("visQubits", jArr [ jObj [ ("name", jStr n), ("qubits", jArr (map (jNum . fromIntegral) qs)) ]
                                    | (n, qs) <- visQ ])
              , ("liftInfo", jArr [ jObj [ ("name", jStr n), ("bit", jNum (fromIntegral idx))
                                         , ("survivedValue", jNum (fromIntegral sv)) ]
                                   | (n, idx, sv) <- liftInfo ])
              , ("wireAlloc", jArr [ jObj [ ("name", jStr n), ("qubits", jArr (map (jNum . fromIntegral) qs))
                                          , ("psi", jArr [ jArr [jNum (realPart z), jNum (imagPart z)] | z <- psi ]) ]
                                   | (n, qs, psi) <- wireAlloc ])
              , ("liftAncilla", jArr [ jNum (fromIntegral q) | (_, q) <- liftAncilla ])
              , ("probes", jArr [ jObj [ ("probe", jNum (fromIntegral i))
                                       , ("leaves", jArr (map leafJson leaves)) ]
                                 | (i, leaves) <- perProbe ])
              ]
        writeFile (outDir ++ "/" ++ name ++ ".leaves.json") js
  where
    -- A cheap re-check of the domain (dimension only), just so a qutrit
    -- program's leaves are not exported (Drop.Lang.Compile already refused it
    -- in 'compileCorpus'; this mirrors that without recomputing 'compile').
    layoutOnly typed = if any (\(_, d) -> not (isPow2 d)) (progCtx typed) then Left () else Right ()
    isPow2 n = n >= 2 && (n .&. (n - 1)) == 0

-- (d): the Householder reflection, the reclaiming proposition --------------------------

approxEqC :: Complex Double -> Complex Double -> Bool
approxEqC a b = magnitude (a - b) < 1e-6

approxEqV :: [Complex Double] -> [Complex Double] -> Bool
approxEqV a b = length a == length b && and (zipWith approxEqC a b)

matVec :: [[Complex Double]] -> [Complex Double] -> [Complex Double]
matVec m v = [ sum (zipWith (*) row v) | row <- m ]

isUnitary :: [[Complex Double]] -> Bool
isUnitary m =
  let n = length m
      dag = [ [ conjugate (m !! j !! i) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
      prod = [ [ sum (zipWith (*) (dag !! i) [ m !! k !! j | k <- [0 .. n - 1] ]) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
  in and [ approxEqC (prod !! i !! j) (if i == j then 1 else 0) | i <- [0 .. n - 1], j <- [0 .. n - 1] ]

-- | Up to a global phase: find a nonzero entry, fit the phase, compare.
approxEqUpToPhase :: [[Complex Double]] -> [[Complex Double]] -> Bool
approxEqUpToPhase m1 m2 =
  case [ (i, j) | i <- [0 .. n - 1], j <- [0 .. n - 1], magnitude (m1 !! i !! j) > 1e-6 ] of
    [] -> and [ magnitude (m2 !! i !! j) < 1e-6 | i <- [0 .. n - 1], j <- [0 .. n - 1] ]
    ((i, j) : _) ->
      let ph = (m2 !! i !! j) / (m1 !! i !! j)
      in magnitude ph > 1e-3 &&
         and [ approxEqC (m2 !! a !! b) (ph * (m1 !! a !! b)) | a <- [0 .. n - 1], b <- [0 .. n - 1] ]
  where n = length m1

u3Matrix :: (Double, Double, Double) -> [[Complex Double]]
u3Matrix (theta, phi, lam) =
  [ [ cos (theta / 2) :+ 0, negate (cis lam) * (sin (theta / 2) :+ 0) ]
  , [ cis phi * (sin (theta / 2) :+ 0), cis (phi + lam) * (cos (theta / 2) :+ 0) ]
  ]

reflectionChecks :: Counters -> IO ()
reflectionChecks c = do
  putStrLn "(d) the Householder reflection R (the reclaiming proposition) and its U(theta,phi,lambda)"
  let ket0 = [1 :+ 0, 0 :+ 0]
      ket1 = [0 :+ 0, 1 :+ 0]
      ketPlus = [1 / sqrt 2 :+ 0, 1 / sqrt 2 :+ 0]
      cases :: [(String, [Complex Double], [Complex Double])]
      cases =
        [ ("psi=|0>, g=|->",              ket0, [1/sqrt 2 :+ 0, negate (1/sqrt 2) :+ 0])
        , ("psi=|0>, g=|1> (tie-break)",   ket0, ket1)
        , ("psi=|0>, g=(|0>+i|1>)/sqrt2",  ket0, [1/sqrt 2 :+ 0, 0 :+ (1/sqrt 2)])
        , ("dirty psi=|+>, g=|+> (R = I)", ketPlus, ketPlus)
        ]
  forM_ cases $ \(nm, psi, g) -> do
    let r = reflectionR psi g
        rpsi = matVec r psi
    check1 c (nm ++ ": R unitary") (isUnitary r)
    check1 c (nm ++ ": R.(R.psi) == psi (involution)") (approxEqV (matVec r rpsi) psi)
    check1 c (nm ++ ": R.psi lands on the ray of g (or R = I, ray of psi)")
      (rayEqual (matVec r psi) g || rayEqual (matVec r g) psi)
    let u3 = u3Matrix (u3OfMatrix r)
    check1 c (nm ++ ": u3OfMatrix reproduces R up to a global phase") (approxEqUpToPhase r u3)
  where
    rayEqual a b =
      let na = norm a; nb = norm b
      in na > 1e-9 && nb > 1e-9 &&
         magnitude (sum (zipWith (\x y -> conjugate x * y) a b)) > (1 - 1e-6) * na * nb
    norm v = sqrt (sum [ magnitude x ** 2 | x <- v ])

-- (e): the third 'Admissible' clause -- k>=2, psi and g
-- proportional but neither a basis state -- via 'proportionalTo' directly
-- and via the fixture test/fixtures/dirty-nonbasis.s (a 2-qubit dirty
-- register allocated non-basis, hit with a cancelling Swap;Swap, and
-- dropped: the certificate is exactly the allocation ray).

reclaimSiteChecks :: Counters -> IO ()
reclaimSiteChecks c = do
  putStrLn "(e) the proportional-certificate clause (Admissible)"
  let plus0 = [1 / sqrt 2 :+ 0, 1 / sqrt 2 :+ 0, 0 :+ 0, 0 :+ 0] :: [Complex Double]
      basis0 = [1 :+ 0, 0 :+ 0, 0 :+ 0, 0 :+ 0] :: [Complex Double]
      basis2 = [0 :+ 0, 0 :+ 0, 1 :+ 0, 0 :+ 0] :: [Complex Double]
  check1 c "proportionalTo: a non-basis state is proportional to itself"
    (proportionalTo plus0 plus0)
  check1 c "proportionalTo: a non-basis state is proportional to a global-phase copy of itself"
    (proportionalTo plus0 (map (* cis (pi / 3)) plus0))
  check1 c "proportionalTo: not proportional to an orthogonal basis state"
    (not (proportionalTo plus0 basis2))
  check1 c "proportionalTo: not proportional when psi itself is a basis state"
    (not (proportionalTo basis0 plus0))
  case TP.parsed "test/fixtures/dirty-nonbasis.s" of
    Left e -> do
      check1 c "dirty-nonbasis.s parses" False
      putStrLn ("    did not parse: " ++ e)
    Right (vis, prog) ->
      case compile (flatToProgram vis prog) of
        Left e -> do
          check1 c "dirty-nonbasis.s compiles" False
          putStrLn ("    REFUSED: " ++ showCompileError e)
        Right txt -> do
          check1 c "dirty-nonbasis.s compiles" True
          check1 c "dirty-nonbasis.s: no \"not emitted\" comment anywhere in the circuit"
            (not ("not emitted" `isInfixOf` txt))
          check1 c "dirty-nonbasis.s: no reclaim comment/gate for 'a' at all"
            (not ("reclaim of a" `isInfixOf` txt))
          check1 c "dirty-nonbasis.s: the cancelling Swap;Swap is still emitted (site reached, not vacuous)"
            (length (filter (\l -> take 4 l == "swap") (lines txt)) == 2)

-- (f): loans -- mcx-dirty.s (B = I, nothing
-- emitted), mcx-dirty-x.s (B = X, one U emitted), mcx-dirty-half.s (unsafe),
-- and the fixture test/fixtures/cz-loan.s (a loan hit with a CZ and no
-- correction: unsafe, the block/rest reshape does not even factor).

loanChecks :: Counters -> IO ()
loanChecks c = do
  putStrLn "(f) the loan redesign: a header `loan` as an extra input register"
  checkQasm "mcx-dirty.s" "programs/mcx-dirty.s"
    [ ("mcx-dirty.s compiles", const True)
    , ("mcx-dirty.s: B = I, nothing emitted (no U(...), no reclaim comment)"
      , \txt -> not ("U(" `isInfixOf` txt) && not ("reclaim of a" `isInfixOf` txt)
                && not ("not emitted" `isInfixOf` txt)) ]
  checkQasm "mcx-dirty-x.s" "programs/mcx-dirty-x.s"
    [ ("mcx-dirty-x.s compiles", const True)
    , ("mcx-dirty-x.s: exactly one U(...) is emitted (the reclaiming gate B = X)"
      , \txt -> length (filter ("U(" `isInfixOf`) (lines txt)) == 1) ]
  checkQasm "mcx-dirty-half.s" "programs/mcx-dirty-half.s"
    [ ("mcx-dirty-half.s compiles", const True)
    , ("mcx-dirty-half.s: drop a dropped unsafe: stays live"
      , \txt -> "dropped unsafe" `isInfixOf` txt) ]
  case TP.parsed "test/fixtures/cz-loan.s" of
    Left e -> do
      check1 c "cz-loan.s parses" False
      putStrLn ("    did not parse: " ++ e)
    Right (vis, prog) ->
      case compile (flatToProgram vis prog) of
        Left e -> do
          check1 c "cz-loan.s compiles" False
          putStrLn ("    REFUSED: " ++ showCompileError e)
        Right txt -> do
          check1 c "cz-loan.s compiles" True
          check1 c "cz-loan.s: drop t dropped unsafe: stays live"
            ("dropped unsafe" `isInfixOf` txt)
  where
    checkQasm nm path expectations = case TP.parsed path of
      Left e -> do
        check1 c (nm ++ " parses") False
        putStrLn ("    did not parse: " ++ e)
      Right (vis, prog) ->
        case compile (flatToProgram vis prog) of
          Left e -> do
            mapM_ (\(cnm, _) -> check1 c cnm False) expectations
            putStrLn ("    " ++ nm ++ " REFUSED: " ++ showCompileError e)
          Right txt -> mapM_ (\(cnm, p) -> check1 c cnm (p txt)) expectations

-- (g) a temporary whose safety depends on a live loan's arrival state.
-- 'computeSafety' probes every loan over its own basis, as the site definition's
-- domain [[Omega]] demands; seeding every loan at |0> instead would call the
-- first program below safe and emit no "stays live" marker, so the circuit
-- would let a caller reuse a qubit still entangled with the loan.
mixedLoanChecks :: Counters -> IO ()
mixedLoanChecks c = do
  putStrLn "(g) a temporary beside a loan: the loan is part of the site map's domain"
  emit "temp-reads-loan" srcReadsLoan
    [ ("a temporary that copies a live loan is emitted as dropped unsafe"
      , \txt -> "t dropped unsafe" `isInfixOf` txt) ]
  emit "temp-reads-loan-back" srcReadsLoanBack
    [ ("the same temporary with the copy undone is not marked unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt))
    , ("and is reclaimed by nothing, its certificate being its own |0>"
      , \txt -> not ("reclaim" `isInfixOf` txt)) ]
  where
    emit nm src expectations = case parseProgram src of
      Left e -> do
        check1 c (nm ++ " parses") False
        putStrLn ("    did not parse: " ++ e)
      Right (vis, prog) -> case compile (flatToProgram vis prog) of
        Left e -> do
          mapM_ (\(cnm, _) -> check1 c cnm False) expectations
          putStrLn ("    " ++ nm ++ " REFUSED: " ++ showCompileError e)
        Right txt -> mapM_ (\(cnm, p) -> check1 c cnm (p txt)) expectations

srcReadsLoan, srcReadsLoanBack :: String
srcReadsLoan =
  "prog temp_reads_loan (x : [2], loan a : [2]) : [2] * [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a t;\n\
  \    drop t;\n\
  \    return (x, a)\n\
  \}"
srcReadsLoanBack =
  "prog temp_reads_loan_back (x : [2], loan a : [2]) : [2] * [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a t;  CX a t;\n\
  \    drop t;\n\
  \    return (x, a)\n\
  \}"

-- (h) a block of SEVERAL registers holding a loan: the site definition's clause (4) with
-- B : H_loan -> H_block (Drop.Lang.Interp.loanResultS). A square B (the block
-- is its loans and nothing else) is emitted in three shapes and no more --
-- B the identity (nothing to undo), B on one qubit, and B a permutation of
-- the basis states. A rectangular B (temporaries beside the loans) is
-- emitted when it is a product B' (x) g~ with B' of one of those shapes,
-- as B'^dagger on the loans then the reflection on the temporaries -- group
-- (k) below; the block here, an untouched loan beside a fresh temporary,
-- has B = I (x) |0> and nothing to write.
blockLoanChecks :: Counters -> IO ()
blockLoanChecks c = do
  putStrLn "(h) a block of several registers: B : H_loan -> H_block"
  emit "block-two-loans-id" srcBlockId
    [ ("two loans dropped as one block, B = I: nothing emitted"
      , \txt -> not ("reclaim" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt)) ]
  emit "block-two-loans-swap" srcBlockSwap
    [ ("Swap a b then drop (a,b): safe, and B = SWAP is emitted, not skipped"
      , \txt -> not ("reclaim" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt))
    , ("the reclaiming gate is SWAP^dagger = SWAP, as three CNOTs"
      , \txt -> ["cx q[1], q[2];", "ctrl @ x q[2], q[1];", "cx q[1], q[2];"]
                  `isInfixOfL` lines (dropWhile (/= 'h') txt)) ]
  emit "block-loan-temp" srcBlockRect
    [ ("a loan beside a fresh temporary: B = I (x) |0>, nothing emitted, no refusal"
      , \txt -> not ("not emitted" `isInfixOf` txt) && not ("reclaim" `isInfixOf` txt))
    , ("and the block is not called unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt)) ]
  where
    -- a contiguous run of lines, ignoring surrounding whitespace
    isInfixOfL needle hay =
      any (\i -> map trim (take (length needle) (drop i hay)) == needle)
          [0 .. length hay]
    trim = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse
    emit nm src expectations = case parseProgram src of
      Left e -> do
        check1 c (nm ++ " parses") False
        putStrLn ("    did not parse: " ++ e)
      Right (vis, prog) -> case compile (flatToProgram vis prog) of
        Left e -> do
          mapM_ (\(cnm, _) -> check1 c cnm False) expectations
          putStrLn ("    " ++ nm ++ " REFUSED: " ++ showCompileError e)
        Right txt -> mapM_ (\(cnm, p) -> check1 c cnm (p txt)) expectations

srcBlockId, srcBlockSwap, srcBlockRect :: String
srcBlockId =
  "prog block_id (x : [2], loan a : [2], loan b : [2]) : [2] {\n\
  \    drop (a, b);\n\
  \    return x\n\
  \}"
srcBlockSwap =
  "prog block_swap (x : [2], loan a : [2], loan b : [2]) : [2] {\n\
  \    Swap a b;\n\
  \    drop (a, b);\n\
  \    return x\n\
  \}"
srcBlockRect =
  "prog block_rect (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"

-- (k) a mixed block of product form, and the shapes around it: at a block
-- holding temporaries beside its
-- loans whose block factor is B = B' (x) g~, the emitter writes B'^dagger on
-- the loan qubits and the reclaiming reflection through psi - g~ on the
-- temporary qubits, in that order. Also here: the block factor that
-- entangles a loan with a temporary (safe by the site definition's clause (4), no product gate,
-- "not emitted"), a loan factor on two qubits (refused as the square case
-- is), `drop ()` (a block of dimension one under the site definition's clause (1), admitted by the
-- parser, nothing to reclaim), and a tuple dropped out of
-- allocation order (the certificate, psi and the qubit list all read in
-- the drop's order -- Drop.Lang.QState.factorSplitOrd; read in machine order the
-- certificate alone read in machine order and this program's reclaim was
-- silently skipped). Every fixture is exported to out-typed/ so that
-- qasm3/compile_check.py simulates its emitted circuit against the
-- machine's expected state, the check the paper's compilation theorem stands on.
mixedProductChecks :: Counters -> IO ()
mixedProductChecks c = do
  putStrLn "(k) a mixed block of product form: B'^dagger on the loans, the reflection on the temporaries"
  emit "mixed-x-plus" srcMixedXPlus
    [ ("loan a with X, temporary t on |+>, drop (a, t): emitted, no refusal, not unsafe"
      , \txt -> not ("not emitted" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt))
    , ("two U(...) lines after the program's gates: X^dagger on a's qubit, the reflection on t's"
      , \txt -> case [ l | l <- lines (afterBody txt), "U(" `isInfixOf` l ] of
                  [u1, u2] -> "q[1];" `isInfixOf` u1 && "q[2];" `isInfixOf` u2
                  _        -> False) ]
  emit "mixed-plus-x-reversed" srcMixedPlusXReversed
    [ ("the same block written drop (t, a): the same two gates, loans first"
      , \txt -> not ("not emitted" `isInfixOf` txt) &&
                case [ l | l <- lines (afterBody txt), "U(" `isInfixOf` l ] of
                  [u1, u2] -> "q[1];" `isInfixOf` u1 && "q[2];" `isInfixOf` u2
                  _        -> False) ]
  emit "mixed-swap-plus" srcMixedSwapPlus
    [ ("two loans swapped beside a temporary on |+>: SWAP^dagger as three CNOTs, then one U on t"
      , \txt -> let body = afterBody txt
                in length [ l | l <- lines body, "cx" `isInfixOf` l || "ctrl @ x" `isInfixOf` l ] == 3
                   && length [ l | l <- lines body, "U(" `isInfixOf` l ] == 1
                   && not ("not emitted" `isInfixOf` txt)) ]
  emit "mixed-entangled" srcMixedEntangled
    [ ("H t; CX t a; drop (a, t): safe by the site definition's clause (4), B entangles the loan with the temporary, not emitted"
      , \txt -> "not emitted" `isInfixOf` txt && "entangles" `isInfixOf` txt)
    , ("and not called unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt)) ]
  emit "mixed-loan-factor-two-qubits" srcMixedTwoQubitLoanFactor
    [ ("H on one of two loans beside a temporary: the loan factor is on two qubits, not emitted"
      , \txt -> "not emitted" `isInfixOf` txt && "more than one qubit" `isInfixOf` txt)
    , ("and not called unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt)) ]
  emit "drop-unit" srcDropUnit
    [ ("drop (): parses, compiles, and writes nothing but its comment"
      , \txt -> "drop (): nothing to reclaim" `isInfixOf` txt
                && not ("U(" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt)) ]
  emit "tuple-out-of-order" srcTupleOutOfOrder
    [ ("new a@|1>, new b@|0>, X a, X b, drop (b, a): the transposition is emitted, not skipped"
      , \txt -> "ctrl @ x" `isInfixOf` afterBody txt || "cx" `isInfixOf` afterBody txt)
    , ("and no refusal"
      , \txt -> not ("not emitted" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt)) ]
  where
    -- the emitted text after the last line of the program's own gates: the
    -- fixtures are written so that their reclaiming lines follow a marker
    -- gate (the last statement before the drop is what the drop reclaims)
    afterBody txt = unlines (drop 1 (dropWhile (not . ("// q[0] = x" `isInfixOf`)) (lines txt)))
    emit nm src expectations = case parseProgram src of
      Left e -> do
        check1 c (nm ++ " parses") False
        putStrLn ("    did not parse: " ++ e)
      Right (vis, prog) -> case compile (flatToProgram vis prog) of
        Left e -> do
          mapM_ (\(cnm, _) -> check1 c cnm False) expectations
          putStrLn ("    " ++ nm ++ " REFUSED: " ++ showCompileError e)
        Right txt -> do
          writeFile (outDir ++ "/" ++ nm ++ ".qasm") txt
          exportLeavesOf nm vis prog
          mapM_ (\(cnm, p) -> check1 c cnm (p txt)) expectations

srcMixedXPlus, srcMixedPlusXReversed, srcMixedSwapPlus, srcMixedEntangled,
  srcMixedTwoQubitLoanFactor, srcDropUnit, srcTupleOutOfOrder :: String
srcMixedXPlus =
  "prog mixed_x_plus (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    X a;\n\
  \    H t;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"
srcMixedPlusXReversed =
  "prog mixed_plus_x_reversed (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    X a;\n\
  \    H t;\n\
  \    drop (t, a);\n\
  \    return x\n\
  \}"
srcMixedSwapPlus =
  "prog mixed_swap_plus (x : [2], loan a : [2], loan b : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    Swap a b;\n\
  \    H t;\n\
  \    drop (a, b, t);\n\
  \    return x\n\
  \}"
srcMixedEntangled =
  "prog mixed_entangled (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    H t;\n\
  \    CX t a;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"
srcMixedTwoQubitLoanFactor =
  "prog mixed_two_qubit_loan_factor (x : [2], loan a : [2], loan b : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    H a;\n\
  \    H t;\n\
  \    drop (a, b, t);\n\
  \    return x\n\
  \}"
srcDropUnit =
  "prog drop_unit (x : [2]) : [2] {\n\
  \    drop ();\n\
  \    return x\n\
  \}"
srcTupleOutOfOrder =
  "prog tuple_out_of_order (x : [2]) : [2] {\n\
  \    new a : [2] @ |1>;\n\
  \    new b : [2] @ |0>;\n\
  \    X a;\n\
  \    X b;\n\
  \    drop (b, a);\n\
  \    return x\n\
  \}"

-- (i) bell-pair.s vs bell-pair-split.s: the same H;CX Bell
-- circuit, dropped as one tuple site (safe, block dimension 4, a non-basis
-- certificate) versus dropped register by register (both drops unsafe).
-- Compare reclaimSiteChecks's dirty-nonbasis.s check above and
-- loanChecks's checkQasm below, which this copies the shape of.
--
-- The block-dimension-4 certificate here needs the general clause:
-- 'emitReclaim's 'otherwise' clause covers every k >= 2 certificate via
-- 'emitGeneralReflectionOps' (checked numerically against 'reflectionR' in
-- 'generalReflectionChecks' below, and against a real OpenQASM 3 parser by
-- qasm3/compile_check.py against out-typed/bell-pair.qasm), so bell-pair.s
-- carries a real reclaiming circuit and no "not emitted" comment.
bellPairChecks :: Counters -> IO ()
bellPairChecks c = do
  putStrLn "(i) bell-pair.s vs bell-pair-split.s: which program a context compares"
  checkQasm "bell-pair.s" "programs/bell-pair.s"
    [ ("bell-pair.s compiles", const True)
    , ("bell-pair.s: drop (a,b) is emitted as a circuit, with no refusal comment"
      , \txt -> not ("not emitted" `isInfixOf` txt))
    , ("bell-pair.s: the general reclaiming reflection's U(...) lines are present"
      , \txt -> "U(" `isInfixOf` txt)
    , ("bell-pair.s: the reflection's negated-controlled phase flip is present"
      , \txt -> "negctrl @ z" `isInfixOf` txt) ]
  checkQasm "bell-pair-split.s" "programs/bell-pair-split.s"
    [ ("bell-pair-split.s compiles", const True)
    , ("bell-pair-split.s: drop a dropped unsafe: stays live"
      , \txt -> "a dropped unsafe" `isInfixOf` txt)
    , ("bell-pair-split.s: drop b dropped unsafe: stays live"
      , \txt -> "b dropped unsafe" `isInfixOf` txt) ]
  where
    checkQasm nm path expectations = case TP.parsed path of
      Left e -> do
        check1 c (nm ++ " parses") False
        putStrLn ("    did not parse: " ++ e)
      Right (vis, prog) ->
        case compile (flatToProgram vis prog) of
          Left e -> do
            mapM_ (\(cnm, _) -> check1 c cnm False) expectations
            putStrLn ("    " ++ nm ++ " REFUSED: " ++ showCompileError e)
          Right txt -> mapM_ (\(cnm, p) -> check1 c cnm (p txt)) expectations

-- (j) the general k-qubit reclaiming reflection:
-- 'emitGeneralReflectionOps qs psi g', simulated exactly as
-- 'Drop.Lang.Compile.renderOp' would print it (via 'opDense' and
-- 'Drop.Lang.QState.applyGate' -- the same tensor/control machinery
-- 'Drop.Lang.Machine' itself uses, not a re-parse of the emitted text),
-- reproduces 'reflectionR psi g' entrywise at 1e-9, with NO global-phase
-- fit (the reclaiming proposition: V^dagger prepares u
-- exactly, so no phase remains to fix). Five fixed cases (Bell, two other
-- k=2 rays, the maximally-mixed-looking (1,1,1,1)/2, and a k=3 GHZ
-- certificate), each at psi = |0..0>, plus a k in {2,3}, 20-vector-each
-- randomized sweep at psi = |0..0> and at a random psi, from a small
-- deterministic PRNG (xorshift64*, fixed seeds) so the check is
-- reproducible.

-- | xorshift64* -- deterministic, seeded, dependency-free (no 'random'
-- package in this cabal file); used only to generate this check's random
-- unit vectors reproducibly.
newtype Rng = Rng Word64

nextW64 :: Rng -> (Word64, Rng)
nextW64 (Rng s0) =
  let s1 = s0 `xor` (s0 `shiftL` 13)
      s2 = s1 `xor` (s1 `shiftR` 7)
      s3 = s2 `xor` (s2 `shiftL` 17)
  in (s3 * 2685821657736338717, Rng s3)

-- | A pseudo-uniform double in [-1, 1], from one PRNG step.
nextD :: Rng -> (Double, Rng)
nextD rng =
  let (w, rng') = nextW64 rng
      frac = fromIntegral (w `mod` 1000000007) / 1000000007 :: Double
  in (2 * frac - 1, rng')

-- | A random unit vector of dimension 'n' (complex entries, each component's
-- real and imaginary part drawn independently in [-1,1] then the whole
-- vector normalised) -- not Haar-random, but that is not needed here: any
-- distribution that is not concentrated on a measure-zero set (proportional
-- to |0..0>, or with w = 0) exercises the general clause.
randomUnitVec :: Int -> Rng -> ([Complex Double], Rng)
randomUnitVec n rng0 =
  let (raw, rngF) = go n rng0 []
      nrm = sqrt (sum [ magnitude z ** 2 | z <- raw ])
  in (map (/ (nrm :+ 0)) raw, rngF)
  where
    go 0 rng acc = (reverse acc, rng)
    go k rng acc =
      let (re, rng1) = nextD rng
          (im, rng2) = nextD rng1
      in go (k - 1 :: Int) rng2 ((re :+ im) : acc)

ketZero :: Int -> [Complex Double]
ketZero k = [ if i == 0 then 1 :+ 0 else 0 :+ 0 | i <- [0 .. 2 ^ k - (1 :: Int)] ]

-- | The unitary 'ops' (time order, first-applied-first) realises, on 'k'
-- qubits numbered 0..k-1 -- exactly 'opDense' fed to 'Drop.Lang.QState.applyGate'
-- at each step, column by column from every basis vector.
simulateOps :: Int -> [Op] -> [[Complex Double]]
simulateOps k ops =
  [ [ cols !! j !! i | j <- [0 .. d - 1] ] | i <- [0 .. d - 1] ]
  where
    d = 2 ^ k :: Int
    dims = replicate k 2
    basisVec j = [ if i == j then 1 :+ 0 else 0 :+ 0 | i <- [0 .. d - 1] ]
    applyStep st op = let (targets, m) = opDense op in applyGate dims m targets st
    cols = [ foldl applyStep (basisVec j) ops | j <- [0 .. d - 1] ]

matClose :: Double -> [[Complex Double]] -> [[Complex Double]] -> Bool
matClose eps a b =
  length a == length b &&
  and [ length ra == length rb &&
        and (zipWith (\x y -> magnitude (x - y) < eps) ra rb)
      | (ra, rb) <- zip a b ]

generalReflectionChecks :: Counters -> IO ()
generalReflectionChecks c = do
  putStrLn "(j) the general k-qubit reclaiming reflection: emitGeneralReflectionOps vs reflectionR"
  let s2 = 1 / sqrt 2 :: Double
      bell = [s2 :+ 0, 0 :+ 0, 0 :+ 0, s2 :+ 0]
      case1 = [s2 :+ 0, 0 :+ s2, 0 :+ 0, 0 :+ 0]
      case2 = [0 :+ 0, s2 :+ 0, s2 :+ 0, 0 :+ 0]
      case3 = map (:+ 0) [0.5, 0.5, 0.5, 0.5]
      ghz = [s2 :+ 0, 0, 0, 0, 0, 0, 0, s2 :+ 0]
  checkOne "Bell (1,0,0,1)/sqrt2, psi=|00>" 2 (ketZero 2) bell
  checkOne "(1,i,0,0)/sqrt2, psi=|00>" 2 (ketZero 2) case1
  checkOne "(0,1,1,0)/sqrt2, psi=|00>" 2 (ketZero 2) case2
  checkOne "(1,1,1,1)/2, psi=|00>" 2 (ketZero 2) case3
  checkOne "k=3 GHZ certificate, psi=|000>" 3 (ketZero 3) ghz
  forM_ [2, 3 :: Int] $ \k -> do
    let d = 2 ^ k
    zeroLoop k d ("k=" ++ show k ++ " psi=|0..0>, random g #") (Rng (0x9E3779B97F4A7C15 + fromIntegral k)) (20 :: Int)
    bothLoop k d ("k=" ++ show k ++ " random psi, random g #") (Rng (0xD1B54A32D192ED03 + fromIntegral k)) (20 :: Int)
  where
    checkOne nm k psi g =
      let r = reflectionR psi g
          ops = emitGeneralReflectionOps [0 .. k - 1] psi g
          sim = simulateOps k ops
      in check1 c (nm ++ ": simulated circuit == reflectionR entrywise at 1e-9") (matClose 1e-9 sim r)
    zeroLoop _ _ _ _ 0 = return ()
    zeroLoop k d nm rng n =
      let (g, rng') = randomUnitVec d rng
      in do
        checkOne (nm ++ show n) k (ketZero k) g
        zeroLoop k d nm rng' (n - 1)
    bothLoop _ _ _ _ 0 = return ()
    bothLoop k d nm rng n =
      let (psi, rng1) = randomUnitVec d rng
          (g, rng2) = randomUnitVec d rng1
      in do
        checkOne (nm ++ show n) k psi g
        bothLoop k d nm rng2 (n - 1)

-- (k) the two-support short form: 'emitTwoSupportReflectionOps'
-- against 'reflectionR', on top of 'generalReflectionChecks's own coverage
-- of 'emitGeneralReflectionOps'. Reuses the same five fixed vectors as (j)
-- above, under the SAME (psi = |0..0>, g = the vector) pairing -- but here
-- that pairing is not just a convenient g to feed the general tree, it is
-- also read as a claim about w = psi - g~'s support, and by hand only four
-- of the five are actually two-support under it: Bell (w supported on
-- {0,3}), (1,i,0,0)/sqrt2 (w on {0,1}), the k=3 GHZ vector (w on {0,7}),
-- and (1,0,0,-1)/sqrt2 (w on {0,3}) all reduce this way, but
-- (0,1,1,0)/sqrt2 does not: psi_0 = 1 and g_0 = 0, so w_0 = 1 unconditionally,
-- and w_1, w_2 are both (generically) nonzero too, giving THREE-support w,
-- not two -- so that case is checked as a required decline (Nothing), not
-- forced into the short form. Then, for k in {2, 3}, 20 seeded random cases
-- each of two shapes: 'zeroPsiLoop' (psi = |0..0>, g random two-support on
-- {0, j} for random j -- the reliable "simplest" construction the task
-- names, since w = psi - g~ then has support inside {0, j} by the same
-- by-hand argument as the Bell case above) and 'bothTwoSupportLoop' (a
-- genuinely random, non-basis psi AND g both supported on the same random
-- pair {p, q} with p, q /= 0 -- "random psi" together with "g supported on
-- two indices neither of which is |0..0>", covering both named
-- constructions at once, since w = psi - g~ is then trivially confined to
-- {p, q} too). Every case asserts BOTH that 'emitTwoSupportReflectionOps'
-- is the clause taken (returns 'Just', not a silent decline into the
-- caller's fallback) and that its simulated circuit reproduces
-- 'reflectionR psi g' entrywise at 1e-9, with no phase fit -- the same
-- 'matClose'/'simulateOps' machinery (j) already uses, so this checks the
-- exact object 'renderOp' would print, not a re-derivation.
twoSupportReflectionChecks :: Counters -> IO ()
twoSupportReflectionChecks c = do
  putStrLn "(k) the two-support short form: emitTwoSupportReflectionOps vs reflectionR"
  let s2 = 1 / sqrt 2 :: Double
      bell = [s2 :+ 0, 0 :+ 0, 0 :+ 0, s2 :+ 0]
      case1 = [s2 :+ 0, 0 :+ s2, 0 :+ 0, 0 :+ 0]
      case2 = [0 :+ 0, s2 :+ 0, s2 :+ 0, 0 :+ 0]
      caseMinus = [s2 :+ 0, 0 :+ 0, 0 :+ 0, negate s2 :+ 0]
      ghz = [s2 :+ 0, 0, 0, 0, 0, 0, 0, s2 :+ 0]
  checkShort "Bell (1,0,0,1)/sqrt2, psi=|00>" 2 (ketZero 2) bell
  checkShort "(1,i,0,0)/sqrt2, psi=|00>" 2 (ketZero 2) case1
  checkFallback "(0,1,1,0)/sqrt2, psi=|00>: w is 3-support, short form must decline" 2 (ketZero 2) case2
  checkShort "k=3 GHZ certificate, psi=|000>" 3 (ketZero 3) ghz
  checkShort "(1,0,0,-1)/sqrt2, psi=|00>" 2 (ketZero 2) caseMinus
  forM_ [2, 3 :: Int] $ \k -> do
    let d = 2 ^ k :: Int
    zeroPsiLoop k d ("k=" ++ show k ++ " psi=|0..0>, random 2-support g #")
      (Rng (0xA24BAED4963EE407 + fromIntegral k)) (20 :: Int)
    bothTwoSupportLoop k d ("k=" ++ show k ++ " random 2-support psi and g, same pair #")
      (Rng (0x9FB21C651E98DF25 + fromIntegral k)) (20 :: Int)
  where
    checkShort nm k psi g = case emitTwoSupportReflectionOps [0 .. k - 1] psi g of
      Nothing -> check1 c (nm ++ ": the two-support clause is taken") False
      Just ops ->
        let r = reflectionR psi g
            sim = simulateOps k ops
        in do
          check1 c (nm ++ ": the two-support clause is taken") True
          check1 c (nm ++ ": simulated short-form circuit == reflectionR entrywise at 1e-9")
            (matClose 1e-9 sim r)
    checkFallback nm k psi g = case emitTwoSupportReflectionOps [0 .. k - 1] psi g of
      Nothing -> check1 c nm True
      Just _  -> check1 c nm False

    embed2 n i j vi vj = [ if idx == i then vi else if idx == j then vj else 0 | idx <- [0 .. n - 1] ]

    nextIdx lo hi rng =
      let (w, rng') = nextW64 rng
          spn = hi - lo + 1
      in (lo + fromIntegral (w `mod` fromIntegral spn), rng')
    nextDistinctPair lo hi rng0 =
      let (p, rng1) = nextIdx lo hi rng0
          (q0, rng2) = nextIdx lo (hi - 1) rng1
          q = if q0 >= p then q0 + 1 else q0
      in ((p, q), rng2)

    zeroPsiLoop _ _ _ _ 0 = return ()
    zeroPsiLoop k d nm rng n =
      let (j, rng1) = nextIdx 1 (d - 1) rng
          (cs, rng2) = randomUnitVec 2 rng1
          g = embed2 d 0 j (cs !! 0) (cs !! 1)
      in do
        checkShort (nm ++ show n) k (ketZero k) g
        zeroPsiLoop k d nm rng2 (n - 1 :: Int)

    bothTwoSupportLoop _ _ _ _ 0 = return ()
    bothTwoSupportLoop k d nm rng n =
      let ((p, q), rng1) = nextDistinctPair 1 (d - 1) rng
          (pv, rng2) = randomUnitVec 2 rng1
          (gv, rng3) = randomUnitVec 2 rng2
          psi = embed2 d p q (pv !! 0) (pv !! 1)
          g   = embed2 d p q (gv !! 0) (gv !! 1)
      in do
        checkShort (nm ++ show n) k psi g
        bothTwoSupportLoop k d nm rng3 (n - 1 :: Int)

main :: IO ()
main = do
  c <- newCounters
  compileCorpus c
  mapM_ exportLeaves corpusFiles
  reflectionChecks c
  reclaimSiteChecks c
  loanChecks c
  mixedLoanChecks c
  blockLoanChecks c
  mixedProductChecks c
  bellPairChecks c
  generalReflectionChecks c
  twoSupportReflectionChecks c
  report c
