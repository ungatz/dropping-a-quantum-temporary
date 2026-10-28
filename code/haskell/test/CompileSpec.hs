-- CompileSpec: the OpenQASM 3 compiler of the typed language, checked on the corpus and on built programs.
--
-- Question: Does Drop.Lang.Compile turn each program it accepts into a circuit
--           that does what the machine says, and refuse each it cannot?
-- Answer:   Groups of checks, each tagged in the printed output:
--           - every programs/*.s file inside the compile domain (a qubit-only
--             program whose gates are diagonal, a permutation, or a
--             single-qubit unitary) compiles, and its circuit is written to
--             ../qasm3/out-typed/<name>.qasm; the qutrit program rus.s is
--             refused with the dimension message, bell-block.s and c.s are
--             refused as outside the gate table; a circuit ends by measuring
--             the register its `return` names;
--           - a JSON export of the machine's leaves (per basis probe of the
--             visible input plus the all-ones probe, following every lift
--             branch) is written to ../qasm3/out-typed/<name>.leaves.json,
--             for qasm3/compile_check.py to compare against the circuit,
--             numerically, outside this process;
--           - the Householder reflection R of the reclaiming proposition is
--             unitary and an involution, takes psi to the ray of g, and
--             Emit.u3OfMatrix reproduces it up to a global phase; the emitted
--             k-qubit circuits (general, two-support and frame-return forms)
--             reproduce reflectionR and frameReturnMatrix entrywise at 1e-9;
--           - loans and blocks: a drop that is safe is reclaimed by the gate
--             B the certificate names (nothing printed when B is the
--             identity), an unsafe drop stays live, and the drops the
--             fragment cannot express are refused with the drop they name;
--           - the pool: freed qubits are reused first-in first-out, and
--             arms of an `if` that disagree on resources are refused.
-- Paper:    thm:compile, thm:compileleaf, sec:lang:compile, app:emitter-contract,
--           fig:loan-return, fig:reclaim-circuits, prop:loanreturn, prop:reuse
-- Shapes:   Program      a typed program, built or elaborated from a file
--           SFile        a parsed file: header, body and the value it returns
--           Op           one printed operation (OpU, OpP, OpX, OpZ, each with its controls)
--           Rng          a xorshift state, for the random vectors

module Main (main) where

import Control.Monad (forM_)
import Data.Bits ((.&.), shiftL, shiftR, xor)
import Data.Complex
import Data.List (intercalate, isInfixOf, isSuffixOf)
import Data.Word (Word64)
import System.Directory (createDirectoryIfMissing)
import Text.Printf (printf)

import Drop.Lang.Scalar (Cyclo(..), iC)
import Drop.Lang.Check (checkProgram, TypeError (BadLiftBlock))
import Drop.Lang.Compile
import Drop.Lang.Compile.Emit
  ( Op (..), opDense, emitGeneralReflectionOps, emitTwoSupportReflectionOps
  , emitFrameReturnOps, frameReturnMatrix, placementIndex, emittedReturnResidualOK
  , reflectionR, u3OfMatrix, proportionalTo, toC
  , wireAllocOf, leavesWithExpected )
import Drop.Lang.Elab (flatToProgram, flatToProgramR)
import Drop.Lang.Criterion (probesFor)
import Drop.Lang.Flat (Prog, VisSpec)
import Drop.Lang.Machine
import Drop.Lang.State (StateV, applyGate)
import Drop.Lang.Syntax
import Drop.Lang.Parser (parseFile, parseProgram)
import Drop.Lang.Render (SFile (..), sfVis)
import qualified Drop.Lang.Checks.Parser as TP

import Harness (Counters, check1, newCounters, report)

-- The corpus ---------------------------------------------------------------

corpusFiles :: [FilePath]
corpusFiles = TP.progFiles

-- | The three fixtures the loan and reclaim checks read besides the corpus.
fixtureFiles :: [FilePath]
fixtureFiles =
  [ "test/fixtures/dirty-nonbasis.s", "test/fixtures/dirty-nonbasis-unsafe.s"
  , "test/fixtures/cz-loan.s" ]

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

compileCorpus :: TP.Corpus -> Counters -> IO ()
compileCorpus corpus c = do
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
  -- The output measurements read what `return` names. These two programs
  -- return a register that is not an input, so measuring the inputs in
  -- declared order would read the wrong qubits.
  check1 c "copy-input.s: result reads t (q[1]), the register it returns, not the dropped input x"
    (case lookup "copy-input.s" results of
       Just (Right txt) -> takeLast 2 (lines txt) == ["// q[1] = t", "result[0] = measure q[1];"]
                           && "bit[1] result;" `elem` lines txt
       _ -> False)
  check1 c "learns-nothing.s: result has two bits, reading x (q[0]) and a (q[1]), the registers it returns"
    (case lookup "learns-nothing.s" results of
       Just (Right txt) -> takeLast 2 (lines txt) == ["result[0] = measure q[0];", "result[1] = measure q[1];"]
                           && "bit[2] result;" `elem` lines txt && "// q[1] = a" `elem` lines txt
       _ -> False)
  where
    takeLast k xs = drop (length xs - k) xs
    tryOne f = case TP.parsedFile corpus f of
      Left e -> do
        putStrLn ("    " ++ f ++ ": did not parse: " ++ e)
        return (baseName f, Left (Other e))
      Right sf -> do
        let typed = typedOf sf
        case compile typed of
          Left e -> return (baseName f, Left e)
          Right txt -> do
            writeFile (outDir ++ "/" ++ stripDotS (baseName f) ++ ".qasm") txt
            return (baseName f, Right txt)

-- | A program as its file writes it: the ordinary inputs, the body, and the
-- value its `return` names -- what `dqt compile` compiles
-- (Drop.Lang.Report.Run.compileText). The circuit ends by measuring that
-- value, so every file this suite writes goes through here; 'flatToProgram'
-- would rebuild the value from the live registers in allocation order.
typedOf :: SFile -> Program Cyclo
typedOf sf = flatToProgramR (sfVis sf) (sfReturn sf) (sfBody sf)

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

-- | One leaf. @retQubits@ is read off the machine's own leaf, not the
-- emitter: the value its term returns, through the layout's wire map, in
-- the value's order -- the qubits the circuit's result[0], result[1], ...
-- must read on this run. A leaf whose term is not a value exports none,
-- which the checker reports as a width mismatch.
leafJson :: [(Name, [Int])] -> (Config Cyclo, [Complex Double]) -> String
leafJson wires (cfg, expected) = jObj
  [ ("names", jArr (map jStr (cfgNames cfg)))
  , ("dims", jArr (map (jNum . fromIntegral) (cfgDims cfg)))
  , ("hidden", jArr (map jStr (cfgHidden cfg)))
  , ("record", jArr [ jArr [jStr n, jNum (fromIntegral b)] | (n, b) <- cfgBits cfg ])
  , ("amp", jArr [ jArr [jNum (realPart z), jNum (imagPart z)] | a <- cfgAmp cfg, let z = toC a ])
  , ("expectedAmp", jArr [ jArr [jNum (realPart z), jNum (imagPart z)] | z <- expected ])
  , ("retQubits", jArr (map (jNum . fromIntegral) retQubits))
  ]
  where
    retQubits = case cfgTerm cfg of
      Return v -> concat [ maybe [] id (lookup n wires) | n <- valueNames v ]
      _        -> []

exportLeaves :: TP.Corpus -> FilePath -> IO ()
exportLeaves corpus f = case TP.parsedFile corpus f of
  Left _ -> return ()
  Right sf -> exportLeavesOf (stripDotS (baseName f)) (typedOf sf)

-- | The leaves export for a typed program, under the name compile_check.py
-- pairs with @<name>.qasm@: the corpus arrives through 'exportLeaves', the
-- fixtures of (k) below directly.
exportLeavesOf :: String -> Program Cyclo -> IO ()
exportLeavesOf name typed = do
    let vis = progCtx typed
    case layoutOnly of
      Left _ -> return ()  -- refused programs (rus) have nothing to export
      Right () -> do
        let probes = probesFor vis :: [(String, StateV Cyclo)]
            perProbe = [ (i, either (const []) id (leavesWithExpected typed inp))
                       | (i, (_, inp)) <- zip [0 :: Int ..] probes ]
            liftInfo = either (const []) id (liftInfoOf typed)
            wireAlloc = either (const []) id (wireAllocOf typed)
            visQ = either (const []) id (visQubitsOf typed)
            liftAncilla = either (const []) id (liftAncillaOf typed)
            wires = either (const []) id (wireQubitsOf typed)
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
                                       , ("leaves", jArr (map (leafJson wires) leaves)) ]
                                 | (i, leaves) <- perProbe ])
              ]
        writeFile (outDir ++ "/" ++ name ++ ".leaves.json") js
  where
    -- A cheap re-check of the domain (dimension only), just so a qutrit
    -- program's leaves are not exported (Drop.Lang.Compile already refused it
    -- in 'compileCorpus'; this mirrors that without recomputing 'compile').
    layoutOnly = if any (\(_, d) -> not (isPow2 d)) (progCtx typed) then Left () else Right ()
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
      dag = [ [ conjugate (m !! j !! i) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]  -- impossible: j, i < n
      prod = [ [ sum (zipWith (*) (dag !! i) [ m !! k !! j | k <- [0 .. n - 1] ]) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]  -- impossible: i, j, k < n
  in and [ approxEqC (prod !! i !! j) (if i == j then 1 else 0) | i <- [0 .. n - 1], j <- [0 .. n - 1] ]  -- impossible: i, j < n

-- | Up to a global phase: find a nonzero entry, fit the phase, compare.
approxEqUpToPhase :: [[Complex Double]] -> [[Complex Double]] -> Bool
approxEqUpToPhase m1 m2 =
  case [ (i, j) | i <- [0 .. n - 1], j <- [0 .. n - 1], magnitude (m1 !! i !! j) > 1e-6 ] of  -- impossible: i, j < n, the size of both square matrices
    [] -> and [ magnitude (m2 !! i !! j) < 1e-6 | i <- [0 .. n - 1], j <- [0 .. n - 1] ]  -- impossible: i, j < n
    ((i, j) : _) ->
      let ph = (m2 !! i !! j) / (m1 !! i !! j)  -- impossible: i, j < n
      in magnitude ph > 1e-3 &&
         and [ approxEqC (m2 !! a !! b) (ph * (m1 !! a !! b)) | a <- [0 .. n - 1], b <- [0 .. n - 1] ]  -- impossible: a, b < n
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

-- Claims about emitted text -------------------------------------------------

-- | A named claim about the text a program compiles to.
type Expectation = (String, String -> Bool)

-- | Fail every expectation of a program the compiler refused, and say why.
failAll :: Counters -> String -> CompileError -> [Expectation] -> IO ()
failAll c nm e expectations = do
  mapM_ (\(cnm, _) -> check1 c cnm False) expectations
  putStrLn ("    " ++ nm ++ " REFUSED: " ++ showCompileError e)

-- | Compile a parsed flat program and check each expectation against its
-- text. A program that does not parse, or is refused, fails them all.
expectEmitted :: Counters -> String -> Either String (VisSpec, Prog Cyclo) -> [Expectation] -> IO ()
expectEmitted c nm parsed expectations = case parsed of
  Left e -> do
    check1 c (nm ++ " parses") False
    putStrLn ("    did not parse: " ++ e)
  Right (vis, prog) -> case compile (flatToProgram vis prog) of
    Left e -> failAll c nm e expectations
    Right txt -> mapM_ (\(cnm, p) -> check1 c cnm (p txt)) expectations

-- | The same for a program text read as its file is: the circuit and the
-- machine's leaves are also written under 'outDir', for qasm3/compile_check.py.
expectEmittedFile :: Counters -> String -> String -> [Expectation] -> IO ()
expectEmittedFile c nm src expectations = case parseFile src of
  Left e -> do
    check1 c (nm ++ " parses") False
    putStrLn ("    did not parse: " ++ e)
  Right sf -> expectEmittedTyped c nm (typedOf sf) expectations

-- | The same for a typed program built directly.
expectEmittedTyped :: Counters -> String -> Program Cyclo -> [Expectation] -> IO ()
expectEmittedTyped c nm typed expectations = case compile typed of
  Left e -> failAll c nm e expectations
  Right txt -> do
    writeFile (outDir ++ "/" ++ nm ++ ".qasm") txt
    exportLeavesOf nm typed
    mapM_ (\(cnm, p) -> check1 c cnm (p txt)) expectations

-- | A string without the spaces at either end.
trimSpaces :: String -> String
trimSpaces = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse

-- | Does the haystack hold these lines in a row, ignoring surrounding whitespace?
containsRun :: [String] -> [String] -> Bool
containsRun needle hay =
  any (\i -> map trimSpaces (take (length needle) (drop i hay)) == needle) [0 .. length hay]

-- (e): the third 'Admissible' clause -- k>=2, psi and g
-- proportional but neither a basis state -- via 'proportionalTo' directly
-- and via the fixture test/fixtures/dirty-nonbasis.s (a 2-qubit temporary
-- allocated non-basis, hit with a cancelling Swap;Swap, and dropped: the
-- certificate is exactly the allocation ray).

reclaimSiteChecks :: TP.Corpus -> Counters -> IO ()
reclaimSiteChecks corpus c = do
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
  case TP.parsed corpus "test/fixtures/dirty-nonbasis.s" of
    Left e -> do
      check1 c "dirty-nonbasis.s parses" False
      putStrLn ("    did not parse: " ++ e)
    Right (vis, prog) ->
      -- the compilation fragment requires basis-state allocations; the
      -- emitter refuses the non-basis one instead of assuming its
      -- preparation in a comment
      case compile (flatToProgram vis prog) of
        Left e -> do
          check1 c "dirty-nonbasis.s: the non-basis allocation is refused as outside the fragment"
            ("outside the compilation fragment" `isInfixOf` showCompileError e
             && "not a computational basis state" `isInfixOf` showCompileError e)
        Right _ ->
          check1 c "dirty-nonbasis.s: the non-basis allocation is refused as outside the fragment" False
  case TP.parsed corpus "test/fixtures/dirty-nonbasis-unsafe.s" of
    Left e -> do
      check1 c "dirty-nonbasis-unsafe.s parses" False
      putStrLn ("    did not parse: " ++ e)
    Right (vis, prog) ->
      case compile (flatToProgram vis prog) of
        Left e ->
          check1 c "dirty-nonbasis-unsafe.s: the non-basis allocation is refused as outside the fragment"
            ("not a computational basis state" `isInfixOf` showCompileError e)
        Right _ ->
          check1 c "dirty-nonbasis-unsafe.s: the non-basis allocation is refused as outside the fragment" False

-- (f): loans -- mcx-dirty.s (B = I, nothing
-- emitted), mcx-dirty-x.s (B = X, one U emitted), mcx-dirty-half.s (unsafe),
-- and the fixture test/fixtures/cz-loan.s (a loan hit with a CZ and no
-- correction: unsafe, the block/rest reshape does not even factor).

loanChecks :: TP.Corpus -> Counters -> IO ()
loanChecks corpus c = do
  putStrLn "(f) the loan redesign: a header `loan` as an extra input register"
  expectEmitted c "mcx-dirty.s" (TP.parsed corpus "programs/mcx-dirty.s")
    [ ("mcx-dirty.s compiles", const True)
    , ("mcx-dirty.s: B = I, nothing emitted (no U(...), no reclaim comment)"
      , \txt -> not ("U(" `isInfixOf` txt) && not ("reclaim of a" `isInfixOf` txt)
                && not ("not emitted" `isInfixOf` txt)) ]
  expectEmitted c "mcx-dirty-x.s" (TP.parsed corpus "programs/mcx-dirty-x.s")
    [ ("mcx-dirty-x.s compiles", const True)
    , ("mcx-dirty-x.s: exactly one U(...) is emitted (the reclaiming gate B = X)"
      , \txt -> length (filter ("U(" `isInfixOf`) (lines txt)) == 1) ]
  expectEmitted c "mcx-dirty-half.s" (TP.parsed corpus "programs/mcx-dirty-half.s")
    [ ("mcx-dirty-half.s compiles", const True)
    , ("mcx-dirty-half.s: drop a dropped unsafe: stays live"
      , \txt -> "dropped unsafe" `isInfixOf` txt) ]
  case TP.parsed corpus "test/fixtures/cz-loan.s" of
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

-- (g) a temporary whose safety depends on a live loan's arrival state.
-- 'computeSafety' probes every loan over its own basis, as the site definition's
-- domain [[Omega]] demands; seeding every loan at |0> instead would call the
-- first program below safe and emit no "stays live" marker, so the circuit
-- would let a caller reuse a qubit still entangled with the loan.
mixedLoanChecks :: Counters -> IO ()
mixedLoanChecks c = do
  putStrLn "(g) a temporary beside a loan: the loan is part of the site map's domain"
  expectEmitted c "temp-reads-loan" (parseProgram srcReadsLoan)
    [ ("a temporary that copies a live loan is emitted as dropped unsafe"
      , \txt -> "t dropped unsafe" `isInfixOf` txt) ]
  expectEmitted c "temp-reads-loan-back" (parseProgram srcReadsLoanBack)
    [ ("the same temporary with the copy undone is not marked unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt))
    , ("and is reclaimed by nothing, its certificate being its own |0>"
      , \txt -> not ("reclaim" `isInfixOf` txt)) ]

srcReadsLoan, srcReadsLoanBack :: String
srcReadsLoan =
  "prog temp_reads_loan (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a t;\n\
  \    drop t;\n\
  \    drop a;\n\
  \    return x\n\
  \}"
srcReadsLoanBack =
  "prog temp_reads_loan_back (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    CX a t;  CX a t;\n\
  \    drop t;\n\
  \    drop a;\n\
  \    return x\n\
  \}"

-- (h) a block of SEVERAL registers holding a loan: the site definition's clause (3) with
-- B : H_loan -> H_block (Drop.Lang.Criterion.loanResultS). A square B (the block
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
  expectEmitted c "block-two-loans-id" (parseProgram srcBlockId)
    [ ("two loans dropped as one block, B = I: nothing emitted"
      , \txt -> not ("reclaim" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt)) ]
  expectEmitted c "block-two-loans-swap" (parseProgram srcBlockSwap)
    [ ("Swap a b then drop (a,b): safe, and B = SWAP is emitted, not skipped"
      , \txt -> not ("reclaim" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt))
    , ("the reclaiming gate is SWAP^dagger = SWAP, as three CNOTs"
      , \txt -> ["cx q[1], q[2];", "ctrl @ x q[2], q[1];", "cx q[1], q[2];"]
                  `containsRun` lines (dropWhile (/= 'h') txt)) ]
  expectEmitted c "block-two-loans-hh" (parseProgram srcBlockHadHad)
    [ ("H on each of two loans: safe, and the general return gate is emitted"
      , \txt -> not ("not emitted" `isInfixOf` txt) && "U(" `isInfixOf` txt)
    , ("the square H tensor H loan factor is not called unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt)) ]
  expectEmitted c "block-loan-temp" (parseProgram srcBlockRect)
    [ ("a loan beside a fresh temporary: B = I (x) |0>, nothing emitted, no refusal"
      , \txt -> not ("not emitted" `isInfixOf` txt) && not ("reclaim" `isInfixOf` txt))
    , ("and the block is not called unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt)) ]

numericAxisChecks :: Counters -> IO ()
numericAxisChecks c = do
  -- a non-basis allocation (3/5, 4/5) is outside the compilation fragment
  -- and refused before any axis is computed; the numerical seam is reached
  -- only through basis allocations, the 'basisRotation' checks below
  mapM_ (\d -> do
    let named suffix = "non-basis allocation d=" ++ show d ++ suffix
        refused result = case result of
          Left err -> "not a computational basis state" `isInfixOf` showCompileError err
          Right _ -> False
    mapM_ (\(what, prog) -> do
      check1 c (named (" " ++ what ++ " refused by fresh compiler as outside the fragment")) (refused (compile prog))
      check1 c (named (" " ++ what ++ " refused by reuse compiler as outside the fragment")) (refused (compileReuse prog)))
      [("tiny phase", nearPhase d (1 / 10^(20 :: Int))), ("resolvable control", nearPhase d (1 / 10^(8 :: Int))), ("unchanged ray", nearPhase d 0)]) [2,4]
  mapM_ (\(name, p) -> do
    check1 c (name ++ " is well typed") (checkProgram p == Right (TReg 2))
    mapM_ (\(mode, compiler) -> check1 c (name ++ " " ++ mode ++ " finite emission")
      (case compiler p of
         Right text -> not (any (`isInfixOf` text) ["NaN", "Infinity"])
         Left _ -> False)) [("fresh", compile), ("reuse", compileReuse)])
    [("basis tiny 1e-100", basisRotation (1 / 10^(100 :: Int))),
     ("basis tiny 1e-163", basisRotation (1 / 10^(163 :: Int)))]
  mapM_ (\(mode, compiler) -> check1 c (mode ++ " underflowed nonzero axis refused by name")
    (case compiler (basisRotation (1 / 10^(400 :: Int))) of
       Left err -> "drop t: numerical reclaiming axis" `isInfixOf` showCompileError err
       Right _ -> False)) [("fresh", compile), ("reuse", compileReuse)]
  check1 c "numerically refused emission exports no expected leaf target"
    (case leavesWithExpected (basisRotation (1 / 10^(400 :: Int))) [1,0] of
       Left err -> "drop t: numerical reclaiming axis" `isInfixOf` showCompileError err
       Right _ -> False)
  where
    basisRotation t =
      let a = fromRational ((1-t*t)/(1+t*t))
          b = fromRational (2*t/(1+t*t))
      in Program [("x",2)] (SDo (StNew "t" 2 [1,0])
           (SDo (StGate [[a,negate b],[b,a]] (VVar "t"))
           (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "x")))))
    nearPhase d t =
      let z = fromRational ((1-t*t)/(1+t*t)) +
              Cyclo 2 [0,1] * fromRational (2*t/(1+t*t))
          psi = if d==2 then [3/5,4/5] else [3/5,0,4/5,0]
          ds = if d==2 then [1,z] else [1,1,z,1]
          matrix = [[if i==j then a else 0 | j <- [0..d-1]] | (i,a) <- zip [0..] ds]
      in Program [("x",2)] (SDo (StNew "t" d psi)
           (SDo (StGate matrix (VVar "t"))
           (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "x")))))

srcBlockHadHad :: String
srcBlockHadHad = unlines
  [ "prog block_hh (x : [2], loan a : [2], loan b : [2]) : [2] {"
  , "    H a; H b; drop (a, b); return x"
  , "}"
  ]

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

-- (k) a mixed block of product form: a block holding temporaries beside its
-- loans, whose block factor is B = B' (x) g~. The emitter writes B'^dagger on
-- the loan qubits and then the reclaiming reflection through psi - g~ on the
-- temporary qubits. Also here: a block factor that entangles a loan with a
-- temporary, and a loan factor on two qubits (both safe by clause (3) of the
-- site definition, both returned by the general return gate); `drop ()`, a
-- block of dimension one under clause (1), with nothing to reclaim; and a
-- tuple dropped out of allocation order (the certificate, psi and the qubit
-- list are all read in the drop's order, Drop.Lang.State.factorSplitOrd).
-- Every fixture is exported to out-typed/, so that qasm3/compile_check.py
-- simulates its circuit against the machine's expected state: the check the
-- compilation theorem stands on.
mixedProductChecks :: Counters -> IO ()
mixedProductChecks c = do
  putStrLn "(k) a mixed block of product form: B'^dagger on the loans, the reflection on the temporaries"
  mixedBlocksAreReclaimed c
  unitAndReorderedDropsAreEmitted c
  branchReturnsKeepTheirOrder c
  loanSitesGetTheirReturnGate c

-- Blocks that hold a loan beside a temporary, or several loans beside one.
mixedBlocksAreReclaimed :: Counters -> IO ()
mixedBlocksAreReclaimed c = do
  expectEmittedFile c "mixed-x-plus" srcMixedXPlus
    [ ("loan a with X, temporary t on |+>, drop (a, t): emitted, no refusal, not unsafe"
      , \txt -> not ("not emitted" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt))
    , ("two U(...) lines after the program's gates: X^dagger on a's qubit, the reflection on t's"
      , \txt -> case [ l | l <- lines (afterProgramBody txt), "U(" `isInfixOf` l ] of
                  [u1, u2] -> "q[1];" `isInfixOf` u1 && "q[2];" `isInfixOf` u2
                  _        -> False) ]
  expectEmittedFile c "mixed-plus-x-reversed" srcMixedPlusXReversed
    [ ("the same block written drop (t, a): the same two gates, loans first"
      , \txt -> not ("not emitted" `isInfixOf` txt) &&
                case [ l | l <- lines (afterProgramBody txt), "U(" `isInfixOf` l ] of
                  [u1, u2] -> "q[1];" `isInfixOf` u1 && "q[2];" `isInfixOf` u2
                  _        -> False) ]
  expectEmittedFile c "mixed-swap-plus" srcMixedSwapPlus
    [ ("two loans swapped beside a temporary on |+>: SWAP^dagger as three CNOTs, then one U on t"
      , \txt -> let body = afterProgramBody txt
                in length [ l | l <- lines body, "cx" `isInfixOf` l || "ctrl @ x" `isInfixOf` l ] == 3
                   && length [ l | l <- lines body, "U(" `isInfixOf` l ] == 1
                   && not ("not emitted" `isInfixOf` txt)) ]
  expectEmittedFile c "mixed-entangled" srcMixedEntangled
    [ ("H t; CX t a; drop (a, t): safe by the site definition's clause (3), B entangles the loan with the temporary, and the return gate is emitted"
      , \txt -> not ("not emitted" `isInfixOf` txt) && "U(" `isInfixOf` txt)
    , ("and not called unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt)) ]
  expectEmittedFile c "mixed-swap-temporary" srcMixedSwapTemporary
    [ ("Swap loan and temporary: safe, not of block-product form, returned by the general return gate"
      , \txt -> not ("not emitted" `isInfixOf` txt) && not ("reclaim of" `isInfixOf` txt))
    , ("the nonsplit Swap block is not called unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt)) ]
  expectEmittedFile c "mixed-loan-factor-two-qubits" srcMixedTwoQubitLoanFactor
    [ ("H on one of two loans beside a temporary: the loan factor is on two qubits, returned by the general return gate"
      , \txt -> not ("not emitted" `isInfixOf` txt) && "U(" `isInfixOf` txt)
    , ("and not called unsafe"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt)) ]

-- A block of dimension one, and a tuple dropped against the allocation order.
unitAndReorderedDropsAreEmitted :: Counters -> IO ()
unitAndReorderedDropsAreEmitted c = do
  expectEmittedFile c "drop-unit" srcDropUnit
    [ ("drop (): parses, compiles, and writes nothing but its comment"
      , \txt -> "drop (): nothing to reclaim" `isInfixOf` txt
                && not ("U(" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt)) ]
  expectEmittedFile c "tuple-out-of-order" srcTupleOutOfOrder
    [ ("new a@|1>, new b@|0>, X a, X b, drop (b, a): the transposition is emitted, not skipped"
      , \txt -> "ctrl @ x" `isInfixOf` afterProgramBody txt || "cx" `isInfixOf` afterProgramBody txt)
    , ("and no refusal"
      , \txt -> not ("not emitted" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt)) ]

-- A return that depends on a lift. No program file can write one (a
-- branch of the surface syntax returns exactly the registers it was
-- handed), so the term is built directly; it is a program of the language,
-- which is checked first. The circuit must measure (y, x) on one record
-- and (x, y) on the other, so the measurements sit inside the branches.
branchReturnsKeepTheirOrder :: Counters -> IO ()
branchReturnsKeepTheirOrder c = do
  check1 c "branch-return-order is a typed program: p = lift[{1}] x; if p then return (y, x) else return (x, y)"
    (checkProgram progBranchReturnOrder == Right (TTensor (TReg 2) (TReg 2)))
  expectEmittedTyped c "branch-return-order" progBranchReturnOrder
    [ ("each branch measures its own return value, in its order, and nothing is measured after the if"
      , \txt -> map trimSpaces (dropWhile (not . ("if (" `isInfixOf`)) (lines txt)) ==
                  [ "if (c[0] == 1) {"
                  , "result[0] = measure q[1];", "result[1] = measure q[0];"
                  , "} else {"
                  , "result[0] = measure q[0];", "result[1] = measure q[1];"
                  , "}" ])
    , ("result has the returned value's two bits"
      , \txt -> "bit[2] result;" `elem` lines txt) ]

-- Five loan sites: every safe block holding loans gets its return gate. The
-- simulation against expectedFinalState is qasm3/compile_check.py on these
-- files; the matrix identity T B = J is 'frameReturnChecks'.
loanSitesGetTheirReturnGate :: Counters -> IO ()
loanSitesGetTheirReturnGate c = do
  expectEmittedFile c "copy-site" srcCopySite
    [ ("the loan copied into a clean temporary and dropped as one block: safe, returned as H, CZ, H on t (the CNOT; its matrix is checked in group (n))"
      , \txt -> not ("dropped unsafe" `isInfixOf` txt) && "ctrl @ z q[0], q[1];" `isInfixOf` txt) ]
  expectEmittedFile c "phase-site" srcPhaseSite
    [ ("S on a loan beside |0>: the diagonal S^dagger"
      , \txt -> "U(0, 0, -pi/2) q[0];" `isInfixOf` txt && not ("not emitted" `isInfixOf` txt)) ]
  expectEmittedFile c "hh-loans" srcHHLoans
    [ ("H on each of two loans: two reflections are printed and the block is not called unsafe"
      , \txt -> "U(" `isInfixOf` txt && not ("dropped unsafe" `isInfixOf` txt)) ]
  expectEmittedFile c "cz-loans" srcCZLoans
    [ ("CZ on two loans (as H; CX; H): the return gate is the diagonal alone, no reflection"
      , \txt -> ("ctrl @ p(-pi) q[0], q[1];" `isInfixOf` txt || "ctrl @ p(pi) q[0], q[1];" `isInfixOf` txt)
                && not ("U(" `isInfixOf` afterCnotLine txt)) ]
  expectEmittedFile c "interleaved-site" srcInterleavedSite
    [ ("a loan between two temporaries on |0>, entangled across all three: reflections are printed, not unsafe"
      , \txt -> "U(" `isInfixOf` txt && not ("dropped unsafe" `isInfixOf` txt)) ]
  expectEmittedFile c "interleaved-site-one" srcInterleavedSiteOne
    [ ("the same with the first temporary allocated in |1>: its placement index is nonzero, reflections printed, not unsafe"
      , \txt -> "U(" `isInfixOf` txt && not ("dropped unsafe" `isInfixOf` txt)) ]

-- | The emitted text after the last line of the program's own gates: the
-- fixtures are written so that their reclaiming lines follow a marker
-- (the last statement before the drop is what the drop reclaims).
afterProgramBody :: String -> String
afterProgramBody txt = unlines (drop 1 (dropWhile (not . ("// q[0] = x" `isInfixOf`)) (lines txt)))

-- | The lines after the program's own CNOT (cz-loans: the second h).
afterCnotLine :: String -> String
afterCnotLine txt = unlines (drop 1 (dropWhile (/= "cx q[0], q[1];") (lines txt)))

-- | @prog (x : [2], y : [2]) : [2] * [2] { p = lift[{1}] x; if p then return
-- (y, x) else return (x, y) }@, as a term: the lift reads x in the basis,
-- and the record decides the order the two registers come back in.
progBranchReturnOrder :: Program Cyclo
progBranchReturnOrder = Program [("x", 2), ("y", 2)]
  (SDo (StLift "p" [1] "x")
    (SIf (BParam "p")
      (SReturn (VPair (VVar "y") (VVar "x")))
      (SReturn (VPair (VVar "x") (VVar "y")))))

branchOrderProgram :: Bool -> Surface Cyclo -> Program Cyclo
branchOrderProgram swapReturn continuation = Program [("x", 2)]
  (SDo (StNew "t1" 2 [1, 0])
  (SDo (StNew "t2" 2 [1, 0])
  (SDo (StLift "p" [1] "x")
  (SBlock (VPair (VVar "a") (VVar "b"))
     (SIf (BParam "p")
        (SReturn (VPair (VVar "t1") (VVar "t2")))
        (SReturn (if swapReturn then VPair (VVar "t2") (VVar "t1")
                               else VPair (VVar "t1") (VVar "t2"))))
     continuation))))

branchContinuation :: Surface Cyclo
branchContinuation =
  SDo (StDrop 0 (VVar "a"))
  (SDo (StNew "u" 2 [1, 0])
  (SDo (StGate [[0, 1], [1, 0]] (VVar "b"))
  (SReturn (VPair (VVar "x") (VPair (VVar "b") (VVar "u"))))))

srcMixedXPlus, srcMixedPlusXReversed, srcMixedSwapPlus, srcMixedEntangled :: String
srcMixedSwapTemporary, srcMixedTwoQubitLoanFactor, srcDropUnit, srcTupleOutOfOrder :: String
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
-- the loan-site programs (the CZ written as H; CX; H, since CZ is not a
-- parser gate)
srcCopySite, srcPhaseSite, srcHHLoans, srcCZLoans, srcInterleavedSite, srcInterleavedSiteOne :: String
srcCopySite = unlines
  [ "prog copysite (loan l : [2]) : 1 {"
  , "    new t : [2] @ |0>;"
  , "    CX l t;"
  , "    drop (l, t);"
  , "    return ()"
  , "}" ]
srcPhaseSite = unlines
  [ "prog phasesite (loan l : [2]) : 1 {"
  , "    new t : [2] @ |0>;"
  , "    S l;"
  , "    drop (l, t);"
  , "    return ()"
  , "}" ]
srcHHLoans = unlines
  [ "prog hhloans (loan a : [2], loan b : [2]) : 1 {"
  , "    H a; H b;"
  , "    drop (a, b);"
  , "    return ()"
  , "}" ]
srcCZLoans = unlines
  [ "prog czloans (loan a : [2], loan b : [2]) : 1 {"
  , "    H b; CX a b; H b;"
  , "    drop (a, b);"
  , "    return ()"
  , "}" ]
srcInterleavedSite = unlines
  [ "prog interleaved (loan l : [2]) : 1 {"
  , "    new t : [2] @ |0>;"
  , "    new u : [2] @ |0>;"
  , "    H t;"
  , "    CX t u;"
  , "    CX l u;"
  , "    drop (t, l, u);"
  , "    return ()"
  , "}" ]
srcInterleavedSiteOne = unlines
  [ "prog interleaved_one (loan l : [2]) : 1 {"
  , "    new t : [2] @ |1>;"
  , "    new u : [2] @ |0>;"
  , "    H t;"
  , "    CX t u;"
  , "    CX l u;"
  , "    drop (t, l, u);"
  , "    return ()"
  , "}" ]

srcMixedEntangled =
  "prog mixed_entangled (x : [2], loan a : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    H t;\n\
  \    CX t a;\n\
  \    drop (a, t);\n\
  \    return x\n\
  \}"
srcMixedSwapTemporary = unlines
  [ "prog mixed_swap_temporary (x : [2], loan a : [2]) : [2] {"
  , "  new t : [2] @ |0>;"
  , "  Swap a t;"
  , "  drop (a, t);"
  , "  return x"
  , "}" ]
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
--
-- The block-dimension-4 certificate needs the general clause: the
-- 'otherwise' clause of 'emitReclaim' covers every k >= 2 certificate via
-- 'emitGeneralReflectionOps' (checked numerically against 'reflectionR' in
-- 'generalReflectionChecks' below, and against a real OpenQASM 3 parser by
-- qasm3/compile_check.py on out-typed/bell-pair.qasm), so bell-pair.s
-- carries a real reclaiming circuit and no "not emitted" comment.
bellPairChecks :: TP.Corpus -> Counters -> IO ()
bellPairChecks corpus c = do
  putStrLn "(i) bell-pair.s vs bell-pair-split.s: which program a context compares"
  expectEmitted c "bell-pair.s" (TP.parsed corpus "programs/bell-pair.s")
    [ ("bell-pair.s compiles", const True)
    , ("bell-pair.s: drop (a,b) is emitted as a circuit, not a refusal comment"
      , \txt -> not ("not emitted" `isInfixOf` txt))
    , ("bell-pair.s: the general reclaiming reflection's U(...) lines are present"
      , \txt -> "U(" `isInfixOf` txt)
    , ("bell-pair.s: the reflection's negated-controlled phase flip is present"
      , \txt -> "negctrl @ z" `isInfixOf` txt) ]
  expectEmitted c "bell-pair-split.s" (TP.parsed corpus "programs/bell-pair-split.s")
    [ ("bell-pair-split.s compiles", const True)
    , ("bell-pair-split.s: drop a dropped unsafe: stays live"
      , \txt -> "a dropped unsafe" `isInfixOf` txt)
    , ("bell-pair-split.s: drop b dropped unsafe: stays live"
      , \txt -> "b dropped unsafe" `isInfixOf` txt) ]

-- (j) the general k-qubit reclaiming reflection:
-- 'emitGeneralReflectionOps qs psi g', simulated exactly as
-- 'Drop.Lang.Compile.Emit.renderOp' would print it (via 'opDense' and
-- 'Drop.Lang.State.applyGate' -- the same tensor/control machinery
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
-- qubits numbered 0..k-1 -- exactly 'opDense' fed to 'Drop.Lang.State.applyGate'
-- at each step, column by column from every basis vector.
simulateOps :: Int -> [Op] -> [[Complex Double]]
simulateOps k ops =
  [ [ cols !! j !! i | j <- [0 .. d - 1] ] | i <- [0 .. d - 1] ]  -- impossible: cols has d columns of d entries each
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
  let thin = map (:+ 0) [0.6, 6e-14, 0.8, 8e-14]
  check1 c "a four-support axis with tiny components uses the general reflection"
    (case emitTwoSupportReflectionOps [0, 1] (ketZero 2) thin of
       Nothing -> True
       Just _ -> False)
  checkOne "four-support certificate with tiny components" 2 (ketZero 2) thin
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

-- (k) the two-support short form: 'emitTwoSupportReflectionOps' against
-- 'reflectionR', on top of what 'generalReflectionChecks' covers for
-- 'emitGeneralReflectionOps'. It takes four of the fixed vectors of (j), and
-- (1,0,0,-1)/sqrt2, under the same pairing (psi = |0..0>, g = the vector), but
-- here the pairing is also a
-- claim about the support of w = psi - g~, and by hand only four of the five
-- are two-support under it: Bell (w on {0,3}), (1,i,0,0)/sqrt2 (w on {0,1}),
-- the k=3 GHZ vector (w on {0,7}) and (1,0,0,-1)/sqrt2 (w on {0,3}). The
-- vector (0,1,1,0)/sqrt2 is not: psi_0 = 1 and g_0 = 0, so w_0 = 1, and w_1
-- and w_2 are both (generically) nonzero, giving a three-support w. That case
-- is checked as a required decline (Nothing). Then, for k in {2, 3}, 20
-- seeded random cases of each of two shapes: 'zeroPsiLoop' (psi = |0..0>, g
-- random two-support on {0, j} for a random j, so w = psi - g~ is supported
-- inside {0, j}) and 'bothTwoSupportLoop' (a random non-basis psi and g both
-- supported on the same random pair {p, q} with p, q /= 0, so w is confined
-- to {p, q}). Every case asserts both that 'emitTwoSupportReflectionOps' is
-- the clause taken (it returns 'Just', not a silent decline into the caller's
-- fallback) and that its simulated circuit reproduces 'reflectionR psi g'
-- entrywise at 1e-9, with no phase fit: the same 'matClose' and 'simulateOps'
-- that (j) uses, so the check is on the object 'renderOp' would print.
twoSupportReflectionChecks :: Counters -> IO ()
twoSupportReflectionChecks c = do
  putStrLn "(k) the two-support short form: emitTwoSupportReflectionOps vs reflectionR"
  twoSupportFixedChecks c
  twoSupportRandomChecks c

-- The fixed vectors: four take the short form, one must decline.
twoSupportFixedChecks :: Counters -> IO ()
twoSupportFixedChecks c = do
  let s2 = 1 / sqrt 2 :: Double
      bell = [s2 :+ 0, 0 :+ 0, 0 :+ 0, s2 :+ 0]
      case1 = [s2 :+ 0, 0 :+ s2, 0 :+ 0, 0 :+ 0]
      case2 = [0 :+ 0, s2 :+ 0, s2 :+ 0, 0 :+ 0]
      caseMinus = [s2 :+ 0, 0 :+ 0, 0 :+ 0, negate s2 :+ 0]
      ghz = [s2 :+ 0, 0, 0, 0, 0, 0, 0, s2 :+ 0]
  checkShortForm c "Bell (1,0,0,1)/sqrt2, psi=|00>" 2 (ketZero 2) bell
  checkShortForm c "(1,i,0,0)/sqrt2, psi=|00>" 2 (ketZero 2) case1
  checkShortFormDeclines c "(0,1,1,0)/sqrt2, psi=|00>: w is 3-support, short form must decline" 2 (ketZero 2) case2
  checkShortForm c "k=3 GHZ certificate, psi=|000>" 3 (ketZero 3) ghz
  checkShortForm c "(1,0,0,-1)/sqrt2, psi=|00>" 2 (ketZero 2) caseMinus

-- Seeded random two-support cases, 20 for each of k = 2, 3 and each shape.
twoSupportRandomChecks :: Counters -> IO ()
twoSupportRandomChecks c =
  forM_ [2, 3 :: Int] $ \k -> do
    let d = 2 ^ k :: Int
    zeroPsiLoop c k d ("k=" ++ show k ++ " psi=|0..0>, random 2-support g #")
      (Rng (0xA24BAED4963EE407 + fromIntegral k)) (20 :: Int)
    bothTwoSupportLoop c k d ("k=" ++ show k ++ " random 2-support psi and g, same pair #")
      (Rng (0x9FB21C651E98DF25 + fromIntegral k)) (20 :: Int)

-- | The short form is taken for these arguments, and its circuit is R.
checkShortForm :: Counters -> String -> Int -> [Complex Double] -> [Complex Double] -> IO ()
checkShortForm c nm k psi g = case emitTwoSupportReflectionOps [0 .. k - 1] psi g of
  Nothing -> check1 c (nm ++ ": the two-support clause is taken") False
  Just ops ->
    let r = reflectionR psi g
        sim = simulateOps k ops
    in do
      check1 c (nm ++ ": the two-support clause is taken") True
      check1 c (nm ++ ": simulated short-form circuit == reflectionR entrywise at 1e-9")
        (matClose 1e-9 sim r)

-- | The short form declines these arguments.
checkShortFormDeclines :: Counters -> String -> Int -> [Complex Double] -> [Complex Double] -> IO ()
checkShortFormDeclines c nm k psi g = case emitTwoSupportReflectionOps [0 .. k - 1] psi g of
  Nothing -> check1 c nm True
  Just _  -> check1 c nm False

-- | The vector of length n that is vi at index i, vj at index j and zero elsewhere.
embed2 :: Int -> Int -> Int -> Complex Double -> Complex Double -> [Complex Double]
embed2 n i j vi vj = [ if idx == i then vi else if idx == j then vj else 0 | idx <- [0 .. n - 1] ]

-- | A pseudo-random index in lo..hi.
nextIdx :: Int -> Int -> Rng -> (Int, Rng)
nextIdx lo hi rng =
  let (w, rng') = nextW64 rng
      spn = hi - lo + 1
  in (lo + fromIntegral (w `mod` fromIntegral spn), rng')

-- | Two different pseudo-random indices in lo..hi.
nextDistinctPair :: Int -> Int -> Rng -> ((Int, Int), Rng)
nextDistinctPair lo hi rng0 =
  let (p, rng1) = nextIdx lo hi rng0
      (q0, rng2) = nextIdx lo (hi - 1) rng1
      q = if q0 >= p then q0 + 1 else q0
  in ((p, q), rng2)

-- | n cases: psi = |0..0> and g random on {0, j}.
zeroPsiLoop :: Counters -> Int -> Int -> String -> Rng -> Int -> IO ()
zeroPsiLoop _ _ _ _ _ 0 = return ()
zeroPsiLoop c k d nm rng n =
  let (j, rng1) = nextIdx 1 (d - 1) rng
      (cs, rng2) = randomUnitVec 2 rng1
      g = embed2 d 0 j (cs !! 0) (cs !! 1)  -- impossible: cs came from randomUnitVec 2, so it has two entries
  in do
    checkShortForm c (nm ++ show n) k (ketZero k) g
    zeroPsiLoop c k d nm rng2 (n - 1)

-- | n cases: psi and g random on the same pair {p, q}.
bothTwoSupportLoop :: Counters -> Int -> Int -> String -> Rng -> Int -> IO ()
bothTwoSupportLoop _ _ _ _ _ 0 = return ()
bothTwoSupportLoop c k d nm rng n =
  let ((p, q), rng1) = nextDistinctPair 1 (d - 1) rng
      (pv, rng2) = randomUnitVec 2 rng1
      (gv, rng3) = randomUnitVec 2 rng2
      psi = embed2 d p q (pv !! 0) (pv !! 1)  -- impossible: pv came from randomUnitVec 2
      g   = embed2 d p q (gv !! 0) (gv !! 1)  -- impossible: gv came from randomUnitVec 2
  in do
    checkShortForm c (nm ++ show n) k psi g
    bothTwoSupportLoop c k d nm rng3 (n - 1)

-- (l) the fragment's conditions on drops, and the block factor's unit
-- scalar. A loan's block factor is fixed only up to a unit scalar, so its
-- shape is tested after 'normaliseSquareIso' divides out the phase of the
-- first nonzero entry of its first column: two loans swapped beside
-- diag(i,1) on another register have B read as i SWAP, which is emitted and
-- not skipped. Both programs are exported to out-typed/ for
-- qasm3/compile_check.py. A loan dropped after a lift or an if, and an input
-- not marked loan dropped at a site that is safe, with a nonzero site map, on
-- some record, are refused by 'fragmentSafety' with the drop they name; an
-- unsafe drop of such an input emits no gate and still compiles, also when
-- the site map is zero on another record, which is not counted as safe
-- (srcUnmarkedUnreach).
fragmentDropChecks :: Counters -> IO ()
fragmentDropChecks c = do
  putStrLn "(l) the fragment's conditions on drops, and the block factor's unit scalar"
  loanPhaseChecks c
  refusedDropChecks c
  branchResourceChecks c

-- A loan factor read up to a unit scalar is still emitted.
loanPhaseChecks :: Counters -> IO ()
loanPhaseChecks c = do
  expectEmittedFile c "loan-phase-swap" srcLoanPhaseSwap
    [ ("two loans swapped beside diag(i,1) on x: B is read as i SWAP and emitted, not skipped"
      , \txt -> not ("not emitted" `isInfixOf` txt) && not ("dropped unsafe" `isInfixOf` txt))
    , ("the program's swap, then the reclaiming SWAP as three CNOTs"
      , \txt -> ["swap q[1], q[2];", "cx q[1], q[2];", "ctrl @ x q[2], q[1];", "cx q[1], q[2];"]
                  `containsRun` lines txt) ]
  expectEmittedFile c "loan-phase-identity" srcLoanPhaseIdentity
    [ ("two untouched loans beside diag(i,1) on x: B is read as i I, and nothing is emitted"
      , \txt -> not ("reclaim" `isInfixOf` txt) && not ("not emitted" `isInfixOf` txt)) ]

-- Drops the fragment cannot express are refused with the drop they name;
-- an unsafe drop still compiles and stays live.
refusedDropChecks :: Counters -> IO ()
refusedDropChecks c = do
  refusesDrop c "a loan dropped after an if, with no lift, is refused" srcLoanAfterIf ["a"] loanMsg
  refusesDrop c "an unsafe loan drop after an if is refused too" srcLoanAfterIfUnsafe ["a"] loanMsg
  refusesDrop c "a loan dropped after a lift is refused" srcLoanAfterLift ["a"] loanMsg
  refusesDrop c "a safe drop of an input not marked loan is refused" srcUnmarkedSafe ["x"] inputMsg
  refusesDrop c "a safe pair holding an input not marked loan is refused" srcUnmarkedPair ["x", "u"] inputMsg
  case parseFile srcUnmarkedUnsafe of
    Left e -> check1 c "unmarked-unsafe parses" False >> putStrLn ("    did not parse: " ++ e)
    Right sf -> case compile (typedOf sf) of
      Left e -> do
        check1 c "an unsafe drop of an input not marked loan still compiles" False
        putStrLn ("    REFUSED: " ++ showCompileError e)
      Right txt -> check1 c "an unsafe drop of an input not marked loan still compiles, and stays live"
                     ("x dropped unsafe: stays live" `isInfixOf` txt)
  case parseFile srcUnmarkedUnreach of
    Left e -> check1 c "unmarked-unreach parses" False >> putStrLn ("    did not parse: " ++ e)
    Right sf -> case compile (typedOf sf) of
      Left e -> do
        check1 c "an input not marked loan, unsafe where reachable and zero elsewhere, is not refused" False
        putStrLn ("    REFUSED: " ++ showCompileError e)
      Right txt -> check1 c "an input not marked loan, unsafe where reachable and zero elsewhere, is not refused"
                     ("x dropped unsafe" `isInfixOf` txt)
  where
    loanMsg = "it drops a loan after a lift or an if"
    inputMsg = "it drops an input not marked loan"

-- | The program is refused as a drop outside the fragment, naming these
-- registers and a reason containing the message.
refusesDrop :: Counters -> String -> String -> [String] -> String -> IO ()
refusesDrop c nm src names msg = case parseFile src of
  Left e -> check1 c (nm ++ ": parses") False >> putStrLn ("    did not parse: " ++ e)
  Right sf -> case compile (typedOf sf) of
    Left (DropOutsideFragment xs why) -> check1 c nm (xs == names && msg `isInfixOf` why)
    Left e -> check1 c nm False >> putStrLn ("    refused otherwise: " ++ showCompileError e)
    Right _ -> check1 c nm False >> putStrLn "    compiled"

-- Arms of an `if` that disagree on the resources they take are refused.
branchResourceChecks :: Counters -> IO ()
branchResourceChecks c = do
  check1 c "the branch-dependent resource example is well typed"
    (checkProgram (branchOrderProgram True branchContinuation) ==
       Right (TTensor (TReg 2) (TTensor (TReg 2) (TReg 2))))
  check1 c "fresh compilation refuses differing expanded resource names"
    (resourceRefused (compile (branchOrderProgram True branchContinuation)))
  check1 c "reuse refuses a wire that would alias a live register"
    (resourceRefused (compileReuse (branchOrderProgram True branchContinuation)))
  check1 c "differing expanded drops name both register statements"
    (case compileReuse (branchOrderProgram True branchContinuation) of
       Left (OutsideFragment msg) ->
         msg == "resource layout differs between if arms: StDrop 0 (VVar \"t1\") versus StDrop 0 (VVar \"t2\")"
       _ -> False)
  check1 c "matching branch resources still compile with reuse"
    (case compileReuse (branchOrderProgram False branchContinuation) of
       Right _ -> True
       Left _ -> False)
  check1 c "a branch-dependent lift target is refused too"
    (resourceRefused (compile (branchOrderProgram True
      (SDo (StLift "q" [0] "a")
        (SReturn (VPair (VVar "x") (VPair (VVar "a") (VVar "b"))))))))
  where
    resourceRefused (Left (OutsideFragment msg)) =
      "resource layout differs between if arms:" `isInfixOf` msg
    resourceRefused _ = False

srcLoanPhaseSwap, srcLoanPhaseIdentity, srcLoanAfterIf, srcLoanAfterIfUnsafe, srcLoanAfterLift :: String
srcUnmarkedSafe, srcUnmarkedPair, srcUnmarkedUnsafe, srcUnmarkedUnreach :: String
srcLoanPhaseSwap =
  "prog loan_phase_swap (loan a : [2], loan b : [2], x : [2]) : [2] {\n\
  \    diag x (i, 1);\n\
  \    Swap a b;\n\
  \    drop (a, b);\n\
  \    return x\n\
  \}"
srcLoanPhaseIdentity =
  "prog loan_phase_identity (loan a : [2], loan b : [2], x : [2]) : [2] {\n\
  \    diag x (i, 1);\n\
  \    drop (a, b);\n\
  \    return x\n\
  \}"
srcLoanAfterIf =
  "prog loan_after_if (loan a : [2], x : [2]) : [2] {\n\
  \    if 1 { X a; } else { X a; }\n\
  \    drop a;\n\
  \    return x\n\
  \}"
srcLoanAfterIfUnsafe =
  "prog loan_after_if_unsafe (loan a : [2], x : [2]) : [2] {\n\
  \    if 0 { CX a x; } else { CX a x; }\n\
  \    drop a;\n\
  \    return x\n\
  \}"
srcLoanAfterLift =
  "prog loan_after_lift (loan a : [2], x : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    H t;\n\
  \    p = lift[{0}] t;\n\
  \    X a;\n\
  \    drop a;\n\
  \    drop t;\n\
  \    return x\n\
  \}"
srcUnmarkedSafe =
  "prog unmarked_safe (x : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    Swap x t;\n\
  \    X x;\n\
  \    drop x;\n\
  \    return t\n\
  \}"
srcUnmarkedPair =
  "prog unmarked_pair (x : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    new u : [2] @ |0>;\n\
  \    Swap x t;\n\
  \    X u;\n\
  \    drop (x, u);\n\
  \    return t\n\
  \}"
srcUnmarkedUnsafe =
  "prog unmarked_unsafe (x : [2]) : [2] {\n\
  \    new t : [2] @ |0>;\n\
  \    X x;\n\
  \    drop x;\n\
  \    return t\n\
  \}"
-- The drop of x is unsafe on the record on which
-- the lift keeps t, and its site map is zero on the other record.
srcUnmarkedUnreach =
  "prog unmunreach (x : [2]) : 1 {\n\
  \    new t : [2] @ |0>;\n\
  \    p = lift[{0}] t;\n\
  \    drop x;\n\
  \    drop t;\n\
  \    return ()\n\
  \}"

-- | One pooling case: its name, its program text, what the allocation
-- report must contain, what the reuse circuit must contain, and what it
-- must not.
type FifoCase = (String, String, [String], [String], [String])

fifoCases :: [FifoCase]
fifoCases = fifoQueueCases ++ fifoUnpooledCases ++ fifoSiteCases

-- Freed qubits are served first in, first out, and by width.
fifoQueueCases :: [FifoCase]
fifoQueueCases =
  [ ( "fifo-tuple-order"
    , unlines [ "prog w1 (x : [2]) : [2] {"
              , "    new t : [2] @ |0>; new u : [2] @ |0>;"
              , "    drop (u, t);"
              , "    new v : [2] @ |1>; new w : [2] @ |0>;"
              , "    drop (v, w); return x"
              , "}" ]
      -- u's qubit (2) is queued before t's (1): v gets 2, w gets 1; v is X-prepared on q[2]
    , [ "\"reuseQubits\":3", "\"name\":\"v\",\"kind\":\"temporary\",\"fresh\":[3],\"reuse\":[2]"
      , "\"name\":\"w\",\"kind\":\"temporary\",\"fresh\":[4],\"reuse\":[1]" ]
    , [ "x q[2];" ], [ "dropped unsafe", "not emitted" ] )
  , ( "fifo-mismatched-width"
    , unlines [ "prog w2 (x : [2]) : [2] {"
              , "    new t : [2] @ |0>; drop t;"
              , "    new u : [4] @ |1>; drop u; return x"
              , "}" ]
      -- one queued qubit (1) and one fresh (2); |1> on [4] sets the low (second) qubit
    , [ "\"reuseQubits\":3", "\"name\":\"u\",\"kind\":\"temporary\",\"fresh\":[2,3],\"reuse\":[1,2]" ]
    , [ "x q[2];" ], [ "x q[1];", "dropped unsafe" ] )
  ]

-- An unsafe temporary, and a returned loan block, are never pooled.
fifoUnpooledCases :: [FifoCase]
fifoUnpooledCases =
  [ ( "unsafe-temporary-not-pooled"
    , unlines [ "prog w3 (x : [2]) : [2] {"
              , "    new t : [2] @ |0>; CX x t; drop t;"
              , "    new u : [2] @ |0>; drop u; return x"
              , "}" ]
    , [ "\"reuseQubits\":3", "\"name\":\"u\",\"kind\":\"temporary\",\"fresh\":[2],\"reuse\":[2]" ]
    , [ "t dropped unsafe" ], [] )
  , ( "returned-loan-block-not-pooled"
    , unlines [ "prog w4 (x : [2], loan a : [2], loan b : [2]) : [2] {"
              , "    H a; H b; drop (a, b);"
              , "    new t : [2] @ |0>; drop t; return x"
              , "}" ]
      -- the H (x) H loan block gets its return gate, but a
      -- returned loan goes back to the caller: its qubits are never served to t
    , [ "\"reuseQubits\":4", "\"name\":\"t\",\"kind\":\"temporary\",\"fresh\":[3],\"reuse\":[3]" ]
    , [ "U(" ], [ "not emitted", "dropped unsafe" ] )
  ]

-- Sites whose reclaiming gates differ by record are pooled; loans dropped one at a time emit a U at each site.
fifoSiteCases :: [FifoCase]
fifoSiteCases =
  [ ( "teleport-twice-two-pooled-sites"
    , unlines [ "prog teleport_twice (b : [2]) : [2] {"
              , "    new m : [2] @ |0>;  H m;"
              , "    new a : [2] @ |0>;  H a;  CX a b;"
              , "    CX m a;  H m;"
              , "    z = lift[{0}] m;  w = lift[{0}] a;"
              , "    if w {} else { X b; }"
              , "    if z {} else { Z b; }"
              , "    drop m;  drop a;"
              , "    new m2 : [2] @ |0>;  H m2;"
              , "    new a2 : [2] @ |0>;  H a2;  CX a2 b;"
              , "    CX m2 a2;  H m2;"
              , "    z2 = lift[{0}] m2;  w2 = lift[{0}] a2;"
              , "    if w2 {} else { X b; }"
              , "    if z2 {} else { Z b; }"
              , "    drop m2;  drop a2;"
              , "    return b"
              , "}" ]
      -- teleportation twice: both sites of the first teleport are pooled
      -- although their reclaiming gates differ by record, and the second
      -- teleport's two allocations are served from them: five qubits fresh, three with
      -- reuse (the two served wires are the saving)
    , [ "\"freshQubits\":5", "\"reuseQubits\":3" ]
    , [], [ "dropped unsafe", "not emitted" ] )
  , ( "split-drops-hh-control"
    , unlines [ "prog w5 (x : [2], loan a : [2], loan b : [2]) : [2] {"
              , "    H a; H b; drop a; drop b; return x"
              , "}" ]
      -- dropping the loans one at a time emits a U at each site
    , [] , [ "U(" ], [ "not emitted", "dropped unsafe" ] )
  ]

fifoPoolChecks :: Counters -> IO ()
fifoPoolChecks c = mapM_ one fifoCases
  where
    one (nm, src, inReport, inReuse, notInReuse) = case parseProgram src of
      Left _ -> check1 c (nm ++ " parses") False
      Right (vis, p) -> do
        let prog = flatToProgram vis p
        check1 c (nm ++ " fresh compilation succeeds")
          (case compile prog of Right _ -> True; Left _ -> False)
        check1 c (nm ++ " exact FIFO allocation")
          (case allocationReport prog of Right rep -> all (`isInfixOf` rep) inReport; Left _ -> False)
        check1 c (nm ++ " emitted pool behavior")
          (case compileReuse prog of
             Right txt -> all (`isInfixOf` txt) inReuse && not (any (`isInfixOf` txt) notInReuse)
             Left _ -> False)

nestedResourceProgram :: Program Cyclo
nestedResourceProgram = Program [("x",2)]
  (foldr SDo rest [StNew n 2 [1,0] | n <- ["a","b","c","d"]])
  where
    pair a b = VPair (VVar a) (VVar b)
    choose a b = SIf (BParam "p") (SReturn (pair a b)) (SReturn (pair b a))
    rest = SDo (StLift "p" [1] "x")
      (SBlock (pair "y" "z") (choose "a" "b")
        (SDo (StDrop 0 (VVar "y"))
          (SBlock (pair "u" "w") (choose "c" "d")
            (SDo (StDrop 1 (VVar "u"))
              (SReturn (VPair (VVar "x") (pair "z" "w")))))))

nestedResourceChecks :: Counters -> IO ()
nestedResourceChecks c = do
  check1 c "nested resource witness is well typed"
    (checkProgram nestedResourceProgram == Right (TTensor (TReg 2) (TTensor (TReg 2) (TReg 2))))
  mapM_ (\(mode,compiler) -> check1 c (mode ++ " names continuation-first failing join")
    (case compiler nestedResourceProgram of
       Left (OutsideFragment msg) -> msg == "resource layout differs between if arms: StDrop 1 (VVar \"c\") versus StDrop 1 (VVar \"d\")"
       _ -> False)) [("fresh",compile),("reuse",compileReuse)]
  case parseProgram "prog r (x : [2]) : [2] { new t : [2] @ |0>; X t; drop t; new u : [2] @ |0>; CX x u; CX x u; drop u; return x }" of
    Left _ -> check1 c "accepted reuse bridge parses" False
    Right (vis,p) -> do
      let prog = flatToProgram vis p
      check1 c "accepted reuse bridge has fresh width 3 and reused width 2"
        (case allocationReport prog of
           Right rep -> all (`isInfixOf` rep) ["\"freshQubits\":3", "\"reuseQubits\":2"]
           Left _ -> False)
      check1 c "accepted reuse bridge emits a pool release"
        (case compileReuse prog of Right txt -> "pool site 0: t" `isInfixOf` txt; Left _ -> False)

-- A block is a set even when a caller constructs the typed syntax directly.
liftBlockChecks :: Counters -> IO ()
liftBlockChecks c = do
  forM_ [[1,1], [1,2,1]] $ \s -> do
    let prog = block s
    check1 c ("duplicate lift block " ++ show s ++ " fails typing")
      (checkProgram prog == Left (BadLiftBlock "w"))
    forM_ [("fresh",compile), ("reuse",compileReuse)] $ \(mode,compiler) ->
      check1 c (mode ++ " refuses duplicate lift block " ++ show s)
        (case compiler prog of Left (NotWellTyped _) -> True; _ -> False)
  check1 c "distinct unsorted lift block remains typed"
    (checkProgram (block [2,1]) == Right (TReg 4))
  forM_ [("fresh",compile), ("reuse",compileReuse)] $ \(mode,compiler) ->
    check1 c (mode ++ " emits distinct unsorted lift block")
      (case compiler (block [2,1]) of Right _ -> True; _ -> False)
  where
    block s = Program [("w",4)] (SDo (StLift "p" s "w") (SReturn (VVar "w"))) :: Program Cyclo

-- Empty circuits need no qubit declaration. A scalar gate on () keeps its
-- phase without selecting a target, in either allocation mode.
emptyAndScalarChecks :: Counters -> IO ()
emptyAndScalarChecks c = do
  let empty = Program [] (SReturn VUnit) :: Program Cyclo
      scalar z = Program [("x", 2)]
        (SDo (StGate [[z]] VUnit) (SReturn (VVar "x"))) :: Program Cyclo
      noQubits txt = not ("qubit[" `isInfixOf` txt)
      phaseKept txt = "gphase(pi/2);" `isInfixOf` txt
      noPhase txt = not ("gphase(" `isInfixOf` txt)
  expectEmittedFile c "empty-program" "prog empty () : 1 { return () }"
    [("empty program emits no quantum declaration", noQubits)]
  expectEmittedTyped c "scalar-global-phase" (scalar iC)
    [("scalar i on () emits a global phase", phaseKept)]
  expectEmittedTyped c "scalar-identity" (scalar 1)
    [("scalar identity on () emits no gate", noPhase)]
  forM_ [("empty program", empty, noQubits),
         ("scalar i", scalar iC, phaseKept),
         ("scalar identity", scalar 1, noPhase)] $ \(name, prog, expected) ->
    check1 c ("reuse: " ++ name ++ " has valid complete output")
      (case compileReuse prog of
         Right txt -> length txt > 0 && expected txt
         Left _ -> False)

main :: IO ()
main = do
  corpus <- TP.readFiles (corpusFiles ++ fixtureFiles)
  c <- newCounters
  compileCorpus corpus c
  mapM_ (exportLeaves corpus) corpusFiles
  reflectionChecks c
  reclaimSiteChecks corpus c
  loanChecks corpus c
  mixedLoanChecks c
  blockLoanChecks c
  numericAxisChecks c
  mixedProductChecks c
  fragmentDropChecks c
  fifoPoolChecks c
  nestedResourceChecks c
  liftBlockChecks c
  emptyAndScalarChecks c
  bellPairChecks corpus c
  generalReflectionChecks c
  twoSupportReflectionChecks c
  frameReturnChecks c
  report c

-- (n) the return gate at a safe site holding loans: the printed operations
-- simulate to 'frameReturnMatrix', that matrix is unitary, and it carries
-- every column of B to the matching column of J.
frameReturnChecks :: Counters -> IO ()
frameReturnChecks c = do
  putStrLn "(n) the return gate T with T B = J: emitFrameReturnOps vs frameReturnMatrix, unitarity, T B = J"
  placementChecks c
  fixedFrameChecks c
  nearOrthogonalFrameChecks c
  czReturnIsDiagonal c
  forM_ [(2, 1), (2, 2), (2, 4), (3, 2), (3, 4), (3, 8)] $ \(k, m) ->
    randomFrameLoop c k m ("k=" ++ show k ++ " m=" ++ show m ++ " random isometry #")
               (Rng (0xA0761D6478BD642F + fromIntegral (8 * k + m))) (12 :: Int)

-- | The i-th basis vector of dimension n.
unitVector :: Int -> Int -> [Complex Double]
unitVector i n = [ if j == i then 1 :+ 0 else 0 :+ 0 | j <- [0 .. n - 1] ]

-- The placement of J e_l when loans and temporaries interleave: registers
-- (t:[2] temporary, l:[2] loan, u:[2] temporary), t allocated in |1>, u in
-- |0>, so t0 = 2 (digits 1,0); loan index l goes to the middle digit.
placementChecks :: Counters -> IO ()
placementChecks c = do
  check1 c "placementIndex interleaves the loan digit between the temporaries' digits"
    ([ placementIndex [(2, False), (2, True), (2, False)] 2 l | l <- [0, 1] ] == [4, 6])
  check1 c "placementIndex with loans first and a four-level temporary in |3>"
    ([ placementIndex [(2, True), (4, False)] 3 l | l <- [0, 1] ] == [3, 7])

-- The four sites of the loan-site programs, each with its B and the columns J.
fixedFrameChecks :: Counters -> IO ()
fixedFrameChecks c = do
  let e = unitVector
      -- the copy site, qubits (l, t): B|b> = |b>|b>, J|b> = |b>|0>
      copyB = [e 0 4, e 3 4]
      -- the phase site: S on the loan beside |0>: columns e_0 and i e_2
      phaseB = [e 0 4, map (* (0 :+ 1)) (e 2 4)]
      -- H (x) H on two loans, square: column l has entries (-1)^{popcount(j & l)} / 2
      hhB = [ [ (if even (popCount2 (j .&. l)) then 0.5 else -0.5) :+ 0 | j <- [0 .. 3 :: Int] ] | l <- [0 .. 3 :: Int] ]
      popCount2 x = length [ () | b <- [0, 1 :: Int], (x `shiftR` b) .&. 1 == 1 ]
  checkFrame c "copy site, B = [e0 e3], J = [e0 e2]" 2 copyB [0, 2]
  check1 c "copy site: the return gate is CNOT (control the loan, target the temporary)"
    (matClose 1e-9 (frameReturnMatrix copyB [0, 2]) [e 0 4, e 1 4, e 3 4, e 2 4])
  checkFrame c "phase site, B = S (x) |0>" 2 phaseB [0, 2]
  checkFrame c "H (x) H on two loans" 2 hhB [0, 1, 2, 3]
  checkFrame c "CZ on two loans" 2 czFrameB [0, 1, 2, 3]

-- | The columns of B for CZ on two loans: the identity with the last one negated.
czFrameB :: [[Complex Double]]
czFrameB = [unitVector 0 4, unitVector 1 4, unitVector 2 4, map negate (unitVector 3 4)]

-- The return gate of CZ on two loans is its diagonal alone.
czReturnIsDiagonal :: Counters -> IO ()
czReturnIsDiagonal c =
  check1 c "CZ on two loans: no reflection, the diagonal alone"
    (case emitFrameReturnOps [0, 1] czFrameB [0, 1, 2, 3] of
       Just ops -> all isPhaseOp ops
       Nothing  -> False)
  where
    isPhaseOp op = case op of { OpP {} -> True; _ -> False }

-- An exactly orthogonal rational rotation must not fail the numerical return
-- check because subtracting a nearby basis vector loses precision.
nearOrthogonalFrameChecks :: Counters -> IO ()
nearOrthogonalFrameChecks c = do
  let nearA = 4000008000003 / 4000008000005 :: Double
      nearC = 4000004 / 4000008000005 :: Double
      nearB = map (map (:+ 0))
        [[nearA, 0, nearC, 0], [0, nearA, 0, nearC],
         [-nearC, 0, nearA, 0], [0, -nearC, 0, nearA]]
      phaseNearB = zipWith (\scale col -> map (* scale) col)
        [0 :+ 1, 0.6 :+ 0.8, (-1) :+ 0, 0 :+ (-1)] nearB
  checkFrame c "near-permutation restores both loans" 2 nearB [0, 1, 2, 3]
  checkFrame c "complex-phase near-aligned frame" 2 phaseNearB [0, 1, 2, 3]
  checkFrame c "permuted-target rectangular frame" 2 (take 2 phaseNearB) [2, 0]

-- | The return gate T for these columns B and placements J on k qubits is
-- unitary, carries B to J, is what the emitted operations simulate to, and
-- passes the compiler's own residual check.
checkFrame :: Counters -> String -> Int -> [[Complex Double]] -> [Int] -> IO ()
checkFrame c nm k bCols jIdx =
  let t = frameReturnMatrix bCols jIdx
      n = 2 ^ k :: Int
      tb = [ [ sum (zipWith (*) row b) | row <- t ] | b <- bCols ]
      eye = [ [ if i == j then 1 :+ 0 else 0 :+ 0 | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
      tDag = [ [ conjugate (t !! j !! i) | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]  -- impossible: t is n x n
      ttDag = [ [ sum [ (t !! i !! l) * (tDag !! l !! j) | l <- [0 .. n - 1] ] | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]  -- impossible: t and tDag are n x n
  in do
    check1 c (nm ++ ": T is unitary at 1e-9") (matClose 1e-9 ttDag eye)
    check1 c (nm ++ ": T B = J entrywise at 1e-9")
      (and [ matClose 1e-9 [col] [unitVector j n] | (col, j) <- zip tb jIdx ])
    case emitFrameReturnOps [0 .. k - 1] bCols jIdx of
      Nothing  -> check1 c (nm ++ ": emitFrameReturnOps emits") False
      Just ops -> do
        check1 c (nm ++ ": every printed angle is finite")
          (all opIsFinite ops)
        check1 c (nm ++ ": simulated circuit == frameReturnMatrix entrywise at 1e-9")
          (matClose 1e-9 (simulateOps k ops) t)
        check1 c (nm ++ ": the emitted operations pass the compiler's own residual check")
          (emittedReturnResidualOK k ops bCols jIdx)
        check1 c (nm ++ ": the residual check rejects the circuit without its diagonal or last gate")
          (null ops || not (emittedReturnResidualOK k (init ops) bCols jIdx)
                    || isIdentityOp (last ops))

-- | Dropping a gate within 2e-9 of the identity need not be detected at 1e-9.
isIdentityOp :: Op -> Bool
isIdentityOp op = case op of
  OpP t _ _     -> abs t <= 2e-9
  OpU t _ _ _ _ -> abs t <= 2e-9
  _             -> False

-- | No printed angle is NaN or infinite.
opIsFinite :: Op -> Bool
opIsFinite op = case op of
  OpU t p l _ _ -> all (\x -> not (isNaN x || isInfinite x)) [t, p, l]
  OpP t _ _     -> not (isNaN t || isInfinite t)
  _             -> True

-- | n random n x m isometries (by Gram-Schmidt on random unit vectors) with
-- random injective placements, each checked as a frame.
randomFrameLoop :: Counters -> Int -> Int -> String -> Rng -> Int -> IO ()
randomFrameLoop _ _ _ _ _ 0 = return ()
randomFrameLoop c k m nm rng n = do
  let d = 2 ^ k :: Int
      (cols, rng1) = gramSchmidt d m rng []
      (jIdx, rng2) = pickDistinct d m rng1 []
  checkFrame c (nm ++ show n) k cols jIdx
  randomFrameLoop c k m nm rng2 (n - 1)

-- | m orthonormal random vectors of dimension d.
gramSchmidt :: Int -> Int -> Rng -> [[Complex Double]] -> ([[Complex Double]], Rng)
gramSchmidt _ 0 rng acc = (reverse acc, rng)
gramSchmidt d m rng acc =
  let (v, rng') = randomUnitVec d rng
      proj u = let ip = sum (zipWith (\a b -> conjugate a * b) u v) in map (* ip) u
      w = foldl (\x u -> zipWith (-) x (proj u)) v acc
      nrm = sqrt (sum [ magnitude z ** 2 | z <- w ])
  in gramSchmidt d (m - 1 :: Int) rng' (map (/ (nrm :+ 0)) w : acc)

-- | m distinct pseudo-random indices below d.
pickDistinct :: Int -> Int -> Rng -> [Int] -> ([Int], Rng)
pickDistinct _ 0 rng acc = (reverse acc, rng)
pickDistinct d m rng acc =
  let (x, rng') = nextD rng
      j = min (d - 1) (floor ((x + 1) / 2 * fromIntegral d)) :: Int
  in if j `elem` acc then pickDistinct d m rng' acc else pickDistinct d (m - 1 :: Int) rng' (j : acc)
