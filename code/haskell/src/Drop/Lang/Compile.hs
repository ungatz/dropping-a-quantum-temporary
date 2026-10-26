-- Drop.Lang.Compile: what circuit a program becomes, and when a program is refused.
--
-- Question: What circuit does a program become, and when is a program refused?
-- Answer:   compileWith walks the expanded term (Syntax.toTerm) and makes four decisions in order,
--           one module each, in the order of EMITTER.md:
--           where every wire and bit goes (Compile.Layout), which drops are safe on which record
--           (Compile.Safety), which wires a later allocation may take over (Compile.Reuse, only
--           for compileReuse), and what text each construct becomes (Compile.Emit). Emission is a
--           plain function of the layout, the safety table, the record the enclosing ifs have
--           fixed so far, and the term; no monad is needed because the resources are decided
--           before it starts. Outside its domain compile returns a named CompileError rather than
--           guessing. allocationReport shows the connection between the decisions for one
--           program: the wires in both layouts, the exact certificate of every site, the gates
--           inserted and whether a block enters the pool; begin there when a circuit looks
--           surprising.
-- Paper:    sec:lang:compile, app:compile, app:emitter-contract, sec:eval:compile.
-- Shapes:   compile, compileReuse  a program to OpenQASM 3 text, or a CompileError.
--           allocationReport        the same decisions as JSON text.

module Drop.Lang.Compile
  ( compile, compileReuse, allocationReport
  , CompileError (..)
  , showCompileError
  , liftInfoOf
  , visQubitsOf
  , wireQubitsOf
  , liftAncillaOf
  ) where

import Data.Char (ord)
import Data.List (intercalate, nub, isInfixOf)
import qualified Data.Map.Strict as Map
import Text.Printf (printf)

import Drop.Lang.Compile.Emit
import Drop.Lang.Compile.Layout
import Drop.Lang.Compile.Reuse
import Drop.Lang.Compile.Safety
import Drop.Lang.Scalar (Cyclo, Amp(showAmp))
import Drop.Lang.Syntax

-- The four decisions ----------------------------------------------------------

-- | The circuit, ending in the measurement of what the program returns. When
-- every branch returns the same value -- every program the parser reads,
-- since a surface branch returns exactly the registers it was handed -- the
-- output measurements follow the whole body once. When the branches return
-- different values, each branch measures its own at its @return@. Either way
-- @result[i]@ holds the i-th qubit of the value returned on the run taken;
-- a loan is never returned (Drop.Lang.Check.loanDiscipline), so never measured.
compile :: Program Cyclo -> Either CompileError String
compile = compileWith False

-- >>> :m + Drop.Lang.Parser

-- The paper's temporary AND, whole: a ccx, a Hadamard, the measured lift, the if, the reclaiming gate under it, then the output.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> either (putStrLn . showCompileError) (mapM_ print . lines) (compile prog)) (parseTyped src)
-- "OPENQASM 3.0;"
-- "include \"stdgates.inc\";"
-- ""
-- "// emitted by Drop.Lang.Compile, the compiler of the paper's language."
-- "// Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller."
-- "qubit[3] q;"
-- "bit[1] c;"
-- "bit[2] result;"
-- ""
-- "// q[0] = x"
-- "// q[1] = y"
-- ""
-- "ccx q[0], q[1], q[2];"
-- "h q[2];"
-- "c[0] = measure q[2];   // lift m: survived <=> c[0] == 1"
-- "if (c[0] == 1) {"
-- "  cz q[0], q[1];"
-- "  U(3.14159265358979270, 0, -pi) q[2];"
-- "} else {"
-- "}"
-- ""
-- "result[0] = measure q[0];"
-- "result[1] = measure q[1];"

-- The three-control Toffoli with a borrowed qubit: the loan is returned by the gate X.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> either (putStrLn . showCompileError) (mapM_ print . lines) (compile prog)) (parseTyped src)
-- "OPENQASM 3.0;"
-- "include \"stdgates.inc\";"
-- ""
-- "// emitted by Drop.Lang.Compile, the compiler of the paper's language."
-- "// Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller."
-- "qubit[5] q;"
-- "bit[4] result;"
-- ""
-- "// q[0] = q1"
-- "// q[1] = q2"
-- "// q[2] = q3"
-- "// q[3] = q"
-- ""
-- "// input register a, a loan: arrives in a state this program does not know"
-- "x q[4];"
-- "ccx q[2], q[4], q[3];"
-- "ccx q[0], q[1], q[4];"
-- "ccx q[2], q[4], q[3];"
-- "ccx q[0], q[1], q[4];"
-- "U(pi, 0, -pi) q[4];"
-- ""
-- "result[0] = measure q[0];"
-- "result[1] = measure q[1];"
-- "result[2] = measure q[2];"
-- "result[3] = measure q[3];"

-- Three of the 19 corpus programs are refused, by name: rus.s by dimension, c.s and bell-block.s by a gate outside the table.
-- >>> readFile "programs/rus.s" >>= \src -> either putStrLn (\prog -> putStrLn (either showCompileError id (compile prog))) (parseTyped src)
-- register x has dimension 3, not a power of two
-- >>> readFile "programs/c.s" >>= \src -> either putStrLn (\prog -> putStrLn (either showCompileError id (compile prog))) (parseTyped src)
-- gate on t q is not in the compile domain (not diagonal, a permutation, or a single-qubit unitary)
-- >>> readFile "programs/bell-block.s" >>= \src -> either putStrLn (\prog -> putStrLn (either showCompileError id (compile prog))) (parseTyped src)
-- gate on t is not in the compile domain (not diagonal, a permutation, or a single-qubit unitary)

-- copy-input.s drops an input; the drop is unsafe and compiles with no reclaiming gate.
-- >>> readFile "programs/copy-input.s" >>= \src -> either putStrLn (\prog -> either (putStrLn . showCompileError) (mapM_ print . lines) (compile prog)) (parseTyped src)
-- "OPENQASM 3.0;"
-- "include \"stdgates.inc\";"
-- ""
-- "// emitted by Drop.Lang.Compile, the compiler of the paper's language."
-- "// Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller."
-- "qubit[2] q;"
-- "bit[1] result;"
-- ""
-- "// q[0] = x"
-- ""
-- "cx q[0], q[1];"
-- "// x dropped unsafe: stays live"
-- ""
-- "// q[1] = t"
-- "result[0] = measure q[1];"

-- | The same circuit with wires reused (Drop.Lang.Compile.Reuse): a later
-- allocation takes over the wires of a block whose drop returned it.
compileReuse :: Program Cyclo -> Either CompileError String
compileReuse = compileWith True

-- Two disjoint lifetimes: the second temporary takes over the first one's wire, so one qubit less.
-- >>> readFile "programs/two-phases.s" >>= \src -> either putStrLn (\prog -> print (fmap (filter (isInfixOf "qubit[") . lines) (compile prog), fmap (filter (isInfixOf "qubit[") . lines) (compileReuse prog))) (parseTyped src)
-- (Right ["qubit[3] q;"],Right ["qubit[2] q;"])
-- >>> readFile "programs/two-phases.s" >>= \src -> either putStrLn (\prog -> either (putStrLn . showCompileError) (mapM_ print . lines) (compileReuse prog)) (parseTyped src)
-- "OPENQASM 3.0;"
-- "include \"stdgates.inc\";"
-- ""
-- "// emitted by Drop.Lang.Compile, the compiler of the paper's language."
-- "// Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller."
-- "qubit[2] q;"
-- "bit[1] result;"
-- ""
-- "// q[0] = x"
-- ""
-- "x q[1];"
-- "h q[1];"
-- "cx q[0], q[1];"
-- "U(pi/2, pi, 0) q[1];"
-- "// pool site 0: t"
-- "x q[1];"
-- "h q[1];"
-- "cx q[0], q[1];"
-- "U(pi/2, 0, -3.14159265358979270) q[1];"
-- "x q[1];"
-- "// pool site 1: u"
-- ""
-- "result[0] = measure q[0];"

-- With nothing allocated after the drop, reuse only adds the pool's comment line for the dropped block, in each arm of the if the drop was copied into.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (do { a <- compile prog; b <- compileReuse prog; Right (filter (`notElem` lines a) (lines b)) })) (parseTyped src)
-- Right ["  // pool site 0: a","  // pool site 0: a"]

-- | Layout, safety, optionally reuse, then emission: the four decisions of the
-- module header, in order. The header is built after the body, from it.
compileWith :: Bool -> Program Cyclo -> Either CompileError String
compileWith reuse prog = do
  initial <- layoutProgram prog
  let core = toTerm (progTerm prog)
  safety <- fragmentSafety prog core initial
  let layout = if reuse then reuseLayout prog safety initial else initial
  let visNames = map fst (progCtx prog)
      rets = returnsOf core
      widthOf v = length (concatMap (wireQubits layout) (valueNames v))
      width = case rets of { (v : _) -> widthOf v; [] -> 0 }
      uniform = case rets of { (v : vs) -> all (== v) vs; [] -> True }
      measure = outputMeasureLines layout visNames
  if all ((== width) . widthOf) rets then Right ()
    else Left (Other "Drop.Lang.Compile: the branches return values of different sizes (not a typed program)")
  body <- compileTerm layout safety (if uniform then const [] else measure) [] core
  let final = case rets of
        (v : _) | uniform, not (null (measure v)) -> "" : measure v
        _ -> []
  Right (unlines (buildHeader layout visNames width body ++ body ++ final))

-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (fmap (length . lines) (compileWith False prog), fmap (length . lines) (compileWith True prog))) (parseTyped src)
-- (Right 23,Right 25)

-- A term that does not type is refused before anything is laid out (here y is neither dropped nor returned).
-- >>> either showCompileError id (compileWith False (Program [("x", 2), ("y", 4)] (SDo (StLift "p" [1] "x") (SIf (BParam "p") (SReturn (VVar "x")) (SReturn (VVar "y"))))))
-- "type error: wire(s) [\"y\"] neither dropped nor returned"

-- | Machine-readable allocation and restoration data, as JSON text: the wires
-- in both layouts, every site's table (verdict, exact certificate, the gates
-- inserted and whether the block enters the pool), the returned values and the
-- lifts. The certificate is exact; emitted angles and their simulation are
-- numerical. @dqt allocation@ prints it.
allocationReport :: Program Cyclo -> Either CompileError String
allocationReport prog = do
  old <- layoutProgram prog
  let core = toTerm (progTerm prog)
  safety <- fragmentSafety prog core old
  let new = reuseLayout prog safety old
      sts = statements core
      loans = [ n | StLoan n _ <- sts ]
      allocs = Map.fromList [ (n, psi) | StNew n _ psi <- sts ]
      kind n | n `elem` loans = "loan"
             | Map.member n allocs = "temporary"
             | otherwise = "input"
      wires = [ jsonObject [("name", jsonString n), ("kind", jsonString (kind n))
                    ,("fresh", jsonInts qs), ("reuse", jsonInts (wireQubits new n))
                    ,("basis", maybe "null" show (Map.lookup n allocs >>= basisIndexOfExact))]
              | (n, qs) <- Map.toList (liWireQ old) ]
      row site names (record, outcome) = do
        gates <- compileDrop new safety record site names
        let status | outcome == UnsafeOutcome = "unsafe"
                   | outcome == UnreachableOutcome = "unreachable"
                   | any (\line -> "not emitted" `isInfixOf` line) gates = "not-emitted"
                   | null gates = "identity"
                   | otherwise = "emitted"
        pure (jsonObject [("record", jsonArray [jsonArray [jsonString n, show b] | (n,b) <- record])
                  ,("verdict", jsonString (verdictName outcome)), ("certificate", certificateJson outcome)
                  ,("restoration", jsonString status), ("gates", jsonArray (map jsonString gates))])
      siteRow (site, names) = do
        rows <- mapM (row site names) (Map.toList (Map.findWithDefault Map.empty site safety))
        pure (jsonObject [("site", show site), ("names", jsonArray (map jsonString names))
                  ,("pooled", if Map.member site (liPoolClears new) then "true" else "false")
                  ,("fresh", jsonInts (concatMap (wireQubits old) names))
                  ,("reuse", jsonInts (concatMap (wireQubits new) names))
                  ,("records", jsonArray rows)])
  -- A report for a circuit that cannot be emitted would be misleading.
  _ <- compile prog
  _ <- compileReuse prog
  sites <- mapM siteRow [ (site, valueNames v) | StDrop site v <- sts ]
  pure (jsonObject [("freshQubits", show (liTotalQubits old)), ("reuseQubits", show (liTotalQubits new))
            ,("wires", jsonArray wires), ("sites", jsonArray sites)
            ,("returns", jsonArray [jsonArray (map jsonString (valueNames v)) | v <- nub (returnsOf core)])
            ,("lifts", jsonArray [jsonObject [("name",jsonString n),("bit",show i),("survivedValue",show v)]
                            | (n,(i,v)) <- Map.toList (liLiftInfo old)])] ++ "\n")

-- The report of mcx-dirty-x.s, one field to a line: the layouts, the loan's site with its certificate B = X and its one gate.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> putStr (either showCompileError (unlines . take 24 . lines . map (\c -> if c == ',' then '\n' else c)) (allocationReport prog))) (parseTyped src)
-- {"freshQubits":5
-- "reuseQubits":5
-- "wires":[{"name":"a"
-- "kind":"loan"
-- "fresh":[4]
-- "reuse":[4]
-- "basis":null}
-- {"name":"q"
-- "kind":"input"
-- "fresh":[3]
-- "reuse":[3]
-- "basis":null}
-- {"name":"q1"
-- "kind":"input"
-- "fresh":[0]
-- "reuse":[0]
-- "basis":null}
-- {"name":"q2"
-- "kind":"input"
-- "fresh":[1]
-- "reuse":[1]
-- "basis":null}
-- {"name":"q3"
-- "kind":"input"

-- A report for a circuit that cannot be emitted is refused with the same message as compile.
-- >>> readFile "programs/rus.s" >>= \src -> either putStrLn (\prog -> putStrLn (either showCompileError id (allocationReport prog))) (parseTyped src)
-- register x has dimension 3, not a power of two

-- | The report's word for a site's outcome on one record.
verdictName :: SafetyOutcome -> String
verdictName (SafeCert _) = "safe"
verdictName (SafeIso _) = "safe-loan"
verdictName UnsafeOutcome = "unsafe"
verdictName UnreachableOutcome = "unreachable"

-- >>> map verdictName [SafeCert [1, 0], SafeIso [[1]], UnsafeOutcome, UnreachableOutcome]
-- ["safe","safe-loan","unsafe","unreachable"]

-- | The exact certificate of an outcome as JSON: the line, the isometry
-- factor, or null.
certificateJson :: SafetyOutcome -> String
certificateJson (SafeCert v) = jsonObject [("kind", jsonString "line"), ("coordinates", jsonArray (map (jsonString . showAmp) v))]
certificateJson (SafeIso m) = jsonObject [("kind", jsonString "isometry-factor"), ("matrix", jsonArray (map (jsonArray . map (jsonString . showAmp)) m))]
certificateJson _ = "null"

-- >>> certificateJson (SafeCert [1, 0])
-- "{\"kind\":\"line\",\"coordinates\":[\"1\",\"0\"]}"
-- >>> certificateJson (SafeIso [[0, 1], [1, 0]])
-- "{\"kind\":\"isometry-factor\",\"matrix\":[[\"0\",\"1\"],[\"1\",\"0\"]]}"
-- >>> certificateJson UnsafeOutcome
-- "null"

-- | A JSON string, with the escapes JSON requires.
jsonString :: String -> String
jsonString s = "\"" ++ concatMap escape s ++ "\""
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\r' = "\\r"
    escape '\t' = "\\t"
    escape c | ord c < 32 = printf "\\u%04x" (ord c)
             | otherwise = [c]

-- >>> jsonString "q[0]"
-- "\"q[0]\""
-- >>> jsonString "a \"quoted\" word\n"
-- "\"a \\\"quoted\\\" word\\n\""
-- >>> jsonString "back\\slash\tand a bell\a"
-- "\"back\\\\slash\\tand a bell\\u0007\""

-- | A JSON array of items already written as JSON.
jsonArray :: [String] -> String
jsonArray xs = "[" ++ intercalate "," xs ++ "]"

-- >>> jsonArray []
-- "[]"
-- >>> jsonArray ["1", "\"a\"", "null"]
-- "[1,\"a\",null]"

-- | A JSON array of numbers.
jsonInts :: [Int] -> String
jsonInts = jsonArray . map show

-- >>> jsonInts [0, 2, 3]
-- "[0,2,3]"
-- >>> jsonInts []
-- "[]"

-- | A JSON object from keys and values already written as JSON.
jsonObject :: [(String, String)] -> String
jsonObject xs = "{" ++ intercalate "," [jsonString k ++ ":" ++ v | (k,v) <- xs] ++ "}"

-- >>> jsonObject [("a", "1"), ("b", jsonInts [2, 3])]
-- "{\"a\":1,\"b\":[2,3]}"
-- >>> jsonObject []
-- "{}"

-- What the checkers ask of the layout -----------------------------------------

-- | The value each leaf of a term returns, left to right.
returnsOf :: Term a -> [Value]
returnsOf (Return v)   = [v]
returnsOf (Do _ m)     = returnsOf m
returnsOf (If _ m1 m2) = returnsOf m1 ++ returnsOf m2

-- >>> returnsOf (Return VUnit :: Term Int)
-- [VUnit]
-- >>> returnsOf (If (BParam "p") (Return (VVar "x")) (Return (VVar "y")) :: Term Int)
-- [VVar "x",VVar "y"]
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in print (returnsOf core)) (parseTyped src)
-- [VPair (VVar "x") (VVar "y"),VPair (VVar "x") (VVar "y")]

-- | Every lift's classical bit index and the qasm-measured value that means
-- "the block survived" -- exported so a checker can translate
-- Drop.Lang.Machine's (paramName, 1=survived) records into the raw c[k]
-- values the emitted circuit actually produces, without re-deriving the
-- direct-vs-block-form and polarity decisions 'layoutProgram' already made.
liftInfoOf :: Program Cyclo -> Either CompileError [(Name, Int, Int)]
liftInfoOf prog = do
  layout <- layoutProgram prog
  Right [ (n, idx, sv) | (n, (idx, sv)) <- Map.toList (liLiftInfo layout) ]

-- temp-and.s: the lift m is the classical bit 0, and the circuit's bit reads 1 when the block survived.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (liftInfoOf prog)) (parseTyped src)
-- Right [("m",0,1)]

-- superdense.s lifts {0}: a lift of {0} survives when the bit reads 0.
-- >>> readFile "programs/superdense.s" >>= \src -> either putStrLn (\prog -> print (liftInfoOf prog)) (parseTyped src)
-- Right [("p0",0,0),("p1",1,0)]
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (liftInfoOf prog)) (parseTyped src)
-- Right []

-- | Every block-lift's indicator ancilla qubit: a
-- physical qubit Drop.Lang.Machine's own leaf state has no wire for at all,
-- since the derived form is not in the source program -- a checker needs
-- this to marginalise the ancilla (always back at |0>, by the lemma's own
-- proof) out of the emitted circuit's state before comparing it to a leaf.
liftAncillaOf :: Program Cyclo -> Either CompileError [(Name, Int)]
liftAncillaOf prog = do
  layout <- layoutProgram prog
  Right (Map.toList (liLiftAncilla layout))

-- Only a block lift has an ancilla: shor.s lifts the block {7} of a 16-level register on qubit 7.
-- >>> readFile "programs/shor.s" >>= \src -> either putStrLn (\prog -> print (liftAncillaOf prog)) (parseTyped src)
-- Right [("s",7)]
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (liftAncillaOf prog)) (parseTyped src)
-- Right []

-- | The physical qubits of every visible (input) wire, in 'progCtx' order.
visQubitsOf :: Program Cyclo -> Either CompileError [(Name, [Int])]
visQubitsOf prog = do
  layout <- layoutProgram prog
  Right [ (n, Map.findWithDefault [] n (liWireQ layout)) | (n, _) <- progCtx prog ]

-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (visQubitsOf prog)) (parseTyped src)
-- Right [("x",[0]),("y",[1])]
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (visQubitsOf prog)) (parseTyped src)
-- Right [("q1",[0]),("q2",[1]),("q3",[2]),("q",[3])]

-- | The physical qubits of every register the layout names -- inputs,
-- allocations and loans -- so a checker can map a returned value's names
-- to the qubits its @result@ bits must read.
wireQubitsOf :: Program Cyclo -> Either CompileError [(Name, [Int])]
wireQubitsOf prog = do
  layout <- layoutProgram prog
  Right (Map.toList (liWireQ layout))

-- Every register the layout names, the temporary a included.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (wireQubitsOf prog)) (parseTyped src)
-- Right [("a",[2]),("x",[0]),("y",[1])]
-- >>> readFile "programs/two-phases.s" >>= \src -> either putStrLn (\prog -> print (wireQubitsOf prog)) (parseTyped src)
-- Right [("t",[1]),("u",[2]),("x",[0])]

