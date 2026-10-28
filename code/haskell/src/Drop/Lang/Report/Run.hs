-- Drop.Lang.Report.Run: running a .s program text, and reporting on its drops.
--
-- Question: What does a program text say at each of its drops, and does it typecheck and compile?
-- Answer:   runText parses a program, refuses what the language refuses before any report is made
--           (a gate that is not unitary, then everything the statics and the loan discipline
--           refuse), and reports every drop site. A trace at a site is a selection word over the
--           top-level lifts before it, so depth d gives 2^d rows; each row is the criterion's
--           verdict and, when the drop is safe, the line a temporary is left on or the isometry a
--           loan is reclaimed with. typecheckText returns the program's name and its result type.
--           compileText typechecks and then compiles to OpenQASM 3; a program outside the
--           compiler's domain is refused by name, never approximated. Each of these has a Text
--           form, which is pure, and a File form, which reads the file and prints: a refusal goes
--           to standard error and the exit status is a failure. This module prints, so IO is
--           allowed here; the Text forms are where the work is.
-- Paper:    thm:notext (the verdict is record-dependent), sec:eval:corpus (the surface corpus),
--           sec:lang:statics (typechecking a file), sec:lang:compile (compilation to circuits).
-- Shapes:   Report       a program's report: its visible registers (rpVis), its body (rpProg) and
--                        one SiteReport for each drop site (rpSites).
--           SiteReport   one drop site (srSite), the lifts before it (srDepth) and its rows (srRows).
--           TraceRow     one selection (trSel), the criterion's verdict there (trVerdict), and the
--                        line (trLine) or the isometry (trCert) when the drop is safe.

module Drop.Lang.Report.Run
  ( Report (..), SiteReport (..), TraceRow (..)
  , runText, runFile, renderReport, surfaceProgram, showSite
  , typecheckText, typecheckFile
  , compileText, compileFile, compileReuseFile, allocationFile
  ) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Drop.Lang.Check (TypeError (..), checkProgram, checkCapacity, showTypeError)
import Drop.Lang.Compile (compile, compileReuse, allocationReport, CompileError, showCompileError)
import Drop.Lang.Elab (flatToProgramR)
import Drop.Lang.Scalar (Amp (..), Cyclo)
import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Parser
import Drop.Lang.Render (SFile (..), sfVis)
import Drop.Lang.Syntax (Ty (..), Program)

-- Report

-- | One trace at one drop site: the selection word, the criterion's verdict,
-- and, when the drop is accepted, the line the temporary is left on ('trLine',
-- a temporary target) or the isometry the loan is reclaimed with ('trCert',
-- a loan target) -- exactly one of the two is ever 'Just', since a site is
-- one or the other, never both (Drop.Lang.Criterion.isLoanTarget).
data TraceRow = TraceRow

-- A row with no line and no isometry: the drop is not safe here.
-- >>> TraceRow [SIn] Unsafe Nothing Nothing
-- TraceRow {trSel = [SIn], trVerdict = Unsafe, trLine = Nothing, trCert = Nothing}

  { trSel     :: [Sel]
  , trVerdict :: Verdict
  , trLine    :: Maybe (StateV Cyclo)
  , trCert    :: Maybe (Matrix Cyclo)
  } deriving Show

data SiteReport = SiteReport

-- >>> SiteReport ["t"] 0 []
-- SiteReport {srSite = ["t"], srDepth = 0, srRows = []}

  { srSite  :: Site
  , srDepth :: Int
  , srRows  :: [TraceRow]
  } deriving Show

data Report = Report

-- >>> Report [("x", 2)] [] []
-- Report {rpVis = [("x",2)], rpProg = [], rpSites = []}

  { rpVis   :: VisSpec
  , rpProg  :: Prog Cyclo
  , rpSites :: [SiteReport]
  } deriving Show

-- | Parse a program text and report on every drop site.
runText :: String -> Either String Report
runText src = do
  (vis, prog) <- surfaceProgram src
  Right (Report vis prog [ siteReport vis pre site | (site, pre) <- sitePrefixes prog ])

-- The temporary AND (each line shown with its quotes, so its indentation stays): one site, one lift, two rows.
-- >>> src <- readFile "programs/temp-and.s"
-- >>> either putStrLn (mapM_ print . lines . renderReport) (runText src)
-- "visible registers: x:2, y:2"
-- "statements: 6, lifts: 1, drop sites: a"
-- "drop a (depth 1):"
-- "  trace 1     Safe          line (0,1)"
-- "  trace 0     Safe          line (1,0)"

-- Text that is not a program is refused with the line.
-- >>> either putStrLn (mapM_ print . lines . renderReport) (runText "nonsense")
-- line 1: expected 'prog' (found 'nonsense')

-- A gate that is not unitary is refused before any report.
-- >>> either (takeWhile (/= ':')) (const "ok") (runText "prog p (x : [2]) : [2] {\n  mat x { 1, 1 ; 1, 1 };\n  return x\n}\n")
-- "gate matrix is not unitary (U U^H is not I)"

-- | Parse a program text and refuse what the language refuses before any
-- report is made on it: a gate that is not unitary ('wellFormed'), then
-- everything the statics and the loan discipline refuse ('checkProgram').
-- @run@, @trace@ and @pass@ all start here, so none of them reports on a
-- program @typecheck@ rejects.
surfaceProgram :: String -> Either String (VisSpec, Prog Cyclo)
surfaceProgram src = do
  (f, pos) <- parseFileAt src
  case checkCapacity (flatToProgramR (sfVis f) (sfReturn f) (sfBody f)) of
    Left e -> Left (showTypeError e)
    Right () -> Right ()
  case wellFormed (sfBody f) of
    Just err -> Left err
    Nothing  -> case checkProgram (flatToProgramR (sfVis f) (sfReturn f) (sfBody f)) of
      Left e  -> Left (atLine pos e ++ "type error: " ++ showTypeError e)
      Right _ -> Right (sfVis f, sfBody f)

-- The visible registers and the length of the body.
-- >>> src <- readFile "programs/temp-and.s"
-- >>> fmap (\(vis, prog) -> (vis, length prog)) (surfaceProgram src)
-- Right ([("x",2),("y",2)],6)

-- The statics refuse a program that returns its loan.
-- >>> either id (const "ok") (surfaceProgram "prog p (x : [2], loan a : [2]) : [2] * [2] {\n  return (x, a)\n}\n")
-- "line 2: type error: a loan is dropped, not returned (the language definition): the return value names the loan a"

siteReport :: VisSpec -> Prog Cyclo -> Site -> SiteReport
siteReport vis prog x = SiteReport x d [ row sel | sel <- allSelections d ]
  where
    d    = liftDepthBeforeS prog x
    pre  = prefixThroughS prog x
    -- A block holding a loan -- one loan, several, or a loan beside
    -- temporaries -- is decided by the site definition's clause (3) and certified by the
    -- block factor B, not by a fixed line (Drop.Lang.Criterion.loanResultS).
    loan = any (isLoanTargetS pre x) x
    row sel = TraceRow sel v
                (if v == Safe && not loan
                   then semanticParkedS vis pre x sel
                   else Nothing)
                (if v == Safe && loan
                   then semanticLoanCertS vis pre x sel
                   else Nothing)
      where v = semanticVerdictS vis pre x sel

-- The temporary AND's drop: depth one, a verdict on each record.
-- >>> src <- readFile "programs/temp-and.s"
-- >>> fmap (\(vis, prog) -> (srDepth (siteReport vis prog ["a"]), map trVerdict (srRows (siteReport vis prog ["a"])))) (surfaceProgram src)
-- Right (1,[Safe,Safe])

-- Printing

showVec :: [Cyclo] -> String
showVec v = "(" ++ intercalate "," (map showAmp v) ++ ")"

-- >>> showVec [1, 0]
-- "(1,0)"
-- >>> showVec [1, fromRational (1/2)]
-- "(1,1/2)"

-- | A site's registers as the source writes them: one name, or a tuple.
showSite :: Site -> String
showSite [x] = x
showSite xs  = "(" ++ intercalate ", " xs ++ ")"

-- >>> showSite ["t"]
-- "t"
-- >>> showSite ["a", "b"]
-- "(a, b)"

bitsOf :: [Sel] -> String
bitsOf []  = "-"
bitsOf sel = concatMap (show . selBit) sel

-- >>> bitsOf [SIn, SOut]
-- "10"
-- >>> bitsOf []
-- "-"

pad :: Int -> String -> String
pad n s = s ++ replicate (max 1 (n - length s)) ' '

-- >>> pad 6 "ab"
-- "ab    "
-- >>> pad 2 "abcd"
-- "abcd "

renderReport :: Report -> String
renderReport (Report vis prog sites) = unlines $
  ("visible registers: " ++ intercalate ", " [ x ++ ":" ++ show d | (x, d) <- vis ])
  : ("statements: " ++ show (length prog)
     ++ ", lifts: " ++ show (length [ () | Lift {} <- prog ])
     ++ ", drop sites: " ++ (case dropSites prog of
                               [] -> "none"
                               ds -> unwords (map showSite ds)))
  : concatMap site sites
  where
    site (SiteReport x d rows) =
      ("drop " ++ showSite x ++ " (depth " ++ show d ++ "):")
      : map (line x) rows
    line _ (TraceRow sel v ln cert) = case (ln, cert) of
      (Just g, _)  -> "  trace " ++ pad 6 (bitsOf sel) ++ pad 14 (show v)
                      ++ "line " ++ showVec g
      (_, Just b)  -> "  trace " ++ pad 6 (bitsOf sel) ++ pad 14 (show v)
                      ++ "B = " ++ showMat b
      (Nothing, Nothing) -> "  trace " ++ pad 6 (bitsOf sel) ++ show v

-- Deutsch-Jozsa has no lift, so its one trace is named "-".
-- >>> src <- readFile "programs/dj.s"
-- >>> either putStrLn (mapM_ print . lines . renderReport) (runText src)
-- "visible registers: x:2"
-- "statements: 7, lifts: 0, drop sites: t"
-- "drop t (depth 0):"
-- "  trace -     Safe          line (1,-1)"

-- Typechecking one file

-- | Parse a program text and typecheck it: the statics of
-- Drop.Lang.Check on the term Drop.Lang.Elab reads off the file, with the header's
-- input context and the body's own @return@. Returns the program's name and
-- its result type, as the header declares it.
typecheckText :: String -> Either String String
typecheckText src = do
  (f, pos) <- parseFileAt src
  let prog = flatToProgramR (sfVis f) (sfReturn f) (sfBody f)
  case checkProgram prog of
    Left e   -> Left (atLine pos e ++ "type error: " ++ showTypeError e)
    Right ty -> Right (sfName f ++ " : " ++ showTyText ty)

-- The program's name and its result type; and the loan discipline's refusal, at its line.
-- >>> src <- readFile "programs/temp-and.s"
-- >>> typecheckText src
-- Right "temp_and : [2] * [2]"
-- >>> typecheckText "prog p (x : [2], loan a : [2]) : [2] * [2] {\n  return (x, a)\n}\n"
-- Left "line 2: type error: a loan is dropped, not returned (the language definition): the return value names the loan a"

-- | Where to report an error the statics found. Drop.Lang.Check works on the
-- typed program, which carries no source position, so the two errors of the
-- loan discipline -- the only ones that name a register the /header/
-- declares, or the body's own @return@ -- are placed here from what the
-- parser recorded. Everything else is reported without a line.
atLine :: SrcPos -> TypeError -> String
atLine pos e = case e of
  LoanReturned _       -> at (spReturnLine pos)
  LoanNotDroppedOnce x -> maybe "" at (lookup x (spLoanLines pos))
  _                    -> ""
  where at n = "line " ++ show n ++ ": "

-- Only the two errors of the loan discipline carry a line; the return line is the file's second.
-- >>> fmap (\(_, pos) -> atLine pos (LoanReturned "a")) (parseFileAt "prog p (x : [2], loan a : [2]) : [2] * [2] {\n  return (x, a)\n}\n")
-- Right "line 2: "

showTyText :: Ty -> String
showTyText TUnit         = "1"
showTyText (TReg d)      = "[" ++ show d ++ "]"
showTyText (TTensor a b) = wrap a ++ " * " ++ showTyText b
  where wrap t@(TTensor _ _) = "(" ++ showTyText t ++ ")"
        wrap t               = showTyText t

-- >>> showTyText TUnit
-- "1"
-- >>> showTyText (TReg 2)
-- "[2]"
-- >>> showTyText (TTensor (TTensor (TReg 2) (TReg 2)) (TReg 3))
-- "([2] * [2]) * [3]"

-- | @dqt typecheck FILE@: parse and typecheck one .s file.
typecheckFile :: FilePath -> IO ()
typecheckFile f = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> die ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case typecheckText src of
      Left err -> die (f ++ ": " ++ err)
      Right ok -> putStrLn ("ok  " ++ f ++ ": prog " ++ ok)

-- >>> typecheckFile "programs/temp-and.s"
-- ok  programs/temp-and.s: prog temp_and : [2] * [2]

-- | Parse, typecheck, then compile to OpenQASM 3.  The compiler's domain is
-- part of its claim (sec:lang:compile): a program outside it is refused by
-- name, never approximated.
compileText :: String -> Either String String
compileText = compileTextWith compile

-- The temporary AND compiles; a qutrit register is outside the compiler's domain and is refused by name.
-- >>> src <- readFile "programs/temp-and.s"
-- >>> fmap (length . lines) (compileText src)
-- Right 23
-- >>> qutrit <- readFile "programs/rus.s"
-- >>> compileText qutrit
-- Left "REFUSED: register x has dimension 3, not a power of two"

compileTextWith :: (Program Cyclo -> Either CompileError String) -> String -> Either String String
compileTextWith emit src = do
  (f, pos) <- parseFileAt src
  let prog = flatToProgramR (sfVis f) (sfReturn f) (sfBody f)
  case checkProgram prog of
    Left e  -> Left (atLine pos e ++ "type error: " ++ showTypeError e)
    Right _ -> case emit prog of
      Left e    -> Left ("REFUSED: " ++ showCompileError e)
      Right txt -> Right txt

-- The same source through the reuse emitter.
-- >>> src <- readFile "programs/dj.s"
-- >>> fmap (take 2 . lines) (compileTextWith compileReuse src)
-- Right ["OPENQASM 3.0;","include \"stdgates.inc\";"]

-- | Read a file and print the circuit it compiles to.
compileFile :: FilePath -> IO ()
compileFile = compileFileWith compile

-- >>> compileFile "programs/dj.s"
-- OPENQASM 3.0;
-- include "stdgates.inc";
-- // emitted by Drop.Lang.Compile, the compiler of the paper's language.
-- // Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller.
-- qubit[2] q;
-- bit[1] result;
-- // q[0] = x
-- x q[1];
-- h q[1];
-- h q[0];
-- cx q[0], q[1];
-- h q[0];
-- U(pi/2, pi, 0) q[1];
-- result[0] = measure q[0];

compileReuseFile :: FilePath -> IO ()
compileReuseFile = compileFileWith compileReuse

-- On this program the reuse emitter adds one line to the circuit: a comment naming the pool site.
-- >>> compileReuseFile "programs/dj.s"
-- OPENQASM 3.0;
-- include "stdgates.inc";
-- // emitted by Drop.Lang.Compile, the compiler of the paper's language.
-- // Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller.
-- qubit[2] q;
-- bit[1] result;
-- // q[0] = x
-- x q[1];
-- h q[1];
-- h q[0];
-- cx q[0], q[1];
-- h q[0];
-- U(pi/2, pi, 0) q[1];
-- // pool site 0: t
-- result[0] = measure q[0];

allocationFile :: FilePath -> IO ()
allocationFile = compileFileWith allocationReport

-- >>> allocationFile "programs/dj.s"
-- {"freshQubits":2,"reuseQubits":2,"wires":[{"name":"t","kind":"temporary","fresh":[1],"reuse":[1],"basis":0},{"name":"x","kind":"input","fresh":[0],"reuse":[0],"basis":null}],"sites":[{"site":0,"names":["t"],"pooled":true,"fresh":[1],"reuse":[1],"records":[{"record":[],"verdict":"safe","certificate":{"kind":"line","coordinates":["1","-1"]},"restoration":"emitted","gates":["U(pi/2, pi, 0) q[1];"]}]}],"returns":[["x"]],"lifts":[]}

compileFileWith :: (Program Cyclo -> Either CompileError String) -> FilePath -> IO ()
compileFileWith emit f = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> die ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case compileTextWith emit src of
      Left err  -> die (f ++ ": " ++ err)
      Right txt -> putStr txt

-- The file forms above are this function with an emitter chosen.
-- >>> compileFileWith compile "programs/dj.s"
-- OPENQASM 3.0;
-- include "stdgates.inc";
-- // emitted by Drop.Lang.Compile, the compiler of the paper's language.
-- // Basis-state scratch starts at zero; other preparation is stated below. Inputs and loans come from the caller.
-- qubit[2] q;
-- bit[1] result;
-- // q[0] = x
-- x q[1];
-- h q[1];
-- h q[0];
-- cx q[0], q[1];
-- h q[0];
-- U(pi/2, pi, 0) q[1];
-- result[0] = measure q[0];

-- | Read a file, report on it, and print the report.  A parse error or a
-- refused program goes to standard error.
runFile :: FilePath -> IO ()
runFile f = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> die ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case runText src of
      Left err  -> die (f ++ ": " ++ err)
      Right rep -> putStr (renderReport rep)

-- | A refused file is a failure, not a report: in a shell, @dqt run bad.s &&
-- next@ must not run @next@.
die :: String -> IO ()
die msg = hPutStrLn stderr msg >> exitFailure

-- Programs the criterion says nothing about

-- | The grammar's own rules -- one binder per name, and no binder inside a
-- branch -- are the parser's, so a program that reaches here has passed them.
-- What is left is a gate matrix the theory does not cover.
-- A block holding a loan is not among them: the site definition's clause (3) is
-- stated for the whole block (sigma_s = B (x) W with B : H_loan -> H_block
-- an isometry, rectangular when temporaries sit beside the loans), and
-- Drop.Lang.Criterion.loanResultS decides it there.
wellFormed :: Amp a => Prog a -> Maybe String
wellFormed prog =
  case [ u | Gate u _ <- flatten prog, not (isUnitary u) ] of
    (u : _) -> Just ("gate matrix is not unitary (U U^H is not I): "
                     ++ showMat u
                     ++ ". The criterion is stated for unitary computations, \
                        \so a verdict here would be about an object the \
                        \theory does not cover.")
    []      -> Nothing
  where
    flatten = concatMap f
    f c@(IfBit _ thn els) = c : flatten thn ++ flatten els
    f c                   = [c]

-- A shear is not unitary; no gates at all is well formed.
-- >>> fmap (take 40) (wellFormed ([Gate [[1, 1], [1, 1]] ["x"]] :: Prog Cyclo))
-- Just "gate matrix is not unitary (U U^H is not"
-- >>> wellFormed ([] :: Prog Cyclo)
-- Nothing

showMat :: Amp a => [[a]] -> String
showMat m = "{ " ++ intercalate " ; " [ intercalate ", " (map showAmp r) | r <- m ] ++ " }"

-- >>> showMat ([[1, 0], [0, 1]] :: [[Cyclo]])
-- "{ 1, 0 ; 0, 1 }"
