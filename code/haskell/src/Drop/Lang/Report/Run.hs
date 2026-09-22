-- Run.hs: running a .s program text and reporting on its drops.
--
-- runText parses, rejects programs the criterion says nothing about (a
-- lift nested in an if, a non-unitary gate), then reports every reachable
-- trace at each drop site: a trace is a selection word over the top-level
-- lifts before the site, so depth d gives 2^d rows. runFile is the same, over a file, printed.

module Drop.Lang.Report.Run
  ( Report (..), SiteReport (..), TraceRow (..)
  , runText, runFile, renderReport, wellFormed, showSite
  , typecheckText, typecheckFile
  , compileText, compileFile
  ) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Drop.Lang.Check (TypeError (..), checkProgram, showTypeError)
import Drop.Lang.Compile (compile, showCompileError)
import Drop.Lang.Elab (flatToProgramR)
import Drop.Lang.Ring (Amp (..), Conj (..))
import Drop.Lang.Cyclo (Cyclo)
import Drop.Lang.QState
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Parser
import Drop.Lang.Typed (Ty (..))

-- Report

-- | One trace at one drop site: the selection word, the criterion's verdict,
-- and, when the drop is accepted, the line the temporary is left on ('trLine',
-- a temporary target) or the isometry the loan is reclaimed with ('trCert',
-- a loan target) -- exactly one of the two is ever 'Just', since a site is
-- one or the other, never both (Drop.Lang.Interp.isLoanTarget).
data TraceRow = TraceRow
  { trSel     :: [Sel]
  , trVerdict :: Verdict
  , trLine    :: Maybe (StateV Cyclo)
  , trCert    :: Maybe (Matrix Cyclo)
  } deriving Show

data SiteReport = SiteReport
  { srSite  :: Site
  , srDepth :: Int
  , srRows  :: [TraceRow]
  } deriving Show

data Report = Report
  { rpVis   :: VisSpec
  , rpProg  :: Prog Cyclo
  , rpSites :: [SiteReport]
  } deriving Show

-- | Parse a program text and report on every drop site.
runText :: String -> Either String Report
runText src = do
  (vis, prog) <- parseProgram src
  case wellFormed prog of
    Just err -> Left err
    Nothing  -> Right (Report vis prog (map (siteReport vis prog) (dropSites prog)))

siteReport :: VisSpec -> Prog Cyclo -> Site -> SiteReport
siteReport vis prog x = SiteReport x d [ row sel | sel <- allSelections d ]
  where
    d    = liftDepthBeforeS prog x
    pre  = prefixThroughS prog x
    -- A block holding a loan -- one loan, several, or a loan beside
    -- temporaries -- is decided by the site definition's clause (4) and certified by the
    -- block factor B, not by a fixed line (Drop.Lang.Interp.loanResultS).
    loan = any (isLoanTargetS pre x) x
    row sel = TraceRow sel v
                (if v == Safe && not loan
                   then semanticParkedS vis pre x sel
                   else Nothing)
                (if v == Safe && loan
                   then semanticLoanCertS vis pre x sel
                   else Nothing)
      where v = semanticVerdictS vis pre x sel

-- Printing

showVec :: [Cyclo] -> String
showVec v = "(" ++ intercalate "," (map showAmp v) ++ ")"

-- | A site's registers as the source writes them: one name, or a tuple.
showSite :: Site -> String
showSite [x] = x
showSite xs  = "(" ++ intercalate ", " xs ++ ")"

bitsOf :: [Sel] -> String
bitsOf []  = "-"
bitsOf sel = concatMap (show . selBit) sel

pad :: Int -> String -> String
pad n s = s ++ replicate (max 1 (n - length s)) ' '

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

-- | Where to report an error the statics found. Drop.Lang.Check works on the
-- typed program, which carries no source position, so the two errors of the
-- loan discipline -- the only ones that name a register the /header/
-- declares, or the body's own @return@ -- are placed here from what the
-- parser recorded. Everything else is reported without a line, as before.
atLine :: SrcPos -> TypeError -> String
atLine pos e = case e of
  LoanReturned _       -> at (spReturnLine pos)
  LoanNotDroppedOnce x -> maybe "" at (lookup x (spLoanLines pos))
  _                    -> ""
  where at n = "line " ++ show n ++ ": "

showTyText :: Ty -> String
showTyText TUnit         = "1"
showTyText (TReg d)      = "[" ++ show d ++ "]"
showTyText (TTensor a b) = wrap a ++ " * " ++ showTyText b
  where wrap t@(TTensor _ _) = "(" ++ showTyText t ++ ")"
        wrap t               = showTyText t

-- | @dqt typecheck FILE@: parse and typecheck one .s file.
typecheckFile :: FilePath -> IO ()
typecheckFile f = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> die ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case typecheckText src of
      Left err -> die (f ++ ": " ++ err)
      Right ok -> putStrLn ("ok  " ++ f ++ ": prog " ++ ok)

-- | Parse, typecheck, then compile to OpenQASM 3.  The compiler's domain is
-- part of its claim (the compilation subsection): a program outside it is refused by
-- name, never approximated.
compileText :: String -> Either String String
compileText src = do
  (f, pos) <- parseFileAt src
  let prog = flatToProgramR (sfVis f) (sfReturn f) (sfBody f)
  case checkProgram prog of
    Left e  -> Left (atLine pos e ++ "type error: " ++ showTypeError e)
    Right _ -> case compile prog of
      Left e    -> Left ("REFUSED: " ++ showCompileError e)
      Right txt -> Right txt

-- | Read a file and print the circuit it compiles to.
compileFile :: FilePath -> IO ()
compileFile f = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> die ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case compileText src of
      Left err  -> die (f ++ ": " ++ err)
      Right txt -> putStr txt

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
-- A block holding a loan is not among them: the site definition's clause (4) is
-- stated for the whole block (sigma_s = B (x) W with B : H_loan -> H_block
-- an isometry, rectangular when temporaries sit beside the loans), and
-- Drop.Lang.Interp.loanResultS decides it there.
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

showMat :: Amp a => [[a]] -> String
showMat m = "{ " ++ intercalate " ; " [ intercalate ", " (map showAmp r) | r <- m ] ++ " }"

-- | U U^H = I, exactly.  There is no tolerance, because the whole package is
-- exact arithmetic.
isUnitary :: (Eq a, Fractional a, Conj a) => [[a]] -> Bool
isUnitary u =
  let n = length u
  in all ((== n) . length) u
     && and [ row i j == (if i == j then 1 else 0) | i <- [0 .. n-1], j <- [0 .. n-1] ]
  where
    row i j = sum [ (u !! i !! k) * conj (u !! j !! k) | k <- [0 .. length u - 1] ]
