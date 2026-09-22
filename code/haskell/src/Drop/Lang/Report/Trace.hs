-- Trace.hs: the run, frame by frame.
--
-- One statement, one frame: the circuit diagram so far, the state as a sum
-- of basis kets, and, where a live temporary factors out, its two factors.
-- Lifted programs run once per selection word; a drop frame also carries
-- 'Drop.Lang.Interp.semanticVerdict', redrawing the whole row each frame.

module Drop.Lang.Report.Trace (traceText, traceFile, showTrace, showVec) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import Data.Maybe (fromMaybe, listToMaybe)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Drop.Lang.Ring (QS2 (..), showAmp, showRat)
import Drop.Lang.Cyclo (Cyclo, toQS2, iC)
import Drop.Lang.QState
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Parser (parseProgram, gateTable)
import Drop.Lang.Report.Run (wellFormed)

-- Gate labels, read back from the matrix

-- | Read back the way 'Drop.Lang.Parser.renderProgram' does from .s text: the named
-- gate first, then diag, perm or phase by shape, mat failing all of those.
gateLabel :: Matrix Cyclo -> String
gateLabel g = case listToMaybe [ nm | (nm, m) <- gateTable, m == g ] of
  Just nm -> nm
  Nothing
    | isPhase g -> "phase"
    | isDiag  g -> "diag"
    | isPerm  g -> "perm"
    | otherwise -> "mat"

isDiag :: Matrix Cyclo -> Bool
isDiag g = n > 0 && all ((== n) . length) g
           && and [ g !! i !! j == 0 | i <- [0 .. n-1], j <- [0 .. n-1], i /= j ]
  where n = length g

-- | Identity everywhere on the diagonal but the last entry: the shape of
-- 'Drop.Lang.Gates.gPhase' and 'Drop.Lang.Gates.gCPhase'.
isPhase :: Matrix Cyclo -> Bool
isPhase g = isDiag g && not (null diag) && all (== 1) (init diag)
  where n    = length g
        diag = [ g !! i !! i | i <- [0 .. n - 1] ]

isPerm :: Matrix Cyclo -> Bool
isPerm g = n > 0 && all ((== n) . length) g && all colOk [0 .. n - 1]
  where
    n = length g
    colOk j = length [ () | i <- [0 .. n-1], g !! i !! j /= 0 ] == 1
              && or [ g !! i !! j == 1 | i <- [0 .. n-1] ]

-- What a statement touches, and its column label

regsOf :: Cmd a -> [String]
regsOf c = case c of
  New x _        -> [x]
  NewState x _ _ -> [x]
  Loan x _   -> [x]
  Gate _ xs      -> xs
  Lift _ x _     -> [x]
  IfBit _ t e    -> dedup (concatMap regsOf t ++ concatMap regsOf e)
  Drop xs        -> xs
  where dedup = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- | The (register, label) pairs a statement places in its column.
cmdCells :: Cmd Cyclo -> [(String, String)]
cmdCells c = case c of
  New x _        -> [(x, "(new)")]
  NewState x _ _ -> [(x, "(dirty)")]
  Loan x _   -> [(x, "(loan)")]
  Gate g xs      -> [ (x, "[" ++ gateLabel g ++ "]") | x <- xs ]
  Lift _ x _     -> [(x, "[lift]")]
  IfBit g t e    -> [ (x, "[if " ++ showGuard g ++ "]") | x <- regsOf (IfBit g t e) ]
  Drop xs        -> [ (x, "(drop)") | x <- xs ]

describeCmd :: Cmd Cyclo -> String
describeCmd c = case c of
  New x d          -> "new " ++ x ++ " : [" ++ show d ++ "] @ |0>"
  NewState x d _   -> "new " ++ x ++ " : [" ++ show d ++ "] @ (...)"
  Loan x d     -> "loan " ++ x ++ " : [" ++ show d ++ "]"
  Gate g xs        -> "gate " ++ gateLabel g ++ " @" ++ unwords xs
  Lift p x b       -> p ++ " = lift[{" ++ intercalate "," (map show b)
                      ++ "}] " ++ x
  IfBit g _ _      -> "if " ++ showGuard g
  Drop xs          -> "drop " ++ unwords xs

-- Display

-- | An amplitude in the notation of the .s scalars: rationals as they are,
-- multiples of 1/sqrt2 as n/rt2, i as i, anything else in the cyclotomic form.
showTrace :: Cyclo -> String
showTrace c
  | c == iC   = "i"
  | c == -iC  = "-i"
  | otherwise = case toQS2 c of
      Just (QS2 a b)
        | b == 0    -> showRat a
        | a == 0    -> showRat (2 * b) ++ "/rt2"
        | otherwise -> showRat a ++ (if b > 0 then "+" else "") ++ showRat (2 * b) ++ "/rt2"
      Nothing -> showAmp c

showVec :: [Cyclo] -> String
showVec v = "(" ++ intercalate "," (map showTrace v) ++ ")"

bitsOf :: [Sel] -> String
bitsOf = concatMap (show . selBit)

padTo :: Int -> String -> String
padTo n s = s ++ replicate (max 0 (n - length s)) ' '

-- | The first test input whose probe does not factor, at a site under a
-- selection: the witness an "unsafe" verdict names. Only meaningful on the
-- temporary path of a loan-free program; once any loan is in scope the
-- probe space is (loan arrival, visible input) pairs -- Drop.Lang.Interp's
-- "Loans" section -- and no single visible input names the witness, so
-- none is reported rather than one that does factor being blamed.
badProbe :: VisSpec -> Prog Cyclo -> String -> [Sel] -> Maybe String
badProbe vis prog x sel
  | isLoanTarget prog x = Nothing
  | not (null (loansBefore prog [x])) = Nothing
  | otherwise =
      listToMaybe [ nm | (nm, inp) <- probesFor vis, isFail (probeResult vis prog x sel inp) ]
  where isFail PFail = True
        isFail _     = False

showMatTrace :: Matrix Cyclo -> String
showMatTrace m = "{ " ++ intercalate " ; " [ intercalate ", " (map showTrace row) | row <- m ] ++ " }"

verdictLine :: VisSpec -> Prog Cyclo -> String -> [Sel] -> String
verdictLine vis prog x sel = "verdict: " ++ case v of
  Unreachable -> "unreachable"
  Safe
    | isLoanTarget pre x -> case semanticLoanCert vis pre x sel of
        Just b  -> "safe, B = " ++ showMatTrace b
        Nothing -> "safe"
    | otherwise -> case semanticParked vis pre x sel of
        Just line -> "safe, line " ++ showVec line ++ " on every test input"
        Nothing   -> "safe"
  Unsafe -> case badProbe vis pre x sel of
    Just nm -> "unsafe (input " ++ nm ++ " leaves " ++ x ++ " entangled)"
    Nothing -> "unsafe"
  where
    pre = prefixThrough prog x
    v   = semanticVerdict vis pre x sel

-- One selection's run, frame by frame

-- | The column each register is introduced in, or Nothing for a visible
-- register, which is there from the start.
newColOf :: VisSpec -> Prog Cyclo -> String -> Maybe Int
newColOf vis prog r
  | r `elem` map fst vis = Nothing
  | otherwise = listToMaybe [ i | (i, c) <- zip [0 ..] prog, introduces c ]
  where
    introduces (New x _)        = x == r
    introduces (NewState x _ _) = x == r
    introduces (Loan x _)   = x == r
    introduces _                = False

-- | A loan has no state to display a run against, so the trace (a display
-- of one representative run, not the exhaustive safety check) seeds every
-- loan at |0>; the safety verdict itself never uses this, since
-- 'semanticVerdict'/'semanticLoanCert' probe every loan input exactly
-- (Drop.Lang.Interp's "Loans" section).
defaultLoanEnv :: Prog Cyclo -> [(String, StateV Cyclo)]
defaultLoanEnv prog = [ (n, ket [d] [0]) | Loan n d <- prog ]

renderSelection :: VisSpec -> Prog Cyclo -> StateV Cyclo -> [Sel] -> [String]
renderSelection vis prog inputVec sel =
  header ++ concatMap frame [0 .. n - 1]
  where
    n      = length prog
    header = if null sel then [] else ["", "selection " ++ bitsOf sel]
    m0     = (initMachL vis inputVec (defaultLoanEnv prog)) { mSel = sel }
    machs  = scanl step m0 prog                     -- machs !! (i+1) is after statement i
    rowOrder  = mNames (last machs)
    visNames  = map fst vis
    nameWidth = maximum (1 : map length rowOrder)
    colWidths = [ max 3 (maximum (3 : [ length lbl | (_, lbl) <- cmdCells c ]))
                | c <- prog ]
    allocCol r = fromMaybe (-1) (newColOf vis prog r)

    pointerRow curF = replicate (nameWidth + 2 + sum (take curF colWidths)) ' '
                      ++ replicate (colWidths !! curF) '^'

    diagramRow curF r = padTo nameWidth r ++ "  " ++ concat
      [ cell i | i <- [0 .. n - 1] ]
      where
        cell i
          | i < allocCol r = replicate (colWidths !! i) ' '
          | Just lbl <- lookup r (cmdCells (prog !! i)) = padTo (colWidths !! i) lbl
          | otherwise = replicate (colWidths !! i) (if i <= curF then '=' else '-')

    frame curF =
      [ "", "frame " ++ show (curF + 1) ++ "/" ++ show n ++ "   "
            ++ describeCmd (prog !! curF) ]
      ++ [ diagramRow curF r | r <- rowOrder ]
      ++ [ pointerRow curF ]
      ++ stateLines
      ++ [ "  " ++ verdictLine vis prog x sel | Drop [x] <- [prog !! curF] ]
      where
        m     = machs !! (curF + 1)
        dropped = concat [ xs | Drop xs <- take (curF + 1) prog ]
        stateLines
          | isZeroS (mAmp m) = ["  (zero state)"]
          | otherwise = ("  |" ++ unwords (mNames m) ++ ">   "
                          ++ intercalate "  " (map term nonzero))
                        : [ factorLine t | t <- mNames m
                          , t `notElem` visNames, t `notElem` dropped ]
          where
            nonzero = [ (idxToLevels (mDims m) k, a)
                      | (k, a) <- zip [0 ..] (mAmp m), a /= 0 ]
            term (levels, a) = showTrace a ++ " |" ++ unwords (map show levels) ++ ">"
            factorLine t = case factorSplit (mDims m) [regPos m t] (mAmp m) of
              Just (vA, vB) ->
                "  " ++ t ++ " = " ++ showVec vA ++ "  "
                ++ unwords [ r | r <- mNames m, r /= t ] ++ " = " ++ showVec vB
              Nothing -> "  " ++ t ++ " entangled with the rest"

-- Entry points

-- | Trace a program text: refuse what 'wellFormed' refuses, then run it
-- frame by frame, once per selection.
traceText :: String -> Maybe String -> Either String String
traceText src inputName = do
  (vis, prog) <- parseProgram src
  case wellFormed prog of
    Just err -> Left err
    Nothing  -> do
      let probes = probesFor vis :: [(String, StateV Cyclo)]
          nm     = fromMaybe "e0" inputName
      inputVec <- case lookup nm probes of
        Just v  -> Right v
        Nothing -> Left ("no test input named " ++ nm ++ "; try one of "
                         ++ intercalate ", " (map fst probes))
      let liftCount = length [ () | Lift {} <- prog ]
          sels      = if liftCount == 0 then [[]] else allSelections liftCount
      Right (unlines (concatMap (renderSelection vis prog inputVec) sels))

-- | Read a file, trace it, and print the trace.  A parse error, a refused
-- program or an unknown test input goes to standard error.
traceFile :: FilePath -> Maybe String -> IO ()
traceFile f inputName = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> die ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case traceText src inputName of
      Left err  -> die (f ++ ": " ++ err)
      Right out -> putStr out

-- | A refused file is a failure, not a report.
die :: String -> IO ()
die msg = hPutStrLn stderr msg >> exitFailure
