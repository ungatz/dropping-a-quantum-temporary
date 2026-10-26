-- Drop.Lang.Report.Trace: the run of a program, frame by frame.
--
-- Question: What does a program do, one statement at a time, and what does each drop read?
-- Answer:   One statement is one frame: the circuit with a pointer under the statement just run (the
--           wires already run are drawn =, the rest -), the state as a sum of basis kets and, for
--           every live temporary, its factor and the rest's, or that it is entangled with the rest.
--           A program with lifts runs once for each selection word, and a frame at a drop of one
--           register also carries the verdict of Drop.Lang.Criterion.semanticVerdict. The circuit
--           is read back from the program: each gate is labelled by the gate table of
--           Drop.Lang.Render, and one that is in no table is called phase, diag, perm or mat by its
--           shape. traceText refuses what surfaceProgram of Drop.Lang.Report.Run refuses; a loan,
--           which has no state to show, is run from |0> for the display only, and the verdict never
--           uses that. traceFile reads a file and prints the trace. This module prints, so IO is
--           allowed here.
-- Paper:    sec:lang:dynamics (what the machine does at each statement), thm:notext (the verdict
--           is record-dependent).
-- Shapes:   gateLabel     the name a gate prints under: from the table, else by shape.
--           cmdCells      for one statement, the (register, label) pairs it places in its column.
--           showTrace     an amplitude in the notation of the .s scalars.
--           renderSelection
--                         the lines of the trace of one selection: a header, then a frame for each
--                         statement.

module Drop.Lang.Report.Trace (traceText, traceFile, showTrace, showVec) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import Data.Maybe (fromMaybe, listToMaybe)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Drop.Lang.Scalar (QS2 (..), showAmp, showRat, Cyclo, toQS2, iC)
import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Render (gateTable)
import Drop.Lang.Report.Run (surfaceProgram)

-- Gate labels, read back from the matrix

-- | Read back the way 'Drop.Lang.Render.renderProgram' does from .s text: the named
-- gate first, then diag, perm or phase by shape, mat failing all of those.
gateLabel :: Matrix Cyclo -> String
gateLabel g = case listToMaybe [ nm | (nm, m) <- gateTable, m == g ] of
  Just nm -> nm
  Nothing
    | isPhase g -> "phase"
    | isDiag  g -> "diag"
    | isPerm  g -> "perm"
    | otherwise -> "mat"

-- A gate in the table prints by its name; one outside it by its shape. The unscaled Hadamard matrix is in no table.
-- >>> fmap gateLabel (lookup "CX" gateTable)
-- Just "CX"
-- >>> gateLabel [[1, 0], [0, fromRational (1/2)]]
-- "phase"
-- >>> gateLabel [[2, 0], [0, 3]]
-- "diag"
-- >>> gateLabel [[0, 0, 1], [1, 0, 0], [0, 1, 0]]
-- "perm"
-- >>> gateLabel [[1, 1], [1, -1]]
-- "mat"

isDiag :: Matrix Cyclo -> Bool
isDiag g = n > 0 && all ((== n) . length) g
           -- impossible: the test above made g n rows of n entries, so i and j are in range
           && and [ g !! i !! j == 0 | i <- [0 .. n-1], j <- [0 .. n-1], i /= j ]
  where n = length g

-- >>> isDiag [[2, 0], [0, 3]]
-- True
-- >>> isDiag [[1, 1], [1, -1]]
-- False

-- | Identity everywhere on the diagonal but the last entry: the shape of
-- 'Drop.Lang.Gates.gPhase' and 'Drop.Lang.Gates.gCPhase'.
isPhase :: Matrix Cyclo -> Bool
isPhase g = isDiag g && not (null diag) && all (== 1) (init diag)
  where n    = length g
        -- impossible: isDiag g is tested first and makes g square, so i is in range
        diag = [ g !! i !! i | i <- [0 .. n - 1] ]

-- Identity but for the last entry of the diagonal.
-- >>> isPhase [[1, 0], [0, fromRational (1/2)]]
-- True
-- >>> isPhase [[2, 0], [0, 3]]
-- False

isPerm :: Matrix Cyclo -> Bool
isPerm g = n > 0 && all ((== n) . length) g && all colOk [0 .. n - 1]
  where
    n = length g
    -- impossible: isPerm tests that every row has n entries before colOk runs, so i and j are in range
    colOk j = length [ () | i <- [0 .. n-1], g !! i !! j /= 0 ] == 1
              -- impossible: the same, for the same i and j
              && or [ g !! i !! j == 1 | i <- [0 .. n-1] ]

-- >>> isPerm [[0, 1], [1, 0]]
-- True
-- >>> isPerm [[1, 1], [1, -1]]
-- False

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

-- >>> regsOf (Drop ["a", "b"] :: Cmd Cyclo)
-- ["a","b"]
-- >>> regsOf (Gate [[1]] ["x"] :: Cmd Cyclo)
-- ["x"]

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

-- The first three statements of Deutsch-Jozsa: a new register, an X, an H.
-- >>> src <- readFile "programs/dj.s"
-- >>> fmap (\(_, prog) -> take 3 (map cmdCells prog)) (surfaceProgram src)
-- Right [[("t","(new)")],[("t","[X]")],[("t","[H]")]]

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

-- >>> src <- readFile "programs/dj.s"
-- >>> fmap (\(_, prog) -> map describeCmd prog) (surfaceProgram src)
-- Right ["new t : [2] @ |0>","gate X @t","gate H @t","gate H @x","gate CX @x t","gate H @x","drop t"]

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

-- Rationals as they are, i as i, and a multiple of 1/sqrt2 as n/rt2.
-- >>> import Drop.Lang.Scalar (invSqrt2C)
-- >>> map showTrace [1, fromRational (1/2), iC, -iC, invSqrt2C]
-- ["1","1/2","i","-i","1/rt2"]

showVec :: [Cyclo] -> String
showVec v = "(" ++ intercalate "," (map showTrace v) ++ ")"

-- >>> showVec [1, -1]
-- "(1,-1)"

bitsOf :: [Sel] -> String
bitsOf = concatMap (show . selBit)

-- >>> bitsOf [SOut]
-- "0"
-- >>> bitsOf [SIn, SOut]
-- "10"

padTo :: Int -> String -> String
padTo n s = s ++ replicate (max 0 (n - length s)) ' '

-- >>> padTo 4 "ab"
-- "ab  "
-- >>> padTo 1 "abcd"
-- "abcd"

-- | The first test input whose probe does not factor, at a site under a
-- selection: the witness an "unsafe" verdict names. Only meaningful on the
-- temporary path of a loan-free program; once any loan is in scope the
-- probe space is (loan arrival, visible input) pairs -- Drop.Lang.Criterion's
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

-- The program that copies its input and forgets it: the sum input is the first that leaves x entangled. A safe drop names none.
-- >>> cp <- readFile "programs/copy-input.s"
-- >>> dj <- readFile "programs/dj.s"
-- >>> fmap (\(vis, prog) -> badProbe vis prog "x" []) (surfaceProgram cp)
-- Right (Just "sum")
-- >>> fmap (\(vis, prog) -> badProbe vis prog "t" []) (surfaceProgram dj)
-- Right Nothing

showMatTrace :: Matrix Cyclo -> String
showMatTrace m = "{ " ++ intercalate " ; " [ intercalate ", " (map showTrace row) | row <- m ] ++ " }"

-- >>> showMatTrace [[1, 0], [0, iC]]
-- "{ 1, 0 ; 0, i }"

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

-- Deutsch-Jozsa's drop is safe on the line (1,-1); copy-input's is not.
-- >>> dj <- readFile "programs/dj.s"
-- >>> cp <- readFile "programs/copy-input.s"
-- >>> fmap (\(vis, prog) -> verdictLine vis prog "t" []) (surfaceProgram dj)
-- Right "verdict: safe, line (1,-1) on every test input"
-- >>> fmap (\(vis, prog) -> verdictLine vis prog "x" []) (surfaceProgram cp)
-- Right "verdict: unsafe (input sum leaves x entangled)"

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

-- A visible register is there from the start; t is introduced by the first statement.
-- >>> src <- readFile "programs/dj.s"
-- >>> fmap (\(vis, prog) -> (newColOf vis prog "x", newColOf vis prog "t")) (surfaceProgram src)
-- Right (Nothing,Just 0)

-- | A loan has no state to display a run against, so the trace (a display
-- of one representative run, not the exhaustive safety check) seeds every
-- loan at |0>; the safety verdict itself never uses this, since
-- 'semanticVerdict'/'semanticLoanCert' probe every loan input exactly
-- (Drop.Lang.Criterion's "Loans" section).
defaultLoanEnv :: Prog Cyclo -> [(String, StateV Cyclo)]
defaultLoanEnv prog = [ (n, ket [d] [0]) | Loan n d <- prog ]

-- The loan of the dirty-ancilla program is seeded at |0>, for the display only.
-- >>> src <- readFile "programs/mcx-dirty.s"
-- >>> fmap (\(_, prog) -> map fst (defaultLoanEnv prog)) (surfaceProgram src)
-- Right ["a"]

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

    -- Column i belongs to statement i: colWidths and prog both have n entries.
    widthAt i = colWidths !! i  -- impossible: i is a statement's index, 0 <= i < n
    statementAt i = prog !! i  -- impossible: i is a statement's index, 0 <= i < n

    pointerRow curF = replicate (nameWidth + 2 + sum (take curF colWidths)) ' '
                      ++ replicate (widthAt curF) '^'

    diagramRow curF r = padTo nameWidth r ++ "  " ++ concat
      [ cell i | i <- [0 .. n - 1] ]
      where
        cell i
          | i < allocCol r = replicate (widthAt i) ' '
          | Just lbl <- lookup r (cmdCells (statementAt i)) = padTo (widthAt i) lbl
          | otherwise = replicate (widthAt i) (if i <= curF then '=' else '-')

    frame curF =
      [ "", "frame " ++ show (curF + 1) ++ "/" ++ show n ++ "   "
            ++ describeCmd (statementAt curF) ]
      ++ [ diagramRow curF r | r <- rowOrder ]
      ++ [ pointerRow curF ]
      ++ stateLines
      ++ [ "  " ++ verdictLine vis prog x sel | Drop [x] <- [statementAt curF] ]
      where
        m     = machs !! (curF + 1)  -- impossible: scanl gives n + 1 machines and curF < n
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

-- The first frame of Deutsch-Jozsa (each line shown with its quotes, so its indentation stays).
-- >>> src <- readFile "programs/dj.s"
-- >>> either putStrLn (\(vis, prog) -> mapM_ print (take 6 (renderSelection vis prog (ket [2] [0]) []))) (surfaceProgram src)
-- ""
-- "frame 1/7   new t : [2] @ |0>"
-- "x  =====------[H][CX][H]------"
-- "t  (new)[X][H]---[CX]---(drop)"
-- "   ^^^^^"
-- "  |x t>   1 |0 0>"

-- Entry points

-- | Trace a program text: refuse what 'surfaceProgram' refuses, then run it
-- frame by frame, once per selection.
traceText :: String -> Maybe String -> Either String String
traceText src inputName = do
  (vis, prog) <- surfaceProgram src
  let probes = probesFor vis :: [(String, StateV Cyclo)]
      nm     = fromMaybe "e0" inputName
  inputVec <- case lookup nm probes of
    Just v  -> Right v
    Nothing -> Left ("no test input named " ++ nm ++ "; try one of "
                     ++ intercalate ", " (map fst probes))
  let liftCount = length [ () | Lift {} <- prog ]
      sels      = if liftCount == 0 then [[]] else allSelections liftCount
  Right (unlines (concatMap (renderSelection vis prog inputVec) sels))

-- The temporary AND runs once for each selection, and the second selection starts at its own header.
-- >>> src <- readFile "programs/temp-and.s"
-- >>> either putStrLn (mapM_ print . take 12 . lines) (traceText src Nothing)
-- ""
-- "selection 1"
-- ""
-- "frame 1/6   new a : [2] @ |0>"
-- "x  =====[CCX]---------[if m]------"
-- "y  =====[CCX]---------[if m]------"
-- "a  (new)[CCX][H][lift]------(drop)"
-- "   ^^^^^"
-- "  |x y a>   1 |0 0 0>"
-- "  a = (1,0)  x y = (1,0,0,0)"
-- ""
-- "frame 2/6   gate CCX @x y a"
-- >>> either putStrLn (mapM_ print . take 3 . dropWhile (/= "selection 0") . lines) (traceText src Nothing)
-- "selection 0"
-- ""
-- "frame 1/6   new a : [2] @ |0>"

-- A test input that does not exist is refused, naming the ones that do.
-- >>> src <- readFile "programs/temp-and.s"
-- >>> either id (const "ok") (traceText src (Just "nope"))
-- "no test input named nope; try one of e0, e1, e2, e3, sum"

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
