-- Drop.Lang.Report.Explain: the static pass, stage by stage, on one program.
--
-- Question: What did each pass of Drop.Lang.Pass make of this program at each of its drops?
-- Answer:   passText prints, for every drop site, the four stages in the order the passes run. The cut
--           is the program up to the drop, split at its first lift. The park runs the prefix on
--           the test inputs and prints the line the temporary is left on and the visible action B.
--           The resolve prints the residual program of each record, each lift a restriction.
--           The decide runs each residual program from the parked line on the test inputs and
--           prints the record's verdict. After the four come the emitted table, one verdict for
--           each record, the criterion's answer beside it, and how many rows agree. A pass that
--           declines is printed as a FAILS line naming the hypothesis, and the stages after it as
--           not reached. A drop of several registers is declined by name, since the chain is
--           stated for one register at a time (explainSite). Every stage is a function of its
--           own, so a stage can be read, and run, alone. passFile reads a file and prints the
--           text; this module prints, so IO is allowed here.
-- Paper:    sec:residual (compiling the record-dependent reclaim), app:residual (the reclaim in
--           detail), thm:perrecord (the criterion on one record).
-- Shapes:   passText      the text for a whole program: one block for each drop site.
--           explainSite   the block of one site, or the decline of a tuple drop.
--           site          the block of one single-register site: its title, the four stages and
--                         the summary, as lines.
--           cutLines, parkLines, resolveLines, decideLines
--                         the lines of one stage, given what the passes before it returned.
--           emittedTable, criterionTable
--                         (selection, verdict) for each record, from the pass and from the criterion.
--           summaryLines  the two tables side by side, with the number of rows that agree.

module Drop.Lang.Report.Explain (passText, passFile) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Drop.Lang.Scalar (Cyclo)
import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass
import Drop.Lang.Render (renderCmd)
import Drop.Lang.Report.Run (surfaceProgram)
import Drop.Lang.Report.Trace (showTrace, showVec)

passText :: String -> Either String String
passText src = do
  (vis, prog) <- surfaceProgram src
  Right (unlines (concatMap (explainSite vis prog) (dropSites prog)))

-- The loop of rus.s, stage by stage (each line shown with its quotes, so its indentation stays).
-- >>> src <- readFile "programs/rus.s"
-- >>> either putStrLn (mapM_ print . take 14 . lines) (passText src)
-- "the static pass at drop t"
-- "visible registers: x:3"
-- ""
-- "1  cut      the program up to the drop, split at its first lift"
-- "   prefix   new t : [3] @ |0>; tilt t;"
-- "   rest     p = lift[{0,1}] t; if p { READ3 x t; } else { READ3 x t; }"
-- ""
-- "2  park     run the prefix on the test inputs; does t come out constant?"
-- "   e0     t = (2/3,2/3,1/3)   rest = (1,0,0)"
-- "   e1     t = (2/3,2/3,1/3)   rest = (0,1,0)"
-- "   e2     t = (2/3,2/3,1/3)   rest = (0,0,1)"
-- "   sum    t = (2/3,2/3,1/3)   rest = (1,1,1)"
-- "   line g    = (1,1,1/2)"
-- "   action B  = [ (2/3,0,0) ; (0,2/3,0) ; (0,0,2/3) ], det 8/27, right-invertible"

-- The same text ends with the table beside the criterion.
-- >>> either putStrLn (mapM_ print . drop 14 . lines) (passText src)
-- ""
-- "3  resolve  one residual program per record; each lift becomes a restriction"
-- "   record 1    transferred (1,1,0)   keep t in {0,1}; if p { READ3 x t; } else { READ3 x t; }"
-- "   record 0    transferred (0,0,1/2) keep t in {2}; if p { READ3 x t; } else { READ3 x t; }"
-- ""
-- "4  decide   run each residual program from g on the test inputs, factor t at the drop"
-- "   record 1    e0 entangled e1 entangled e2 entangled sum (1,1,0)   -> refuse"
-- "   record 0    e0 (0,0,1) e1 (0,0,1) e2 (0,0,1) sum (0,0,1)   -> admit"
-- ""
-- "emitted table 1: refuse   0: admit"
-- "the criterion 1: unsafe   0: safe   agree 2/2"
-- ""

-- A program that is not one is refused with the line.
-- >>> either id (const "ok") (passText "nonsense")
-- "line 1: expected 'prog' (found 'nonsense')"

-- | The pass chain is stated one register at a time (Drop.Lang.Pass.Cut), so a
-- tuple drop -- one site (the composite-temporary proposition) -- is declined by name here
-- rather than answered by a chain that was never proved for it.
explainSite :: VisSpec -> Prog Cyclo -> Site -> [String]
explainSite vis prog [x] = site vis prog x
explainSite _ _ xs =
  [ "the static pass at drop (" ++ intercalate ", " xs ++ ")"
  , "   declines: the pass chain is stated for one register at a time; the"
  , "   criterion's own answer at this site is in `dqt run`."
  , "" ]

-- A drop of two registers is declined by name.
-- >>> src <- readFile "programs/bell-pair.s"
-- >>> either putStrLn (\(vis, prog) -> mapM_ print (explainSite vis prog ["a", "b"])) (surfaceProgram src)
-- "the static pass at drop (a, b)"
-- "   declines: the pass chain is stated for one register at a time; the"
-- "   criterion's own answer at this site is in `dqt run`."
-- ""

-- | One drop site, stage by stage: the cut, the parked line, the residual
-- program of each record with its decision, and the emitted table beside the
-- criterion's answer.
site :: VisSpec -> Prog Cyclo -> String -> [String]
site vis prog x =
  [ "the static pass at drop " ++ x
  , "visible registers: " ++ intercalate ", " [ n ++ ":" ++ show d | (n, d) <- vis ]
  , "" ]
  ++ cutLines ecut ++ [""]
  ++ parkLines vis x ecut epark ++ [""]
  ++ resolveLines epark eres ++ [""]
  ++ decideLines vis x eres ++ [""]
  ++ summaryLines (emittedTable vis depth sels epark eres) (criterionTable vis prog x sels) ++ [""]
  where
    depth = liftDepthBefore prog x
    sels  = allSelections depth
    ecut  = cut prog x
    epark = ecut >>= park vis
    eres  = epark >>= \p -> fmap ((,) p) (resolve vis p)

-- The temporary AND: the cut and the lift are there, the park declines, and the table says so.
-- >>> src <- readFile "programs/temp-and.s"
-- >>> either putStrLn (\(vis, prog) -> mapM_ print (site vis prog "a")) (surfaceProgram src)
-- "the static pass at drop a"
-- "visible registers: x:2, y:2"
-- ""
-- "1  cut      the program up to the drop, split at its first lift"
-- "   prefix   new a : [2] @ |0>; CCX x y a; H a;"
-- "   rest     m = lift[{1}] a; if m { diag x y (1, 1, 1, -1); } else { }"
-- ""
-- "2  park     run the prefix on the test inputs; does a come out constant?"
-- "   e0     a = (1/rt2,1/rt2)   rest = (1,0,0,0)"
-- "   e1     a = (1/rt2,1/rt2)   rest = (0,1,0,0)"
-- "   e2     a = (1/rt2,1/rt2)   rest = (0,0,1,0)"
-- "   e3     a = (1/rt2,-1/rt2)   rest = (0,0,0,1)"
-- "   sum    a entangled with the rest"
-- "   FAILS: prefix-parks; the check declines here"
-- ""
-- "3  resolve  one residual program per record; each lift becomes a restriction"
-- "   (not reached)"
-- ""
-- "4  decide   run each residual program from g on the test inputs, factor a at the drop"
-- "   (not reached)"
-- ""
-- "emitted table 1: declines   0: declines"
-- "the criterion 1: safe   0: safe   (the check declined; the criterion still decides)"
-- ""

-- Stage 1: cut --------------------------------------------------------------

cutLines :: Either String (Cut Cyclo) -> [String]
cutLines ecut = header 1 "cut" "the program up to the drop, split at its first lift"
  ++ case ecut of
       Left h  -> [fail' h]
       Right c ->
         [ "   prefix   " ++ render (cPrefix c)
         , "   rest     " ++ (if null (cRest c) then "(no lift before the drop)"
                              else render (cRest c)) ]

-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> mapM_ print (cutLines (cut prog "t"))
-- "1  cut      the program up to the drop, split at its first lift"
-- "   prefix   new t : [3] @ |0>; tilt t;"
-- "   rest     p = lift[{0,1}] t; if p { READ3 x t; } else { READ3 x t; }"

-- Stage 2: park -------------------------------------------------------------

parkLines :: VisSpec -> String -> Either String (Cut Cyclo) -> Either String (Parked Cyclo) -> [String]
parkLines vis x ecut epark =
  header 2 "park" ("run the prefix on the test inputs; does " ++ x
                   ++ " come out constant?")
  ++ case ecut of
       Left _  -> ["   (not reached)"]
       Right c ->
         [ "   " ++ pad 7 nm ++ factorLine vis x c inp | (nm, inp) <- probesFor vis ]
         ++ case epark of
              Left h  -> [fail' h]
              Right p ->
                [ "   line g    = " ++ showVec (pLine p)
                , "   action B  = " ++ showMat (pAction p)
                  ++ (if rightInvertible (pAction p)
                        then ", det " ++ showTrace (detM (pAction p)) ++ ", right-invertible"
                        else ", not right-invertible") ]

-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> let ecut = cut prog "t"
-- >>> mapM_ print (parkLines vis "t" ecut (ecut >>= park vis))
-- "2  park     run the prefix on the test inputs; does t come out constant?"
-- "   e0     t = (2/3,2/3,1/3)   rest = (1,0,0)"
-- "   e1     t = (2/3,2/3,1/3)   rest = (0,1,0)"
-- "   e2     t = (2/3,2/3,1/3)   rest = (0,0,1)"
-- "   sum    t = (2/3,2/3,1/3)   rest = (1,1,1)"
-- "   line g    = (1,1,1/2)"
-- "   action B  = [ (2/3,0,0) ; (0,2/3,0) ; (0,0,2/3) ], det 8/27, right-invertible"

-- | What the prefix leaves the temporary as, on one test input.
factorLine :: VisSpec -> String -> Cut Cyclo -> StateV Cyclo -> String
factorLine vis x c inp =
  let m = runStmts (initMach vis inp) (cPrefix c) [] Nothing
  in case factorSplit (mDims m) [regPos m x] (mAmp m) of
       Nothing     -> x ++ " entangled with the rest"
       Just (t, r) -> x ++ " = " ++ showVec t ++ "   rest = " ++ showVec r

-- What the prefix leaves of t on the first test input: the basis state |0> after the tilt.
-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> either putStrLn (\c -> putStrLn (factorLine vis "t" c (snd (probesFor vis !! 0)))) (cut prog "t")
-- t = (2/3,2/3,1/3)   rest = (1,0,0)

-- Stage 3: resolve ----------------------------------------------------------

resolveLines :: Either String (Parked Cyclo)
             -> Either String (Parked Cyclo, [Record Cyclo]) -> [String]
resolveLines epark eres =
  header 3 "resolve" "one residual program per record; each lift becomes a restriction"
  ++ case eres of
       Left h | either (const False) (const True) epark -> [fail' h]
              | otherwise -> ["   (not reached)"]
       Right (p, recs) ->
         [ "   " ++ pad 12 (recordName r) ++ pad 22 ("transferred " ++ showVec (transferred p r))
           ++ renderSteps (rSteps r)
         | r <- recs ]

-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> let epark = cut prog "t" >>= park vis
-- >>> mapM_ print (resolveLines epark (epark >>= \p -> fmap ((,) p) (resolve vis p)))
-- "3  resolve  one residual program per record; each lift becomes a restriction"
-- "   record 1    transferred (1,1,0)   keep t in {0,1}; if p { READ3 x t; } else { READ3 x t; }"
-- "   record 0    transferred (0,0,1/2) keep t in {2}; if p { READ3 x t; } else { READ3 x t; }"

-- Stage 4: decide -----------------------------------------------------------

decideLines :: VisSpec -> String -> Either String (Parked Cyclo, [Record Cyclo]) -> [String]
decideLines vis x eres =
  header 4 "decide" ("run each residual program from g on the test inputs, factor "
                     ++ x ++ " at the drop")
  ++ case eres of
       Left _ -> ["   (not reached)"]
       Right (p, recs) ->
         [ "   " ++ pad 12 (recordName r)
           ++ unwords [ nm ++ " " ++ probeWord res | (nm, res) <- probeRecord vis p r ]
           ++ "   -> " ++ verdictName (decide vis p r)
         | r <- recs ]

-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> let epark = cut prog "t" >>= park vis
-- >>> mapM_ print (decideLines vis "t" (epark >>= \p -> fmap ((,) p) (resolve vis p)))
-- "4  decide   run each residual program from g on the test inputs, factor t at the drop"
-- "   record 1    e0 entangled e1 entangled e2 entangled sum (1,1,0)   -> refuse"
-- "   record 0    e0 (0,0,1) e1 (0,0,1) e2 (0,0,1) sum (0,0,1)   -> admit"

probeWord :: ProbeResult Cyclo -> String
probeWord PZero     = "zero"
probeWord PFail     = "entangled"
probeWord (PLine l) = showVec l

-- >>> map probeWord [PZero, PFail, PLine [1, 0]]
-- ["zero","entangled","(1,0)"]

-- The table, and the criterion for comparison -------------------------------

-- | The rows the pass emits: one per record, or the one row of a pass that
-- stopped at the prefix, or a declined row per selection.
emittedTable :: VisSpec -> Int -> [[Sel]] -> Either String (Parked Cyclo)
             -> Either String (Parked Cyclo, [Record Cyclo]) -> [([Sel], RVerdict)]
emittedTable vis depth sels epark eres = case eres of
  Right (p, recs) -> [ (rSel r, decide vis p r) | r <- recs ]
  Left _ | depth == 0, Left "prefix-parks" <- epark -> [([], Refuse)]
         | otherwise -> [ (sel, HypothesesFail) | sel <- sels ]

-- rus.s: record 1 is refused and record 0 admitted. The temporary AND's pass declines, so each record shows HypothesesFail.
-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> let epark = cut prog "t" >>= park vis
-- >>> emittedTable vis 1 (allSelections 1) epark (epark >>= \p -> fmap ((,) p) (resolve vis p))
-- [([SIn],Refuse),([SOut],Admit)]
-- >>> and' <- readFile "programs/temp-and.s"
-- >>> Right (visA, progA) <- return (surfaceProgram and')
-- >>> let eparkA = cut progA "a" >>= park visA
-- >>> emittedTable visA 1 (allSelections 1) eparkA (eparkA >>= \p -> fmap ((,) p) (resolve visA p))
-- [([SIn],HypothesesFail),([SOut],HypothesesFail)]

-- | The criterion's verdict at every selection, on the program up to the drop.
criterionTable :: VisSpec -> Prog Cyclo -> String -> [[Sel]] -> [([Sel], Verdict)]
criterionTable vis prog x sels = [ (sel, semanticVerdict vis pre x sel) | sel <- sels ]
  where pre = prefixThrough prog x

-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> criterionTable vis prog "t" (allSelections 1)
-- [([SIn],Unsafe),([SOut],Safe)]

summaryLines :: [([Sel], RVerdict)] -> [([Sel], Verdict)] -> [String]
summaryLines table crit =
  [ "emitted table " ++ row [ (sel, verdictName v) | (sel, v) <- table ]
  , "the criterion " ++ row [ (sel, criterionName v) | (sel, v) <- crit ]
    ++ "   " ++ agreement table crit ]

-- >>> mapM_ print (summaryLines [([SIn], Refuse), ([SOut], Admit)] [([SIn], Unsafe), ([SOut], Safe)])
-- "emitted table 1: refuse   0: admit"
-- "the criterion 1: unsafe   0: safe   agree 2/2"

row :: [([Sel], String)] -> String
row cells = intercalate "   " [ selName sel ++ ": " ++ v | (sel, v) <- cells ]

-- >>> row [([SIn], "safe"), ([SOut], "unsafe")]
-- "1: safe   0: unsafe"
-- >>> row [([], "declines")]
-- "-: declines"

-- | How many of the answered rows the criterion confirms.
agreement :: [([Sel], RVerdict)] -> [([Sel], Verdict)] -> String
agreement table crit =
  let n = length [ () | ((_, rv), (_, sv)) <- zip table crit, rv /= HypothesesFail
                      , confirms rv sv ]
      m = length [ () | (_, rv) <- table, rv /= HypothesesFail ]
  in if m == 0 then "(the check declined; the criterion still decides)"
     else "agree " ++ show n ++ "/" ++ show m

-- Every row confirmed; a declined table; one row wrong.
-- >>> agreement [([SIn], Refuse), ([SOut], Admit)] [([SIn], Unsafe), ([SOut], Safe)]
-- "agree 2/2"
-- >>> agreement [([SIn], HypothesesFail)] [([SIn], Safe)]
-- "(the check declined; the criterion still decides)"
-- >>> agreement [([SIn], Refuse), ([SOut], Admit)] [([SIn], Safe), ([SOut], Safe)]
-- "agree 1/2"

-- | A row is confirmed when the criterion's verdict is the one it names; an
-- unreachable row is also confirmed by a safe criterion.
confirms :: RVerdict -> Verdict -> Bool
confirms Admit Safe          = True
confirms Refuse Unsafe       = True
confirms RUnreachable Unreachable  = True
confirms RUnreachable Safe   = True
confirms _ _                       = False

-- A row that names unreachable is also confirmed by a safe criterion.
-- >>> [ confirms Admit Safe, confirms Refuse Safe, confirms RUnreachable Unreachable, confirms RUnreachable Safe ]
-- [True,False,True,True]

recordName :: Record Cyclo -> String
recordName r = "record " ++ selName (rSel r)

-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> fmap (map recordName) (cut prog "t" >>= park vis >>= resolve vis)
-- Right ["record 1","record 0"]

selName :: [Sel] -> String
selName []  = "-"
selName sel = concatMap (show . selBit) sel

-- >>> selName []
-- "-"
-- >>> selName [SIn, SOut]
-- "10"

header :: Int -> String -> String -> [String]
header n nm what = [show n ++ "  " ++ pad 9 nm ++ what]

-- >>> header 2 "park" "run the prefix"
-- ["2  park     run the prefix"]

fail' :: String -> String
fail' h = "   FAILS: " ++ h ++ "; the check declines here"

-- >>> fail' "prefix-parks"
-- "   FAILS: prefix-parks; the check declines here"

verdictName :: RVerdict -> String
verdictName Admit          = "admit"
verdictName Refuse         = "refuse"
verdictName RUnreachable   = "unreachable"
verdictName HypothesesFail = "declines"

-- >>> map verdictName [Admit, Refuse, RUnreachable, HypothesesFail]
-- ["admit","refuse","unreachable","declines"]

criterionName :: Verdict -> String
criterionName Safe   = "safe"
criterionName Unsafe = "unsafe"
criterionName Unreachable  = "unreachable"

-- >>> map criterionName [Safe, Unsafe, Unreachable]
-- ["safe","unsafe","unreachable"]

render :: Prog Cyclo -> String
render = unwords . map renderCmd

-- >>> src <- readFile "programs/rus.s"
-- >>> fmap (\(_, prog) -> render (take 2 prog)) (surfaceProgram src)
-- Right "new t : [3] @ |0>; tilt t;"

renderSteps :: [Step Cyclo] -> String
renderSteps = unwords . map one
  where one (Keep y ks) = "keep " ++ y ++ " in {" ++ intercalate "," (map show ks) ++ "};"
        one (Run seg)   = render seg

-- >>> src <- readFile "programs/rus.s"
-- >>> Right (vis, prog) <- return (surfaceProgram src)
-- >>> fmap (map (renderSteps . rSteps)) (cut prog "t" >>= park vis >>= resolve vis)
-- Right ["keep t in {0,1}; if p { READ3 x t; } else { READ3 x t; }","keep t in {2}; if p { READ3 x t; } else { READ3 x t; }"]

showMat :: Matrix Cyclo -> String
showMat b = "[ " ++ intercalate " ; " (map showVec b) ++ " ]"

-- >>> showMat [[1, 0], [0, 1]]
-- "[ (1,0) ; (0,1) ]"

pad :: Int -> String -> String
pad n s = s ++ replicate (max 1 (n - length s)) ' '

-- >>> pad 6 "ab"
-- "ab    "
-- >>> pad 2 "abcd"
-- "abcd "

passFile :: FilePath -> IO ()
passFile f = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> die ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case passText src of
      Left err  -> die (f ++ ": " ++ err)
      Right out -> putStr out

-- | A refused file is a failure, not a report.
die :: String -> IO ()
die msg = hPutStrLn stderr msg >> exitFailure
