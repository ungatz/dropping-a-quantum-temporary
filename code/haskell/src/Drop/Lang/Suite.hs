-- Drop.Lang.Suite: every check of the language layer, and the table of drop verdicts the paper's programs give.
--
-- Question: What does the language layer say at every drop of the programs of the paper, and do all its checks hold?
-- Answer:   The suite is a list of named groups of checks: a group for each textbook algorithm, one
--           for the tilt family, and one each for the infrastructure (the scalar field, the bounded
--           enumeration, the concrete syntax, the passes). suiteGroups builds the list from the
--           corpus, and suiteCheckCount counts its checks, so no printed count is written down.
--           suiteRun reads the corpus, prints one row for each program and drop site (how many
--           selections, how many are safe, unsafe and unreachable, and whether the runtime check
--           agrees with the criterion), then runs each group and prints how many of its checks
--           pass and the name of every one that fails. It returns the number of failing checks;
--           suiteMain turns that into the exit status. Printing is this module's job (the only IO
--           here is suiteRun and suiteMain).
-- Paper:    sec:lang:algorithms (the algorithms as programs), app:corpus (the corpus, site by site),
--           sec:boundary (why the record matters), thm:notext (the verdict is record-dependent).
-- Shapes:   GroupKind       Algorithm, Boundary or Infrastructure: what a group is about.
--           Group           a name, a kind and the checks (a name and whether it holds).
--           suiteGroups     the groups, in the order they run, given the corpus.
--           Row             one summary line: program, drop site, selections, safe, unsafe,
--                           unreachable, and whether the runtime check agrees.

module Drop.Lang.Suite
  ( GroupKind (..), Group (..)
  , suiteGroups, suiteCheckCount, suiteAlgorithms
  , suiteMain, suiteRun
  ) where

import Data.List (intercalate)
import System.Exit (exitFailure, exitSuccess)
import Drop.Lang.Scalar
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass
import qualified Drop.Lang.Scalar as Cyclo
import qualified Drop.Lang.Programs.BV as BV
import qualified Drop.Lang.Programs.DJ as DJ
import qualified Drop.Lang.Programs.Grover as Grover
import qualified Drop.Lang.Programs.QPE as QPE
import qualified Drop.Lang.Programs.RUS as RUS
import qualified Drop.Lang.Programs.Shor as Shor
import qualified Drop.Lang.Programs.Simon as Simon
import qualified Drop.Lang.Programs.Superdense as Superdense
import qualified Drop.Lang.Programs.Teleport as Teleport
import qualified Drop.Lang.Programs.TempAnd as TempAnd
import qualified Drop.Lang.Programs.Tilt as Tilt
import qualified Drop.Lang.Checks.Exhaustive as TestExhaustive
import Drop.Lang.Checks.Parser (Corpus, readCorpus)
import qualified Drop.Lang.Checks.Parser as TestParser
import qualified Drop.Lang.Checks.Pass as TestPass

-- The Groups

-- | What a group is about.  Algorithm groups are the textbook algorithms of
-- the corpus table; Boundary is the tilt family, the artifact's witness for the
-- boundary result (sec:boundary; the paper prints it on a qubit, thm:notext);
-- Infrastructure is the scalar field, the bounded enumeration, the concrete
-- syntax and the passes.
data GroupKind = Algorithm | Boundary | Infrastructure deriving (Eq, Show)

-- >>> [Algorithm, Boundary, Infrastructure]
-- [Algorithm,Boundary,Infrastructure]
-- >>> Algorithm == Boundary
-- False

data Group = Group

-- A group is its name, its kind and its checks.
-- >>> let demo = Group "demo" Boundary [("holds", True), ("fails", False)]
-- >>> (gName demo, gKind demo, map fst (gChecks demo))
-- ("demo",Boundary,["holds","fails"])

  { gName   :: String
  , gKind   :: GroupKind
  , gChecks :: [(String, Bool)]
  }

suiteGroups :: Corpus -> [Group]
suiteGroups corpus =
  [ Group "DJ"         Algorithm      DJ.checks
  , Group "BV"         Algorithm      BV.checks
  , Group "Grover"     Algorithm      Grover.checks
  , Group "QPE"        Algorithm      QPE.checks
  , Group "superdense" Algorithm      Superdense.checks
  , Group "teleport"   Algorithm      Teleport.checks
  , Group "RUS"        Algorithm      RUS.checks
  , Group "Shor"       Algorithm      Shor.checks
  , Group "Simon"      Algorithm      Simon.checks
  , Group "temp-AND"   Algorithm      TempAnd.checks
  , Group "tilt"       Boundary       Tilt.checks
  , Group "scalars"    Infrastructure Cyclo.cycloChecks
  , Group "exhaustive" Infrastructure TestExhaustive.checks
  , Group "syntax"     Infrastructure (TestParser.checks corpus)
  , Group "passes"     Infrastructure (TestPass.checks corpus)
  ]

-- The groups, in the order they run: the algorithms, the tilt family, then the infrastructure.
-- >>> corpus <- readCorpus
-- >>> map gName (suiteGroups corpus)
-- ["DJ","BV","Grover","QPE","superdense","teleport","RUS","Shor","Simon","temp-AND","tilt","scalars","exhaustive","syntax","passes"]
-- >>> [ gKind g | g <- suiteGroups corpus, gKind g /= Algorithm ]
-- [Boundary,Infrastructure,Infrastructure,Infrastructure,Infrastructure]

-- | How many individual checks the suite runs.  Computed, never written
-- down.
suiteCheckCount :: Corpus -> Int
suiteCheckCount corpus = sum (map (length . gChecks) (suiteGroups corpus))

-- >>> corpus <- readCorpus
-- >>> suiteCheckCount corpus
-- 279
-- >>> [ (gName g, length (gChecks g)) | g <- take 3 (suiteGroups corpus) ]
-- [("DJ",20),("BV",12),("Grover",5)]

-- | The groups that are textbook algorithms, by name.  A group's name and
-- kind do not depend on what was read, so no file is needed to list them.
suiteAlgorithms :: [String]
suiteAlgorithms = [ gName g | g <- suiteGroups [], gKind g == Algorithm ]

-- >>> suiteAlgorithms
-- ["DJ","BV","Grover","QPE","superdense","teleport","RUS","Shor","Simon","temp-AND"]

-- The Summary Table

-- | One summary line: the program, the drop site, the number of selections,
-- how many are safe, unsafe and unreachable, and whether the runtime check
-- agrees with the criterion on all of them.
data Row = Row String String Int Int Int Int String

-- A row is printed in columns.
-- >>> printRow (Row "demo" "t" 2 1 1 0 "yes (2/2)")
-- demo                              t     2       1      1        0       yes (2/2)

mkRow :: Amp a => String -> VisSpec -> Prog a -> String -> Row
mkRow name vis prog target =
  Row name target (length sels) nSafe nUnsafe nUnre agreeStr
  where
    d       = liftDepthBefore prog target
    sels    = allSelections d
    svs     = [ semanticVerdict vis prog target sel | sel <- sels ]
    nSafe   = length [ () | Safe   <- svs ]
    nUnsafe = length [ () | Unsafe <- svs ]
    nUnre   = length [ () | Unreachable  <- svs ]
    rep     = residualCheck vis prog target
    ags     = [ agreeRC (reVerdict e) sv | (e, sv) <- zip (rTable rep) svs ]
    agreeStr
      | Disagree `elem` ags   = "DISAGREES"
      | all (== Declines) ags = "declines"
      | all (== Agree) ags    = "yes (" ++ show (length ags) ++ "/"
                                        ++ show (length ags) ++ ")"
      | otherwise             = "mixed"

-- Deutsch-Jozsa with f = x: one site, no lift, so one selection, and it is safe.
-- >>> printRow (mkRow "DJ f=x" DJ.visDJ (DJ.djProg DJ.fId) "t")
-- DJ f=x                            t     1       1      0        0       yes (1/1)

-- Without the uncompute the same drop is unsafe.
-- >>> printRow (mkRow "DJ f=x, no uncompute" DJ.visDJ (DJ.djNoUncompute DJ.fId) "t")
-- DJ f=x, no uncompute              t     1       0      1        0       yes (1/1)

-- Teleportation drops the measured register m: four selections, all safe, and the runtime check declines.
-- >>> printRow (mkRow "teleport drop m" Teleport.visT Teleport.teleP "m")
-- teleport drop m                   m     4       4      0        0       declines

pad :: Int -> String -> String
pad n s = s ++ replicate (max 1 (n - length s)) ' '

-- >>> pad 6 "ab"
-- "ab    "
-- >>> pad 2 "abcd"
-- "abcd "

printRow :: Row -> IO ()
printRow (Row nm site nsel safe unsafe unre agr) =
  putStrLn $ pad 34 nm ++ pad 6 site ++ pad 8 (show nsel)
           ++ pad 7 (show safe) ++ pad 9 (show unsafe)
           ++ pad 8 (show unre) ++ agr

-- >>> printRow (Row "demo" "t" 2 1 1 0 "yes (2/2)")
-- demo                              t     2       1      1        0       yes (2/2)

rowsQS2 :: [Row]
rowsQS2 =
  [ mkRow ("DJ " ++ nm) DJ.visDJ (DJ.djProg f) "t"
  | (nm, f) <- DJ.oracles ]
  ++
  [ mkRow "DJ f=x, no uncompute" DJ.visDJ (DJ.djNoUncompute DJ.fId) "t"
  , mkRow "Grover 1 iteration"   Grover.visG Grover.groverProg "t"
  , mkRow "Grover, no uncompute" Grover.visG Grover.groverBroken "t"
  ]
  ++
  [ mkRow ("BV s=" ++ show s1 ++ show s2) BV.visBV (BV.bvProg s1 s2) "t"
  | (s1, s2) <- BV.strings ]
  ++
  [ mkRow ("teleport drop " ++ tgt) Teleport.visT Teleport.teleP tgt
  | tgt <- ["m", "a"] ]
  ++
  [ mkRow ("superdense " ++ show b0 ++ show b1) Superdense.visSD
          (Superdense.superdenseProg (b0, b1)) "a"
  | (b0, b1) <- Superdense.bitPairs ]

-- >>> length rowsQS2
-- 17
-- >>> printRow (rowsQS2 !! 0)
-- DJ f=0                            t     1       1      0        0       yes (1/1)

rowsRat :: [Row]
rowsRat =
  [ mkRow "tilt (1/3 matrix)"        Tilt.visTilt Tilt.tiltProg  "t"
  , mkRow "tilt (3/5-4/5 rotations)" Tilt.visTilt Tilt.tilt2Prog "t"
  , mkRow "RUS iteration, unrolled"  RUS.visR     RUS.rusProg    "t"
  ]

-- >>> mapM_ printRow rowsRat
-- tilt (1/3 matrix)                 t     2       1      1        0       yes (2/2)
-- tilt (3/5-4/5 rotations)          t     2       1      1        0       yes (2/2)
-- RUS iteration, unrolled           t     2       1      1        0       yes (2/2)

rowsCyclo :: [Row]
rowsCyclo =
  [ mkRow "QPE(T), 3 counting qubits" QPE.visQPE QPE.qpeT "psi" ]

-- >>> mapM_ printRow rowsCyclo
-- QPE(T), 3 counting qubits         psi   1       1      0        0       yes (1/1)

-- The Runner

runGroup :: Group -> IO Int
runGroup (Group gname _ cs) = do
  let failures = [ nm | (nm, ok) <- cs, not ok ]
  putStrLn $ pad 14 gname ++ show (length cs - length failures) ++ "/"
           ++ show (length cs) ++ " checks pass"
  mapM_ (\nm -> putStrLn ("  FAIL: " ++ nm)) failures
  return (length failures)

-- A group of checks that all hold prints one line and counts no failure.
-- >>> runGroup (Group "demo" Algorithm [("holds", True)])
-- demo          1/1 checks pass
-- 0

-- | Run the whole suite and return the number of failing checks.  The
-- process-exiting wrapper is 'suiteMain'; this one returns so that a red
-- check does not kill the rest of the run.
suiteRun :: IO Int
suiteRun = do
  corpus <- readCorpus
  putStrLn (replicate 84 '=')
  putStrLn ("language layer: " ++ show (suiteCheckCount corpus) ++ " checks in "
            ++ show (length (suiteGroups corpus)) ++ " groups")
  putStrLn ("algorithms covered (" ++ show (length suiteAlgorithms) ++ "): "
            ++ intercalate ", " suiteAlgorithms)
  putStrLn "drop verdicts per program, drop site and selection"
  putStrLn (replicate 84 '=')
  putStrLn $ pad 34 "program" ++ pad 6 "drop" ++ pad 8 "#sel"
           ++ pad 7 "#safe" ++ pad 9 "#unsafe" ++ pad 8 "#unre"
           ++ "runtime check agrees?"
  putStrLn (replicate 84 '-')
  mapM_ printRow rowsQS2
  mapM_ printRow rowsRat
  mapM_ printRow rowsCyclo
  putStrLn (replicate 84 '=')
  nfails <- mapM runGroup (suiteGroups corpus)
  putStrLn (replicate 84 '=')
  let total = sum nfails
  if total == 0
    then putStrLn "ALL CHECKS PASS"
    else putStrLn (show total ++ " CHECKS FAILED")
  return total

-- The whole suite: the table of verdicts, then each group. A zero means no check failed.
-- >>> suiteRun
-- ====================================================================================
-- language layer: 279 checks in 15 groups
-- algorithms covered (10): DJ, BV, Grover, QPE, superdense, teleport, RUS, Shor, Simon, temp-AND
-- drop verdicts per program, drop site and selection
-- ====================================================================================
-- program                           drop  #sel    #safe  #unsafe  #unre   runtime check agrees?
-- ------------------------------------------------------------------------------------
-- DJ f=0                            t     1       1      0        0       yes (1/1)
-- DJ f=1                            t     1       1      0        0       yes (1/1)
-- DJ f=x                            t     1       1      0        0       yes (1/1)
-- DJ f=1-x                          t     1       1      0        0       yes (1/1)
-- DJ f=x, no uncompute              t     1       0      1        0       yes (1/1)
-- Grover 1 iteration                t     1       1      0        0       yes (1/1)
-- Grover, no uncompute              t     1       0      1        0       yes (1/1)
-- BV s=00                           t     1       1      0        0       yes (1/1)
-- BV s=01                           t     1       1      0        0       yes (1/1)
-- BV s=10                           t     1       1      0        0       yes (1/1)
-- BV s=11                           t     1       1      0        0       yes (1/1)
-- teleport drop m                   m     4       4      0        0       declines
-- teleport drop a                   a     4       4      0        0       declines
-- superdense 00                     a     4       2      0        2       yes (4/4)
-- superdense 01                     a     4       2      0        2       yes (4/4)
-- superdense 10                     a     4       2      0        2       yes (4/4)
-- superdense 11                     a     4       2      0        2       yes (4/4)
-- tilt (1/3 matrix)                 t     2       1      1        0       yes (2/2)
-- tilt (3/5-4/5 rotations)          t     2       1      1        0       yes (2/2)
-- RUS iteration, unrolled           t     2       1      1        0       yes (2/2)
-- QPE(T), 3 counting qubits         psi   1       1      0        0       yes (1/1)
-- ====================================================================================
-- DJ            20/20 checks pass
-- BV            12/12 checks pass
-- Grover        5/5 checks pass
-- QPE           13/13 checks pass
-- superdense    12/12 checks pass
-- teleport      14/14 checks pass
-- RUS           5/5 checks pass
-- Shor          6/6 checks pass
-- Simon         5/5 checks pass
-- temp-AND      15/15 checks pass
-- tilt          15/15 checks pass
-- scalars       11/11 checks pass
-- exhaustive    11/11 checks pass
-- syntax        127/127 checks pass
-- passes        8/8 checks pass
-- ====================================================================================
-- ALL CHECKS PASS
-- 0

suiteMain :: IO ()
suiteMain = do
  n <- suiteRun
  if n == 0 then exitSuccess else exitFailure
