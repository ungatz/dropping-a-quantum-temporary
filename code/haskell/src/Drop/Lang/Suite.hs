-- Suite.hs: the check suite for the language layer.
--
-- Prints one summary row per program and drop site, then runs every named
-- group of checks.  The suite's size is derived from the group list rather
-- than written down, so no printed count can go stale.

module Drop.Lang.Suite
  ( GroupKind (..), Group (..)
  , suiteGroups, suiteCheckCount, suiteAlgorithms
  , suiteMain, suiteRun
  ) where

import Data.List (intercalate)
import System.Exit (exitFailure, exitSuccess)
import Drop.Lang.Ring
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Pass
import qualified Drop.Lang.Cyclo as Cyclo
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
import qualified Drop.Lang.Checks.Parser as TestParser
import qualified Drop.Lang.Checks.Pass as TestPass

-- The Groups

-- | What a group is about.  Algorithm groups are the textbook algorithms of
-- the corpus table; Boundary is the program the boundary result
-- (the section on why the record matters) is proved with; Infrastructure is the scalar field, the
-- bounded enumeration and the concrete syntax.
data GroupKind = Algorithm | Boundary | Infrastructure deriving (Eq, Show)

data Group = Group
  { gName   :: String
  , gKind   :: GroupKind
  , gChecks :: [(String, Bool)]
  }

suiteGroups :: [Group]
suiteGroups =
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
  , Group "syntax"     Infrastructure TestParser.checks
  , Group "passes"     Infrastructure TestPass.checks
  ]

-- | How many individual checks the suite runs.  Computed, never written
-- down.
suiteCheckCount :: Int
suiteCheckCount = sum (map (length . gChecks) suiteGroups)

-- | The groups that are textbook algorithms, by name.
suiteAlgorithms :: [String]
suiteAlgorithms = [ gName g | g <- suiteGroups, gKind g == Algorithm ]

-- The Summary Table

-- | One summary line: the program, the drop site, the number of selections,
-- how many are safe, unsafe and unreachable, and whether the runtime check
-- agrees with the criterion on all of them.
data Row = Row String String Int Int Int Int String

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

pad :: Int -> String -> String
pad n s = s ++ replicate (max 1 (n - length s)) ' '

printRow :: Row -> IO ()
printRow (Row nm site nsel safe unsafe unre agr) =
  putStrLn $ pad 34 nm ++ pad 6 site ++ pad 8 (show nsel)
           ++ pad 7 (show safe) ++ pad 9 (show unsafe)
           ++ pad 8 (show unre) ++ agr

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

rowsRat :: [Row]
rowsRat =
  [ mkRow "tilt (1/3 matrix)"        Tilt.visTilt Tilt.tiltProg  "t"
  , mkRow "tilt (3/5-4/5 rotations)" Tilt.visTilt Tilt.tilt2Prog "t"
  , mkRow "RUS iteration, unrolled"  RUS.visR     RUS.rusProg    "t"
  ]

rowsCyclo :: [Row]
rowsCyclo =
  [ mkRow "QPE(T), 3 counting qubits" QPE.visQPE QPE.qpeT "psi" ]

-- The Runner

runGroup :: Group -> IO Int
runGroup (Group gname _ cs) = do
  let failures = [ nm | (nm, ok) <- cs, not ok ]
  putStrLn $ pad 14 gname ++ show (length cs - length failures) ++ "/"
           ++ show (length cs) ++ " checks pass"
  mapM_ (\nm -> putStrLn ("  FAIL: " ++ nm)) failures
  return (length failures)

-- | Run the whole suite and return the number of failing checks.  The
-- process-exiting wrapper is 'suiteMain'; this one returns so that a red
-- check does not kill the rest of the run.
suiteRun :: IO Int
suiteRun = do
  putStrLn (replicate 84 '=')
  putStrLn ("language layer: " ++ show suiteCheckCount ++ " checks in "
            ++ show (length suiteGroups) ++ " groups")
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
  nfails <- mapM runGroup suiteGroups
  putStrLn (replicate 84 '=')
  let total = sum nfails
  if total == 0
    then putStrLn "ALL CHECKS PASS"
    else putStrLn (show total ++ " CHECKS FAILED")
  return total

suiteMain :: IO ()
suiteMain = do
  n <- suiteRun
  if n == 0 then exitSuccess else exitFailure
