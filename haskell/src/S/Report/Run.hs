-- Run.hs: running a .s program text and reporting on its drops.
--
-- runText parses, rejects programs the criterion says nothing about (a
-- lift nested in an if, a non-unitary gate), then reports every reachable
-- trace at each drop site: a trace is a selection word over the top-level
-- lifts before the site, so depth d gives 2^d rows. runFile is the same, over a file, printed.

module S.Report.Run
  ( Report (..), SiteReport (..), TraceRow (..)
  , runText, runFile, renderReport, wellFormed
  ) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import System.IO (hPutStrLn, stderr)

import S.Lang.Ring (Amp (..), Conj (..))
import S.Lang.Cyclo (Cyclo)
import S.Lang.QState
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass (liftInside)
import S.Lang.Parser

-- Report

-- | One trace at one drop site: the selection word, the criterion's verdict,
-- and, when the drop is accepted, the line the temporary is left on.
data TraceRow = TraceRow
  { trSel     :: [Sel]
  , trVerdict :: Verdict
  , trLine    :: Maybe (StateV Cyclo)
  } deriving Show

data SiteReport = SiteReport
  { srSite  :: String
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

siteReport :: VisSpec -> Prog Cyclo -> String -> SiteReport
siteReport vis prog x = SiteReport x d [ row sel | sel <- allSelections d ]
  where
    d   = liftDepthBefore prog x
    pre = prefixThrough prog x
    row sel = TraceRow sel v (if v == Admissible
                                then semanticParked vis pre x sel
                                else Nothing)
      where v = semanticVerdict vis pre x sel

-- Printing

showVec :: [Cyclo] -> String
showVec v = "(" ++ intercalate "," (map showAmp v) ++ ")"

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
                               ds -> unwords ds))
  : concatMap site sites
  where
    site (SiteReport x d rows) =
      ("drop " ++ x ++ " (depth " ++ show d ++ "):")
      : map (line x) rows
    line _ (TraceRow sel v ln) = case ln of
      Nothing -> "  trace " ++ pad 6 (bitsOf sel) ++ show v
      Just g  -> "  trace " ++ pad 6 (bitsOf sel) ++ pad 14 (show v)
                 ++ "line " ++ showVec g

-- | Read a file, report on it, and print the report.  A parse error or a
-- refused program goes to standard error.
runFile :: FilePath -> IO ()
runFile f = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> hPutStrLn stderr ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case runText src of
      Left err  -> hPutStrLn stderr (f ++ ": " ++ err)
      Right rep -> putStr (renderReport rep)

-- Programs the criterion says nothing about

wellFormed :: Amp a => Prog a -> Maybe String
wellFormed prog
  | liftInside prog =
      Just "a `lift` nested inside an `if` is not supported: selections allot \
           \one bit per top-level lift. Lift before the `if`, or branch on \
           \an already-lifted bit."
  | otherwise = case [ u | Gate u _ <- flatten prog, not (isUnitary u) ] of
      []      -> Nothing
      (u : _) -> Just ("gate matrix is not unitary (U U^H is not I): "
                       ++ showMat u
                       ++ ". The criterion is stated for unitary computations, \
                          \so a verdict here would be about an object the \
                          \theory does not cover.")
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
