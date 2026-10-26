-- Harness: how a test suite counts its checks and says which failed.
--
-- Question: What do the typed, compile, well-formed and demo suites share?
-- Answer:   A suite makes a 'Counters' value, runs each check through
--           'check1' (a name and a Bool) or 'checkWhy' (a name and either
--           () or the reason it failed), and ends with 'report'. A check
--           prints one line, "  PASS  name" or "  FAIL  name"; a failure
--           from 'checkWhy' also prints its reason on the next line,
--           indented eight spaces. 'report' prints a blank line and
--           "N checks, p passed, f failed", and exits with failure when any
--           check failed. The statement suite (Spec.hs) pairs each claim of
--           the paper with a sentence and counts those itself.
-- Paper:    none (the harness states no claim).
-- Shapes:   Counters   the number of checks passed and the number failed

module Harness
  ( Counters
  , newCounters
  , check1
  , checkWhy
  , report
  ) where

import Control.Monad (unless)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import System.Exit (exitFailure)

-- | The checks passed and the checks failed so far.
data Counters = Counters { cPass :: IORef Int, cFail :: IORef Int }

-- | A fresh count: nothing passed, nothing failed.
newCounters :: IO Counters
newCounters = Counters <$> newIORef 0 <*> newIORef 0

-- | Run one check: count it and print its line.
check1 :: Counters -> String -> Bool -> IO ()
check1 c name ok = do
  modifyIORef' (if ok then cPass c else cFail c) (+ 1)
  putStrLn ((if ok then "  PASS  " else "  FAIL  ") ++ name)

-- | Run one check that can say why it failed: the reason is printed under
-- the FAIL line.
checkWhy :: Counters -> String -> Either String () -> IO ()
checkWhy c name result = do
  check1 c name (result == Right ())
  either (\why -> putStrLn ("        " ++ why)) pure result

-- | Print the totals; exit with failure when any check failed.
report :: Counters -> IO ()
report c = do
  p <- readIORef (cPass c)
  f <- readIORef (cFail c)
  putStrLn ""
  putStrLn (show (p + f) ++ " checks, " ++ show p ++ " passed, " ++ show f ++ " failed")
  unless (f == 0) exitFailure
