-- DemoSpec: program (c) of the paper, lowered, exposed and witnessed, compared exactly.
--
-- Question: Do the other forms of program (c) compute what program (c) computes?
-- Answer:   Four checks, all on the exact amplitudes of Drop.Lang.Interp (no
--           tolerance). (1) After its lift, programs/c.s and its lowering to
--           one-qubit gates and CX (programs/c-decomposed.s) act alike on
--           every basis state of the temporary and the visible register.
--           (2) On the kept record, programs/c-exposed.s has the map of
--           programs/c-witness.s, whose extra register stays at |0>. (3) The
--           weight of that record depends on the input: 2 on (1,1) and 0 on
--           (1,-1). (4) The witness the paper prints for (c)
--           (examples/paper/c-kept-record-witness.s) returns v and matches
--           programs/c.s on the kept record. The suite runs every check
--           and reports; only a program that fails to load stops it.
-- Paper:    thm:perrecord, fig:record-witness, sec:meas:programs
-- Shapes:   a program is a list of commands (Cmd Cyclo), loaded from a file;
--           an amplitude list is the state a run ends in

module Main (main) where

import System.Exit (die)

import Drop.Lang.Scalar (Cyclo)
import Drop.Lang.Interp (initMach, runStmts, mAmp)
import Drop.Lang.Parser (parseFile)
import Drop.Lang.Render (SFile (..))
import Drop.Lang.State (norm2S)
import Drop.Lang.Flat (Cmd (..), Sel (..), VisSpec)

import Harness (Counters, check1, newCounters, report)

-- | The commands of a program file, or the reason it did not load.
load :: FilePath -> IO [Cmd Cyclo]
load path = do
  src <- readFile path
  either die (pure . sfBody) (parseFile src)

-- | The i-th computational basis vector of dimension d.
basis :: Int -> Int -> [Cyclo]
basis d i = [if j == i then 1 else 0 | j <- [0 .. d - 1]]

-- | The commands after the first lift and before the first drop.
afterLift :: [Cmd Cyclo] -> [Cmd Cyclo]
afterLift = takeWhile notDrop . drop 1 . dropWhile notLift
  where
    notLift Lift{} = False
    notLift _ = True
    notDrop Drop{} = False
    notDrop _ = True

-- | The amplitudes a run ends in, for the given registers, record and input.
execute :: VisSpec -> [Cmd Cyclo] -> [Sel] -> [Cyclo] -> [Cyclo]
execute vis cmds sel input = mAmp (runStmts (initMach vis input) cmds sel Nothing)

-- | The record that keeps the lift's outcome 1.
kept :: [Sel]
kept = [SIn]

-- (1) After the lift, the lowered program acts as program (c).
loweringAgrees :: Counters -> IO ()
loweringAgrees c = do
  original <- load "programs/c.s"
  lowered <- load "programs/c-decomposed.s"
  let vAction cmds = execute [("t", 2), ("q", 2)] (afterLift cmds) []
  check1 c "V lowering agrees on every basis column, exactly"
    (all (\i -> vAction original (basis 4 i) == vAction lowered (basis 4 i)) [0 .. 3])

-- (2) and (3) The exposed form on the kept record: its map is the witness's, and its weight varies.
keptRecordMatchesWitness :: Counters -> IO ()
keptRecordMatchesWitness c = do
  exposed <- load "programs/c-exposed.s"
  witness <- load "programs/c-witness.s"
  let source input = execute [("q", 2)] exposed kept input
      target input = execute [("q", 2)] witness kept input
      -- impossible: the witness has three registers of two levels, so its amplitude list has 8 entries
      omitA amp = [amp !! (2 * i) | i <- [0 .. 3]]
      -- impossible: the same 8 entries
      zeroA amp = all (== 0) [amp !! (2 * i + 1) | i <- [0 .. 3]]
  check1 c "program (c)'s exposed kept-record map equals its witness, exactly"
    (all (\i -> let amp = target (basis 2 i)
                in zeroA amp && source (basis 2 i) == omitA amp) [0 .. 1])
  check1 c "the kept-record weight depends on the input"
    (norm2S (source [1, 1]) == 2 && norm2S (source [1, -1]) == 0)

-- (4) The witness the paper prints returns v and matches program (c) on the kept record.
paperWitnessMatches :: Counters -> IO ()
paperWitnessMatches c = do
  paperC <- load "programs/c.s"
  paperWitness <- load "examples/paper/c-kept-record-witness.s"
  let cKept input = execute [("q", 2)] paperC kept input
      witnessKept input = execute [("v", 2)] paperWitness kept input
      -- impossible: program (c) holds q and t, two registers of two levels, so its list has 4 entries
      cReturned input = [cKept input !! (2 * i) | i <- [0 .. 1]]
      -- impossible: the witness holds v, t and a, three registers of two levels, so its list has 8 entries
      witnessReturned input = [witnessKept input !! (4 * i) | i <- [0 .. 1]]
      -- impossible: the 4 entries of program (c)
      cHiddenZero input = all (== 0) [cKept input !! (2 * i + 1) | i <- [0 .. 1]]
      witnessHiddenZero input = all (== 0)
        [witnessKept input !! j | j <- [0 .. 7], j `mod` 4 /= 0]  -- impossible: the 8 entries of the witness
  check1 c "paper's program-(c) kept-record witness returns v and matches c exactly"
    (all (\i -> let input = basis 2 i
                in cHiddenZero input && witnessHiddenZero input
                   && cReturned input == witnessReturned input) [0 .. 1])

main :: IO ()
main = do
  c <- newCounters
  loweringAgrees c
  keptRecordMatchesWitness c
  paperWitnessMatches c
  report c
