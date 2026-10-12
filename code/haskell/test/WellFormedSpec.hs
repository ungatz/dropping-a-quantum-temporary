-- WellFormedSpec.hs: every consumer of an internal program refuses an
-- ill-formed one by name.
--
-- The parser and the statics refuse these programs, but each representation
-- below can be built without them: a flat 'Prog' as a list of commands, a
-- typed 'Program' as a term, a theory program as a constructor tree. An
-- engine that answered on such a program would answer wrongly: a drop is the
-- identity on the state, so a gate after it would run, and the criterion
-- would call the drop safe. One program per rule and per consumer; each must
-- be refused, and the refusal must name what is wrong.

module Main (main) where

import Control.Exception (ErrorCall (..), evaluate, try)
import Data.IORef
import Data.List (isInfixOf)
import System.Exit (exitFailure)

import Drop.Lang.Check (TypeError (..), checkProgram)
import Drop.Lang.Compile (CompileError (..), compile)
import Drop.Lang.Cyclo (Cyclo)
import Drop.Lang.Gates (gCX, gHC, gX)
import Drop.Lang.Interp
import qualified Drop.Lang.Machine as M
import Drop.Lang.Parser (renderCmd)
import Drop.Lang.Pass (chain, chainStopped)
import Drop.Lang.Report.Run (runText, typecheckText)
import Drop.Lang.Syntax
import Drop.Lang.Typed

import qualified Drop.Bridge as B
import qualified Drop.Theory.Lifted as L
import qualified Drop.Theory.Many.Multi as MM
import qualified Drop.Theory.Program.Gates as TG
import qualified Drop.Theory.Program.Machine as TM
import qualified Drop.Theory.Program.Syntax as TS
import qualified Drop.Theory.Program.Typing as TT
import Drop.Theory.Algebra.Scalar (kone, kzero)

type Counter = IORef (Int, Int)

-- | The value, forced in full, must raise an 'error' whose message
-- contains @want@.
refuses :: Show b => Counter -> String -> String -> b -> IO ()
refuses c name want x = do
  r <- try (evaluate (length (show x)))
  case r of
    Left (ErrorCall msg)
      | want `isInfixOf` msg -> pass c name
      | otherwise            -> failWith c name ("refused, but said: " ++ msg)
    Right _ -> failWith c name "answered instead of refusing"

-- | A 'Left' whose rendering contains @want@.
leftWith :: Show e => Counter -> String -> String -> Either e b -> IO ()
leftWith c name want r = case r of
  Left e | want `isInfixOf` show e -> pass c name
         | otherwise               -> failWith c name ("refused, but said: " ++ show e)
  Right _ -> failWith c name "accepted"

check :: Counter -> String -> Bool -> IO ()
check c name ok = if ok then pass c name else failWith c name "false"

pass, failWith' :: Counter -> String -> IO ()
pass c name = modifyIORef c (\(p, f) -> (p + 1, f)) >> putStrLn ("  PASS  " ++ name)
failWith' c name = modifyIORef c (\(p, f) -> (p, f + 1)) >> putStrLn ("  FAIL  " ++ name)

failWith :: Counter -> String -> String -> IO ()
failWith c name why = failWith' c name >> putStrLn ("        " ++ why)

vis :: VisSpec
vis = [("v", 2)]

-- | The verdict at one site, under the empty selection.
at :: Prog Cyclo -> Site -> Verdict
at prog x = semanticVerdictS vis prog x []

main :: IO ()
main = do
  c <- newIORef (0, 0)

  putStrLn "(1) the flat engine, Drop.Lang.Interp"
  refuses c "a gate after the drop of its register" "has been dropped"
    (at [New "t" 2, Gate gHC ["t"], Drop ["t"], Gate gCX ["t", "v"]] ["t"])
  refuses c "a register dropped twice" "has been dropped"
    (at [New "t" 2, Drop ["t"], Drop ["t"]] ["t"])
  refuses c "a gate before the allocation" "no register t"
    (at [Gate gX ["t"], New "t" 2, Drop ["t"]] ["t"])
  refuses c "a dropped name allocated again" "has been dropped"
    (at [New "t" 2, Drop ["t"], New "t" 2, Drop ["t"]] ["t"])
  refuses c "a lift on a dropped register" "has been dropped"
    (verdict vis [New "t" 2, Gate gHC ["t"], Drop ["t"], Lift "p" "t" [1], New "s" 2, Drop ["s"]]
       :: [DropReport])
  refuses c "one register twice in a gate" "named twice"
    (at [New "t" 2, Gate gX ["t"], Gate gCX ["t", "t"], Drop ["t"]] ["t"])
  refuses c "a CX matrix on one register" "rows does not act"
    (at [New "t" 2, Gate gCX ["t"], Drop ["t"]] ["t"])
  refuses c "a register of dimension 0" "at least 2 levels"
    (at [New "t" 0, New "u" 2, Gate gCX ["v", "u"], Drop ["u"]] ["u"])
  refuses c "a state of three amplitudes for a qubit" "needs 2 amplitudes"
    (at [NewState "t" 2 [1, 0, 0], Drop ["t"]] ["t"])
  refuses c "a lift block out of range" "is not a nonempty"
    (verdict vis [New "t" 2, Gate gHC ["t"], Lift "p" "t" [5], Drop ["t"]] :: [DropReport])
  refuses c "a lift block that is every level" "is not a nonempty"
    (verdict vis [New "t" 2, Gate gHC ["t"], Lift "p" "t" [0, 1], Drop ["t"]] :: [DropReport])
  refuses c "a guard on a parameter never lifted, under (0 && q)" "not lifted"
    (at [New "t" 2, IfBit (GAnd (GBit False) (GParam "q")) [Gate gX ["t"]] [], Drop ["t"]] ["t"])
  refuses c "a drop inside an if branch, then a gate after it" "inside an if branch"
    (at [New "t" 2, IfBit (GBit True) [Drop ["t"]] [], Gate gCX ["t", "v"], Drop ["t"]] ["t"])
  refuses c "an allocation inside an if branch" "inside an if branch"
    (at [IfBit (GBit True) [New "u" 2] [], Drop ["u"]] ["u"])
  refuses c "dropSites on a drop inside a branch" "inside an if branch"
    (dropSites ([New "t" 2, IfBit (GBit True) [Drop ["t"]] [Drop ["t"]]] :: Prog Cyclo))
  refuses c "the pass chain on a use after the drop" "has been dropped"
    (chainStopped (chain vis ([New "t" 2, Gate gHC ["t"], Drop ["t"], Gate gCX ["t", "v"]] :: Prog Cyclo) "t"))
  check c "the elaborated form still runs: arms that allocate and drop, run to the end"
    (let prog = [IfBit (GBit True) [New "u" 2, Gate gCX ["v", "u"], Gate gCX ["v", "u"], Drop ["u"]] [New "u" 2, Drop ["u"]]]
         m = runStmts (initMach vis [1, 0]) (prog :: Prog Cyclo) [] Nothing
     in mAmp m == [1, 0, 0, 0])
  check c "a well-formed program keeps its verdict"
    (at [New "t" 2, Gate gCX ["v", "t"], Gate gCX ["v", "t"], Drop ["t"]] ["t"] == Safe)

  putStrLn "(2) the statics, Drop.Lang.Check"
  let prog1 st = Program [("v", 2)] (SDo st (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "v")))) :: Program Cyclo
  check c "a non-unitary gate is refused by the Gate rule's premise"
    (checkProgram nonUnitary == Left (GateNotUnitary ["t"]))
  check c "new with a state that is not a unit vector"
    (checkProgram (prog1 (StNew "t" 2 [1, 1])) == Left (StateNotUnit "t" 2))
  check c "new with a state of the wrong length"
    (checkProgram (prog1 (StNew "t" 2 [1, 0, 0])) == Left (StateLength "t" 2 3))
  check c "a register of dimension 1"
    (checkProgram (prog1 (StNew "t" 1 [1])) == Left (BadDimension "t" 1))
  check c "a header register of dimension 1"
    (checkProgram (Program [("v", 1)] (SReturn (VVar "v")) :: Program Cyclo) == Left (BadDimension "v" 1))

  putStrLn "(3) the five-rule machine, Drop.Lang.Machine"
  let term1 = Do (StNew "t" 2 [1, 0]) (Do (StDrop 0 (VVar "t")) (Do (StGate gX (VVar "t")) (Return (VVar "v"))))
  refuses c "a gate on a register the run has dropped" "which has been dropped"
    (map M.cfgAmp (M.run (M.initConfig vis [1, 0] (term1 :: Term Cyclo))))
  let term2 = Do (StNew "t" 2 [1, 0]) (Do (StLift "p" [0, 1] "t") (Do (StDrop 0 (VVar "t")) (Return (VVar "v"))))
  refuses c "a lift whose block is every level" "nonempty proper"
    (map M.cfgAmp (M.run (M.initConfig vis [1, 0] (term2 :: Term Cyclo))))

  putStrLn "(4) the compiler, Drop.Lang.Compile"
  let gateAfterDrop = Program [("v", 2)] (SDo (StNew "t" 2 [1, 0]) (SDo (StDrop 0 (VVar "t"))
                        (SDo (StGate gCX (VPair (VVar "t") (VVar "v"))) (SReturn (VVar "v"))))) :: Program Cyclo
  check c "a use after the drop is refused by the statics first"
    (case compile gateAfterDrop of Left (NotWellTyped _) -> True; _ -> False)
  let armBinder = Program [("v", 2)] (SIf (BLit False) (SReturn (VVar "v"))
                    (SDo (StNew "u" 2 [1, 0]) (SDo (StGate gCX (VPair (VVar "v") (VVar "u")))
                      (SDo (StDrop 0 (VVar "u")) (SReturn (VVar "v")))))) :: Program Cyclo
  leftWith c "an allocation inside an if branch is outside the fragment" "inside an if branch" (compile armBinder)
  let twice = Program [("v", 2)] (SDo (StNew "t" 2 [1, 0]) (SDo (StDrop 0 (VVar "t"))
                (SDo (StNew "t" 2 [1, 0]) (SDo (StDrop 1 (VVar "t")) (SReturn (VVar "v")))))) :: Program Cyclo
  leftWith c "a name bound twice is outside the fragment" "bound twice" (compile twice)
  let sameSite = Program [("v", 2)] (SDo (StNew "t" 2 [1, 0]) (SDo (StDrop 0 (VVar "t"))
                   (SDo (StNew "u" 2 [1, 0]) (SDo (StDrop 0 (VVar "u")) (SReturn (VVar "v")))))) :: Program Cyclo
  leftWith c "two drops with one site id are outside the fragment" "site id" (compile sameSite)
  let loanBack = Program [("v", 2)] (SDo (StLoan "a" 2) (SReturn (VPair (VVar "v") (VVar "a")))) :: Program Cyclo
  check c "a returned loan is refused by the loan discipline first"
    (case compile loanBack of Left (NotWellTyped _) -> True; _ -> False)

  putStrLn "(5) the reports, Drop.Lang.Report.Run"
  leftWith c "typecheck refuses a non-unitary diag" "not unitary"
    (typecheckText "prog f (r : [2]) : [2] {\n  new t : [2] @ |0>;\n  diag t (2, 1);\n  drop t;\n  return r\n}\n")
  check c "run refuses a returned loan"
    (case runText "prog f (r : [2], loan a : [2]) : [2] * [2] {\n  CX a r;\n  return (r, a)\n}\n" of
       Left e -> "loan is dropped, not returned" `isInfixOf` e
       Right _ -> False)
  check c "a state of the wrong length renders in full, not as a ket"
    (not ("|0>" `isInfixOf` renderCmd (NewState "t" 2 [1, 0, 0])))

  putStrLn "(6) the theory layer"
  let m1 = MM.MProgram "alloc index 2 on a qubit" "v" 2 [MM.MNew "a" 2 0, MM.MNew "b" 2 2, MM.MDrop "a", MM.MDrop "b"]
  leftWith c "Multi: an allocation index outside the register" "allocation index" (MM.scopeCheck m1)
  let m3 = MM.MProgram "CX on one qubit" "v" 2 [MM.MNew "a" 2 0, MM.MApply "CX" TG.mCX ["a"], MM.MDrop "a"]
  leftWith c "Multi: a 4x4 matrix on one qubit" "not a square matrix" (MM.scopeCheck m3)
  let m4 = MM.MProgram "CX on (a,a)" "v" 2 [MM.MNew "a" 2 0, MM.MApply "CX" TG.mCX ["a", "a"], MM.MDrop "a"]
  leftWith c "Multi: one register twice in a gate" "twice" (MM.scopeCheck m4)
  let m5 = MM.MProgram "not unitary" "v" 2 [MM.MNew "a" 2 0, MM.MApply "N" [[kone, kone], [kzero, kone]] ["a"], MM.MDrop "a"]
  leftWith c "Multi: a non-unitary gate" "not unitary" (MM.scopeCheck m5)
  refuses c "Multi: runMulti checks first" "allocation index" (MM.runMulti m1 [kone, kzero])
  let p1 = TS.Program "alloc index 5 on tmp[2]" "v" 2 (TS.New "t" 2 5 (TS.Drop "t" (TS.Ret "v")))
  check c "Bridge: an ill-typed theory program has no translation"
    (case B.toS p1 of Nothing -> True; Just _ -> False)
  refuses c "Theory machine: a gate on a dropped register" "has been dropped"
    (TM.cfgAmp (TM.stepTerm (TM.initConfig "v" 2 [kone, kzero])
       (TS.New "t" 2 0 (TS.Drop "t" (TS.Act ("t1", "v1") (TG.gHt 2) ("t", "v") (TS.Ret "v1"))))))
  leftWith c "Lifted: the core New premise" "allocation index"
    (L.checkLProgram (L.LProgram "bad" "v" 2 (L.LNew "t" 2 5 (L.LDrop "t" (L.LRet "v")))))
  check c "Typing.checkGate is the premise Lifted reuses"
    (case TT.checkGate (TG.gHt 2) 3 2 of Left _ -> True; Right _ -> False)

  (p, f) <- readIORef c
  putStrLn (show p ++ " passed, " ++ show f ++ " failed")
  if f == 0 then pure () else exitFailure

nonUnitary :: Program Cyclo
nonUnitary =
  Program [("v", 2)]
    (SDo (StNew "t" 2 [1, 0])
      (SDo (StGate [[1, 1], [0, 1]] (VVar "t"))
        (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "v")))))
