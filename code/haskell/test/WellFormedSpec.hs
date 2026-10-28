-- WellFormedSpec: every consumer of an internal program refuses an ill-formed one by name.
--
-- Question: When a program is built without the parser or the statics, does
--           each consumer of it refuse the ill-formed ones, and say why?
-- Answer:   The parser and the statics refuse these programs, but each
--           representation below can be built without them: a flat list of
--           commands, a typed program as a term, a theory program as a
--           constructor tree. An engine that answered on such a program
--           would answer wrongly: a drop is the identity on the state, so a
--           gate after it would run, and the criterion would call the drop
--           safe. The suite gives one program per rule and per consumer
--           (the flat engine, the statics, the five-rule machine, the
--           compiler, the reports, the theory layer); each must be refused,
--           and the refusal must name what is wrong. Parser boundary checks
--           also cover integer limits, block names and gate value forms.
-- Paper:    sec:lang:statics, sec:lang:dynamics, sec:lang:compile, app:implementation
-- Shapes:   a flat program is a list of commands (Prog Cyclo); a typed
--           program is a term (Program Cyclo); a theory program is a tree
--           (Drop.Theory.Program.Syntax.Program); a refusal is an 'error' or a Left

module Main (main) where

import Control.Exception (ErrorCall (..), evaluate, try)
import Data.List (isInfixOf)

import Drop.Lang.Check (TypeError (..), checkProgram)
import Drop.Lang.Compile (CompileError (..), compile)
import Drop.Lang.Scalar (Cyclo)
import Drop.Lang.Gates (gCX, gHC, gX)
import Drop.Lang.Interp
import Drop.Lang.Criterion
import qualified Drop.Lang.Machine as M
import Drop.Lang.Parser (parseFile, parseProgram)
import Drop.Lang.Render (renderCmd)
import Drop.Lang.Pass (chain, chainStopped)
import Drop.Lang.Report.Run (runText, typecheckText)
import Drop.Lang.Flat
import Drop.Lang.Syntax

import qualified Drop.Bridge as B
import qualified Drop.Theory.Lifted as L
import qualified Drop.Theory.Many.Multi as MM
import qualified Drop.Theory.Program.Gates as TG
import qualified Drop.Theory.Program.Machine as TM
import qualified Drop.Theory.Program.Syntax as TS
import qualified Drop.Theory.Program.Typing as TT
import Drop.Theory.Algebra.Scalar (kone, kzero)

import Harness (Counters, check1, checkWhy, newCounters, report)

-- | The value, forced in full, must raise an 'error' whose message
-- contains @want@.
refuses :: Show b => Counters -> String -> String -> b -> IO ()
refuses c name want x = do
  r <- try (evaluate (length (show x)))
  checkWhy c name $ case r of
    Left (ErrorCall msg)
      | want `isInfixOf` msg -> Right ()
      | otherwise            -> Left ("refused, but said: " ++ msg)
    Right _ -> Left "answered instead of refusing"

-- | A 'Left' whose rendering contains @want@.
leftWith :: Show e => Counters -> String -> String -> Either e b -> IO ()
leftWith c name want r = checkWhy c name $ case r of
  Left e | want `isInfixOf` show e -> Right ()
         | otherwise               -> Left ("refused, but said: " ++ show e)
  Right _ -> Left "accepted"

-- | The one visible register of the flat programs below.
vis :: VisSpec
vis = [("v", 2)]

-- | The verdict at one site, under the empty selection.
at :: Prog Cyclo -> Site -> Verdict
at prog x = semanticVerdictS vis prog x []

-- | Each ill-formed program of the flat engine is refused, and the refusal names what is wrong.
flatEngineRefusesIllFormed :: Counters -> IO ()
flatEngineRefusesIllFormed c = do
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
  check1 c "the elaborated form still runs: arms that allocate and drop, run to the end"
    (let prog = [IfBit (GBit True) [New "u" 2, Gate gCX ["v", "u"], Gate gCX ["v", "u"], Drop ["u"]] [New "u" 2, Drop ["u"]]]
         m = runStmts (initMach vis [1, 0]) (prog :: Prog Cyclo) [] Nothing
     in mAmp m == [1, 0, 0, 0])
  check1 c "a well-formed program keeps its verdict"
    (at [New "t" 2, Gate gCX ["v", "t"], Gate gCX ["v", "t"], Drop ["t"]] ["t"] == Safe)

-- | Each ill-formed program of the statics is refused, and the refusal names what is wrong.
staticsRefuseIllFormed :: Counters -> IO ()
staticsRefuseIllFormed c = do
  putStrLn "(2) the statics, Drop.Lang.Check"
  let prog1 st = Program [("v", 2)] (SDo st (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "v")))) :: Program Cyclo
  check1 c "a non-unitary gate is refused by the Gate rule's premise"
    (checkProgram nonUnitary == Left (GateNotUnitary ["t"]))
  check1 c "new with a state that is not a unit vector"
    (checkProgram (prog1 (StNew "t" 2 [1, 1])) == Left (StateNotUnit "t" 2))
  check1 c "new with a state of the wrong length"
    (checkProgram (prog1 (StNew "t" 2 [1, 0, 0])) == Left (StateLength "t" 2 3))
  check1 c "a register of dimension 1"
    (checkProgram (prog1 (StNew "t" 1 [1])) == Left (BadDimension "t" 1))
  check1 c "a header register of dimension 1"
    (checkProgram (Program [("v", 1)] (SReturn (VVar "v")) :: Program Cyclo) == Left (BadDimension "v" 1))

-- | Each ill-formed program of the five-rule machine is refused, and the refusal names what is wrong.
machineRefusesIllFormed :: Counters -> IO ()
machineRefusesIllFormed c = do
  putStrLn "(3) the five-rule machine, Drop.Lang.Machine"
  let term1 = Do (StNew "t" 2 [1, 0]) (Do (StDrop 0 (VVar "t")) (Do (StGate gX (VVar "t")) (Return (VVar "v"))))
  refuses c "a gate on a register the run has dropped" "which has been dropped"
    (map M.cfgAmp (M.run (M.initConfig vis [1, 0] (term1 :: Term Cyclo))))
  let term2 = Do (StNew "t" 2 [1, 0]) (Do (StLift "p" [0, 1] "t") (Do (StDrop 0 (VVar "t")) (Return (VVar "v"))))
  refuses c "a lift whose block is every level" "nonempty proper"
    (map M.cfgAmp (M.run (M.initConfig vis [1, 0] (term2 :: Term Cyclo))))

-- | Each ill-formed program of the compiler is refused, and the refusal names what is wrong.
compilerRefusesIllFormed :: Counters -> IO ()
compilerRefusesIllFormed c = do
  putStrLn "(4) the compiler, Drop.Lang.Compile"
  let gateAfterDrop = Program [("v", 2)] (SDo (StNew "t" 2 [1, 0]) (SDo (StDrop 0 (VVar "t"))
                        (SDo (StGate gCX (VPair (VVar "t") (VVar "v"))) (SReturn (VVar "v"))))) :: Program Cyclo
  check1 c "a use after the drop is refused by the statics first"
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
  check1 c "a returned loan is refused by the loan discipline first"
    (case compile loanBack of Left (NotWellTyped _) -> True; _ -> False)

-- | Each ill-formed program of the reports is refused, and the refusal names what is wrong.
reportsRefuseIllFormed :: Counters -> IO ()
reportsRefuseIllFormed c = do
  putStrLn "(5) the reports, Drop.Lang.Report.Run"
  leftWith c "typecheck refuses a non-unitary diag" "not unitary"
    (typecheckText "prog f (r : [2]) : [2] {\n  new t : [2] @ |0>;\n  diag t (2, 1);\n  drop t;\n  return r\n}\n")
  check1 c "run refuses a returned loan"
    (case runText "prog f (r : [2], loan a : [2]) : [2] * [2] {\n  CX a r;\n  return (r, a)\n}\n" of
       Left e -> "loan is dropped, not returned" `isInfixOf` e
       Right _ -> False)
  check1 c "a state of the wrong length renders in full, not as a ket"
    (not ("|0>" `isInfixOf` renderCmd (NewState "t" 2 [1, 0, 0])))

-- | Each ill-formed program of the theory layer is refused, and the refusal names what is wrong.
theoryLayerRefusesIllFormed :: Counters -> IO ()
theoryLayerRefusesIllFormed c = do
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
  check1 c "Bridge: an ill-typed theory program has no translation"
    (case B.toS p1 of Nothing -> True; Just _ -> False)
  refuses c "Theory machine: a gate on a dropped register" "has been dropped"
    (TM.cfgAmp (TM.stepTerm (TM.initConfig "v" 2 [kone, kzero])
       (TS.New "t" 2 0 (TS.Drop "t" (TS.Act ("t1", "v1") (TG.gHt 2) ("t", "v") (TS.Ret "v1"))))))
  leftWith c "Lifted: the core New premise" "allocation index"
    (L.checkLProgram (L.LProgram "bad" "v" 2 (L.LNew "t" 2 5 (L.LDrop "t" (L.LRet "v")))))
  check1 c "Typing.checkGate is the premise Lifted reuses"
    (case TT.checkGate (TG.gHt 2) 3 2 of Left _ -> True; Right _ -> False)

-- | The parser keeps source integers and names intact, and reads the gate
-- values the grammar defines alongside the whitespace argument spelling.
parserBoundaryChecks :: Counters -> IO ()
parserBoundaryChecks c = do
  putStrLn "(7) the parser boundary"
  integerBoundaryChecks c
  gateValueChecks c
  leftWith c "a repeated name in a block pattern" "repeated register in block pattern"
    (typecheckText "prog f (x : [2], y : [2]) : [2] * [2] { (z,z) = { return (x,y) }; return (z,y) }")
  check1 c "distinct names in a block pattern remain accepted"
    (typecheckText "prog f (x : [2], y : [2]) : [2] * [2] { (z,w) = { return (x,y) }; return (z,w) }"
       == Right "f : [2] * [2]")

-- | Dimensions and levels are checked before an Integer becomes an Int;
-- products are checked before they can wrap to a smaller dimension.
integerBoundaryChecks :: Counters -> IO ()
integerBoundaryChecks c = do
  let largest = show (maxBound :: Int)
      firstBeyond = toInteger (maxBound :: Int) + 1
      wrappedZero = show (2 * firstBeyond)
      wrappedOne = show (2 * firstBeyond + 1)
      wrappedTwo = show (2 * firstBeyond + 2)
  leftWith c "the first integer beyond the Int range" "outside the supported range"
    (typecheckText ("prog f (x : [" ++ show firstBeyond ++ "]) : [2] { return x }"))
  leftWith c "a dimension literal above the Int range" "outside the supported range"
    (typecheckText ("prog f (x : [" ++ wrappedTwo ++ "]) : [2] { return x }"))
  leftWith c "a ket level above the Int range" "outside the supported range"
    (typecheckText ("prog f () : [2] { new t : [2] @ |" ++ wrappedZero ++ ">; return t }"))
  leftWith c "a lift level above the Int range" "outside the supported range"
    (typecheckText ("prog f (x : [2]) : [2] { p = lift[{" ++ wrappedOne ++ "}] x; return x }"))
  check1 c "the largest representable dimension literal parses without allocation"
    (case parseFile ("prog f (x : [" ++ largest ++ "]) : [" ++ largest ++ "] { return x }") of
       Right _ -> True
       Left _  -> False)
  leftWith c "a gate declaration's dimension product cannot wrap" "supported dimension range"
    (parseFile ("gate V : [" ++ largest ++ "] * [2] = diag (1); prog f () : 1 { return () }"))
  leftWith c "a gate argument's dimension product cannot wrap" "supported dimension range"
    (parseFile ("prog f (x : [" ++ largest ++ "], y : [2]) : [" ++ largest
                ++ "] * [2] { mat x y { 1 }; return (x,y) }"))

-- | Unit, pair and nested-pair gate arguments name the same factors as
-- their whitespace spellings; duplicate names are still refused.
gateValueChecks :: Counters -> IO ()
gateValueChecks c = do
  let unit body = "prog f () : 1 { " ++ body ++ " return () }"
      pair body = "prog f (x : [2], y : [2]) : [2] * [2] { " ++ body ++ " return (x,y) }"
      same a b = case (parseProgram a, parseProgram b) of
        (Right p, Right q) -> p == q
        _                  -> False
  check1 c "a declared phase gate acts on the unit value"
    (typecheckText ("gate Phase : 1 = diag (i); " ++ unit "Phase (); ") == Right "f : 1")
  mapM_ (\body -> check1 c ("a unit gate value: " ++ body)
                     (typecheckText (unit body) == Right "f : 1"))
    ["mat () { i };", "diag () (i);", "perm () (0);"]
  check1 c "a named gate accepts nested pairs and unit factors"
    (same (pair "CX (x,((),y));") (pair "CX x y;"))
  check1 c "a diagonal gate accepts a pair and keeps whitespace arguments"
    (same (pair "diag (x,y) (1,1,1,i);") (pair "diag x y (1,1,1,i);"))
  check1 c "a permutation gate accepts a pair and keeps whitespace arguments"
    (same (pair "perm (x,y) (0 1 3 2);") (pair "perm x y (0 1 3 2);"))
  check1 c "a matrix gate accepts a pair and keeps whitespace arguments"
    (same (pair "mat (x,y) { 1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1 };")
          (pair "mat x y { 1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1 };"))
  leftWith c "a gate value cannot name one register twice" "repeated register"
    (typecheckText (pair "CX (x,(x,()));"))
  leftWith c "a unit gate matrix still needs the unit dimension" "needs 1 entries"
    (typecheckText (unit "diag () (1,1);"))

main :: IO ()
main = do
  c <- newCounters
  flatEngineRefusesIllFormed c
  staticsRefuseIllFormed c
  machineRefusesIllFormed c
  compilerRefusesIllFormed c
  reportsRefuseIllFormed c
  theoryLayerRefusesIllFormed c
  parserBoundaryChecks c
  report c

-- | A gate that is not unitary, so the Gate rule's premise fails.
nonUnitary :: Program Cyclo
nonUnitary =
  Program [("v", 2)]
    (SDo (StNew "t" 2 [1, 0])
      (SDo (StGate [[1, 1], [0, 1]] (VVar "t"))
        (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "v")))))
