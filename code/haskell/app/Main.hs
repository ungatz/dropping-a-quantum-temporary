-- | The @dqt@ command line: one subcommand per object the paper describes.
-- Every number the paper prints is computed here, not transcribed.
module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStr, hPutStrLn, stderr)
import Data.List (intercalate)

import Drop.Bridge
import Drop.Theory.Corpus.Classical
import Drop.Theory.Criterion
import Drop.Theory.Corpus.Examples
import Drop.Theory.Lifted
import Drop.Theory.Lifted.Programs
import Drop.Theory.Many.Multi
import Drop.Theory.Many.Nested (nestedReport)
import Drop.Theory.Pretty
import Drop.Theory.Report
import Drop.Theory.Residual
import Drop.Theory.Algebra.Scalar (showK)
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing
import Drop.Theory.Criterion.Witness

import qualified Drop.Lang.Report.Run as SRun
import qualified Drop.Lang.Suite as SSuite
import qualified Drop.Lang.Report.Trace as STrace
import qualified Drop.Lang.Report.Explain as SExplain

usage :: String
usage = unlines
  [ "dqt -- the drop criterion and its checker"
  , ""
  , "  dqt list                 every program in the catalogue, with its verdict"
  , "  dqt show    <name>       the program, sugared and raw"
  , "  dqt check   <name>       the verdict, both routes, and the evidence"
  , "  dqt gram    <name>       the core map, its slices, and the Gram matrix"
  , "  dqt witness <name>       synthesise the shape sep(R,W), and verify it"
  , "  dqt context <name>       what a client can see"
  , "  dqt multi                many temporaries: bundling, joint vs per-register"
  , "  dqt nested               nested allocation: does the witness survive?"
  , "  dqt lifted               dynamic lifting: the verdict profile"
  , "  dqt residual             the runtime check, as an emitted table"
  , "  dqt classical            the classical core, and the two-level converse"
  , "  dqt all                  everything, in the paper's order"
  , ""
  , "the two engines, and the language layer"
  , ""
  , "  dqt bridge               the two engines, and the two runtime checks"
  , "  dqt run <file.s>         run one surface program and report on its drops"
  , "  dqt typecheck <file.s>   parse and typecheck one surface program"
  , "  dqt compile <file.s>     compile one surface program to OpenQASM 3"
  , "  dqt trace <file.s> [--input NAME]"
  , "                            the run, frame by frame, one temporary at a time"
  , "  dqt pass <file.s>        the static pass behind the runtime check, stage by stage"
  , "  dqt suite                the language layer: "
      ++ show SSuite.suiteCheckCount ++ " checks over "
      ++ show (length SSuite.suiteAlgorithms) ++ " algorithms"
  ]

main :: IO ()
main = do
  as <- getArgs
  case as of
    ["list"]              -> putStr cmdList
    ["show",    n]        -> withProgram n (putStr . prettyBoth)
    ["check",   n]        -> withProgram n (putStr . reportProgram)
    ["gram",    n]        -> withProgram n (putStr . reportGram)
    ["witness", n]        -> withProgram n (putStr . reportWitness)
    ["context", n]        -> withProgram n (putStr . reportContext)
    ["multi"]             -> putStr cmdMulti
    ["nested"]            -> putStr nestedReport
    ["lifted"]            -> putStr cmdLifted
    ["residual"]          -> putStr cmdResidual
    ["classical"]         -> putStr cmdClassical
    ["all"]               -> putStr cmdAll
    ["bridge"]            -> putStr bridgeReport >> putStrLn ""
                             >> putStr residualBridgeReport
    ["run", f]            -> SRun.runFile f
    ["typecheck", f]      -> SRun.typecheckFile f
    ["compile",   f]      -> SRun.compileFile f
    ["trace", f]          -> STrace.traceFile f Nothing
    ["trace", f, "--input", inp] -> STrace.traceFile f (Just inp)
    ["pass", f]           -> SExplain.passFile f
    ["suite"]             -> SSuite.suiteMain
    []                    -> putStr usage
    ("-h" : _)            -> putStr usage
    ("--help" : _)        -> putStr usage
    ("help" : _)          -> putStr usage
    -- An unrecognised subcommand must not exit 0: in a shell, `dqt typo &&
    -- next` would otherwise run `next`. Usage goes to standard error here
    -- for the same reason: it is a diagnostic, not output.
    (c : _)               -> do
      hPutStrLn stderr ("dqt: no such subcommand: " ++ c)
      hPutStr stderr usage
      exitFailure

withProgram :: String -> (Program -> IO ()) -> IO ()
withProgram n k = case byName n of
  Just p  -> k p
  Nothing -> do
    putStrLn ("no program named " ++ show n ++ "; try `dqt list'")
    exitFailure

prettyBoth :: Program -> String
prettyBoth p = prettySugared p ++ "\nthe same term, unsugared:\n\n" ++ pretty (progTerm p)

cmdList :: String
cmdList = table ["name", "shape?", "verdict", "witness"]
  [ [ n
    , yn (inSepShape p)
    , either (const "ill-typed") verdictWord (checkProgram p)
    , either (const "-") witnessWord (checkProgram p) ]
  | (n, p) <- catalogue ]
  where
    yn b = if b then "yes" else "no"
    verdictWord tp = case verdict tp of
      Safe _     -> "SAFE"
      Vacuous    -> "vacuous"
      Unsafe _ r -> "UNSAFE (rank " ++ show r ++ ")"
    witnessWord tp = case synthesize tp of
      Right w -> if wDegenerate w then "sep(1,W)" else "sep(R,W)"
      Left _  -> "none"

-- | How many catalogue programs the criterion accepts, and how many are
-- literally of the separable shape.  Both are counted here rather than
-- written down.
admittedCount, inShapeCount, catalogueSize :: Int
admittedCount = length [ () | (_, p) <- catalogue, admitted p ]
  where admitted p = case checkProgram p of
          Right tp -> case verdict tp of
            Safe _  -> True
            Vacuous -> True
            _       -> False
          Left _   -> False
inShapeCount  = length [ () | (_, p) <- catalogue, inSepShape p ]
catalogueSize = length catalogue

cmdMulti :: String
cmdMulti = unlines (concatMap one [bellPair, wideVisible, nestedThree])
  where
    one p = subHead (mLabel p)
      ++ kvs
         [ ("temporaries", intercalate ", "
             [ t ++ "[" ++ show d ++ "]" | (t,d,_) <- mTemporaries p ])
         , ("bundling keeps the denotation",
             okBad "yes" "NO" (bundlePreservesDenotation p))
         , ("joint verdict (what the core sees)", safeWord (jointSafe p))
         , ("each wire alone (strictly finer)", intercalate ", "
             [ t ++ " " ++ safeWord (wireSafe p t) | (t,_,_) <- mTemporaries p ])
         , ("every wire separately fixed", yesNoE (everyWireSafe p)) ]
    safeWord = either (\e -> "error: " ++ show e)
                      (\b -> if b then "safe" else "unsafe")
    yesNoE   = either (\e -> "error: " ++ show e) yesNo

cmdLifted :: String
cmdLifted = unlines (concatMap one
  [liftedWitness, liftedWitnessNoRead, classicalCoreNaiveEncoding])
  where
    one p = case checkLProgram p of
      Left e   -> subHead (lLabel p) ++ kv "TYPE ERROR" (show e)
      Right tp -> subHead (lLabel p)
        ++ kv "lift depth" (show (ltDepth tp) ++ "   ("
                            ++ show (2 ^ ltDepth tp :: Int)
                            ++ " measurement records)")
        ++ blank
        ++ [ "      " ++ padSep 8 "trace" ++ padSep 10 "weight" ++ "verdict"
           , "      " ++ replicate 7 '\9472' ++ " " ++ replicate 9 '\9472'
             ++ " " ++ replicate (measure - 24) '\9472' ]
        ++ concatMap traceRow (verdictProfile tp)
        ++ blank
        ++ kvs
           [ ("the same verdict at every trace", yesNo (constantProfile tp))
           , ("oracle-split", yesNo (oracleSplit tp))
           , ("so no record-oblivious verdict can accept it",
               yesNo (everySoundRecordObliviousVerdictRejects tp)) ]
    traceRow tv = case lines (show (tvVerdict tv)) of
      []       -> []
      (l : ls) ->
        let w      = measure - 24
            hang x = "      " ++ replicate 18 ' ' ++ x
            first  = "      " ++ padSep 8 (filter (/= '"') (show (tvTrace tv)))
                     ++ padSep 10 (maybe "-" showK (tvWeight tv))
        in case wrapAt w l of
             []       -> []
             (f : fs) -> (first ++ f) : map hang (fs ++ concat
                           [ wrapAt w (dropWhile (== ' ') x) | x <- ls ])

cmdResidual :: String
cmdResidual = unlines (concatMap one [liftedWitness, liftedWitnessNoRead])
  where
    one p = case checkLProgram p of
      Left e   -> kv "TYPE ERROR" (show e)
      Right tp -> subHead (lLabel p) ++ explainTable tp

cmdClassical :: String
cmdClassical = unlines $
  subHead (cpLabel classicalWitness)
  ++ [ "      outcome " ++ padSep 8 (filter (/= '"') (show b))
       ++ (if sf then "safe" else "leaks the visible bit")
     | (b, sf) <- classicalProfile classicalWitness ]
  ++ blank
  ++ kv "one text, opposite verdicts"
        (yesNo (classicalSplit classicalWitness))
  ++ blank
  ++ para "Checked over every permutation: a two-level temporary is never underdetermined."
  ++ blank
  ++ kvs
     ([ ("a two-level temporary, |V| = " ++ show v,
          okBad "never underdetermined" "underdetermined"
                (twoLevelsNeverSplit v))
      | v <- [2 :: Int, 3, 4] ]
      ++ [ ("three levels can split", yesNo threeLevelsCanSplit) ])

cmdAll :: String
cmdAll = unlines $
  masthead
  ++ sectionHead 1 "the catalogue"
       (show catalogueSize ++ " programs, decided")
  ++ para "shape? is whether the source is literally sep(R,W); witness is whether one can be built."
  ++ blank
  ++ [cmdList]
  ++ para (show admittedCount ++ " of " ++ show catalogueSize
           ++ " drops are safe; " ++ show inShapeCount
           ++ " programs are literally separable.")

  ++ sectionHead 2 "three programs in full" "where a verdict comes from"
  ++ para "(A) and (C) are safe on different lines. (B) is (C) plus one instruction, and leaks."
  ++ concatMap detail ["example-A", "example-B", "example-C"]

  ++ sectionHead 3 "many temporaries" "bundling, and what it costs"
  ++ para "Several temporaries bundle into one wire of the product dimension, so the core decides them jointly."
  ++ [cmdMulti]
  ++ para "The Bell pair separates joint from per-wire: dropping both is safe, neither wire is on a ray of its own."

  ++ sectionHead 4 "dynamic lifting" "one text, two verdicts"
  ++ para "A lift keeps the surviving branch unnormalised. The record comes from the run, so the verdict is indexed by it."
  ++ [cmdLifted]
  ++ para "The first program is the witness: one text, two records, opposite verdicts."

  ++ sectionHead 5 "the runtime check" "the verdict, as an emitted table"
  ++ para "One row per record, computed before the run. Each block ends with the check that the table and the criterion agree at every entry."
  ++ [cmdResidual]

  ++ sectionHead 6 "the classical core" "the obstruction is not quantum"
  ++ para "One fair trit, one permutation, one partial read, no superposition, and the verdict still depends on the outcome."
  ++ [cmdClassical]
  ++ [rule]
  ++ para "Computed by this binary in exact arithmetic. No number here was transcribed by hand."
  where
    detail n = case byName n of
      Nothing -> []
      Just p  -> subHead (progLabel p)
                 ++ programHeader p
                 ++ (case checkProgram p of
                       Left _   -> []
                       Right tp -> typedGramReport tp
                                   ++ blank
                                   ++ explainWitness tp (synthesize tp))

-- | Title and notation.
masthead :: [String]
masthead =
  [ thickRule
  , "  SAFE TO DROP"
  , "  when a quantum temporary may be discarded, and what it costs"
  , thickRule ]
  ++ blank
  ++ para "drop t does nothing at run time. The question is whether the rest of the program can tell."
  ++ blank
  ++ [ "  NOTATION" ]
  ++ [ "    " ++ padSep 16 k ++ v
     | (k, v) <-
       [ ("d, m",          "dimension of the temporary, and of the visible register")
       , ("K",             "the core map  H_m --> H_d (x) H_m")
       , ("K_i",           "slice i: what the program does to the visible")
       , ("",              "register when the temporary sits at level i")
       , ("[g]",           "a ray, written in its canonical representative")
       , ("sep(R,W)",      "prepare by R, compute by W, drop: the separable shape")
       , ("record",        "which branch survived at each measurement")
       , ("rank <= 1",     "the slices lie on one line, so K = g (x) W, so the")
       , ("",              "temporary carried nothing about the visible input")
       ] ]
