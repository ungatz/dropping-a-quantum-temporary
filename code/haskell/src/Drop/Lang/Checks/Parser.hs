-- Drop.Lang.Checks.Parser: the checks that read the .s files, and the one place the suite reads the disk.
--
-- Question: Do the shipped .s programs parse, print back to themselves, and mean what their module counterparts mean?
-- Answer:   Yes, and the suite shows it without any check opening a file. readCorpus reads every shipped
--           program once into a Corpus; every function below takes that corpus as its first argument.
--           checks is the concatenation of eight lists, in this order. fileChecks: each file parses,
--           printing it and parsing it again gives the program back, and then the whole file back.
--           snippetChecks: sources that use grammar the shipped files do not, printed and read back.
--           pairChecks: each file with a module counterpart is that module's program as syntax.
--           agreementChecks: the file and its module give the same verdict at every selection.
--           valueChecks: numbers re-derived through the text, such as Grover landing on the marked
--           item and program (c) being safe on one record and unsafe on the other. loanChecks: a
--           borrowed loan returns as it arrived, and deleting the restoring Toffoli is refused.
--           refusalChecks: every malformed source and every retired spelling is refused at the
--           line its message names. traceChecks: the trace of dj.s has one frame per statement and
--           ends on the verdict the checks above already pin. readFiles and readCorpus are the only
--           functions here that touch the disk; Suite.suiteRun, app/Main.hs and the test programs
--           call readCorpus once and pass the result down.
-- Paper:    sec:lang:syntax (the syntax of programs), app:corpus (the corpus, site by site),
--           sec:eval:corpus (the surface corpus), thm:notext (program (c): one text, two records).
-- Shapes:   Corpus           the text of each file by its path, or the reason it could not be read.
--           progFiles        the shipped programs, as paths from the package root.
--           paired           for each file with a module counterpart: its path, visible registers
--                            and the module's program moved into the parser's scalar field.
--           snippets         (name, source): grammar the shipped files do not reach.
--           badInputs        (name, line, source): a source that must be refused, and the line the
--                            message names.
--           legacySpellings  (name, line, source, needle): a retired spelling, the line it is
--                            refused at, and the form the message must name instead.

module Drop.Lang.Checks.Parser
  ( Corpus, readCorpus, readFiles
  , checks, progFiles, parsed, parsedFile, fileSrc
  ) where

import Control.Exception (IOException, try)
import Data.List (isInfixOf, isPrefixOf)

import Drop.Lang.Scalar (Cyclo, embedQS2, Conj)
import Drop.Lang.Gates (gX)
import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Parser
import Drop.Lang.Render
import Drop.Lang.Report.Trace (traceText)
import qualified Drop.Lang.Programs.DJ as DJ
import qualified Drop.Lang.Programs.Grover as Grover
import qualified Drop.Lang.Programs.QPE as QPE
import qualified Drop.Lang.Programs.RUS as RUS
import qualified Drop.Lang.Programs.Shor as Shor
import qualified Drop.Lang.Programs.Simon as Simon
import qualified Drop.Lang.Programs.Superdense as Superdense
import qualified Drop.Lang.Programs.Teleport as Teleport
import qualified Drop.Lang.Programs.TempAnd as TempAnd

-- The corpus: the files the checks read -------------------------------------

-- | Each file's text, or the reason it could not be read, by path.
type Corpus = [(FilePath, Either String String)]

-- The corpus is read once; a path is the key.
-- >>> corpus <- readCorpus
-- >>> length corpus
-- 19
-- >>> take 1 (map fst corpus)
-- ["programs/dj.s"]

-- | The shipped programs. Paths are relative to the package root, where the
-- suite is run.
progFiles :: [FilePath]
progFiles = map ("programs/" ++)
  [ "dj.s", "grover.s", "qpe.s", "teleport.s", "rus.s"
  , "superdense.s", "mcx-dirty.s", "mcx-dirty-x.s", "mcx-dirty-half.s"
  , "shor.s", "simon.s", "temp-and.s"
  , "temp-general.s"
  , "learns-nothing.s", "bell-block.s"
  , "c.s", "copy-input.s"
  , "bell-pair.s", "bell-pair-split.s" ]

-- The first three shipped programs, and how many there are.
-- >>> take 3 progFiles
-- ["programs/dj.s","programs/grover.s","programs/qpe.s"]
-- >>> length progFiles
-- 19

-- | Read the named files; one that cannot be read keeps the reason.
readFiles :: [FilePath] -> IO Corpus
readFiles = mapM one
  where
    one f = do
      r <- try (readFile f) :: IO (Either IOException String)
      return (f, either (Left . show) Right r)

-- A file that is not there keeps the reason; the others are read.
-- >>> corpus <- readFiles ["programs/dj.s", "programs/no-such-file.s"]
-- >>> [ (f, either (const "unreadable") (const "read") r) | (f, r) <- corpus ]
-- [("programs/dj.s","read"),("programs/no-such-file.s","unreadable")]

-- | Read every shipped program: the one place the checks touch the disk.
readCorpus :: IO Corpus
readCorpus = readFiles progFiles

-- The corpus is the shipped programs, in the order of progFiles.
-- >>> corpus <- readCorpus
-- >>> map fst corpus == progFiles
-- True
-- >>> all (either (const False) (const True) . snd) corpus
-- True

-- | The text of one file of the corpus. A path nobody read is a 'Left'
-- naming it.
fileSrc :: Corpus -> FilePath -> Either String String
fileSrc corpus f = case lookup f corpus of
  Just r  -> r
  Nothing -> Left ("not in the corpus: " ++ f)

-- The first lines of the smallest program, and the reason a path nobody read gives.
-- >>> corpus <- readCorpus
-- >>> fmap (take 3 . lines) (fileSrc corpus "programs/dj.s")
-- Right ["-- dj.s: Deutsch-Jozsa on one input qubit, |-> temporary, oracle f(x) = x as","-- CX with control x and target t.  Token-identical to the listing in","-- the paper's syntax section (sec:lang:syntax)."]
-- >>> fileSrc corpus "programs/no-such-file.s"
-- Left "not in the corpus: programs/no-such-file.s"

parsed :: Corpus -> FilePath -> Either String (VisSpec, Prog Cyclo)
parsed corpus f = fileSrc corpus f >>= parseProgram

-- A file as a program: its visible registers and the length of its body.
-- >>> corpus <- readCorpus
-- >>> fmap (\(vis, prog) -> (vis, length prog)) (parsed corpus "programs/dj.s")
-- Right ([("x",2)],7)
-- >>> fmap (\(vis, prog) -> (vis, length prog)) (parsed corpus "programs/temp-and.s")
-- Right ([("x",2),("y",2)],6)
-- >>> either id (const "parsed") (parsed [] "programs/dj.s")
-- "not in the corpus: programs/dj.s"

parsedFile :: Corpus -> FilePath -> Either String SFile
parsedFile corpus f = fileSrc corpus f >>= parseFile

-- A file as a whole: its name, and what it returns.
-- >>> corpus <- readCorpus
-- >>> fmap sfName (parsedFile corpus "programs/temp-and.s")
-- Right "temp_and"
-- >>> fmap (renderValue . sfReturn) (parsedFile corpus "programs/temp-and.s")
-- Right "(x, y)"

-- | The files that have a module counterpart, with that module's program
-- moved into the parser's scalar field.
paired :: [(FilePath, VisSpec, Prog Cyclo)]
paired =
  [ ("programs/dj.s",        DJ.visDJ,   mapProg embedQS2 (DJ.djPaper DJ.fId))
  , ("programs/grover.s",    Grover.visG, mapProg embedQS2 Grover.groverProg)
  , ("programs/qpe.s",       QPE.visQPE, QPE.qpeT)
  , ("programs/teleport.s",  Teleport.visT, mapProg embedQS2 Teleport.teleP)
  , ("programs/rus.s",       RUS.visR,   mapProg fromRational RUS.rusProg)
  , ("programs/superdense.s", Superdense.visSD
    , mapProg embedQS2 (Superdense.superdenseProg (1, 1)))
  , ("programs/shor.s",      Shor.visShor, Shor.shorMeasured)
  , ("programs/simon.s",     Simon.visSimon, Simon.simonMeasured)
  , ("programs/temp-and.s",  TempAnd.visXY, TempAnd.andUncomputedByMeasurement)
  ]

-- The files that have a module counterpart.
-- >>> [ f | (f, _, _) <- paired ]
-- ["programs/dj.s","programs/grover.s","programs/qpe.s","programs/teleport.s","programs/rus.s","programs/superdense.s","programs/shor.s","programs/simon.s","programs/temp-and.s"]

-- Parse-Render Identity

parseRenderId :: Either String (VisSpec, Prog Cyclo) -> Bool
parseRenderId (Left _) = False
parseRenderId (Right (vis, prog)) =
  case parseProgram (renderProgram vis prog) of
    Right (vis', prog') -> vis' == vis && prog' == prog
    Left _              -> False

-- Printing a program and reading it back gives the program; an unreadable file fails.
-- >>> corpus <- readCorpus
-- >>> parseRenderId (parsed corpus "programs/temp-and.s")
-- True
-- >>> parseRenderId (Left "unreadable")
-- False

-- | The whole file, header and return value and declarations included:
-- @parseFile . renderFile@ is the identity on 'SFile'.
fileRenderId :: Either String SFile -> Bool
fileRenderId (Left _) = False
fileRenderId (Right f) = parseFile (renderFile f) == Right f

-- The same for the whole file, header and return value included.
-- >>> corpus <- readCorpus
-- >>> fileRenderId (parsedFile corpus "programs/mcx-dirty-x.s")
-- True
-- >>> fileRenderId (Left "unreadable")
-- False

-- | Sources exercising parts of the grammar the shipped files do not.
snippets :: [(String, String)]
snippets = scalarSnippets ++ loanSnippets ++ blockSnippets

-- The six sources, by name.
-- >>> map fst snippets
-- ["new @ an amplitude vector, diag and Swap over the tower","qutrits, scalar sums and products, a nested if","a header loan, a gate and a drop","T, S and a declared gate","a tuple drop is one site, and a compound guard","a block, and a parameter that leaves scope at its brace"]

-- | Amplitude vectors, scalar sums and products, qutrits, a nested if.
scalarSnippets :: [(String, String)]
scalarSnippets =
  [ ( "new @ an amplitude vector, diag and Swap over the tower"
    , unlines
        [ "prog s1 (x : [2]) : [2] {"
        , "  new t : [2] @ (1/rt2, -1/rt2);"
        , "  diag t (1, z8^3);"
        , "  diag x t (1, 1, 1, i);   -- two registers: a controlled phase"
        , "  Swap x t;"
        , "  drop t;"
        , "  return x"
        , "}"
        ] )
  , ( "qutrits, scalar sums and products, a nested if"
    , unlines
        [ "prog s2 (x : [3]) : [3] {"
        , "  new t : [3] @ (1/2*z8-1/2*z8^3, 1/2*z16, 1/2*i);"
        , "  tilt t;"
        , "  p = lift[{0,1}] t;"
        , "  if p { READ3 x t; } else { if p { READ3 x t; } else { } }"
        , "  drop t;"
        , "  return x"
        , "}"
        ] )
  ]

-- >>> map fst scalarSnippets
-- ["new @ an amplitude vector, diag and Swap over the tower","qutrits, scalar sums and products, a nested if"]

-- | A loan in the header, and gates declared in the file.
loanSnippets :: [(String, String)]
loanSnippets =
  [ ( "a header loan, a gate and a drop"
    , unlines
        [ "prog s3 (x : [2], loan t : [2]) : [2] {"
        , "  CX x t;"
        , "  drop t;"
        , "  return x"
        , "}"
        ] )
  , ( "T, S and a declared gate"
    , unlines
        [ "gate W : [2] = mat { 1, 0 ; 0, z8 };"
        , "prog s4 (x : [2]) : [2] {"
        , "  new t : [2] @ |0>;"
        , "  T t;"
        , "  S t;"
        , "  W t;"
        , "  CX x t;"
        , "  drop t;"
        , "  return x"
        , "}"
        ] )
  ]

-- >>> map fst loanSnippets
-- ["a header loan, a gate and a drop","T, S and a declared gate"]

-- | A tuple drop, a compound guard, and a block that ends a parameter's scope.
blockSnippets :: [(String, String)]
blockSnippets =
  [ ( "a tuple drop is one site, and a compound guard"
    , unlines
        [ "prog s5 (x : [2]) : [2] {"
        , "  new t : [2] @ |1>;"
        , "  new u : [2] @ |0>;"
        , "  H t;"
        , "  CX t u;"
        , "  p = lift[{0}] x;"
        , "  if !p && (p || p) { Z t; } else { }"
        , "  drop (t, u);"
        , "  return x"
        , "}"
        ] )
  , ( "a block, and a parameter that leaves scope at its brace"
    , unlines
        [ "prog s6 () : [2] {"
        , "  new a : [2] @ |0>;"
        , "  new x : [2] @ |0>;"
        , "  H a;  CX a x;"
        , "  y = { p = lift[{0}] x; return x };"
        , "  drop a;"
        , "  return y"
        , "}"
        ] )
  ]

-- >>> map fst blockSnippets
-- ["a tuple drop is one site, and a compound guard","a block, and a parameter that leaves scope at its brace"]

-- Verdict Agreement With The Modules

-- | Same visible spec, same lift depth at the target, same verdict at every
-- selection.  The parsed program runs over the tower and the reference over
-- its own field.
agreeOn :: (Eq a, Fractional a, Conj a)
        => Corpus -> FilePath -> VisSpec -> Prog a -> String -> Bool
agreeOn corpus f visE progE tgt = case parsed corpus f of
  Left _ -> False
  Right (vis, prog) ->
    vis == visE
    && liftDepthBefore prog tgt == liftDepthBefore progE tgt
    && and [ semanticVerdict vis prog tgt sel == semanticVerdict visE progE tgt sel
           | sel <- allSelections (liftDepthBefore progE tgt) ]

-- The file agrees with the module's program at its drop; a program that is not the file's disagrees.
-- >>> corpus <- readCorpus
-- >>> agreeOn corpus "programs/dj.s" DJ.visDJ (DJ.djProg DJ.fId) "t"
-- True
-- >>> agreeOn corpus "programs/dj.s" DJ.visDJ (DJ.djNoUncompute DJ.fId) "t"
-- False

-- | The criterion's verdict at a site of a parsed file.
verdictOf :: Corpus -> FilePath -> String -> [Sel] -> Maybe Verdict
verdictOf corpus f tgt sel = case parsed corpus f of
  Left _            -> Nothing
  Right (vis, prog) -> Just (semanticVerdict vis prog tgt sel)

-- Program (c): one text, safe on one record and unsafe on the other. A file nobody read has no verdict.
-- >>> corpus <- readCorpus
-- >>> verdictOf corpus "programs/c.s" "t" [SIn]
-- Just Safe
-- >>> verdictOf corpus "programs/c.s" "t" [SOut]
-- Just Unsafe
-- >>> verdictOf [] "programs/c.s" "t" [SIn]
-- Nothing


-- | The same, on one record.
parkedRecOf :: Corpus -> FilePath -> String -> [Sel] -> Maybe (StateV Cyclo)
parkedRecOf corpus f tgt sel = case parsed corpus f of
  Left _            -> Nothing
  Right (vis, prog) -> semanticParked vis prog tgt sel

-- The line program (c) leaves the temporary on, on the record where its drop is safe.
-- >>> corpus <- readCorpus
-- >>> parkedRecOf corpus "programs/c.s" "t" [SIn]
-- Just [Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]
-- >>> parkedRecOf corpus "programs/c.s" "t" [SOut]
-- Nothing

-- | The isometry a safe loan site's drop reclaims with, at a site of a
-- parsed file.
certOf :: Corpus -> FilePath -> String -> Maybe (Matrix Cyclo)
certOf corpus f tgt = case parsed corpus f of
  Left _            -> Nothing
  Right (vis, prog) -> semanticLoanCert vis prog tgt []

-- The gate a loan is reclaimed with: the identity, and an X when the program flips the loan first.
-- >>> corpus <- readCorpus
-- >>> certOf corpus "programs/mcx-dirty.s" "a"
-- Just [[Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]],[Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]]]
-- >>> certOf corpus "programs/mcx-dirty-x.s" "a"
-- Just [[Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]],[Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]]

runFileOn :: Corpus -> FilePath -> [Sel] -> StateV Cyclo -> Maybe (Mach Cyclo)
runFileOn corpus f sel inp = case parsed corpus f of
  Left _            -> Nothing
  Right (vis, prog) -> Just (runStmts (initMach vis inp) prog sel Nothing)

-- Grover's file, run on the all-zero input, names its registers in order.
-- >>> corpus <- readCorpus
-- >>> fmap mNames (runFileOn corpus "programs/grover.s" [] (ket [2, 2] [0, 0]))
-- Just ["x1","x2","t"]

-- Malformed Inputs

-- | Sources that must be refused, each with the line the message names.
-- A program is written on one line per statement so the line is the point.
badInputs :: [(String, Int, String)]   -- (name, expected line, source)
badInputs =
  [ ("unknown gate",         2, "prog p (x : [2]) : [2] {\nFOO x;\nreturn x }\n")
  , ("malformed scalar",     2,
     "prog p (x : [2]) : [2] {\nnew u : [2] @ (1/2, blah);\ndrop u; return x }\n")
  , ("lift level out of range", 3,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\nq = lift[{5}] t;\ndrop t; return x }\n")
  , ("unknown register",     2, "prog p (x : [2]) : [2] {\nH y;\nreturn x }\n")
  , ("gate dimension",       3,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\nCX t;\ndrop t; return x }\n")
  , ("if on an unbound bit", 2, "prog p (x : [2]) : [2] {\nif q { } else { }\nreturn x }\n")
  , ("missing prog header",  1, "new t : [2] @ |0>;\n")
  , ("new @ not a unit vector", 2,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ (1, 1);\ndrop t; return x }\n")
  , ("new @ the zero vector",   2,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ (0, 0);\ndrop t; return x }\n")
  , ("newdirty is gone",     2, "prog p (x : [2]) : [2] {\nnewdirty t : [2];\nreturn x }\n")
  , ("a loan is not a statement", 2,
     "prog p (x : [2]) : [2] {\nloan t : [2];\nreturn x }\n")
  , ("vis is gone",          2, "prog p (x : [2]) : [2] {\nvis y : [2];\nreturn x }\n")
  , ("mat wrong shape",      2, "prog p (x : [2]) : [2] {\nmat x { 1, 0 ; 0 };\nreturn x }\n")
  , ("mat wrong dimension",  3,
     "prog p (x : [2]) : [2] {\nnew t : [3] @ |0>;\nmat x t { 1, 0 ; 0, 1 };\ndrop t; return x }\n")
  , ("diag wrong count",     2, "prog p (x : [2]) : [2] {\ndiag x (1, 1, 1);\nreturn x }\n")
  , ("perm repeated image",  2, "prog p (x : [2]) : [2] {\nperm x (0 0);\nreturn x }\n")
  , ("perm image out of range", 2, "prog p (x : [2]) : [2] {\nperm x (0 2);\nreturn x }\n")
  , ("repeated register",    2,
     "prog p (x : [2], y : [2]) : [2] * [2] {\nmat x x { 1, 0, 0, 0 ; 0, 1, 0, 0 ; 0, 0, 1, 0 ; 0, 0, 0, 1 };\nreturn (x, y) }\n")
  , ("gate on a dropped register", 4,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\ndrop t;\nH t;\nreturn x }\n")
  , ("drop inside an if branch", 4,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\nb = lift[{1}] t;\nif b { drop t; } else { }\ndrop t; return x }\n")
  , ("new inside an if branch", 4,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\nb = lift[{0}] t;\nif b { new u : [2] @ |0>; } else { }\ndrop t; return x }\n")
  , ("lift inside an if branch", 4,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\nb = lift[{0}] t;\n\
      \if b { c = lift[{0}] t; } else { }\ndrop t; return x }\n")
  , ("a dropped name allocated again", 4,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\ndrop t;\nnew t : [2] @ |0>;\ndrop t; return x }\n")
  , ("a lift parameter bound twice", 4,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\nb = lift[{0}] t;\nb = lift[{1}] t;\ndrop t; return x }\n")
  , ("a register neither dropped nor returned", 3,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\nreturn x }\n")
  , ("the result type does not match the return", 1,
     "prog p (x : [2]) : [3] {\nreturn x }\n")
  , ("a parameter out of scope after its block", 4,
     "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\ny = { q = lift[{0}] t; return t };\n\
      \if q { Z x; } else { }\ndrop y;\nreturn x }\n")
  ]

-- The first three refusals, with the line each names, and how many there are.
-- >>> map (\(name, ln, _) -> (name, ln)) (take 3 badInputs)
-- [("unknown gate",2),("malformed scalar",2),("lift level out of range",3)]
-- >>> length badInputs
-- 27

badCheck :: (String, Int, String) -> (String, Bool)
badCheck (nm, ln, src) =
  ( "malformed (" ++ nm ++ ") is a parse error at line " ++ show ln
  , case parseProgram src of
      Left err -> ("line " ++ show ln ++ ":") `isPrefixOf` err
      Right _  -> False )

-- A refusal check: its name says the line, and it holds.
-- >>> map badCheck (take 1 badInputs)
-- [("malformed (unknown gate) is a parse error at line 2",True)]

-- | The explicit-binding spellings the language does not accept: what it
-- accepts is exactly the printed grammar. Each is refused at the right
-- line, with a message naming the printed form instead.
-- (name, expected line, source, substring the message must name)
legacySpellings :: [(String, Int, String, String)]
legacySpellings =
  [ ( "t = new [2] @ |0>;"
    , 2
    , "prog p (x : [2]) : [2] {\nt = new [2] @ |0>;\ndrop t; return x }\n"
    , "new t : [2] @ |0>;" )
  , ( "t = S t;"
    , 3
    , "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\nt = S t;\ndrop t; return x }\n"
    , "S t;" )
  , ( "(x, t) = CX x t;"
    , 3
    , "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\n(x, t) = CX x t;\ndrop t; return x }\n"
    , "CX x t;" )
  , ( "() = drop t;"
    , 3
    , "prog p (x : [2]) : [2] {\nnew t : [2] @ |0>;\n() = drop t;\nreturn x }\n"
    , "drop t;" )
  ]

-- The refused spellings, and the line each is refused at.
-- >>> map (\(name, ln, _, _) -> (name, ln)) legacySpellings
-- [("t = new [2] @ |0>;",2),("t = S t;",3),("(x, t) = CX x t;",3),("() = drop t;",3)]

legacyCheck :: (String, Int, String, String) -> (String, Bool)
legacyCheck (nm, ln, src, needle) =
  ( "legacy spelling `" ++ nm ++ "` is refused at line " ++ show ln
    ++ " naming `" ++ needle ++ "`"
  , case parseProgram src of
      Left err -> ("line " ++ show ln ++ ":") `isPrefixOf` err
                  && ("`" ++ needle ++ "`") `isInfixOf` err
      Right _  -> False )

-- >>> map legacyCheck (take 1 legacySpellings)
-- [("legacy spelling `t = new [2] @ |0>;` is refused at line 2 naming `new t : [2] @ |0>;`",True)]

-- The Trace Command

djTraceText :: Corpus -> Either String String
djTraceText corpus = fileSrc corpus "programs/dj.s" >>= \src -> traceText src Nothing

-- The first lines of the trace of Deutsch-Jozsa's file (each line shown with its quotes, so its indentation stays).
-- >>> corpus <- readCorpus
-- >>> either putStrLn (mapM_ print . take 6 . lines) (djTraceText corpus)
-- ""
-- "frame 1/7   new t : [2] @ |0>"
-- "x  =====------[H][CX][H]------"
-- "t  (new)[X][H]---[CX]---(drop)"
-- "   ^^^^^"
-- "  |x t>   1 |0 0>"

-- The Checks

checks :: Corpus -> [(String, Bool)]
checks corpus = concat
  [ fileChecks corpus, snippetChecks, pairChecks corpus
  , agreementChecks corpus, valueChecks corpus, loanChecks corpus
  , refusalChecks, traceChecks corpus ]

-- The whole group: every list below, in this order.
-- >>> corpus <- readCorpus
-- >>> length (checks corpus)
-- 127
-- >>> all snd (checks corpus)
-- True

-- | Every shipped file parses, and parsing what was printed gives the file
-- back, as a program and as a whole file.
fileChecks :: Corpus -> [(String, Bool)]
fileChecks corpus = concat
  [ [ (f ++ " parses", either (const False) (const True) (parsed corpus f))
    | f <- progFiles ]
  , [ (f ++ ": parse . render is the identity on the syntax", parseRenderId (parsed corpus f))
    | f <- progFiles ]
  , -- the whole file, header, declarations and return value included
    [ (f ++ ": parseFile . renderFile is the identity on the file", fileRenderId (parsedFile corpus f))
    | f <- progFiles ]
  ]

-- Every shipped file, three times over: parses, prints back, prints back whole.
-- >>> corpus <- readCorpus
-- >>> take 2 (fileChecks corpus)
-- [("programs/dj.s parses",True),("programs/grover.s parses",True)]
-- >>> length (fileChecks corpus) == 3 * length progFiles
-- True

-- | The grammar the shipped files do not reach, round-tripped.
snippetChecks :: [(String, Bool)]
snippetChecks =
  [ ("snippet, parse . render is the identity: " ++ nm
    , parseRenderId (parseProgram src))
  | (nm, src) <- snippets ]

-- >>> take 2 snippetChecks
-- [("snippet, parse . render is the identity: new @ an amplitude vector, diag and Swap over the tower",True),("snippet, parse . render is the identity: qutrits, scalar sums and products, a nested if",True)]
-- >>> length snippetChecks
-- 6

-- | Each file with a module counterpart is that module's program.
pairChecks :: Corpus -> [(String, Bool)]
pairChecks corpus =
  [ (f ++ " is the module's program as syntax", parsed corpus f == Right (vis, prog))
  | (f, vis, prog) <- paired ]

-- >>> corpus <- readCorpus
-- >>> take 2 (pairChecks corpus)
-- [("programs/dj.s is the module's program as syntax",True),("programs/grover.s is the module's program as syntax",True)]
-- >>> length (pairChecks corpus)
-- 9

-- | Verdict agreement, each module run in its own scalar field.
agreementChecks :: Corpus -> [(String, Bool)]
agreementChecks corpus =
  [ ( "dj.s verdicts agree with the DJ module (f=x), parked [|->]"
    , agreeOn corpus "programs/dj.s" DJ.visDJ (DJ.djProg DJ.fId) "t"
      && case parsed corpus "programs/dj.s" of
           Right (vis, prog) ->
             probeResult vis prog "t" [] (ket [2] [0]) == PLine [1, -1]
           Left _ -> False )
  , ( "grover.s verdicts agree with ExGrover"
    , agreeOn corpus "programs/grover.s" Grover.visG Grover.groverProg "t" )
  , ( "qpe.s verdicts agree with ExQPE at the drop of psi"
    , agreeOn corpus "programs/qpe.s" QPE.visQPE QPE.qpeT "psi" )
  , ( "teleport.s verdicts agree with ExTeleport at both drops"
    , all (agreeOn corpus "programs/teleport.s" Teleport.visT Teleport.teleP)
          ["m", "a"] )
  , ( "rus.s verdicts agree with ExRUS"
    , agreeOn corpus "programs/rus.s" RUS.visR RUS.rusProg "t" )
  , ( "superdense.s verdicts agree with ExSuperdense at (1,1)"
    , agreeOn corpus "programs/superdense.s" Superdense.visSD
              (Superdense.superdenseProg (1, 1)) "a" )
  , ( "shor.s verdicts agree with the Shor module, opposite verdicts on the two records"
    , agreeOn corpus "programs/shor.s" Shor.visShor Shor.shorMeasured "w" )
  , ( "simon.s verdicts agree with ExSimon, both records safe on different lines"
    , agreeOn corpus "programs/simon.s" Simon.visSimon Simon.simonMeasured "w" )
  , ( "temp-and.s verdicts agree with ExTempAnd, both records safe on different lines"
    , agreeOn corpus "programs/temp-and.s" TempAnd.visXY
              TempAnd.andUncomputedByMeasurement "a" )
  ]

-- >>> corpus <- readCorpus
-- >>> take 2 (agreementChecks corpus)
-- [("dj.s verdicts agree with the DJ module (f=x), parked [|->]",True),("grover.s verdicts agree with ExGrover",True)]
-- >>> length (agreementChecks corpus)
-- 9

-- | One number per file, re-derived through the text.
valueChecks :: Corpus -> [(String, Bool)]
valueChecks corpus =
  [ ( "DJ with its lift: the block {0} of x carries weight 0 on |0>, f = x being balanced"
    , norm2S (mAmp (runStmts (initMach DJ.visDJ (ket [2] [0]))
                             (mapProg embedQS2 (DJ.djProg DJ.fId)) [SIn] Nothing))
        == 0 )
  , ( "grover.s lands exactly on the marked item |11>"
    , case runFileOn corpus "programs/grover.s" [] (ket [2, 2] [0, 0]) of
        Just m  -> stateProportional (mAmp m) (ket (mDims m) [1, 1, 0])
        Nothing -> False )
  , ( "qpe.s: the final state is |001> tensor |1> exactly"
    , fmap mAmp (runFileOn corpus "programs/qpe.s" [] (ket [2,2,2] [0,0,0]))
        == Just (ket [2,2,2,2] [0,0,1,1]) )
  , ( "c.s: one text, two records, opposite verdicts (Theorem notext)"
    , verdictOf corpus "programs/c.s" "t" [SIn]  == Just Safe
      && verdictOf corpus "programs/c.s" "t" [SOut] == Just Unsafe
      && parkedRecOf corpus "programs/c.s" "t" [SIn] == Just [1, 0] )
  , ( "copy-input.s: the program that copies its input and forgets it is refused"
    , verdictOf corpus "programs/copy-input.s" "x" [] == Just Unsafe )
  , ( "learns-nothing.s: one site, unsafe, and the input is untouched"
    , verdictOf corpus "programs/learns-nothing.s" "t" [] == Just Unsafe
      && fmap (dropSites . snd) (parsed corpus "programs/learns-nothing.s")
           == Right [["t"]] )
  , ( "teleport.s: b carries the message (1,1) at every selection"
    , case parsed corpus "programs/teleport.s" of
        Right (vis, prog) ->
          and [ case factorSplit (mDims m) [regPos m "b"] (mAmp m) of
                  Just (vb, _) -> stateProportional vb [1, 1]
                  Nothing      -> False
              | sel <- allSelections 2
              , let m = runStmts (initMach vis (ket [2] [0])) prog sel Nothing ]
        Left _ -> False )
  , ( "rus.s: exact branch weights 8/9 and 1/9 on probe e0"
    , case parsed corpus "programs/rus.s" of
        Right (vis, prog) ->
          branchWeight vis prog "t" [SIn]  (ket [3] [0]) == 8 / 9
          && branchWeight vis prog "t" [SOut] (ket [3] [0]) == 1 / 9
        Left _ -> False )
  , ( "superdense.s: the pair (1,1) is read back with weight 1"
    , fmap (norm2S . mAmp)
           (runFileOn corpus "programs/superdense.s" [SOut, SOut] (ket [2] [0]))
        == Just 1
      && and [ fmap (norm2S . mAmp)
                    (runFileOn corpus "programs/superdense.s" sel (ket [2] [0]))
                 == Just 0
             | sel <- allSelections 2, sel /= [SOut, SOut] ] )
  ]

-- >>> corpus <- readCorpus
-- >>> take 2 (map fst (valueChecks corpus))
-- ["DJ with its lift: the block {0} of x carries weight 0 on |0>, f = x being balanced","grover.s lands exactly on the marked item |11>"]
-- >>> length (valueChecks corpus)
-- 9

-- | The borrowed loan: the drop's certificate is the fixed gate B it is
-- reclaimed with (a loan carries no state to report a "line" of), and
-- deleting the restoring Toffoli is refused.
loanChecks :: Corpus -> [(String, Bool)]
loanChecks corpus =
  [ ( "mcx-dirty.s: drop a admitted, B = I (the loan returns as it arrived)"
    , verdictOf corpus "programs/mcx-dirty.s" "a" [] == Just Safe
      && certOf corpus "programs/mcx-dirty.s" "a" == Just [[1, 0], [0, 1]] )
  , ( "mcx-dirty-x.s: drop a admitted, B = X (one extra flip up front, one back)"
    , verdictOf corpus "programs/mcx-dirty-x.s" "a" [] == Just Safe
      && certOf corpus "programs/mcx-dirty-x.s" "a" == Just [[0, 1], [1, 0]] )
  , ( "mcx-dirty-half.s: one Toffoli deleted, drop a refused"
    , verdictOf corpus "programs/mcx-dirty-half.s" "a" [] == Just Unsafe )
  , ( "mcx-dirty-x.s is mcx-dirty.s with one extra X on the loan"
    , case (parsed corpus "programs/mcx-dirty.s", parsed corpus "programs/mcx-dirty-x.s") of
        (Right (v0, c0 : rest0), Right (vx, cx)) ->
          v0 == vx && cx == c0 : Gate gX ["a"] : rest0
        _ -> False )
  ]

-- >>> corpus <- readCorpus
-- >>> take 2 (loanChecks corpus)
-- [("mcx-dirty.s: drop a admitted, B = I (the loan returns as it arrived)",True),("mcx-dirty-x.s: drop a admitted, B = X (one extra flip up front, one back)",True)]
-- >>> length (loanChecks corpus)
-- 4

-- | The malformed sources and the refused spellings are each refused at the
-- right line.
refusalChecks :: [(String, Bool)]
refusalChecks = map badCheck badInputs ++ map legacyCheck legacySpellings

-- >>> take 2 refusalChecks
-- [("malformed (unknown gate) is a parse error at line 2",True),("malformed (malformed scalar) is a parse error at line 2",True)]
-- >>> length refusalChecks == length badInputs + length legacySpellings
-- True

-- | The trace command: one frame per statement in every selection, and
-- the drop of t reads the same verdict the checks above already pin.
traceChecks :: Corpus -> [(String, Bool)]
traceChecks corpus =
  [ ( "dj.s trace: one frame per statement, in every selection"
    , case (parsed corpus "programs/dj.s", djTraceText corpus) of
        (Right (_, prog), Right txt) ->
          let frames = length [ () | l <- lines txt, "frame " `isPrefixOf` l ]
              sels   = max 1 (length [ () | l <- lines txt
                                           , "selection " `isPrefixOf` l ])
          in frames == length prog * sels
        _ -> False )
  , ( "dj.s trace: last verdict line reads safe, line (1,-1)"
    , case djTraceText corpus of
        Right txt ->
          case reverse [ l | l <- lines txt
                            , "verdict:" `isPrefixOf` dropWhile (== ' ') l ] of
            (v : _) -> "safe, line (1,-1) on every test input" `isInfixOf` v
            []      -> False
        Left _ -> False )
  ]

-- >>> corpus <- readCorpus
-- >>> traceChecks corpus
-- [("dj.s trace: one frame per statement, in every selection",True),("dj.s trace: last verdict line reads safe, line (1,-1)",True)]
