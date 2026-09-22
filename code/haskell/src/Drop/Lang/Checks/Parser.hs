-- Parser.hs: checks for the .s concrete syntax and for the programs in
-- programs/.
--
-- Checks: every file parses; parse . render is the identity on the syntax;
-- paired files agree with their module counterpart in syntax and verdict.
-- Files are read with unsafePerformIO since the check runner is pure.

module Drop.Lang.Checks.Parser (checks, progFiles, parsed, parsedFile, fileSrc) where

import Control.Exception (IOException, try)
import Data.List (isInfixOf, isPrefixOf)
import System.IO.Unsafe (unsafePerformIO)

import Drop.Lang.Cyclo (Cyclo, embedQS2)
import Drop.Lang.Gates (gX)
import Drop.Lang.QState
import Drop.Lang.Ring (Conj)
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Parser
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

-- Reading The Shipped Programs. Paths are relative to the package root,
-- where the suite is run.

progFiles :: [FilePath]
progFiles = map ("programs/" ++)
  [ "dj.s", "grover.s", "qpe.s", "teleport.s", "rus.s"
  , "superdense.s", "mcx-dirty.s", "mcx-dirty-x.s", "mcx-dirty-half.s"
  , "shor.s", "simon.s", "temp-and.s"
  , "temp-general.s"
  , "learns-nothing.s", "bell-block.s"
  , "c.s", "copy-input.s"
  , "bell-pair.s", "bell-pair-split.s" ]

fileSrc :: FilePath -> Either String String
fileSrc f = unsafePerformIO $ do
  r <- try (readFile f) :: IO (Either IOException String)
  return (either (Left . show) Right r)
{-# NOINLINE fileSrc #-}

parsed :: FilePath -> Either String (VisSpec, Prog Cyclo)
parsed f = fileSrc f >>= parseProgram

parsedFile :: FilePath -> Either String SFile
parsedFile f = fileSrc f >>= parseFile

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

-- Parse-Render Identity

parseRenderId :: Either String (VisSpec, Prog Cyclo) -> Bool
parseRenderId (Left _) = False
parseRenderId (Right (vis, prog)) =
  case parseProgram (renderProgram vis prog) of
    Right (vis', prog') -> vis' == vis && prog' == prog
    Left _              -> False

-- | The whole file, header and return value and declarations included:
-- @parseFile . renderFile@ is the identity on 'SFile'.
fileRenderId :: Either String SFile -> Bool
fileRenderId (Left _) = False
fileRenderId (Right f) = parseFile (renderFile f) == Right f

-- | Sources exercising parts of the grammar the shipped files do not.
snippets :: [(String, String)]
snippets =
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
  , ( "a header loan, a gate and a drop"
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
  , ( "a tuple drop is one site, and a compound guard"
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

-- Verdict Agreement With The Modules

-- | Same visible spec, same lift depth at the target, same verdict at every
-- selection.  The parsed program runs over the tower and the reference over
-- its own field.
agreeOn :: (Eq a, Fractional a, Conj a)
        => FilePath -> VisSpec -> Prog a -> String -> Bool
agreeOn f visE progE tgt = case parsed f of
  Left _ -> False
  Right (vis, prog) ->
    vis == visE
    && liftDepthBefore prog tgt == liftDepthBefore progE tgt
    && and [ semanticVerdict vis prog tgt sel == semanticVerdict visE progE tgt sel
           | sel <- allSelections (liftDepthBefore progE tgt) ]

-- | The criterion's verdict at a site of a parsed file.
verdictOf :: FilePath -> String -> [Sel] -> Maybe Verdict
verdictOf f tgt sel = case parsed f of
  Left _            -> Nothing
  Right (vis, prog) -> Just (semanticVerdict vis prog tgt sel)


-- | The same, on one record.
parkedRecOf :: FilePath -> String -> [Sel] -> Maybe (StateV Cyclo)
parkedRecOf f tgt sel = case parsed f of
  Left _            -> Nothing
  Right (vis, prog) -> semanticParked vis prog tgt sel

-- | The isometry a safe loan site's drop reclaims with, at a site of a
-- parsed file.
certOf :: FilePath -> String -> Maybe (Matrix Cyclo)
certOf f tgt = case parsed f of
  Left _            -> Nothing
  Right (vis, prog) -> semanticLoanCert vis prog tgt []

runFileOn :: FilePath -> [Sel] -> StateV Cyclo -> Maybe (Mach Cyclo)
runFileOn f sel inp = case parsed f of
  Left _            -> Nothing
  Right (vis, prog) -> Just (runStmts (initMach vis inp) prog sel Nothing)

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
  , ("newdirty is refused",  2, "prog p (x : [2]) : [2] {\nnewdirty t : [2];\nreturn x }\n")
  , ("a loan is not a statement", 2,
     "prog p (x : [2]) : [2] {\nloan t : [2];\nreturn x }\n")
  , ("vis is refused",       2, "prog p (x : [2]) : [2] {\nvis y : [2];\nreturn x }\n")
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

badCheck :: (String, Int, String) -> (String, Bool)
badCheck (nm, ln, src) =
  ( "malformed (" ++ nm ++ ") is a parse error at line " ++ show ln
  , case parseProgram src of
      Left err -> ("line " ++ show ln ++ ":") `isPrefixOf` err
      Right _  -> False )

-- | The explicit-binding spellings the language does not accept: what it
-- accepts is exactly the printed grammar. Each is refused at the right
-- line, with a message naming the printed form instead.
-- (name, expected line, source, substring the message must name)
bindingSpellings :: [(String, Int, String, String)]
bindingSpellings =
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

bindingCheck :: (String, Int, String, String) -> (String, Bool)
bindingCheck (nm, ln, src, needle) =
  ( "the binding spelling `" ++ nm ++ "` is refused at line " ++ show ln
    ++ " naming `" ++ needle ++ "`"
  , case parseProgram src of
      Left err -> ("line " ++ show ln ++ ":") `isPrefixOf` err
                  && ("`" ++ needle ++ "`") `isInfixOf` err
      Right _  -> False )

-- The Trace Command

djTraceText :: Either String String
djTraceText = fileSrc "programs/dj.s" >>= \src -> traceText src Nothing

-- The Checks

checks :: [(String, Bool)]
checks = concat
  [ [ (f ++ " parses", either (const False) (const True) (parsed f))
    | f <- progFiles ]
  , [ (f ++ ": parse . render is the identity on the syntax", parseRenderId (parsed f))
    | f <- progFiles ]
  , -- the whole file, header, declarations and return value included
    [ (f ++ ": parseFile . renderFile is the identity on the file", fileRenderId (parsedFile f))
    | f <- progFiles ]
  , [ ("snippet, parse . render is the identity: " ++ nm
      , parseRenderId (parseProgram src))
    | (nm, src) <- snippets ]
  , [ (f ++ " is the module's program as syntax", parsed f == Right (vis, prog))
    | (f, vis, prog) <- paired ]
  , -- verdict agreement, each module run in its own scalar field
    [ ( "dj.s verdicts agree with the DJ module (f=x), parked [|->]"
      , agreeOn "programs/dj.s" DJ.visDJ (DJ.djProg DJ.fId) "t"
        && case parsed "programs/dj.s" of
             Right (vis, prog) ->
               probeResult vis prog "t" [] (ket [2] [0]) == PLine [1, -1]
             Left _ -> False )
    , ( "grover.s verdicts agree with ExGrover"
      , agreeOn "programs/grover.s" Grover.visG Grover.groverProg "t" )
    , ( "qpe.s verdicts agree with ExQPE at the drop of psi"
      , agreeOn "programs/qpe.s" QPE.visQPE QPE.qpeT "psi" )
    , ( "teleport.s verdicts agree with ExTeleport at both drops"
      , all (agreeOn "programs/teleport.s" Teleport.visT Teleport.teleP)
            ["m", "a"] )
    , ( "rus.s verdicts agree with ExRUS"
      , agreeOn "programs/rus.s" RUS.visR RUS.rusProg "t" )
    , ( "superdense.s verdicts agree with ExSuperdense at (1,1)"
      , agreeOn "programs/superdense.s" Superdense.visSD
                (Superdense.superdenseProg (1, 1)) "a" )
    , ( "shor.s verdicts agree with the Shor module, opposite verdicts on the two records"
      , agreeOn "programs/shor.s" Shor.visShor Shor.shorMeasured "w" )
    , ( "simon.s verdicts agree with ExSimon, both records safe on different lines"
      , agreeOn "programs/simon.s" Simon.visSimon Simon.simonMeasured "w" )
    , ( "temp-and.s verdicts agree with ExTempAnd, both records safe on different lines"
      , agreeOn "programs/temp-and.s" TempAnd.visXY
                TempAnd.andUncomputedByMeasurement "a" )
    ]
  , -- one number per file, re-derived through the text
    [ ( "DJ with its lift: the block {0} of x carries weight 0 on |0>, f = x being balanced"
      , norm2S (mAmp (runStmts (initMach DJ.visDJ (ket [2] [0]))
                               (mapProg embedQS2 (DJ.djProg DJ.fId)) [SIn] Nothing))
          == 0 )
    , ( "grover.s lands exactly on the marked item |11>"
      , case runFileOn "programs/grover.s" [] (ket [2, 2] [0, 0]) of
          Just m  -> stateProportional (mAmp m) (ket (mDims m) [1, 1, 0])
          Nothing -> False )
    , ( "qpe.s: the final state is |001> tensor |1> exactly"
      , fmap mAmp (runFileOn "programs/qpe.s" [] (ket [2,2,2] [0,0,0]))
          == Just (ket [2,2,2,2] [0,0,1,1]) )
    , ( "c.s: one text, two records, opposite verdicts (Theorem notext)"
      , verdictOf "programs/c.s" "t" [SIn]  == Just Safe
        && verdictOf "programs/c.s" "t" [SOut] == Just Unsafe
        && parkedRecOf "programs/c.s" "t" [SIn] == Just [1, 0] )
    , ( "copy-input.s: the program that copies its input and forgets it is refused"
      , verdictOf "programs/copy-input.s" "x" [] == Just Unsafe )
    , ( "learns-nothing.s: one site, unsafe, and the input is untouched"
      , verdictOf "programs/learns-nothing.s" "t" [] == Just Unsafe
        && fmap (dropSites . snd) (parsed "programs/learns-nothing.s")
             == Right [["t"]] )
    , ( "teleport.s: b carries the message (1,1) at every selection"
      , case parsed "programs/teleport.s" of
          Right (vis, prog) ->
            and [ case factorSplit (mDims m) [regPos m "b"] (mAmp m) of
                    Just (vb, _) -> stateProportional vb [1, 1]
                    Nothing      -> False
                | sel <- allSelections 2
                , let m = runStmts (initMach vis (ket [2] [0])) prog sel Nothing ]
          Left _ -> False )
    , ( "rus.s: exact branch weights 8/9 and 1/9 on probe e0"
      , case parsed "programs/rus.s" of
          Right (vis, prog) ->
            branchWeight vis prog "t" [SIn]  (ket [3] [0]) == 8 / 9
            && branchWeight vis prog "t" [SOut] (ket [3] [0]) == 1 / 9
          Left _ -> False )
    , ( "superdense.s: the pair (1,1) is read back with weight 1"
      , fmap (norm2S . mAmp)
             (runFileOn "programs/superdense.s" [SOut, SOut] (ket [2] [0]))
          == Just 1
        && and [ fmap (norm2S . mAmp)
                      (runFileOn "programs/superdense.s" sel (ket [2] [0]))
                   == Just 0
               | sel <- allSelections 2, sel /= [SOut, SOut] ] )
    ]
  , -- the borrowed loan: the drop's certificate is the fixed gate B it
    -- is reclaimed with (a loan carries no state to report a "line" of),
    -- and deleting the restoring Toffoli is refused
    [ ( "mcx-dirty.s: drop a admitted, B = I (the loan returns as it arrived)"
      , verdictOf "programs/mcx-dirty.s" "a" [] == Just Safe
        && certOf "programs/mcx-dirty.s" "a" == Just [[1, 0], [0, 1]] )
    , ( "mcx-dirty-x.s: drop a admitted, B = X (one extra flip up front, one back)"
      , verdictOf "programs/mcx-dirty-x.s" "a" [] == Just Safe
        && certOf "programs/mcx-dirty-x.s" "a" == Just [[0, 1], [1, 0]] )
    , ( "mcx-dirty-half.s: one Toffoli deleted, drop a refused"
      , verdictOf "programs/mcx-dirty-half.s" "a" [] == Just Unsafe )
    , ( "mcx-dirty-x.s is mcx-dirty.s with one extra X on the loan"
      , case (parsed "programs/mcx-dirty.s", parsed "programs/mcx-dirty-x.s") of
          (Right (v0, c0 : rest0), Right (vx, cx)) ->
            v0 == vx && cx == c0 : Gate gX ["a"] : rest0
          _ -> False )
    ]
  , map badCheck badInputs
  , map bindingCheck bindingSpellings
  , -- the trace command: one frame per statement in every selection, and
    -- the drop of t reads the same verdict the checks above already pin
    [ ( "dj.s trace: one frame per statement, in every selection"
      , case (parsed "programs/dj.s", djTraceText) of
          (Right (_, prog), Right txt) ->
            let frames = length [ () | l <- lines txt, "frame " `isPrefixOf` l ]
                sels   = max 1 (length [ () | l <- lines txt
                                             , "selection " `isPrefixOf` l ])
            in frames == length prog * sels
          _ -> False )
    , ( "dj.s trace: last verdict line reads safe, line (1,-1)"
      , case djTraceText of
          Right txt ->
            case reverse [ l | l <- lines txt
                              , "verdict:" `isPrefixOf` dropWhile (== ' ') l ] of
              (v : _) -> "safe, line (1,-1) on every test input" `isInfixOf` v
              []      -> False
          Left _ -> False )
    ]
  ]
