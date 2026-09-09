-- Parser.hs: checks for the .s concrete syntax and for the programs in
-- programs/.
--
-- Checks: every file parses; parse . render is the identity on the syntax;
-- paired files agree with their module counterpart in syntax and verdict.
-- Files are read with unsafePerformIO since the check runner is pure.

module S.Test.Parser (checks, progFiles, parsed, fileSrc) where

import Control.Exception (IOException, try)
import Data.List (isInfixOf, isPrefixOf)
import System.IO.Unsafe (unsafePerformIO)

import S.Lang.Cyclo (Cyclo, embedQS2)
import S.Lang.QState
import S.Lang.Syntax
import S.Lang.Interp
import S.Lang.Parser
import S.Report.Trace (traceText)
import qualified S.Programs.DJ as DJ
import qualified S.Programs.BV as BV
import qualified S.Programs.Grover as Grover
import qualified S.Programs.QPE as QPE
import qualified S.Programs.RUS as RUS
import qualified S.Programs.Shor as Shor
import qualified S.Programs.Simon as Simon
import qualified S.Programs.Superdense as Superdense
import qualified S.Programs.Teleport as Teleport
import qualified S.Programs.TempAnd as TempAnd
import qualified S.Programs.Tilt as Tilt

-- Reading The Shipped Programs. Paths are relative to the package root,
-- where the suite is run.

progFiles :: [FilePath]
progFiles = map ("programs/" ++)
  [ "dj.s", "bv.s", "grover.s", "qpe.s", "teleport.s", "rus.s", "tilt.s"
  , "superdense.s", "mcx-dirty.s", "mcx-dirty-plus.s", "mcx-dirty-half.s"
  , "shor.s", "simon.s", "temp-and.s" ]

fileSrc :: FilePath -> Either String String
fileSrc f = unsafePerformIO $ do
  r <- try (readFile f) :: IO (Either IOException String)
  return (either (Left . show) Right r)
{-# NOINLINE fileSrc #-}

parsed :: FilePath -> Either String (VisSpec, Prog Cyclo)
parsed f = fileSrc f >>= parseProgram

-- | The files that have a module counterpart, with that module's program
-- moved into the parser's scalar field.
paired :: [(FilePath, VisSpec, Prog Cyclo)]
paired =
  [ ("programs/dj.s",        DJ.visDJ,   mapProg embedQS2 (DJ.djProg DJ.fId))
  , ("programs/bv.s",        BV.visBV,   mapProg embedQS2 (BV.bvProg 1 1))
  , ("programs/grover.s",    Grover.visG, mapProg embedQS2 Grover.groverProg)
  , ("programs/qpe.s",       QPE.visQPE, QPE.qpeT)
  , ("programs/teleport.s",  Teleport.visT, mapProg embedQS2 Teleport.teleP)
  , ("programs/rus.s",       RUS.visR,   mapProg fromRational RUS.rusProg)
  , ("programs/tilt.s",      Tilt.visTilt, mapProg fromRational Tilt.tiltProg)
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

-- | Sources exercising parts of the grammar the shipped files do not.
snippets :: [(String, String)]
snippets =
  [ ( "newdirty, phase and Swap over the tower"
    , unlines
        [ "vis x:2;"
        , "newdirty t:2 @ (1/rt2, -1/rt2);"
        , "phase (z8^3) t;"
        , "phase (i) x t;      -- two registers: a controlled phase"
        , "gate Swap x t;"
        , "drop t;"
        ] )
  , ( "qutrits, scalar sums and products, a nested if"
    , unlines
        [ "vis x:3;"
        , "newdirty t:3 @ (1/2*z8-1/2*z8^3, 1/2*z16, 1/2*i);"
        , "gate tilt t;"
        , "lift p = meas t in {0,1};"
        , "if p { gate READ3 x t; } else { if p { gate READ3 x t; } else { } }"
        , "drop t;"
        ] )
  , ( "T, S and a 3/5*z8 phase"
    , unlines
        [ "vis x:2;"
        , "new t:2;"
        , "gate T t;"
        , "gate S t;"
        , "phase (3/5*z8) t;"
        , "gate CX x t;"
        , "drop t;"
        ] )
  ]

-- Verdict Agreement With The Modules

-- | Same visible spec, same lift depth at the target, same verdict at every
-- selection.  The parsed program runs over the tower and the reference over
-- its own field.
agreeOn :: (Eq a, Fractional a)
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

-- | The line the temporary is left constant on at a site of a parsed file.
parkedOf :: FilePath -> String -> Maybe (StateV Cyclo)
parkedOf f tgt = case parsed f of
  Left _            -> Nothing
  Right (vis, prog) -> semanticParked vis prog tgt []

runFileOn :: FilePath -> [Sel] -> StateV Cyclo -> Maybe (Mach Cyclo)
runFileOn f sel inp = case parsed f of
  Left _            -> Nothing
  Right (vis, prog) -> Just (runStmts (initMach vis inp) prog sel Nothing)

-- Malformed Inputs

badInputs :: [(String, Int, String)]   -- (name, expected line, source)
badInputs =
  [ ("unknown gate",         2, "vis x:2;\ngate FOO x;\n")
  , ("malformed scalar",     3, "vis x:2;\nnew t:2;\nnewdirty u:2 @ (1/2, blah);\n")
  , ("lift level out of range", 3, "vis x:2;\nnew t:2;\nlift p = meas t in {5};\n")
  , ("unknown register",     2, "vis x:2;\ngate H y;\n")
  , ("gate dimension",       3, "vis x:2;\nnew t:2;\ngate CX t;\n")
  , ("if on an unbound bit", 3, "vis x:2;\nnew t:2;\nif p { } else { }\n")
  , ("missing vis line",     1, "new t:2;\n")
  , ("newdirty not a unit vector", 2, "vis x:2;\nnewdirty t:2 @ (1, 1);\n")
  , ("newdirty the zero vector",   2, "vis x:2;\nnewdirty t:2 @ (0, 0);\n")
  , ("mat wrong shape",      2, "vis x:2;\nmat x { 1, 0 ; 0 };\n")
  , ("mat wrong dimension",  3, "vis x:2;\nnew t:3;\nmat x t { 1, 0 ; 0, 1 };\n")
  , ("diag wrong count",     2, "vis x:2;\ndiag x (1, 1, 1);\n")
  , ("perm repeated image",  2, "vis x:2;\nperm x (0 0);\n")
  , ("perm image out of range", 2, "vis x:2;\nperm x (0 2);\n")
  , ("repeated register",    2, "vis x:2, y:2;\nmat x x { 1, 0, 0, 0 ; 0, 1, 0, 0 ; 0, 0, 1, 0 ; 0, 0, 0, 1 };\n")
  , ("gate on a dropped register", 4,
     "vis x:2;\nnew t:2;\ndrop t;\ngate H t;\n")
  ]

badCheck :: (String, Int, String) -> (String, Bool)
badCheck (nm, ln, src) =
  ( "malformed (" ++ nm ++ ") is a parse error at line " ++ show ln
  , case parseProgram src of
      Left err -> ("line " ++ show ln ++ ":") `isPrefixOf` err
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
    , ( "bv.s verdicts agree with ExBV s=11, parked [|->]"
      , agreeOn "programs/bv.s" BV.visBV (BV.bvProg 1 1) "t"
        && case parsed "programs/bv.s" of
             Right (vis, prog) ->
               probeResult vis prog "t" [] (ket [2,2] [0,0]) == PLine [1, -1]
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
    , ( "tilt.s verdicts agree with the Tilt module, opposite verdicts intact"
      , agreeOn "programs/tilt.s" Tilt.visTilt Tilt.tiltProg "t" )
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
    [ ( "dj.s: the block {0} of x carries weight 0 on |0>, f = x being balanced"
      , fmap (norm2S . mAmp) (runFileOn "programs/dj.s" [SIn] (ket [2] [0]))
          == Just 0 )
    , ( "grover.s lands exactly on the marked item |11>"
      , case runFileOn "programs/grover.s" [] (ket [2, 2] [0, 0]) of
          Just m  -> stateProportional (mAmp m) (ket (mDims m) [1, 1, 0])
          Nothing -> False )
    , ( "qpe.s: the final state is |001> tensor |1> exactly"
      , fmap mAmp (runFileOn "programs/qpe.s" [] (ket [2,2,2] [0,0,0]))
          == Just (ket [2,2,2,2] [0,0,1,1]) )
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
    , ( "tilt.s: exact branch weights 8/9 and 1/9 on probe e0"
      , case parsed "programs/tilt.s" of
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
  , -- the borrowed dirty ancilla: the loan comes back on its own ray, and
    -- deleting the restoring Toffoli is refused
    [ ( "mcx-dirty.s: drop a admitted, parked on the loan's ray (1,0)"
      , verdictOf "programs/mcx-dirty.s" "a" [] == Just Admissible
        && parkedOf "programs/mcx-dirty.s" "a" == Just [1, 0] )
    , ( "mcx-dirty-plus.s: drop a admitted, parked on the |+> loan's ray"
      , verdictOf "programs/mcx-dirty-plus.s" "a" [] == Just Admissible
        && parkedOf "programs/mcx-dirty-plus.s" "a" == Just [1, 1] )
    , ( "mcx-dirty-half.s: one Toffoli deleted, drop a refused"
      , verdictOf "programs/mcx-dirty-half.s" "a" [] == Just Inadmissible )
    , ( "the dirty pair differs only in the loaned state"
      , case (parsed "programs/mcx-dirty.s", parsed "programs/mcx-dirty-plus.s") of
          (Right (v0, c0 : t0), Right (vp, cp : tp)) ->
            v0 == vp
            && t0 == tp     -- everything after the loan agrees
            && c0 /= cp     -- and the loan itself does not
          _ -> False )
    ]
  , map badCheck badInputs
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
