-- Drop.Lang.Checks.Pass: the game the static pass has to win.
--
-- Question: Does a pass change the run, and does the table the passes emit agree with the criterion?
-- Answer:   A pass may change the form and must not change the run, so the test is the chain: for
--           every single-register drop site of the corpus, every record and every test input, all
--           the forms the passes made (chainAgreesAt) mean the same state at the drop. Then the
--           verdict the last form yields is compared with the criterion. The check declines on
--           some files, by the name of the hypothesis that failed, and the suite pins which: a
--           site the check answers passes through all four forms, a site it declines stops at the
--           form whose hypothesis failed, and decliningFiles is exactly the list the check names,
--           so every other file agrees with the criterion at every record. Two programs of the
--           paper's section are built here as text (chainProg: two lifts with only a visible gate
--           between them; betweenProg: a joint gate between two lifts) and the pass is run on
--           them. The last check reads the printed pass on rus.s. Every function that reads a
--           file takes the Corpus of Drop.Lang.Checks.Parser as its first argument.
-- Paper:    sec:residual (compiling the record-dependent reclaim), thm:perrecord (the criterion on
--           one record), app:residual (the reclaim in detail).
-- Shapes:   programs      the corpus files that parse, each with its visible registers and program.
--           sites         one entry per single-register drop site of the corpus, with its file.
--           decliningFiles
--                         the files at which the check declines, sorted.
--           chainProg, betweenProg
--                         the two programs of the section, as .s text.

module Drop.Lang.Checks.Pass (checks) where

import Data.List (isInfixOf, sort)

import Drop.Lang.Scalar (Cyclo)
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass
import Drop.Lang.Report.Explain (passText)
import Drop.Lang.Parser (parseProgram)
import Drop.Lang.Checks.Parser (Corpus, progFiles, parsed, fileSrc)

-- The corpus

programs :: Corpus -> [(FilePath, VisSpec, Prog Cyclo)]
programs corpus = [ (f, vis, prog) | f <- progFiles, Right (vis, prog) <- [parsed corpus f] ]

-- Every shipped file parses, so the programs are the files, in order.
-- >>> import Drop.Lang.Checks.Parser (readCorpus)
-- >>> corpus <- readCorpus
-- >>> length (programs corpus) == length progFiles
-- True
-- >>> [ f | (f, _, _) <- take 3 (programs corpus) ]
-- ["programs/dj.s","programs/grover.s","programs/qpe.s"]

sites :: Corpus -> [(FilePath, VisSpec, Prog Cyclo, String)]
-- The pass chain is stated one register at a time, so a tuple drop site
-- (the composite-temporary proposition) is not among the sites it is checked at.
sites corpus = [ (f, vis, prog, x) | (f, vis, prog) <- programs corpus, [x] <- dropSites prog ]

-- Single-register drop sites only: a tuple drop is not among them.
-- >>> corpus <- readCorpus
-- >>> length (sites corpus)
-- 21
-- >>> [ (f, x) | (f, _, _, x) <- take 4 (sites corpus) ]
-- [("programs/dj.s","t"),("programs/grover.s","t"),("programs/qpe.s","psi"),("programs/teleport.s","m")]

-- | Every form the passes made, at one site, means one state.
chainAgreesAt :: VisSpec -> Prog Cyclo -> String -> Bool
chainAgreesAt vis prog x = case map stageMeaning (chainStages (chain vis prog x)) of
  []           -> False
  (m0 : rest) -> and
    [ same (m0 sel inp) (m sel inp)
    | m <- rest
    , sel <- allSelections (liftDepthBefore prog x)
    , (_, inp) <- probesFor vis ]
  where same a b = mNames a == mNames b && mAmp a == mAmp b

-- The four forms of the rus.s drop mean the same state; so do the forms of the temporary AND, which stops after the cut.
-- >>> corpus <- readCorpus
-- >>> fmap (\(vis, prog) -> chainAgreesAt vis prog "t") (parsed corpus "programs/rus.s")
-- Right True
-- >>> fmap (\(vis, prog) -> chainAgreesAt vis prog "a") (parsed corpus "programs/temp-and.s")
-- Right True

-- | How far the passes got, per site: four forms when the check answers.
stageNamesAt :: VisSpec -> Prog Cyclo -> String -> [String]
stageNamesAt vis prog x = map stageName (chainStages (chain vis prog x))

-- Four forms where the check answers, two where it declines at the prefix.
-- >>> corpus <- readCorpus
-- >>> fmap (\(vis, prog) -> stageNamesAt vis prog "t") (parsed corpus "programs/rus.s")
-- Right ["source","cut","park","resolve"]
-- >>> fmap (\(vis, prog) -> stageNamesAt vis prog "w") (parsed corpus "programs/shor.s")
-- Right ["source","cut"]

-- The corpus, and where the check declines

decliningFiles :: Corpus -> [FilePath]
decliningFiles corpus = sort
  [ f | (f, vis, prog) <- programs corpus
      , or [ HypothesesFail `elem` map reVerdict (rTable (residualCheck vis prog x))
           | [x] <- dropSites prog ] ]

-- The files at which the check declines: program (c), copy-input, the three loan programs, the measured Shor, Simon,
-- teleport and temporary AND, and the general-uncomputation transcript.
-- >>> corpus <- readCorpus
-- >>> decliningFiles corpus
-- ["programs/c.s","programs/copy-input.s","programs/mcx-dirty-half.s","programs/mcx-dirty-x.s","programs/mcx-dirty.s","programs/shor.s","programs/simon.s","programs/teleport.s","programs/temp-and.s","programs/temp-general.s"]

answeringOK :: Corpus -> Bool
answeringOK corpus = any hasLift answering && all agreesEverywhere answering
  where
    answering = [ (vis, prog) | (f, vis, prog) <- programs corpus
                              , f `notElem` decliningFiles corpus ]
    hasLift (_, prog) = any isLift prog
    agreesEverywhere (vis, prog) = and
      [ agreeRC (reVerdict e) (semanticVerdict vis prog x (reSel e)) == Agree
      | [x] <- dropSites prog, e <- rTable (residualCheck vis prog x) ]

-- Every other file agrees with the criterion at every record, and at least one of them has a lift.
-- >>> corpus <- readCorpus
-- >>> answeringOK corpus
-- True

-- Two programs of the section

-- | Two lifts on the temporary with only a visible gate between them.
chainProg :: String
chainProg = unlines
  [ "prog chain (x : [3]) : [3] {", "  new t : [3] @ |0>;", "  tilt t;"
  , "  p = lift[{0,1}] t;", "  tilt x;", "  q = lift[{1,2}] t;"
  , "  drop t;", "  return x", "}" ]

-- The program as text (each line shown with its quotes, so its indentation stays).
-- >>> mapM_ print (lines chainProg)
-- "prog chain (x : [3]) : [3] {"
-- "  new t : [3] @ |0>;"
-- "  tilt t;"
-- "  p = lift[{0,1}] t;"
-- "  tilt x;"
-- "  q = lift[{1,2}] t;"
-- "  drop t;"
-- "  return x"
-- "}"

-- | The chain corollary: after a chain of lifts the temporary is left on g cut to
-- the intersection of the blocks the outcomes kept, so folding the
-- restrictions into one at the front changes nothing.
chainCorollaryOK :: Bool
chainCorollaryOK = case parseProgram chainProg of
  Left _ -> False
  Right (vis, prog) -> case cut prog "t" >>= park vis of
    Left _  -> False
    Right p -> case resolve vis p of
      Left _     -> False
      Right recs -> length recs == 4 && and
        [ mAmp (interpRecord vis p r inp) == mAmp (interpRecord vis p (folded p r) inp)
        | r <- recs, (_, inp) <- probesFor vis ]
  where
    folded p r =
      let kept = foldr (\ks acc -> [ l | l <- acc, l `elem` ks ]) [0 .. pDim p - 1]
                       [ ks | Keep y ks <- rSteps r, y == "t" ]
      in r { rSteps = Keep "t" kept : [ s | s@(Run _) <- rSteps r ] }

-- >>> chainCorollaryOK
-- True

-- | A joint gate between two lifts is not a hypothesis of the check: the
-- pass cuts at the first lift and runs the rest as written.
betweenProg :: String
betweenProg = unlines
  [ "prog between (x : [3]) : [3] {", "  new t : [3] @ |0>;", "  tilt t;"
  , "  p = lift[{0,1}] t;", "  READ3 x t;", "  q = lift[{0}] t;"
  , "  drop t;", "  return x", "}" ]

-- >>> mapM_ print (lines betweenProg)
-- "prog between (x : [3]) : [3] {"
-- "  new t : [3] @ |0>;"
-- "  tilt t;"
-- "  p = lift[{0,1}] t;"
-- "  READ3 x t;"
-- "  q = lift[{0}] t;"
-- "  drop t;"
-- "  return x"
-- "}"

betweenOK :: Bool
betweenOK = case parseProgram betweenProg of
  Left _ -> False
  Right (vis, prog) ->
    let r = residualCheck vis prog "t"
    in rDepth r == 2 && length (rTable r) == 4 && all snd (rHyps r)
       && all (\e -> agreeRC (reVerdict e)
                       (semanticVerdict vis prog "t" (reSel e)) == Agree)
              (rTable r)

-- >>> betweenOK
-- True

rusPass :: Corpus -> Either String String
rusPass corpus = fileSrc corpus "programs/rus.s" >>= passText

-- The first lines of the printed pass on rus.s, and the line the last check reads.
-- >>> corpus <- readCorpus
-- >>> either putStrLn (mapM_ print . take 6 . lines) (rusPass corpus)
-- "the static pass at drop t"
-- "visible registers: x:3"
-- ""
-- "1  cut      the program up to the drop, split at its first lift"
-- "   prefix   new t : [3] @ |0>; tilt t;"
-- "   rest     p = lift[{0,1}] t; if p { READ3 x t; } else { READ3 x t; }"
-- >>> fmap (filter ("emitted table" `isInfixOf`) . lines) (rusPass corpus)
-- Right ["emitted table 1: refuse   0: admit"]

checks :: Corpus -> [(String, Bool)]
checks corpus =
  [ ("the passes preserve the run at every site, record and test input"
    , all (\(_, vis, prog, x) -> chainAgreesAt vis prog x) (sites corpus))
  , ("a site the check answers passes through all four forms"
    , stageNamesAt visRus rusProg "t" == ["source", "cut", "park", "resolve"])
  , ("a site the check declines stops at the form whose hypothesis failed"
    , stageNamesAt visShor shorProg "w" == ["source", "cut"]
      && chainStopped (chain visShor shorProg "w") == Just "prefix-parks")
  , ("the check declines on c, copy-input, shor, simon, teleport, temp-and,\
     \ the general-uncomputation transcript, and every loan (a different\
     \ theorem, Drop.Lang.Pass.Cut's target-is-a-loan), and nowhere else"
    , decliningFiles corpus == sort [ "programs/c.s", "programs/copy-input.s"
                             , "programs/shor.s", "programs/simon.s"
                             , "programs/teleport.s", "programs/temp-and.s"
                             , "programs/temp-general.s"
                             , "programs/mcx-dirty.s", "programs/mcx-dirty-x.s"
                             , "programs/mcx-dirty-half.s" ])
  , ("every other file agrees with the criterion at every record", answeringOK corpus)
  , ("the chain corollary: two lifts fold to the intersection of the kept blocks"
    , chainCorollaryOK)
  , ("a joint gate between two lifts is answered, not declined", betweenOK)
  , ("the printed pass on rus.s emits refuse at 1, admit at 0, and agrees 2/2"
    , case rusPass corpus of
        Right txt -> "emitted table 1: refuse   0: admit" `isInfixOf` txt
                     && "agree 2/2" `isInfixOf` txt
        Left _    -> False)
  ]
  where
    (visRus, rusProg) = fromFile "programs/rus.s"
    (visShor, shorProg) = fromFile "programs/shor.s"
    fromFile f = case parsed corpus f of
      Right vp -> vp
      -- refusal: a corpus file that does not parse stops the suite, naming the file
      Left e   -> error ("Drop.Lang.Checks.Pass: " ++ f ++ ": " ++ e)

-- The first check states the chain claim over every site; the second is the rus.s chain.
-- >>> corpus <- readCorpus
-- >>> length (checks corpus)
-- 8
-- >>> map fst (take 2 (checks corpus))
-- ["the passes preserve the run at every site, record and test input","a site the check answers passes through all four forms"]
-- >>> all snd (checks corpus)
-- True
