-- Pass.hs: the game the static pass has to win.
--
-- A pass may change the form and must not change the run, so the test is
-- the chain: for every drop site of the corpus, every record and every test
-- input, all the forms the passes made mean the same state at the drop.
-- Then the verdict the last form yields is compared with the criterion.

module Drop.Lang.Checks.Pass (checks) where

import Data.List (isInfixOf, sort)

import Drop.Lang.Cyclo (Cyclo)
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Pass
import Drop.Lang.Report.Explain (passText)
import Drop.Lang.Parser (parseProgram)
import Drop.Lang.Checks.Parser (progFiles, parsed, fileSrc)

-- The corpus

corpus :: [(FilePath, VisSpec, Prog Cyclo)]
corpus = [ (f, vis, prog) | f <- progFiles, Right (vis, prog) <- [parsed f] ]

sites :: [(FilePath, VisSpec, Prog Cyclo, String)]
-- The pass chain is stated one register at a time, so a tuple drop site
-- (the composite-temporary proposition) is not among the sites it is checked at.
sites = [ (f, vis, prog, x) | (f, vis, prog) <- corpus, [x] <- dropSites prog ]

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

-- | How far the passes got, per site: four forms when the check answers.
stageNamesAt :: VisSpec -> Prog Cyclo -> String -> [String]
stageNamesAt vis prog x = map stageName (chainStages (chain vis prog x))

-- The corpus, and where the check declines

decliningFiles :: [FilePath]
decliningFiles = sort
  [ f | (f, vis, prog) <- corpus
      , or [ HypothesesFail `elem` map reVerdict (rTable (residualCheck vis prog x))
           | [x] <- dropSites prog ] ]

answeringOK :: Bool
answeringOK = any hasLift answering && all agreesEverywhere answering
  where
    answering = [ (vis, prog) | (f, vis, prog) <- corpus, f `notElem` decliningFiles ]
    hasLift (_, prog) = any isLift prog
    agreesEverywhere (vis, prog) = and
      [ agreeRC (reVerdict e) (semanticVerdict vis prog x (reSel e)) == Agree
      | [x] <- dropSites prog, e <- rTable (residualCheck vis prog x) ]

-- Two programs of the section

-- | Two lifts on the temporary with only a visible gate between them.
chainProg :: String
chainProg = unlines
  [ "prog chain (x : [3]) : [3] {", "  new t : [3] @ |0>;", "  tilt t;"
  , "  p = lift[{0,1}] t;", "  tilt x;", "  q = lift[{1,2}] t;"
  , "  drop t;", "  return x", "}" ]

-- | Corollary 7.3: after a chain of lifts the temporary is left on g cut to
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

-- | A joint gate between two lifts is not a hypothesis of the check: the
-- pass cuts at the first lift and runs the rest as written.
betweenProg :: String
betweenProg = unlines
  [ "prog between (x : [3]) : [3] {", "  new t : [3] @ |0>;", "  tilt t;"
  , "  p = lift[{0,1}] t;", "  READ3 x t;", "  q = lift[{0}] t;"
  , "  drop t;", "  return x", "}" ]

betweenOK :: Bool
betweenOK = case parseProgram betweenProg of
  Left _ -> False
  Right (vis, prog) ->
    let r = residualCheck vis prog "t"
    in rDepth r == 2 && length (rTable r) == 4 && all snd (rHyps r)
       && all (\e -> agreeRC (reVerdict e)
                       (semanticVerdict vis prog "t" (reSel e)) == Agree)
              (rTable r)

rusPass :: Either String String
rusPass = fileSrc "programs/rus.s" >>= passText

checks :: [(String, Bool)]
checks =
  [ ("the passes preserve the run at every site, record and test input"
    , all (\(_, vis, prog, x) -> chainAgreesAt vis prog x) sites)
  , ("a site the check answers passes through all four forms"
    , stageNamesAt visRus rusProg "t" == ["source", "cut", "park", "resolve"])
  , ("a site the check declines stops at the form whose hypothesis failed"
    , stageNamesAt visShor shorProg "w" == ["source", "cut"]
      && chainStopped (chain visShor shorProg "w") == Just "prefix-parks")
  , ("the check declines on c, copy-input, shor, simon, teleport, temp-and,\
     \ the general-uncomputation transcript, and every loan (a different\
     \ theorem, Drop.Lang.Pass.Cut's target-is-a-loan), and nowhere else"
    , decliningFiles == sort [ "programs/c.s", "programs/copy-input.s"
                             , "programs/shor.s", "programs/simon.s"
                             , "programs/teleport.s", "programs/temp-and.s"
                             , "programs/temp-general.s"
                             , "programs/mcx-dirty.s", "programs/mcx-dirty-x.s"
                             , "programs/mcx-dirty-half.s" ])
  , ("every other file agrees with the criterion at every record", answeringOK)
  , ("the chain corollary: two lifts fold to the intersection of the kept blocks"
    , chainCorollaryOK)
  , ("a joint gate between two lifts is answered, not declined", betweenOK)
  , ("the printed pass on rus.s emits refuse at 1, admit at 0, and agrees 2/2"
    , case rusPass of
        Right txt -> "emitted table 1: refuse   0: admit" `isInfixOf` txt
                     && "agree 2/2" `isInfixOf` txt
        Left _    -> False)
  ]
  where
    (visRus, rusProg) = fromFile "programs/rus.s"
    (visShor, shorProg) = fromFile "programs/shor.s"
    fromFile f = case parsed f of
      Right vp -> vp
      Left e   -> error ("Drop.Lang.Checks.Pass: " ++ f ++ ": " ++ e)
