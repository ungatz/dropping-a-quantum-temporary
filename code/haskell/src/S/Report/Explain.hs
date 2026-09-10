-- Explain.hs: the static pass, stage by stage, on one program.
--
-- `dqt pass file.s` prints what each pass of S.Pass made of the program
-- at every drop site: the cut, the parked line and visible action, the
-- residual program of each record, the test-input runs behind each
-- verdict, and the emitted table beside the criterion's answer.

module S.Report.Explain (passText, passFile) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import S.Lang.Cyclo (Cyclo)
import S.Lang.QState
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass
import S.Lang.Parser (parseProgram, renderCmd)
import S.Report.Run (wellFormed)
import S.Report.Trace (showTrace, showVec)

passText :: String -> Either String String
passText src = do
  (vis, prog) <- parseProgram src
  case wellFormed prog of
    Just err -> Left err
    Nothing  -> Right (unlines (concatMap (site vis prog) (dropSites prog)))

site :: VisSpec -> Prog Cyclo -> String -> [String]
site vis prog x =
  [ "the static pass at drop " ++ x
  , "visible registers: " ++ intercalate ", " [ n ++ ":" ++ show d | (n, d) <- vis ]
  , "" ]
  ++ stage1 ++ [""] ++ stage2 ++ [""] ++ stage34 ++ [""] ++ summary ++ [""]
  where
    depth  = liftDepthBefore prog x
    sels   = allSelections depth

    -- Stage 1: cut
    ecut = cut prog x
    stage1 = header 1 "cut" "the program up to the drop, split at its first lift"
      ++ case ecut of
           Left h  -> [fail' h]
           Right c ->
             [ "   prefix   " ++ render (cPrefix c)
             , "   rest     " ++ (if null (cRest c) then "(no lift before the drop)"
                                  else render (cRest c)) ]

    -- Stage 2: park
    epark = ecut >>= park vis
    stage2 = header 2 "park" ("run the prefix on the test inputs; does " ++ x
                              ++ " come out constant?")
      ++ case ecut of
           Left _  -> ["   (not reached)"]
           Right c ->
             [ "   " ++ pad 7 nm ++ factorLine c inp | (nm, inp) <- probesFor vis ]
             ++ case epark of
                  Left h  -> [fail' h]
                  Right p ->
                    [ "   line g    = " ++ showVec (pLine p)
                    , "   action B  = " ++ showMat (pAction p)
                      ++ (if rightInvertible (pAction p)
                            then ", det " ++ showTrace (detM (pAction p)) ++ ", right-invertible"
                            else ", not right-invertible") ]
    factorLine c inp =
      let m = runStmts (initMach vis inp) (cPrefix c) [] Nothing
      in case factorSplit (mDims m) [regPos m x] (mAmp m) of
           Nothing     -> x ++ " entangled with the rest"
           Just (t, r) -> x ++ " = " ++ showVec t ++ "   rest = " ++ showVec r

    -- Stages 3 and 4: resolve, decide
    eres = epark >>= \p -> fmap ((,) p) (resolve vis p)
    stage34 =
      header 3 "resolve" "one residual program per record; each lift becomes a restriction"
      ++ case eres of
           Left h | either (const False) (const True) epark -> [fail' h]
                  | otherwise -> ["   (not reached)"]
           Right (p, recs) ->
             [ "   " ++ pad 12 (recordName r) ++ pad 22 ("transferred " ++ showVec (transferred p r))
               ++ renderSteps (rSteps r)
             | r <- recs ]
      ++ [""]
      ++ header 4 "decide" ("run each residual program from g on the test inputs, factor "
                            ++ x ++ " at the drop")
      ++ case eres of
           Left _ -> ["   (not reached)"]
           Right (p, recs) ->
             [ "   " ++ pad 12 (recordName r)
               ++ unwords [ nm ++ " " ++ probe res | (nm, res) <- probeRecord vis p r ]
               ++ "   -> " ++ verdictName (decide vis p r)
             | r <- recs ]
    probe PZero     = "zero"
    probe PFail     = "entangled"
    probe (PLine l) = showVec l

    -- The table, and the criterion for comparison
    table = case eres of
      Right (p, recs) -> [ (rSel r, decide vis p r) | r <- recs ]
      Left _ | depth == 0, Left "prefix-parks" <- epark -> [([], Refuse)]
             | otherwise -> [ (sel, HypothesesFail) | sel <- sels ]
    crit = [ (sel, semanticVerdict vis pre x sel) | sel <- sels ]
      where pre = prefixThrough prog x
    summary =
      [ "emitted table " ++ row [ (sel, verdictName v) | (sel, v) <- table ]
      , "the criterion " ++ row [ (sel, criterionName v) | (sel, v) <- crit ]
        ++ "   " ++ agreement ]
    row cells = intercalate "   " [ selName sel ++ ": " ++ v | (sel, v) <- cells ]
    -- S.Pass.agreeRC is the one reading of "the check and the criterion
    -- agree"; the declining rows are already out, so Agree is the question.
    agreement =
      let n = length [ () | ((_, rv), (_, sv)) <- zip table crit
                          , rv /= HypothesesFail, agreeRC rv sv == Agree ]
          m = length [ () | (_, rv) <- table, rv /= HypothesesFail ]
      in if m == 0 then "(the check declined; the criterion still decides)"
         else "agree " ++ show n ++ "/" ++ show m

    recordName r = "record " ++ selName (rSel r)
    selName []  = "-"
    selName sel = concatMap (show . selBit) sel

header :: Int -> String -> String -> [String]
header n nm what = [show n ++ "  " ++ pad 9 nm ++ what]

fail' :: String -> String
fail' h = "   FAILS: " ++ h ++ "; the check declines here"

verdictName :: RVerdict -> String
verdictName Admit          = "admit"
verdictName Refuse         = "refuse"
verdictName RUnreachable   = "unreachable"
verdictName HypothesesFail = "declines"

criterionName :: Verdict -> String
criterionName Admissible   = "safe"
criterionName Inadmissible = "unsafe"
criterionName Unreachable  = "unreachable"

render :: Prog Cyclo -> String
render = unwords . map renderCmd

renderSteps :: [Step Cyclo] -> String
renderSteps = unwords . map one
  where one (Keep y ks) = "keep " ++ y ++ " in {" ++ intercalate "," (map show ks) ++ "};"
        one (Run seg)   = render seg

showMat :: Matrix Cyclo -> String
showMat b = "[ " ++ intercalate " ; " (map showVec b) ++ " ]"

pad :: Int -> String -> String
pad n s = s ++ replicate (max 1 (n - length s)) ' '

passFile :: FilePath -> IO ()
passFile f = do
  r <- try (readFile f) :: IO (Either IOException String)
  case r of
    Left e    -> die ("cannot read " ++ f ++ ": " ++ show e)
    Right src -> case passText src of
      Left err  -> die (f ++ ": " ++ err)
      Right out -> putStr out

-- | A refused file is a failure, not a report.
die :: String -> IO ()
die msg = hPutStrLn stderr msg >> exitFailure
