-- Drop.Lang.Pass.Decide: pass 4, the one that answers.
--
-- Question: Is the temporary left on one line under this record?
-- Answer:   A residual program has no measurement left in it, so the criterion applies to it
--           unchanged: run it on the test inputs, factor the temporary out of each result, and
--           ask whether the surviving inputs leave it on one and the same line. A record that no
--           input survives is unreachable; one line for all survivors is admitted; anything
--           else is refused. decide never declines. The fourth verdict, HypothesesFail, is the
--           row Drop.Lang.Pass writes when an earlier pass declined, so no residual program
--           reached decide at all.
-- Paper:    fig:criterion (the criterion), thm:perrecord (the criterion on one record).
-- Shapes:   RVerdict  Admit (one line), Refuse (not one line), RUnreachable (no input survives)
--                     or HypothesesFail (an earlier pass declined; decide never says it).

module Drop.Lang.Pass.Decide
  ( RVerdict (..), probeRecord, decide ) where

import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass.Park
import Drop.Lang.Pass.Resolve

-- The verdict --------------------------------------------------------------------

-- | What the check can answer. The criterion answers with 'Verdict';
-- 'HypothesesFail' is the check declining, which it does when an earlier
-- pass could not establish its hypothesis.
data RVerdict = Admit | Refuse | RUnreachable | HypothesesFail
  deriving (Eq, Show)

-- >>> [Admit, Refuse, RUnreachable, HypothesesFail]
-- [Admit,Refuse,RUnreachable,HypothesesFail]

-- | The record's residual program on each test input, factored at the drop.
probeRecord :: (Eq a, Fractional a)
            => VisSpec -> Parked a -> Record a -> [(String, ProbeResult a)]
probeRecord vis p r =
  [ (nm, result (interpRecord vis p r inp)) | (nm, inp) <- probesFor vis ]
  where
    result m
      | isZeroS (mAmp m) = PZero
      | otherwise = case factorSplit (mDims m) [regPos m (pSite p)] (mAmp m) of
          Nothing     -> PFail
          Just (t, _) -> PLine (canonicalLine t)

-- The repeat-until-success step. Under bit 0 every input leaves t on the basis line |2>.
-- Under bit 1 the three basis inputs leave it entangled, and only the all-ones input factors.
-- >>> :m + Drop.Lang.Pass Drop.Lang.Programs.RUS Drop.Lang.Programs.Superdense Drop.Lang.Programs.TempAnd
-- >>> let parkedRus = either error id (cut rusProg "t" >>= park visR)
-- >>> let recsRus = either error id (resolve visR parkedRus)
-- >>> mapM_ (print . probeRecord visR parkedRus) recsRus
-- [("e0",PFail),("e1",PFail),("e2",PFail),("sum",PLine [1 % 1,1 % 1,0 % 1])]
-- [("e0",PLine [0 % 1,0 % 1,1 % 1]),("e1",PLine [0 % 1,0 % 1,1 % 1]),("e2",PLine [0 % 1,0 % 1,1 % 1]),("sum",PLine [0 % 1,0 % 1,1 % 1])]

-- | Admit when every surviving test input leaves the temporary on one line;
-- unreachable when the record has no surviving input at all.
decide :: (Eq a, Fractional a) => VisSpec -> Parked a -> Record a -> RVerdict
decide vis p r = case [ res | (_, res) <- probeRecord vis p r, res /= PZero ] of
  []   -> RUnreachable
  live | all isLine live && allEqual [ l | PLine l <- live ] -> Admit
       | otherwise -> Refuse
  where
    isLine (PLine _) = True
    isLine _         = False

-- One line for every survivor is admitted; a record whose survivors disagree is refused.
-- >>> map (\r -> (rSel r, decide visR parkedRus r)) recsRus
-- [([SIn],Refuse),([SOut],Admit)]

-- Superdense coding of the message (1, 1): the first lift never keeps its block {0} on any test
-- input, so the two records whose first bit is 1 are unreachable and the other two are admitted.
-- >>> let parkedSd = either error id (cut (superdenseProg (1, 1)) "a" >>= park visSD)
-- >>> let recsSd = either error id (resolve visSD parkedSd)
-- >>> map (\r -> (rSel r, decide visSD parkedSd r)) recsSd
-- [([SIn,SIn],RUnreachable),([SIn,SOut],RUnreachable),([SOut,SIn],Admit),([SOut,SOut],Admit)]

-- Decide has no decline of its own. The row of a program whose prefix does not park is written
-- by Drop.Lang.Pass.residualCheck: the temporary AND declines at park, so both its rows say so.
-- >>> map reVerdict (rTable (residualCheck visXY andUncomputedByMeasurement "a"))
-- [HypothesesFail,HypothesesFail]
