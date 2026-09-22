-- Decide.hs: pass 4 of the static pass, the one that answers.
--
-- A residual program has no measurement left in it, so the criterion of
-- the criterion section applies to it unchanged: run it on the test inputs and ask
-- whether the surviving ones leave the temporary on one and the same line.

module Drop.Lang.Pass.Decide
  ( RVerdict (..), probeRecord, decide ) where

import Drop.Lang.QState
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Pass.Park
import Drop.Lang.Pass.Resolve

-- | What the check can answer. The criterion answers with 'Verdict';
-- 'HypothesesFail' is the check declining, which it does when an earlier
-- pass could not establish its hypothesis.
data RVerdict = Admit | Refuse | RUnreachable | HypothesesFail
  deriving (Eq, Show)

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
