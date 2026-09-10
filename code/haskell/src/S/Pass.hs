-- Pass.hs: the static pass behind the runtime check.
--
-- Four passes, each in its own module, each with a form and an
-- interpreter for that form:
--
--   source --cut--> Cut --park--> Parked --resolve--> [Record] --decide--> table
--
-- A pass may change the form, never the run. 'chain' collects the meaning
-- of every form so "the passes preserve the program" is a statement about
-- a list, checked by S.Test.Pass over every drop site, record and test
-- input. Each pass checks one hypothesis and declines by name rather than
-- answering; 'residualCheck' composes the four into the runtime check.

module S.Pass
  ( -- * The four passes, in order
    module S.Pass.Cut
  , module S.Pass.Park
  , module S.Pass.Resolve
  , module S.Pass.Decide
    -- * The chain of forms, as data
  , Meaning, Stage (..), Chain (..), chain
    -- * The table the pass emits
  , ResEntry (..), ResReport (..), residualCheck
  , Agreement (..), agreeRC
  ) where

import S.Lang.QState
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass.Cut
import S.Pass.Park
import S.Pass.Resolve
import S.Pass.Decide

-- The chain of forms

-- | What every form means: the state at the drop site, for a record and a
-- visible input of the original program.
type Meaning a = [Sel] -> StateV a -> Mach a

data Stage a = Stage
  { stageName    :: String     -- ^ the pass that made this form
  , stageMeaning :: Meaning a
  }

-- | The forms one drop site passes through, in order. The list stops at the
-- first pass whose hypothesis fails, and that hypothesis is named.
data Chain a = Chain
  { chainStages  :: [Stage a]
  , chainStopped :: Maybe String
  }

chain :: (Eq a, Fractional a) => VisSpec -> Prog a -> String -> Chain a
chain vis prog x = case cut prog x of
  Left h  -> Chain [source] (Just h)
  Right c -> case park vis c of
    Left h  -> Chain [source, cutStage c] (Just h)
    Right p -> case resolve vis p of
      Left h     -> Chain [source, cutStage c, parkStage p] (Just h)
      Right recs -> Chain [source, cutStage c, parkStage p, recordStage p recs] Nothing
  where
    source     = Stage "source" (interpSource vis prog x)
    cutStage c = Stage "cut"    (interpCut vis c)
    parkStage  = Stage "park" . interpParked vis
    -- The prefix delivered B v to the visible register, so a residual
    -- program is run from there; that is what makes this comparable with
    -- the forms before it, which are run from v.
    recordStage p recs = Stage "resolve" $ \sel inp ->
      case [ r | r <- recs, rSel r == sel ] of
        (r : _) -> interpRecord vis p r (mulMV (pAction p) inp)
        []      -> error "chain: no record for this selection"

-- The table

data ResEntry a = ResEntry
  { reSel         :: [Sel]
  , reBits        :: [Int]
  , reTransferred :: Maybe (StateV a)
  , reVerdict     :: RVerdict
  } deriving Show

data ResReport a = ResReport
  { rTarget :: String
  , rDepth  :: Int
  , rHyps   :: [(String, Bool)]     -- ^ in the order the passes checked them
  , rParked :: Maybe (StateV a)     -- ^ the line the prefix leaves the temporary on
  , rTable  :: [ResEntry a]
  } deriving Show

-- | Run the passes and emit the table: one row per record over the lifts
-- before the drop. A failed hypothesis declines at every row, with one
-- exception. Without a lift the prefix is the whole program, so a prefix
-- that does not leave the temporary constant is not a hypothesis failing,
-- it is the criterion refusing.
residualCheck :: (Eq a, Fractional a)
              => VisSpec -> Prog a -> String -> ResReport a
residualCheck vis prog x = case cut prog x of
  Left h  -> declined [(h, False)] Nothing
  Right c -> case park vis c of
    Left h
      | null (cRest c) -> ResReport x 0 [(hCut, True), (h, False)] Nothing
                            [ResEntry [] [] Nothing Refuse]
      | otherwise      -> declined [(hCut, True), (h, False)] Nothing
    Right p -> case resolve vis p of
      Left h -> declined [(hCut, True), (hPark, True), (h, False)] (Just (pLine p))
      Right recs ->
        ResReport x d
          ([(hCut, True), (hPark, True)] ++ [ (hLift, True) | d > 0 ])
          (Just (pLine p))
          [ ResEntry (rSel r) (map selBit (rSel r)) (Just (transferred p r))
                     (decide vis p r)
          | r <- recs ]
  where
    d = liftDepthBefore prog x
    declined hyps g =
      ResReport x d hyps g
        [ ResEntry sel (map selBit sel) Nothing HypothesesFail
        | sel <- allSelections d ]
    hCut  = "target-allocated-before-lifts"
    hPark = "prefix-parks"
    hLift = "B-right-invertible"

-- Agreement between the check and the criterion

-- | The check reporting unreachable where the criterion accepts still counts
-- as agreement: neither refuses. Declining is neither.
data Agreement = Agree | Disagree | Declines deriving (Eq, Show)

agreeRC :: RVerdict -> Verdict -> Agreement
agreeRC HypothesesFail _            = Declines
agreeRC Admit          Admissible   = Agree
agreeRC Refuse         Inadmissible = Agree
agreeRC RUnreachable   Unreachable  = Agree
agreeRC RUnreachable   Admissible   = Agree
agreeRC _              _            = Disagree
