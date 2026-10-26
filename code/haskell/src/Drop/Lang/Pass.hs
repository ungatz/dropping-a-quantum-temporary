-- Drop.Lang.Pass: the static pass behind the per-record table.
--
-- Question: Can the verdict at a drop be read off the program before it runs, one record at a time,
--           and how do we know the passes changed nothing?
-- Answer:   Four passes, each in its own module, each with a form and an interpreter for that form:
--
--             source --cut--> Cut --park--> Parked --resolve--> [Record] --decide--> table
--
--           A pass may change the form, never the run. chain collects the meaning of every form,
--           so "the passes preserve the program" is a statement about a list, checked by
--           Drop.Lang.Checks.Pass over every single-register drop site of the corpus, every record
--           and every test input. cut, park and resolve each check a hypothesis and decline by
--           name rather than answering; decide answers. residualCheck composes the four and
--           writes the table: one row per record of the lifts before the drop, each row Admit,
--           Refuse, RUnreachable, or HypothesesFail when a pass declined. agreeRC sets a row
--           beside the criterion's verdict.
-- Paper:    sec:residual (compiling the record-dependent reclaim), thm:perrecord (the criterion on
--           one record), app:residual (the reclaim in detail).
-- Shapes:   Meaning a    what a form means: the machine at the drop, for a record and a visible input.
--           Stage a      one form: the pass that made it (stageName) and its meaning (stageMeaning).
--           Chain a      the forms one drop site passes through (chainStages), and the hypothesis
--                        that stopped the list, if one did (chainStopped).
--           ResEntry a   one row of the table: the record (reSel) and its bits (reBits), the state
--                        the first lift hands on (reTransferred) and the verdict (reVerdict).
--           ResReport a  the table for one target: its depth (rDepth, the lifts before the drop),
--                        the hypotheses in the order they were checked (rHyps), the parked line
--                        (rParked) and the rows (rTable).
--           Agreement    Agree, Disagree or Declines: a row beside the criterion.
--
-- This module re-exports the four passes.

module Drop.Lang.Pass
  ( -- * The four passes, in order
    module Drop.Lang.Pass.Cut
  , module Drop.Lang.Pass.Park
  , module Drop.Lang.Pass.Resolve
  , module Drop.Lang.Pass.Decide
    -- * The chain of forms, as data
  , Meaning, Stage (..), Chain (..), chain
    -- * The table the pass emits
  , ResEntry (..), ResReport (..), residualCheck
  , Agreement (..), agreeRC
  ) where

import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass.Cut
import Drop.Lang.Pass.Park
import Drop.Lang.Pass.Resolve
import Drop.Lang.Pass.Decide

-- The chain of forms ------------------------------------------------------------

-- | What every form means: the state at the drop site, for a record and a
-- visible input of the original program.
type Meaning a = [Sel] -> StateV a -> Mach a

-- The source form's meaning on the abstract's temporary AND: the registers it holds at the drop.
-- >>> :m + Drop.Lang.Programs.TempAnd Drop.Lang.Programs.RUS Drop.Lang.Programs.DJ Drop.Lang.Programs.Superdense
-- >>> let src = interpSource visXY andUncomputedByMeasurement "a"
-- >>> mNames (src [SIn] (ket [2, 2] [0, 0]))
-- ["x","y","a"]

data Stage a = Stage
  { stageName    :: String     -- ^ the pass that made this form
  , stageMeaning :: Meaning a
  }

-- >>> stageName (Stage "source" src)
-- "source"

-- | The forms one drop site passes through, in order. The list stops at the
-- first pass whose hypothesis fails, and that hypothesis is named.
data Chain a = Chain
  { chainStages  :: [Stage a]
  , chainStopped :: Maybe String
  }

-- >>> chainStopped (Chain [Stage "source" src] (Just "prefix-parks"))
-- Just "prefix-parks"
-- >>> map stageName (chainStages (Chain [Stage "source" src] Nothing))
-- ["source"]

-- | The forms of the program at the drop of @x@, from the source on, each as
-- a meaning.
chain :: (Eq a, Fractional a) => VisSpec -> Prog a -> String -> Chain a
chain vis prog x = requireFlat SurfaceFragment (visScope vis) prog `seq` case cut prog x of
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
        -- refusal: a selection that is not one of the records of the program's lifts
        []      -> error "chain: no record for this selection"

-- A program the passes answer for goes through all four forms and nothing stops it.
-- >>> let chainRus = chain visR rusProg "t"
-- >>> map stageName (chainStages chainRus)
-- ["source","cut","park","resolve"]
-- >>> chainStopped chainRus
-- Nothing

-- Every form means the same: at each selection, the four forms leave the same state at the drop.
-- Under bit 0, from |0>, that state has one nonzero amplitude, at index 8, in every form.
-- >>> let ms = map stageMeaning (chainStages chainRus)
-- >>> [ allEqual [ mAmp (m sel (ket [3] [0])) | m <- ms ] | sel <- allSelections 1 ]
-- [True,True]
-- >>> let nonzero sel m = [ (i, a) | (i, a) <- zip [0 :: Int ..] (mAmp (m sel (ket [3] [0]))), a /= 0 ]
-- >>> mapM_ (print . nonzero [SOut]) ms
-- [(8,1 % 3)]
-- [(8,1 % 3)]
-- [(8,1 % 3)]
-- [(8,1 % 3)]

-- The temporary AND stops after cut: its prefix entangles the temporary, so park declines.
-- >>> let chainAnd = chain visXY andUncomputedByMeasurement "a"
-- >>> map stageName (chainStages chainAnd)
-- ["source","cut"]
-- >>> chainStopped chainAnd
-- Just "prefix-parks"

-- A loan target stops at once, with only the source form.
-- >>> let chainLoan = chain [] ([Loan "a" 2, Drop ["a"]] :: Prog Rational) "a"
-- >>> map stageName (chainStages chainLoan)
-- ["source"]
-- >>> chainStopped chainLoan
-- Just "target-is-a-loan"

-- The table ---------------------------------------------------------------------

data ResEntry a = ResEntry
  { reSel         :: [Sel]
  , reBits        :: [Int]
  , reTransferred :: Maybe (StateV a)
  , reVerdict     :: RVerdict
  } deriving Show

-- A row written by hand: the record whose lift kept its block, refused.
-- >>> ResEntry [SIn] [1] Nothing Refuse :: ResEntry Rational
-- ResEntry {reSel = [SIn], reBits = [1], reTransferred = Nothing, reVerdict = Refuse}

data ResReport a = ResReport
  { rTarget :: String
  , rDepth  :: Int
  , rHyps   :: [(String, Bool)]     -- ^ in the order the passes checked them
  , rParked :: Maybe (StateV a)     -- ^ the line the prefix leaves the temporary on
  , rTable  :: [ResEntry a]
  } deriving Show

-- A report with no rows, written by hand.
-- >>> ResReport "t" 0 [] Nothing [] :: ResReport Rational
-- ResReport {rTarget = "t", rDepth = 0, rHyps = [], rParked = Nothing, rTable = []}

-- | Run the passes and emit the table: one row per record over the lifts
-- before the drop. A failed hypothesis declines at every row, with one
-- exception. Without a lift the prefix is the whole program, so a prefix
-- that does not leave the temporary constant is not a hypothesis failing,
-- it is the criterion refusing.
residualCheck :: (Eq a, Fractional a)
              => VisSpec -> Prog a -> String -> ResReport a
residualCheck vis prog x = requireFlat SurfaceFragment (visScope vis) prog `seq` case cut prog x of
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

-- With no lift the table has one row. Deutsch-Jozsa parks the |-> temporary and admits it.
-- >>> let tableDj = residualCheck visDJ (djProg fId) "t"
-- >>> (rDepth tableDj, map reVerdict (rTable tableDj), all snd (rHyps tableDj))
-- (0,[Admit],True)

-- The unsafe Toffoli has no lift either, and its prefix does not park: the one exception, a row that refuses.
-- >>> residualCheck visXY andComputed "a"
-- ResReport {rTarget = "a", rDepth = 0, rHyps = [("target-allocated-before-lifts",True),("prefix-parks",False)], rParked = Nothing, rTable = [ResEntry {reSel = [], reBits = [], reTransferred = Nothing, reVerdict = Refuse}]}

-- The repeat-until-success step: one lift, two rows. Bit 1 keeps the block {0,1} and is refused; bit 0 is admitted.
-- >>> let tableRus = residualCheck visR rusProg "t"
-- >>> (rDepth tableRus, rHyps tableRus, rParked tableRus)
-- (1,[("target-allocated-before-lifts",True),("prefix-parks",True),("B-right-invertible",True)],Just [1 % 1,1 % 1,1 % 2])
-- >>> mapM_ print (rTable tableRus)
-- ResEntry {reSel = [SIn], reBits = [1], reTransferred = Just [1 % 1,1 % 1,0 % 1], reVerdict = Refuse}
-- ResEntry {reSel = [SOut], reBits = [0], reTransferred = Just [0 % 1,0 % 1,1 % 2], reVerdict = Admit}

-- Superdense coding of (1, 1): two lifts, four rows; the records whose first bit is 1 are unreachable.
-- >>> map (\e -> (reBits e, reVerdict e)) (rTable (residualCheck visSD (superdenseProg (1, 1)) "a"))
-- [([1,1],RUnreachable),([1,0],RUnreachable),([0,1],Admit),([0,0],Admit)]

-- The temporary AND declines at park: every row says so, though the criterion accepts both records.
-- >>> let tableAnd = residualCheck visXY andUncomputedByMeasurement "a"
-- >>> (rDepth tableAnd, rHyps tableAnd, map reVerdict (rTable tableAnd))
-- (1,[("target-allocated-before-lifts",True),("prefix-parks",False)],[HypothesesFail,HypothesesFail])

-- Agreement between the check and the criterion ----------------------------------

-- | The check reporting unreachable where the criterion accepts still counts
-- as agreement: neither refuses. Declining is neither.
data Agreement = Agree | Disagree | Declines deriving (Eq, Show)

-- >>> [Agree, Disagree, Declines]
-- [Agree,Disagree,Declines]

-- | One row of the table beside the criterion's verdict on the same record.
agreeRC :: RVerdict -> Verdict -> Agreement
agreeRC HypothesesFail _            = Declines
agreeRC Admit          Safe         = Agree
agreeRC Refuse         Unsafe       = Agree
agreeRC RUnreachable   Unreachable  = Agree
agreeRC RUnreachable   Safe         = Agree
agreeRC _              _            = Disagree

-- >>> agreeRC Admit Safe
-- Agree
-- >>> agreeRC Refuse Unsafe
-- Agree
-- >>> agreeRC RUnreachable Safe
-- Agree
-- >>> agreeRC Admit Unsafe
-- Disagree
-- >>> agreeRC HypothesesFail Unsafe
-- Declines

-- Row by row on the repeat-until-success step: the table and the criterion agree on both records.
-- >>> map (\e -> agreeRC (reVerdict e) (semanticVerdict visR rusProg "t" (reSel e))) (rTable tableRus)
-- [Agree,Agree]
