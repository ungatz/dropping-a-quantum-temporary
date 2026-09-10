-- |
-- Module      : DQT.Residual
--
-- The compiler emits a table from classical outcome bits to verdict,
-- computed statically and consulted at the lift; it inspects no quantum
-- state, unlike the semantic criterion it must agree with.
module DQT.Residual
  ( -- * The table
    Hypotheses(..)
  , ResidualEntry(..)
  , ResidualTable(..)
  , residualCheck
    -- * Ground truth, and the comparison
  , semanticVerdictAt
  , residualAgrees
    -- * Reporting
  , explainTable
  ) where

import Data.List (dropWhileEnd, intercalate)
import DQT.Criterion (Verdict(..), verdictOfCoreMap)
import DQT.Lifted
import DQT.Algebra.Linear
import DQT.Pretty
import DQT.Algebra.Scalar
import DQT.Criterion.Split (Split(..), canonicalLine, factorSplit)

-- | What the pass checked before it was willing to rule.
data Hypotheses
  = Parks Vec Mat K
      -- ^ the prefix leaves the temporary constant on this ray, with this
      -- visible action, whose determinant is nonzero. Positional rather
      -- than named: the other constructor has none of these, and a
      -- partial selector would be a runtime error waiting to happen.
  | DoesNotPark String
      -- ^ the prefix does not leave the temporary constant, so the check
      -- abstains: sound, and not a completeness claim

instance Show Hypotheses where
  show (Parks g w dt) =
    "prefix parks on the line " ++ show g
    ++ ", visible action " ++ show w ++ " with det " ++ show dt
  show (DoesNotPark why) = "ABSTAINS: " ++ why

-- | One row of the emitted table.
data ResidualEntry = ResidualEntry
  { reTrace       :: Trace
  , reBlocks      :: [[Int]]   -- ^ the surviving block at each lift
  , reTransferred :: Vec       -- ^ the state that outcome transferred to the temporary
  , reAdmits      :: Bool      -- ^ the check's verdict
  }

-- | The object the pass emits.  This map from classical outcome bits to a
-- verdict is the runtime check; at run time it is one table lookup.
data ResidualTable = ResidualTable
  { rtLabel      :: String
  , rtDepth      :: Int
  , rtHypotheses :: Hypotheses
  , rtEntries    :: [ResidualEntry]
  }

-- The pass

residualCheck :: LTypedProgram -> ResidualTable
residualCheck tp = ResidualTable
  { rtLabel      = lLabel p
  , rtDepth      = depth
  , rtHypotheses = hyps
  , rtEntries    = entries }
  where
    p     = ltProgram tp
    d     = ltTmpDim tp
    m     = ltVisDim tp
    i0    = ltAlloc tp
    depth = ltDepth tp

    -- Step 1: cut the run at its lifts. The prefix is the same for every
    -- trace, since it precedes the first lift, so it can be read off any
    -- trace.
    firstTrace = case allTraces depth of
                   (t : _) -> t
                   []      -> []
    cut = do
      (tname, tdim, alloc, stmts, _ret) <- flattenAlong p firstTrace
      pure (tname, tdim, alloc, span notLift stmts)
    notLift (SLift _ _ _) = False
    notLift _             = True

    isLift (SLift _ _ _) = True
    isLift _             = False

    -- Step 2: the hypothesis that the prefix leaves the temporary constant,
    -- checked on the visible basis.
    hyps = case cut of
      Nothing -> DoesNotPark "the trace is too short to flatten the program"
      Just (_, _, _, (prefix, rest))
        | not (liftsAreConsecutive rest) -> DoesNotPark betweenTheLifts
        | otherwise                      -> parkingOf prefix

    -- The pass reads the temporary's state once, at the first lift, and masks
    -- it by each surviving block.  That is the state after the last lift only
    -- when nothing between them has moved it, so a statement sitting between
    -- two lifts -- 'DQT.Lifted.Programs.liveTradeRespread' is the corpus's
    -- example, with a re-spreading gate there -- is outside what this pass
    -- covers.  It abstains, which costs it that program's table and keeps it
    -- sound; masking across the gate would not be.
    liftsAreConsecutive ss = not (any isLift (dropWhile isLift ss))
    betweenTheLifts =
      "a statement sits between two lifts; the pass reads the temporary's \
      \state at the first lift and has no way to carry it across that statement"

    parkingOf prefix =
      case mapM (splitAfterPrefix prefix) [0 .. m-1] of
        Nothing -> DoesNotPark "the prefix does not factor at some visible input"
        Just [] -> DoesNotPark "the visible register is empty"
        Just sps@(sp0 : _)
          | not (allSame (map (canonicalLine . splitLeft) sps)) ->
              DoesNotPark "the prefix factors but parks on different lines at different inputs"
          | kIsZero dt -> DoesNotPark ("the visible action is not right-invertible (det = "
                                        ++ show dt ++ ")")
          | otherwise  -> Parks (canonicalLine (splitLeft sp0)) w dt
          where
            w  = matFromCols (map splitRight sps)
            dt = det w

    -- run the prefix on the visible basis vector j, and split off the temporary
    -- The temporary sits at tensor position 1 throughout: gates rename registers
    -- but never move them, so the position is stable even though the name is not.
    splitAfterPrefix prefix j =
      let c = runStmts (initialConfig j) prefix
      in factorSplit (lcDims c) [1] (lcAmp c)

    initialConfig j = LConfig
      { lcNames   = [lVis p, tmpName]
      , lcDims    = [m, d]
      , lcDropped = []
      , lcAmp     = tensorV (vbasis m j) (vbasis d i0)
      , lcStore   = []
      , lcTrace   = replicate depth In      -- unused: the prefix is lift-free
      , lcUsed    = 0 }

    tmpName = ltTmpName tp

    -- Steps 3 and 4: one row per trace.
    entries = [ entryFor tr | tr <- allTraces depth ]

    entryFor tr = ResidualEntry
      { reTrace       = tr
      , reBlocks      = surviving
      , reTransferred = transferred
      , reAdmits      = admits }
      where
        (surviving, transferred, admits) = case (hyps, flattenAlong p tr) of
          -- The premise is re-checked here and not only in 'hyps': 'hyps' reads
          -- the first trace, and a conditional can put a lift in one branch
          -- alone, so a later trace can have a shape the first one did not.
          (Parks g _ _, Just (_, _, _, stmts, _))
            | liftsAreConsecutive (dropWhile notLift stmts) ->
            let rest      = dropWhile notLift stmts
                liftBlocks = [ b | SLift _ _ b <- rest ]
                surv      = zipWith survivingBlock liftBlocks tr
                keep      = foldr intersect [0 .. d-1] surv
                gT        = [ if l `elem` keep then g !! l else kzero
                            | l <- [0 .. d-1] ]
                before    = takeWhile notLift stmts ++ takeWhile isLift rest
                liveNames = namesAfter [lVis p, tmpName] before
            in (surv, gT, runContinuation liveNames gT (afterLifts rest))
          _ -> ([], [], False)

        survivingBlock b ch = case ch of
          In  -> b
          Out -> [ l | l <- [0 .. d-1], l `notElem` b ]

    intersect xs ys = [ x | x <- xs, x `elem` ys ]

    -- everything after the last lift
    afterLifts stmts = reverse (takeWhile isNotLift (reverse stmts))
      where isNotLift (SLift _ _ _) = False
            isNotLift _             = True

    -- Step 4: run the continuation from the transferred state, on every visible
    -- test input, and apply the criterion to the resulting map.
    runContinuation liveNames gT cont
      | all kIsZero gT = True     -- zero-weight branch: no state, no obligation
      | otherwise =
          case verdictOfCoreMap d m k of
            Safe _  -> True
            Vacuous -> True
            Unsafe _ _ -> False
      where
        k = matFromCols [ column j | j <- [0 .. m-1] ]
        column j =
          let c0 = LConfig { lcNames   = liveNames
                           , lcDims    = [m, d]
                           , lcDropped = []
                           , lcAmp     = tensorV (vbasis m j) gT
                           , lcStore   = []
                           , lcTrace   = []
                           , lcUsed    = 0 }
              c  = runStmts c0 cont
          in matVec (reorder (lcDims c) [1, 0]) (lcAmp c)

    allSame []       = True
    allSame (x : xs) = all (== x) xs

-- Ground truth

-- | The semantic criterion, evaluated by re-running the whole program under
-- the trace.  This is what the runtime check's table must reproduce, and it
-- is computed a different way on purpose.
semanticVerdictAt :: LTypedProgram -> Trace -> Bool
semanticVerdictAt tp tr = case tvVerdict (verdictAt tp tr) of
  Safe _     -> True
  Vacuous    -> True
  Unsafe _ _ -> False

-- | Does the emitted table agree with the semantic criterion at every entry?
--
-- 'Nothing' when the check abstained (so there is nothing to compare); otherwise
-- the list of traces where the two disagree, which must be empty.
residualAgrees :: LTypedProgram -> Maybe [Trace]
residualAgrees tp = case rtHypotheses tbl of
  DoesNotPark _ -> Nothing
  Parks _ _ _   -> Just [ reTrace e | e <- rtEntries tbl
                        , reAdmits e /= semanticVerdictAt tp (reTrace e) ]
  where tbl = residualCheck tp

-- Reporting

explainTable :: LTypedProgram -> [String]
explainTable tp =
  kvs [ ("lift depth", show (rtDepth tbl) ++ "   (so the table has "
                       ++ show (2 ^ rtDepth tbl :: Int) ++ " entries)") ]
  ++ (case rtHypotheses tbl of
        DoesNotPark why -> kv "hypotheses" ("ABSTAINS: " ++ why)
        Parks g w dt ->
          kv "the prefix parks on the line" (showVecR g)
          ++ kv "det of the visible action W" (showK dt)
          ++ blank
          ++ boxedMat "W" (map (map showK) w))
  ++ blank
  ++ para "The emitted object. At run time each row is one lookup:"
  ++ blank
  ++ [ "      " ++ lay header, "      " ++ lay ruleRow ]
       -- An abstaining check refuses every record, so it refuses the safe ones
       -- too.  That is its incompleteness, which the hypotheses line above
       -- already reports; it is not a disagreement, and only a check that ruled
       -- can disagree.
  ++ [ "      " ++ lay (cells e) ++ flag e | e <- rtEntries tbl ]
  ++ blank
  ++ kv "agrees with the criterion"
        (case residualAgrees tp of
           Nothing -> "not compared: the check abstained, so it refuses every record"
           Just [] -> "yes, at every entry"
           Just ts -> "NO, they differ at " ++ show (length ts) ++ " record(s)")
  where
    tbl = residualCheck tp
    abstained = case rtHypotheses tbl of
      DoesNotPark _ -> True
      Parks _ _ _   -> False

    -- The columns are measured, not guessed.  A trace prints as @[In,Out]@ and
    -- a transferred state as a list of exact scalars, so both outgrow any
    -- constant width as the depth or the dimension rises, and 'padTo' keeps the
    -- separating space while losing the alignment.
    header  = ["trace", "surviving", "transferred", "emitted", "semantics"]
    cells e = [ showTraceR (reTrace e)
              , showBlocks (reBlocks e)
              , showVecR (reTransferred e)
              , if reAdmits e then "admit" else "refuse"
              , if semanticVerdictAt tp (reTrace e) then "admit" else "refuse" ]
    widths  = [ maximum (length h : map (length . (!! i) . cells) (rtEntries tbl))
              | (i, h) <- zip [0 :: Int ..] header ]
    ruleRow = [ replicate w '\9472' | w <- widths ]
    lay xs  = dropWhileEnd (== ' ') (concat (zipWith padTo (map (+ 1) widths) xs))
    flag e  = if abstained || reAdmits e == semanticVerdictAt tp (reTrace e)
                then "" else "   DISAGREES"

    showTraceR t = filter (/= '"') (show t)
    showBlocks bs = intercalate "," [ "{" ++ intercalate "," (map show b) ++ "}"
                                    | b <- bs ]
    showVecR v = "[" ++ intercalate "," (map showK v) ++ "]"
