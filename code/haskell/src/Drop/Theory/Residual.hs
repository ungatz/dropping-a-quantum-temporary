-- Drop.Theory.Residual: the table of verdicts, one row for each measurement record.
--
-- Question: Can the verdict of a drop that follows lifts be read off a table indexed by the
--           measurement record, built from the program text before any run?
-- Answer:   residualCheck cuts the program at its first lift. If the statements before it leave the
--           temporary on one line g at every visible input, with a visible action W whose
--           determinant is not zero, the pass parks (Hypotheses). Then each record of the table
--           says which levels of g survive its lifts; the state g restricted to them is the
--           transferred state, and the statements after the last lift are run once from it, on
--           every visible basis input, and judged by the matrix criterion (a row is admit or
--           refuse). If the prefix does not park, the pass abstains and every row refuses.
--           semanticVerdictAt instead re-runs the whole program under a record and applies the
--           criterion; residualAgrees compares the two row by row, and explainTable prints the table.
-- Paper:    sec:residual (compiling the record-dependent reclaim), app:residual, app:perrecord.
-- Shapes:   Hypotheses    Parks, with the line g, the visible action W and its determinant, or
--                         DoesNotPark, with the reason.
--           ResidualEntry one row: the record, the surviving block at each lift, the transferred
--                         state and whether the row admits.
--           ResidualTable the label, the lift depth, the hypotheses and the 2^depth rows.

module Drop.Theory.Residual
  ( -- * The table
    Hypotheses(..)
  , ResidualEntry(..)
  , ResidualTable(..)
  , residualCheck
    -- * Ground truth, and the comparison
  , residualAgrees
    -- * Reporting
  , explainTable
  ) where

import Data.List (intercalate, intersect)
import Drop.Theory.Criterion (verdictOfCoreMap)
import Drop.Theory.Lifted
import Drop.Theory.Algebra.Linear
import Drop.Theory.Pretty
import Drop.Theory.Program.Syntax (Name)
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Criterion.Split (Split(..), canonicalLine, factorSplit)

-- | What the pass checked before it was willing to rule.
data Hypotheses
  = Parks Vec Mat K
      -- ^ the prefix leaves the temporary constant on this ray, with this
      -- visible action, whose determinant is nonzero. Positional rather
      -- than named: the other constructor has none of these, and a
      -- partial selector would be a runtime error waiting to happen.
  | DoesNotPark String
      -- ^ the prefix does not leave the temporary constant (or is not shown to),
      -- so the check abstains and says nothing about the program

-- The tilted witness parks the temporary on one line; a qubit that splits after a joint gate does not.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> case rtHypotheses (residualCheck tp) of { Parks g w d -> (g, w, d); DoesNotPark _ -> ([], [], kzero) }
-- ([1,1,1/2],[[1,0,0],[0,1,0],[0,0,1]],1)
-- >>> let Right tq = checkLProgram qubitSplitAfterJointGate
-- >>> case rtHypotheses (residualCheck tq) of { DoesNotPark why -> why; Parks {} -> "" }
-- "the prefix does not factor at some visible input"

instance Show Hypotheses where
  show (Parks g w dt) =
    "prefix parks on the line " ++ show g
    ++ ", visible action " ++ show w ++ " with det " ++ show dt
  show (DoesNotPark why) = "ABSTAINS: " ++ why

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> let Right tr = checkLProgram sameChannelSafe
-- >>> rtHypotheses (residualCheck tp)
-- prefix parks on the line [1,1,1/2], visible action [[1,0,0],[0,1,0],[0,0,1]] with det 1
-- >>> rtHypotheses (residualCheck tr)
-- ABSTAINS: the prefix factors but parks on different lines at different inputs
-- >>> DoesNotPark "the visible register is empty"
-- ABSTAINS: the visible register is empty

-- | One row of the table.
data ResidualEntry = ResidualEntry
  { reTrace       :: Trace
  , reBlocks      :: [[Int]]   -- ^ the surviving block at each lift
  , reTransferred :: Vec       -- ^ the state that record transfers to the temporary
  , reAdmits      :: Bool      -- ^ the row's ruling: True admits the drop
  }

-- One row for each record: the tilted witness refuses In and admits Out.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> map (\e -> (reTrace e, reBlocks e, reTransferred e, reAdmits e)) (rtEntries (residualCheck tp))
-- [([In],[[0,1]],[1,1,0],False),([Out],[[2]],[0,0,1/2],True)]

-- | The table the pass emits: a map from the measurement record to admit or refuse,
-- with the hypotheses it rests on.
data ResidualTable = ResidualTable
  { rtLabel      :: String
  , rtDepth      :: Int
  , rtHypotheses :: Hypotheses
  , rtEntries    :: [ResidualEntry]
  }

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitnessNoRead
-- >>> let t = residualCheck tp
-- >>> (rtLabel t, rtDepth t, length (rtEntries t))
-- ("the witness with the read deleted: tilt, lift, drop",1,2)

-- The pass

-- | The table for a program: the hypothesis the pass checked, and one row for each measurement record.
residualCheck :: LTypedProgram -> ResidualTable
residualCheck tp = ResidualTable
  { rtLabel      = lLabel (ltProgram tp)
  , rtDepth      = ltDepth tp
  , rtHypotheses = hyps
  , rtEntries    = tableRows tp hyps }
  where
    hyps = parkingHypothesis tp

-- Two programs the pass rules on, and one it abstains on.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> fmap (map reAdmits . rtEntries . residualCheck) (checkLProgram liftedWitness)
-- Right [False,True]
-- >>> fmap (map reAdmits . rtEntries . residualCheck) (checkLProgram liftedWitnessNoRead)
-- Right [True,True]
-- >>> fmap (map reAdmits . rtEntries . residualCheck) (checkLProgram sameChannelSafe)
-- Right [False,False]

-- | The statements before the first lift. They are the same for every record, so the
-- first record of the run order is enough to read them off. 'Nothing' when that record
-- is too short to flatten the program.
prefixBeforeLifts :: LTypedProgram -> Maybe [LStmt]
prefixBeforeLifts tp = do
  (_, _, _, stmts, _) <- flattenAlong (ltProgram tp) firstRecord
  pure (takeWhile notLift stmts)
  where
    firstRecord = case allTraces (ltDepth tp) of
                    (t : _) -> t
                    []      -> []      -- impossible: allTraces never returns the empty list

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> fmap length (prefixBeforeLifts tp)
-- Just 1

-- | Does the prefix leave the temporary constant, and with what visible action?
parkingHypothesis :: LTypedProgram -> Hypotheses
parkingHypothesis tp = case prefixBeforeLifts tp of
  Nothing     -> DoesNotPark "the trace is too short to flatten the program"
  Just prefix -> parkingOf tp prefix

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> parkingHypothesis tp
-- prefix parks on the line [1,1,1/2], visible action [[1,0,0],[0,1,0],[0,0,1]] with det 1

-- | The hypothesis of a prefix, checked on the visible basis: the prefix factors at every
-- visible input, on one line, with a visible action that is right-invertible.
parkingOf :: LTypedProgram -> [LStmt] -> Hypotheses
parkingOf tp prefix =
  case mapM (prefixSplit tp prefix) [0 .. ltVisDim tp - 1] of
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

-- With no statements the temporary sits on its allocation state.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> parkingOf tp []
-- prefix parks on the line [1,0,0], visible action [[1,0,0],[0,1,0],[0,0,1]] with det 1
-- >>> fmap (parkingOf tp) (prefixBeforeLifts tp)
-- Just prefix parks on the line [1,1,1/2], visible action [[1,0,0],[0,1,0],[0,0,1]] with det 1

-- | Run the prefix on the visible basis vector @j@ and split off the temporary.
-- The temporary sits at tensor position 1 throughout: gates rename registers
-- but never move them, so the position is stable even though the name is not.
prefixSplit :: LTypedProgram -> [LStmt] -> Int -> Maybe Split
prefixSplit tp prefix j = factorSplit (lcDims c) [1] (lcAmp c)
  where
    c = runStmts (startConfig tp j) prefix

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> fmap splitLeft (prefixSplit tp [] 0)
-- Just [1,0,0]
-- >>> fmap (fmap splitLeft . (\p -> prefixSplit tp p 1)) (prefixBeforeLifts tp)
-- Just (Just [2/3,2/3,1/3])

-- | The configuration before the first statement: the visible register in basis
-- state @j@, the temporary in its allocation state.
startConfig :: LTypedProgram -> Int -> LConfig
startConfig tp j = LConfig
  { lcNames   = [lVis (ltProgram tp), ltTmpName tp]
  , lcDims    = [m, d]
  , lcDropped = []
  , lcAmp     = tensorV (vbasis m j) (vbasis d (ltAlloc tp))
  , lcStore   = []
  , lcTrace   = replicate (ltDepth tp) In      -- unused: the prefix is lift-free
  , lcUsed    = 0 }
  where
    m = ltVisDim tp
    d = ltTmpDim tp

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> let c = startConfig tp 1 in (lcNames c, lcDims c, lcAmp c)
-- (["v","t"],[3,3],[0,0,0,1,0,0,0,0,0])

-- | Every row of the table, one for each record in run order.
tableRows :: LTypedProgram -> Hypotheses -> [ResidualEntry]
tableRows tp hyps = [ tableRow tp hyps tr | tr <- allTraces (ltDepth tp) ]

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> map reTrace (tableRows tp (parkingHypothesis tp))
-- [[In],[Out]]
-- >>> map reAdmits (tableRows tp (parkingHypothesis tp))
-- [False,True]

-- | The row of one record: a parked row when the prefix parks and the record can be
-- flattened, and a refusing row otherwise.
tableRow :: LTypedProgram -> Hypotheses -> Trace -> ResidualEntry
tableRow tp (Parks g _ _) tr
  | Just (_, _, _, stmts, _) <- flattenAlong (ltProgram tp) tr = parkedRow tp g tr stmts
tableRow _ _ tr = refusingRow tr

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> let e = tableRow tp (parkingHypothesis tp) [Out] in (reBlocks e, reTransferred e, reAdmits e)
-- ([[2]],[0,0,1/2],True)
-- >>> let e = tableRow tp (DoesNotPark "no") [Out] in (reBlocks e, reTransferred e, reAdmits e)
-- ([],[],False)

-- | The row of a record the pass cannot rule on: nothing survives, nothing is transferred.
refusingRow :: Trace -> ResidualEntry
refusingRow tr = ResidualEntry
  { reTrace       = tr
  , reBlocks      = []
  , reTransferred = []
  , reAdmits      = False }

-- >>> let e = refusingRow [Out] in (reTrace e, reBlocks e, reTransferred e, reAdmits e)
-- ([Out],[],[],False)

-- | The row of one record when the prefix parks the temporary on the line of @g@:
-- the record picks the surviving levels, which give the transferred state, and the
-- statements after the last lift are judged from that state.
parkedRow :: LTypedProgram -> Vec -> Trace -> [LStmt] -> ResidualEntry
parkedRow tp g tr stmts = ResidualEntry
  { reTrace       = tr
  , reBlocks      = surviving
  , reTransferred = transferred
  , reAdmits      = continuationAdmitted tp names transferred (afterLastLift rest) }
  where
    rest        = dropWhile notLift stmts
    surviving   = zipWith (survivingBlock (ltTmpDim tp)) [ b | SLift _ _ b <- rest ] tr
    transferred = transferredState (ltTmpDim tp) g surviving
    before      = takeWhile notLift stmts ++ takeWhile isLift rest
    names       = namesAfter [lVis (ltProgram tp), ltTmpName tp] before

-- The record In keeps levels 0 and 1 of the temporary; the read after the lift leaks, so the row refuses.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> let Parks g _ _ = parkingHypothesis tp
-- >>> let Just (_, _, _, ss, _) = flattenAlong (ltProgram tp) [In]
-- >>> let e = parkedRow tp g [In] ss in (reBlocks e, reTransferred e, reAdmits e)
-- ([[0,1]],[1,1,0],False)

-- | The levels of the temporary that one lift keeps: the measured block for the choice
-- 'In', its complement among the @d@ levels for 'Out'.
survivingBlock :: Int -> [Int] -> Choice -> [Int]
survivingBlock _ b In  = b
survivingBlock d b Out = [ l | l <- [0 .. d-1], l `notElem` b ]

-- >>> survivingBlock 3 [0, 1] In
-- [0,1]
-- >>> survivingBlock 3 [0, 1] Out
-- [2]

-- | The state the record transfers to the temporary: @g@ on the levels every lift
-- keeps, zero elsewhere.
transferredState :: Int -> Vec -> [[Int]] -> Vec
transferredState d g surviving =
  -- impossible: g has one entry for each of the d levels of the temporary
  [ if l `elem` keep then g !! l else kzero | l <- [0 .. d-1] ]
  where
    keep = foldr intersect [0 .. d-1] surviving

-- The line g keeps only the levels every lift keeps.
-- >>> transferredState 3 [kone, kone, kzero] [[0, 1], [0]]
-- [1,0,0]
-- >>> transferredState 3 [kone, kone, kone] [[0, 1], [1, 2]]
-- [0,1,0]
-- >>> transferredState 3 [kone, kone, kone] []
-- [1,1,1]

-- | The statements after the last lift.
afterLastLift :: [LStmt] -> [LStmt]
afterLastLift = reverse . takeWhile notLift . reverse

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> let Just (_, _, _, ss, _) = flattenAlong (ltProgram tp) [In]
-- >>> length ss
-- 4
-- >>> length (afterLastLift ss)
-- 2
-- >>> length (afterLastLift [])
-- 0

-- | Is the statement a lift?
isLift :: LStmt -> Bool
isLift (SLift _ _ _) = True
isLift _             = False

-- >>> map isLift [SDrop "t", SLift "p" "t" [0]]
-- [False,True]

-- | Is the statement anything but a lift?
notLift :: LStmt -> Bool
notLift = not . isLift

-- >>> map notLift [SDrop "t", SLift "p" "t" [0]]
-- [True,False]

-- | The row's ruling: run the continuation from the transferred state on every visible
-- basis input and apply the criterion to the resulting map.
continuationAdmitted :: LTypedProgram -> [Name] -> Vec -> [LStmt] -> Bool
continuationAdmitted tp names gT cont
  | all kIsZero gT = True     -- zero-weight branch: no state, no obligation
  | otherwise      = admissible (verdictOfCoreMap (ltTmpDim tp) (ltVisDim tp)
                                                  (continuationMap tp names gT cont))

-- The tilted witness: from the state the record In transfers, the read leaks; with nothing transferred there is nothing to leak.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> let Just (_, _, _, ss, _) = flattenAlong (ltProgram tp) [In]
-- >>> let rest = dropWhile notLift ss
-- >>> let names = namesAfter ["v", "t"] (takeWhile notLift ss ++ takeWhile isLift rest)
-- >>> continuationAdmitted tp names [kone, kone, kzero] (afterLastLift rest)
-- False
-- >>> continuationAdmitted tp names [kzero, kzero, kzero] (afterLastLift rest)
-- True

-- | The map from the visible register to the temporary and the visible register that the
-- continuation performs on the transferred state: column @j@ is the run on basis input @j@.
continuationMap :: LTypedProgram -> [Name] -> Vec -> [LStmt] -> Mat
continuationMap tp names gT cont = matFromCols [ column j | j <- [0 .. m-1] ]
  where
    m = ltVisDim tp
    d = ltTmpDim tp
    column j =
      let c0 = LConfig { lcNames   = names
                       , lcDims    = [m, d]
                       , lcDropped = []
                       , lcAmp     = tensorV (vbasis m j) gT
                       , lcStore   = []
                       , lcTrace   = []
                       , lcUsed    = 0 }
          c  = runStmts c0 cont
      in matVec (reorder (lcDims c) [1, 0]) (lcAmp c)

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> let Just (_, _, _, ss, _) = flattenAlong (ltProgram tp) [In]
-- >>> let rest = dropWhile notLift ss
-- >>> let names = namesAfter ["v", "t"] (takeWhile notLift ss ++ takeWhile isLift rest)
-- >>> let k = continuationMap tp names [kone, kone, kzero] (afterLastLift rest) in (matRows k, matCols k)
-- (9,3)

-- | Are all the elements of the list equal?
allSame :: Eq a => [a] -> Bool
allSame []       = True
allSame (x : xs) = all (== x) xs

-- >>> allSame [1, 1, 1 :: Int]
-- True
-- >>> allSame [1, 2 :: Int]
-- False
-- >>> allSame ([] :: [Int])
-- True

-- Ground truth

-- | The semantic criterion, evaluated by re-running the whole program under
-- the trace.  This is what the table must reproduce, and it is computed a
-- different way on purpose.
semanticVerdictAt :: LTypedProgram -> Trace -> Bool
semanticVerdictAt tp tr = admissible (tvVerdict (verdictAt tp tr))

-- The criterion re-run on the whole program: the same two answers as the table.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> map (semanticVerdictAt tp) (allTraces 1)
-- [False,True]

-- | Does the table agree with the semantic criterion at every entry?
--
-- 'Nothing' when the check abstained (so there is nothing to compare); otherwise
-- the list of traces where the two disagree, which must be empty.
residualAgrees :: LTypedProgram -> Maybe [Trace]
residualAgrees tp = case rtHypotheses tbl of
  DoesNotPark _ -> Nothing
  Parks _ _ _   -> Just [ reTrace e | e <- rtEntries tbl
                        , reAdmits e /= semanticVerdictAt tp (reTrace e) ]
  where tbl = residualCheck tp

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> fmap residualAgrees (checkLProgram liftedWitness)
-- Right (Just [])
-- >>> fmap residualAgrees (checkLProgram liftedWitnessNoRead)
-- Right (Just [])
-- >>> fmap residualAgrees (checkLProgram qubitSplitAfterJointGate)
-- Right Nothing

-- Reporting

-- | The table as lines of text: the hypotheses, the visible action of the prefix, and one
-- line for each record with the table's ruling beside the criterion's.
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
  ++ [ "      " ++ padSep 7 "trace" ++ padSep 12 "surviving"
       ++ padSep 20 "transferred" ++ padSep 9 "emitted" ++ "semantics" ]
  ++ [ "      " ++ replicate 6 '\9472' ++ " " ++ replicate 11 '\9472' ++ " "
       ++ replicate 19 '\9472' ++ " " ++ replicate 8 '\9472' ++ " "
       ++ replicate 9 '\9472' ]
  ++ [ "      " ++ padSep 7 (showTraceR (reTrace e))
       ++ padSep 12 (showBlocks (reBlocks e))
       ++ padSep 20 (showVecR (reTransferred e))
       ++ padSep 9 (if reAdmits e then "admit" else "refuse")
       ++ (if reAdmits e == semanticVerdictAt tp (reTrace e)
             then (if reAdmits e then "admit" else "refuse")
             else "DISAGREES")
     | e <- rtEntries tbl ]
  ++ blank
  ++ kv "agrees with the criterion"
        (okBad "yes, at every entry" "NO, they differ somewhere"
               (residualAgrees tp == Just []))
  where
    tbl = residualCheck tp
    showTraceR t = filter (/= '"') (show t)
    showBlocks bs = intercalate "," [ "{" ++ intercalate "," (map show b) ++ "}"
                                    | b <- bs ]
    showVecR v = "[" ++ intercalate "," (map showK v) ++ "]"

-- The first lines of the printed table, each shown as a string.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> mapM_ print (take 4 (explainTable tp))
-- "  lift depth                      : 1 (so the table has 2 entries)"
-- "  the prefix parks on the line    : [1,1,1/2]"
-- "  det of the visible action W     : 1"
-- ""
-- >>> mapM_ print (drop 9 (explainTable tp))
-- ""
-- "      trace  surviving   transferred         emitted  semantics"
-- "      \9472\9472\9472\9472\9472\9472 \9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472 \9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472 \9472\9472\9472\9472\9472\9472\9472\9472 \9472\9472\9472\9472\9472\9472\9472\9472\9472"
-- "      [In]   {0,1}       [1,1,0]             refuse   refuse"
-- "      [Out]  {2}         [0,0,1/2]           admit    admit"
-- ""
-- "  agrees with the criterion       : yes, at every entry"
