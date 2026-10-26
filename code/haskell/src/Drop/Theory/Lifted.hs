-- Drop.Theory.Lifted: programs with measurements, run under a measurement record.
--
-- Question: What does a program that measures its temporary denote, and what is the verdict of its drop on each
--           measurement record?
-- Answer:   A lift measures a block of the temporary and binds the outcome to a classical parameter; a
--           conditional reads a parameter. A record (Trace) holds one choice, In or Out, for each lift in run
--           order: In keeps the measured block and Out its complement. The semantics is not normalised, so
--           the squared norm of a branch is its probability. Fixing a record settles every conditional, so
--           coreMapAt is the matrix of the program on that record, and verdictAt applies the criterion to
--           it, giving Safe, Unsafe, or Unreachable when the matrix is zero. verdictProfile is the verdict at
--           every record. constantProfile asks whether all records of nonzero weight get the same ruling,
--           and oracleSplit is its negation. flattenAlong turns the run along a record into a list of
--           statements, which Drop.Theory.Residual cuts and reruns.
-- Paper:    sec:meas:forms (the lift and the record), sec:meas:meta (one matrix per record), sec:meas:leaf
--           (the site on one record), app:meas-tree.
-- Shapes:   Choice, Trace   which branch of a lift survives, and one choice for each lift of a run.
--           LTerm           a term of the lifted calculus: the core, plus LLift and LIf.
--           LTypedProgram   a program that has been checked, with its temporary and its lift depth.
--           LConfig         a run in progress: names, dimensions, amplitudes, parameters, the record left.
--           LStmt           one statement of the straight line a run executes.
--           TraceVerdict    the verdict at one record, with the branch weight at each visible input.

module Drop.Theory.Lifted
  ( -- * Measurement records
    Choice(..)
  , Trace
  , allTraces
    -- * Syntax
  , PName
  , LTerm(..)
  , LProgram(..)
    -- * Typing
  , LTypeError(..)
  , checkLProgram
  , LTypedProgram(..)
    -- * Running
  , LConfig(..)
  , coreMapAt
    -- * Flattening a run into statements
  , LStmt(..)
  , flattenAlong
  , runStmts
  , namesAfter
    -- * Verdicts
  , admissible
  , TraceVerdict(..)
  , tvWeight
  , verdictAt
  , verdictProfile
  , constantProfile
  , oracleSplit
  , everySoundStaticDisciplineRejects
  ) where

import Data.List (nub)

import Drop.Theory.Criterion (Certificate(..), Verdict(..), certificateOfCoreMap, verdictOfCoreMap)
import Drop.Theory.Algebra.Linear
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Criterion.Split (canonicalLine)
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing (Ctx, TypeError (..), checkGate, ctxExtend, ctxLookup, ctxNames, ctxRemove, ctxRename)

-- Measurement records

-- | Which branch of a lift survives: the one inside the measured block, or the
-- one outside it.
data Choice = In | Out deriving (Eq, Show)

-- A lift keeps the measured block (In) or its complement (Out).
-- >>> [In, Out]
-- [In,Out]
-- >>> In == Out
-- False

-- | A measurement record: one choice per lift, in run order, supplied by
-- the run, never by the text. A static analysis is a function that does
-- not receive one.
type Trace = [Choice]

-- A record holds one choice for each lift, in run order.
-- >>> [In, Out] :: Trace
-- [In,Out]

-- | All @2^d@ traces at depth @d@, in a fixed order.
allTraces :: Int -> [Trace]
allTraces 0 = [[]]
allTraces n = [ c : t | c <- [In, Out], t <- allTraces (n-1) ]

-- A depth d has 2^d records.
-- >>> allTraces 0
-- [[]]
-- >>> allTraces 1
-- [[In],[Out]]
-- >>> allTraces 2
-- [[In,In],[In,Out],[Out,In],[Out,Out]]
-- >>> length (allTraces 3)
-- 8

-- Syntax

type PName = String

-- >>> ("p" :: PName)
-- "p"

-- | The lifted calculus: the affine core plus two constructs.
data LTerm
  = LRet  Name
  | LNew  Name Int Int LTerm
  | LAct  (Name, Name) Gate (Name, Name) LTerm
  | LLift PName Name [Int] LTerm
      -- ^ @let p = lift (meas t in S) in e@ (the theory layer's own
      -- notation, not the .s surface spelling, which writes
      -- @p = lift[S] t;@): the one rule connecting the two
      -- sorts, where a state-level event creates a parameter-level binding.
  | LIf   PName LTerm LTerm
      -- ^ @if p then e1 else e0@, branching on a lifted parameter.
  | LDrop Name LTerm

-- The first statement of the smallest lifted programs allocates the temporary.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> case lTerm liftedWitnessNoRead of { LNew t d i0 _ -> (t, d, i0); _ -> ("", 0, 0) }
-- ("t",3,0)
-- >>> case lTerm sameChannelSafe of { LNew t d i0 _ -> (t, d, i0); _ -> ("", 0, 0) }
-- ("t",2,0)

data LProgram = LProgram
  { lLabel  :: String
  , lVis    :: Name
  , lVisDim :: Int
  , lTerm   :: LTerm
  }

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> (lLabel liftedWitnessNoRead, lVis liftedWitnessNoRead, lVisDim liftedWitnessNoRead)
-- ("the witness with the read deleted: tilt, lift, drop","v",3)

-- | The number of @lift@ nodes on the longest path: a static count, read off
-- the text, and an upper bound on how many outcomes a run can lift. It is
-- not a prediction of that number, since a program with two lifts may
-- execute one.
liftDepth :: LTerm -> Int
liftDepth (LRet _)         = 0
liftDepth (LNew _ _ _ e)   = liftDepth e
liftDepth (LAct _ _ _ e)   = liftDepth e
liftDepth (LDrop _ e)      = liftDepth e
liftDepth (LLift _ _ _ e)  = 1 + liftDepth e
liftDepth (LIf _ e1 e0)    = max (liftDepth e1) (liftDepth e0)

-- The number of lifts on the longest path of the text.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> liftDepth (LRet "v")
-- 0
-- >>> liftDepth (lTerm liftedWitnessNoRead)
-- 1
-- >>> liftDepth (LLift "p" "t" [0] (LLift "q" "t" [0] (LRet "v")))
-- 2
-- >>> liftDepth (LIf "p" (LRet "v") (LLift "q" "t" [0] (LRet "v")))
-- 1

-- Typing

data LTypeError
  = LUnbound Name
  | LUnboundParam PName
  | LNotTemporary Name
  | LBadBlock [Int] Int
  | LLeftover [Name]
  | LDuplicateParam PName
  | LBranchTypes
  | LMustAllocate
  | LCore TypeError
    -- ^ a premise the core rules state for New and Act, which the lifted
    -- calculus inherits: 'Drop.Theory.Program.Typing'
  deriving (Eq)

-- The errors are shown by the instance below.
-- >>> LNotTemporary "v" == LNotTemporary "v"
-- True
-- >>> LBranchTypes == LMustAllocate
-- False

instance Show LTypeError where
  show (LUnbound x)        = "unbound register " ++ show x
  show (LUnboundParam p)   = "unbound parameter " ++ show p
                             ++ " (a conditional may only read a parameter a "
                             ++ "previous lift bound)"
  show (LNotTemporary x)   = show x ++ " is not a temporary, so it cannot be "
                             ++ "measured or dropped"
  show (LBadBlock s d)     = "the measured block " ++ show s
                             ++ " is not a subset of [0.." ++ show (d-1) ++ "]"
  show (LLeftover xs)      = "names left over at the end: " ++ show xs
  show (LDuplicateParam p) = "the parameter " ++ show p ++ " is already bound"
  show LBranchTypes        = "the two branches of a conditional disagree"
  show LMustAllocate       = "a program must begin with an allocation"
  show (LCore e)           = show e

-- >>> either show (const "typed") (checkLProgram (LProgram "x" "v" 2 (LRet "v")))
-- "a program must begin with an allocation"
-- >>> either show (const "typed") (checkLProgram (LProgram "x" "v" 2 (LNew "t" 2 0 (LIf "p" (LRet "v") (LRet "v")))))
-- "unbound parameter \"p\" (a conditional may only read a parameter a previous lift bound)"
-- >>> either show (const "typed") (checkLProgram (LProgram "x" "v" 2 (LNew "t" 2 0 (LLift "p" "t" [0, 5] (LDrop "t" (LRet "v"))))))
-- "the measured block [0,5] is not a subset of [0..1]"
-- >>> either show (const "typed") (checkLProgram (LProgram "x" "v" 2 (LNew "t" 2 0 (LRet "v"))))
-- "names left over at the end: [\"t\"]"
-- >>> either show (const "typed") (checkLProgram (LProgram "x" "v" 2 (LNew "t" 2 0 (LDrop "v" (LRet "v")))))
-- "\"v\" is not a temporary, so it cannot be measured or dropped"
-- >>> either show (const "typed") (checkLProgram (LProgram "x" "v" 2 (LNew "t" 2 0 (LLift "p" "t" [0] (LLift "p" "t" [1] (LDrop "t" (LRet "v")))))))
-- "the parameter \"p\" is already bound"
-- >>> either show (const "typed") (checkLProgram (LProgram "x" "v" 2 (LNew "t" 2 0 (LLift "p" "t" [0] (LIf "p" (LDrop "t" (LRet "v")) (LRet "v"))))))
-- "names left over at the end: [\"t\"]"

data LTypedProgram = LTypedProgram
  { ltProgram :: LProgram
  , ltTmpName :: Name
  , ltTmpDim  :: Int
  , ltAlloc   :: Int
  , ltVisDim  :: Int
  , ltDepth   :: Int
  }

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> (ltTmpName tp, ltTmpDim tp, ltAlloc tp, ltVisDim tp, ltDepth tp)
-- ("t",3,0,3,1)

-- | The two-sorted judgement @Delta ; Gamma |- e@.
--
-- The parameter context @Delta@ is a list of names: duplicable and
-- weakenable, so a parameter need not be used and may be read twice. The
-- state context @Gamma@ is affine. The @LLift@ rule is
-- the only place a state-level event reaches across.
lcheck :: [PName] -> Ctx -> LTerm -> Either LTypeError ()
lcheck _ g (LRet v) =
  case ctxLookup v g of
    Nothing -> Left (LUnbound v)
    Just _ | length g /= 1 -> Left (LLeftover (filter (/= v) (ctxNames g)))
           | otherwise     -> Right ()

-- New and Act carry the core rules' premises unchanged (the lifted calculus
-- is the core plus lift and if): a register has at least one level, the
-- allocation index is one of them, a gate is a unitary of the right shape,
-- and its two outputs are fresh, distinct names.
lcheck ps g (LNew t d i0 e)
  | t `elem` ctxNames g = Left (LUnbound t)
  | d < 1               = Left (LCore (BadRegisterDimension t d))
  | i0 < 0 || i0 >= d   = Left (LCore (BadAllocIndex i0 d))
  | otherwise           = lcheck ps (ctxExtend t (Tmp d) g) e

lcheck ps g (LAct (t',v') u (t,v) e) =
  case (ctxLookup t g, ctxLookup v g) of
    (Just (Tmp d), Just (Vis m)) -> do
      either (Left . LCore) Right (checkGate u d m)
      if t' == v' then Left (LCore (GateOutputsCoincide t')) else Right ()
      mapM_ (\x -> if x `elem` ctxNames (ctxRemove t (ctxRemove v g))
                     then Left (LCore (DuplicateName x)) else Right ())
            [t', v']
      lcheck ps (ctxRename v v' (Vis m) (ctxRename t t' (Tmp d) g)) e
    (Nothing, _) -> Left (LUnbound t)
    (_, Nothing) -> Left (LUnbound v)
    _            -> Left (LNotTemporary t)

lcheck ps g (LLift p t s e)
  | p `elem` ps = Left (LDuplicateParam p)
  | otherwise = case ctxLookup t g of
      Just (Tmp d)
        | all (\l -> l >= 0 && l < d) s -> lcheck (p : ps) g e
        | otherwise                     -> Left (LBadBlock s d)
      Just _  -> Left (LNotTemporary t)
      Nothing -> Left (LUnbound t)

lcheck ps g (LIf p e1 e0)
  | p `notElem` ps = Left (LUnboundParam p)
  | otherwise      = lcheck ps g e1 >> lcheck ps g e0

lcheck ps g (LDrop t e) =
  case ctxLookup t g of
    Just (Tmp _) -> lcheck ps (ctxRemove t g) e
    Just _       -> Left (LNotTemporary t)
    Nothing      -> Left (LUnbound t)

-- The parameter context first, then the register context.
-- >>> lcheck [] [("v", Vis 2)] (LRet "v")
-- Right ()
-- >>> lcheck [] [("v", Vis 2)] (LRet "w")
-- Left unbound register "w"
-- >>> lcheck ["p"] [("v", Vis 2), ("t", Tmp 2)] (LIf "p" (LDrop "t" (LRet "v")) (LDrop "t" (LRet "v")))
-- Right ()
-- >>> lcheck [] [("v", Vis 2), ("t", Tmp 2)] (LIf "p" (LDrop "t" (LRet "v")) (LDrop "t" (LRet "v")))
-- Left unbound parameter "p" (a conditional may only read a parameter a previous lift bound)

checkLProgram :: LProgram -> Either LTypeError LTypedProgram
checkLProgram p = case lTerm p of
  LNew t d i0 body -> do
    lcheck [] [(lVis p, Vis (lVisDim p))] (LNew t d i0 body)
    pure LTypedProgram { ltProgram = p
                       , ltTmpName = t
                       , ltTmpDim  = d
                       , ltAlloc   = i0
                       , ltVisDim  = lVisDim p
                       , ltDepth   = liftDepth (lTerm p) }
  _ -> Left LMustAllocate

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> fmap ltDepth (checkLProgram liftedWitness)
-- Right 1
-- >>> fmap ltDepth (checkLProgram sameChannelSafe)
-- Right 1
-- >>> fmap ltDepth (checkLProgram (LProgram "x" "v" 2 (LNew "t" 2 0 (LDrop "t" (LRet "v")))))
-- Right 0

-- Running

-- | A run in progress (paper: app:meas-tree): the register names and dimensions, an
-- unnormalised state, the parameter store, and the part of the record not yet used.
data LConfig = LConfig
  { lcNames   :: [Name]
  , lcDims    :: [Int]
  , lcDropped :: [Name]
  , lcAmp     :: Vec
  , lcStore   :: [(PName, Int)]
  , lcTrace   :: Trace
  , lcUsed    :: Int          -- ^ how many outcomes this run actually lifted
  }

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitnessNoRead
-- >>> let c = runLifted tp (vbasis 3 0) [Out]
-- >>> (lcNames c, lcDims c, lcDropped c, lcStore c, lcTrace c, lcUsed c)
-- (["v1","t1"],[3,3],["t1"],[("p",0)],[],1)

lstep :: LConfig -> LTerm -> LConfig
lstep c (LRet _) = c

lstep c (LNew t d i0 e) =
  lstep c { lcNames = lcNames c ++ [t]
          , lcDims  = lcDims c ++ [d]
          , lcAmp   = tensorV (lcAmp c) (vbasis d i0) } e

lstep c (LAct (t',v') u (t,v) e) =
  lstep c { lcNames = map ren (lcNames c)
          , lcAmp   = matVec (applyGateAt (lcDims c) (gateMat u) [pos t, pos v])
                             (lcAmp c) } e
  where
    -- impossible: a checked program names only registers that are live
    pos x = maybe (error ("Drop.Theory.Lifted: no register " ++ x)) id
                  (lookup x (zip (lcNames c) [0 ..]))
    ren x | x == t = t' | x == v = v' | otherwise = x

lstep c (LDrop t e) = lstep c { lcDropped = lcDropped c ++ [t] } e

lstep c (LLift p t s e) =
  case lcTrace c of
    -- refusal: the record has fewer choices than the run has lifts
    []          -> error "Drop.Theory.Lifted: measurement record exhausted"
    (ch : rest) ->
      let -- impossible: a checked program measures a live temporary
          pos  = maybe (error "Drop.Theory.Lifted: no register") id
                       (lookup t (zip (lcNames c) [0 ..]))
          -- impossible: pos indexes lcNames, which has an entry in lcDims for each name
          d    = lcDims c !! pos
          keep = case ch of
                   In  -> s
                   Out -> [ l | l <- [0 .. d-1], l `notElem` s ]
      in lstep c { lcAmp   = projectLevels (lcDims c) pos keep (lcAmp c)
                 , lcStore = (p, case ch of In -> 1; Out -> 0) : lcStore c
                 , lcTrace = rest
                 , lcUsed  = lcUsed c + 1 } e

lstep c (LIf p e1 e0) =
  case lookup p (lcStore c) of
    Just 1  -> lstep c e1
    Just _  -> lstep c e0
    -- impossible: the typing rule of a conditional needs a parameter that an earlier lift bound
    Nothing -> error ("Drop.Theory.Lifted: parameter " ++ p ++ " not in the store")

-- One term at a time: a return changes nothing, a new adjoins a register, a drop records a name.
-- >>> lcAmp (lstep (LConfig ["v"] [2] [] [kone, kzero] [] [] 0) (LRet "v"))
-- [1,0]
-- >>> lcAmp (lstep (LConfig ["v"] [2] [] [kone, kzero] [] [] 0) (LNew "t" 2 1 (LRet "v")))
-- [0,1,0,0]
-- >>> lcDropped (lstep (LConfig ["v", "t"] [2, 2] [] [kone, kzero, kzero, kzero] [] [] 0) (LDrop "t" (LRet "v")))
-- ["t"]
-- >>> lcStore (lstep (LConfig ["v", "t"] [2, 2] [] [kone, kzero, kzero, kzero] [] [Out] 0) (LLift "p" "t" [0] (LRet "v")))
-- [("p",0)]

-- | Run a lifted program on a visible input under a measurement record.
runLifted :: LTypedProgram -> Vec -> Trace -> LConfig
runLifted tp psi tr =
  lstep LConfig { lcNames   = [lVis (ltProgram tp)]
                , lcDims    = [ltVisDim tp]
                , lcDropped = []
                , lcAmp     = psi
                , lcStore   = []
                , lcTrace   = tr
                , lcUsed    = 0 }
        (lTerm (ltProgram tp))

-- The tilted trit of the witness, lifted on the block {0,1}: record In keeps weight 8/9, Out keeps 1/9.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitnessNoRead
-- >>> let c = runLifted tp (vbasis 3 0) [In] in (lcUsed c, vnorm2 (lcAmp c))
-- (1,8/9)
-- >>> let c = runLifted tp (vbasis 3 0) [Out] in (lcUsed c, vnorm2 (lcAmp c))
-- (1,1/9)

-- | The denotation of a lifted program /at a given trace/: @H_m -> H_d (x)
-- H_m@, the dropped register first, exactly as in the measurement-free
-- case. The map depends on the trace.
coreMapAt :: LTypedProgram -> Trace -> Mat
coreMapAt tp tr = matFromCols [ column j | j <- [0 .. m - 1] ]
  where
    m = ltVisDim tp
    column j =
      let c      = runLifted tp (vbasis m j) tr
          -- impossible: lcDropped lists names of registers of the run
          idxOf x = maybe (error "Drop.Theory.Lifted.coreMapAt: no register") id
                          (lookup x (zip (lcNames c) [0 ..]))
          dropIx = map idxOf (lcDropped c)
          order  = dropIx ++ [ i | i <- [0 .. length (lcDims c) - 1]
                                 , i `notElem` dropIx ]
      in matVec (reorder (lcDims c) order) (lcAmp c)

-- The matrix of the program on a record: the dropped temporary first, then the visible register.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitnessNoRead
-- >>> let k = coreMapAt tp [In] in (matRows k, matCols k)
-- (9,3)
-- >>> let k = coreMapAt tp [In] in map (vnorm2 . matColumn k) [0, 1, 2]
-- [8/9,8/9,8/9]
-- >>> let k = coreMapAt tp [Out] in map (vnorm2 . matColumn k) [0, 1, 2]
-- [1/9,1/9,1/9]

-- Flattening a run into a statement list

-- | A statement of the straight line a particular run executes.
--
-- Terms nest and branch; a /run/ does not.  Fixing a measurement record resolves
-- every conditional, so along one trace the program is a list.  That is the
-- representation the residual pass wants, because the pass has to cut the run
-- into the segments before and after each lift.
data LStmt
  = SAct (Name, Name) Gate (Name, Name)
  | SLift PName Name [Int]
  | SDrop Name

-- The statements of a run have three kinds.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> case flattenAlong liftedWitnessNoRead [In] of { Just (_, _, _, ss, _) -> map (\s -> case s of { SAct {} -> "act"; SLift {} -> "lift"; SDrop {} -> "drop" }) ss; Nothing -> [] }
-- ["act","lift","drop"]

-- | Flatten a lifted program along a measurement record: the temporary's
-- name, dimension and allocation index, the statements the run executes,
-- and the name returned at the end.
--
-- Returns 'Nothing' when the trace is too short: a run's lift count is
-- not a function of the text.
flattenAlong :: LProgram -> Trace -> Maybe (Name, Int, Int, [LStmt], Name)
flattenAlong p tr0 = case lTerm p of
  LNew t d i0 body -> do
    (ss, ret) <- go body tr0 []
    pure (t, d, i0, ss, ret)
  _ -> Nothing
  where
    go :: LTerm -> Trace -> [(PName, Int)] -> Maybe ([LStmt], Name)
    go (LRet v)          _  _  = Just ([], v)
    go (LNew _ _ _ _)    _  _  = Nothing        -- one temporary scope
    go (LAct o g i e)    tr st = do (ss, r) <- go e tr st
                                    pure (SAct o g i : ss, r)
    go (LDrop t e)       tr st = do (ss, r) <- go e tr st
                                    pure (SDrop t : ss, r)
    go (LLift q x b e)   tr st = case tr of
      []        -> Nothing
      (c : tr') -> do (ss, r) <- go e tr' ((q, case c of In -> 1; Out -> 0) : st)
                      pure (SLift q x b : ss, r)
    go (LIf q e1 e0)     tr st = case lookup q st of
      Just 1  -> go e1 tr st
      Just _  -> go e0 tr st
      Nothing -> Nothing

-- Along a record every conditional is settled, so the run is a list.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> fmap (\(t, d, i0, ss, r) -> (t, d, i0, length ss, r)) (flattenAlong liftedWitness [In])
-- Just ("t",3,0,4,"v2")
-- >>> fmap (\(t, d, i0, ss, r) -> (t, d, i0, length ss, r)) (flattenAlong liftedWitness [Out])
-- Just ("t",3,0,4,"v2")
-- >>> fmap (\(_, _, _, ss, _) -> length ss) (flattenAlong sameChannelSafe [In])
-- Just 4
-- >>> fmap (\(_, _, _, ss, _) -> length ss) (flattenAlong liftedWitness [])
-- Nothing

-- | Execute a statement list on a configuration. The residual pass uses
-- this to run a /segment/ of a program starting from a state it chose: the
-- check never re-runs the program, it runs the continuation from the
-- transferred state.
--
-- A segment chosen by a pass need not have met the checker, so a statement
-- that names a register the run has already dropped is refused by name: a
-- drop changes nothing in the amplitude, and the run would go through.
runStmts :: LConfig -> [LStmt] -> LConfig
runStmts c [] = c
runStmts c (s : _)
  | (x : _) <- [ x | x <- stmtNames s, x `elem` lcDropped c ] =
      -- refusal: a statement names a register the run has already dropped
      error ("Drop.Theory.Lifted.runStmts: register " ++ x ++ " has been dropped")
  where
    stmtNames (SDrop t)          = [t]
    stmtNames (SAct _ _ (t, v))  = [t, v]
    stmtNames (SLift _ x _)      = [x]
runStmts c (s : ss) = case s of
  SDrop t -> runStmts c { lcDropped = lcDropped c ++ [t] } ss
  SAct (t',v') u (t,v) ->
    runStmts c { lcNames = map (ren t v t' v') (lcNames c)
               , lcAmp   = matVec (applyGateAt (lcDims c) (gateMat u)
                                     [pos c t, pos c v]) (lcAmp c) } ss
  SLift q x b -> case lcTrace c of
    -- refusal: the record has fewer choices than the statements have lifts
    []        -> error "Drop.Theory.Lifted.runStmts: measurement record exhausted"
    (ch : tl) ->
      let i    = pos c x
          -- impossible: i indexes lcNames, which has an entry in lcDims for each name
          d    = lcDims c !! i
          keep = case ch of
                   In  -> b
                   Out -> [ l | l <- [0 .. d-1], l `notElem` b ]
      in runStmts c { lcAmp   = projectLevels (lcDims c) i keep (lcAmp c)
                    , lcStore = (q, case ch of In -> 1; Out -> 0) : lcStore c
                    , lcTrace = tl
                    , lcUsed  = lcUsed c + 1 } ss
  where
    -- refusal: a segment chosen by a pass may name a register the run does not have
    pos cf x = maybe (error ("Drop.Theory.Lifted.runStmts: no register " ++ x)) id
                     (lookup x (zip (lcNames cf) [0 ..]))
    ren t v t' v' x | x == t = t' | x == v = v' | otherwise = x

-- Run the statements of a record from a configuration of our own.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Just (_, _, _, ss, _) = flattenAlong liftedWitnessNoRead [In]
-- >>> let c = runStmts (LConfig ["v", "t"] [3, 3] [] (tensorV (vbasis 3 0) (vbasis 3 0)) [] [In] 0) ss
-- >>> (lcNames c, lcDropped c, lcUsed c, length (lcAmp c))
-- (["v1","t1"],["t1"],1,9)
-- >>> runStmts (LConfig ["v"] [2] [] [kone, kzero] [] [] 0) []  `seq` ()
-- ()

-- | The register names live after a statement list, given the names live
-- before.  Gates rename registers in place and never move them, so the tensor
-- /positions/ are stable while the /names/ change; a pass that wants to restart
-- a segment from a state of its own choosing needs the names that segment
-- expects, and this computes them without running anything.
namesAfter :: [Name] -> [LStmt] -> [Name]
namesAfter = foldl step
  where
    step ns (SAct (t',v') _ (t,v)) =
      map (\x -> if x == t then t' else if x == v then v' else x) ns
    step ns _ = ns

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Just (_, _, _, ss, _) = flattenAlong liftedWitness [In]
-- >>> namesAfter ["v", "t"] ss
-- ["v2","t2"]
-- >>> namesAfter ["v", "t"] []
-- ["v","t"]

-- Verdicts

-- | Does the verdict allow the drop?  'Unreachable' does: there is no state for the drop to be about.
admissible :: Verdict -> Bool
admissible (Safe _)     = True
admissible Unreachable  = True
admissible (Unsafe _ _) = False

-- A safe or unreachable drop is allowed, an unsafe one is not.
-- >>> admissible Unreachable
-- True
-- >>> admissible (Unsafe Nothing 2)
-- False
-- >>> admissible (Safe (Certificate [kone] [[kone]]))
-- True

-- | The verdict at one trace, with the branch's exact weight attached.
data TraceVerdict = TraceVerdict
  { tvTrace   :: Trace
  , tvWeights :: [K]          -- ^ the branch's exact probability at each visible basis input
  , tvVerdict :: Verdict
  , tvParked  :: Maybe Vec    -- ^ the line the drop leaves the temporary constant on, when the drop is safe
  }

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram sameChannelSafe
-- >>> let tv = verdictAt tp [In]
-- >>> (tvTrace tv, tvWeights tv, tvParked tv)
-- ([In],[1/2,1/2],Just [1,0])

-- | The branch weight, when it is the same at every visible basis input:
-- true whenever the lift acts on the temporary alone.
tvWeight :: TraceVerdict -> Maybe K
tvWeight tv = case nub (tvWeights tv) of
  [w] -> Just w
  _   -> Nothing

-- The weight of a record, when it is the same at every visible input.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> map (tvWeight . verdictAt tp) (allTraces 1)
-- [Just 8/9,Just 1/9]
-- >>> tvWeight (TraceVerdict [In] [kone, kzero] Unreachable Nothing)
-- Nothing

instance Show TraceVerdict where
  show tv = show (tvTrace tv) ++ "  weight "
            ++ maybe (show (tvWeights tv)) show (tvWeight tv)
            ++ "  " ++ show (tvVerdict tv)

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> mapM_ print (lines (show (verdictAt tp [In])))
-- "[In]  weight 8/9  UNSAFE (slice rank 2, so the temporary carries 1 dimension(s) of information about the input)"
-- "  witness minor at rows (0,1) columns (0,2): 4/9 /= 0"
-- >>> mapM_ print (lines (show (verdictAt tp [Out])))
-- "[Out]  weight 1/9  SAFE, parked on the line [0,0,1]"

-- | The drop verdict on one trace.
--
-- A branch of zero weight carries no state, so the drop there is about nothing and
-- imposes no condition: its verdict is 'Unreachable', not 'Unsafe'.
verdictAt :: LTypedProgram -> Trace -> TraceVerdict
verdictAt tp tr = TraceVerdict
  { tvTrace   = tr
  , tvWeights = w
  , tvVerdict = v
  , tvParked  = pk }
  where
    d  = ltTmpDim tp
    m  = ltVisDim tp
    k  = coreMapAt tp tr
    w  = [ vnorm2 (matColumn k j) | j <- [0 .. m-1] ]
    v  = verdictOfCoreMap d m k
    pk = canonicalLine . certParked <$> certificateOfCoreMap d m k

-- The tilted witness: the record In (weight 8/9) is unsafe, the record Out (weight 1/9) safe.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram liftedWitness
-- >>> map (admissible . tvVerdict . verdictAt tp) (allTraces 1)
-- [False,True]
-- >>> map (tvParked . verdictAt tp) (allTraces 1)
-- [Nothing,Just [0,0,1]]
-- >>> map (tvWeights . verdictAt tp) (allTraces 1)
-- [[8/9,8/9,8/9],[1/9,1/9,1/9]]

-- | The verdict profile of a program: its verdict at every trace, in run order.
--
-- One yes or no for the whole program can match every record of nonzero weight
-- only when the profile is constant ('constantProfile').
verdictProfile :: LTypedProgram -> [TraceVerdict]
verdictProfile tp = [ verdictAt tp tr | tr <- allTraces (ltDepth tp) ]

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> let Right tp = checkLProgram qubitSplitAfterJointGate
-- >>> length (verdictProfile tp)
-- 2
-- >>> map (\v -> case tvVerdict v of { Safe _ -> "safe"; Unsafe _ _ -> "unsafe"; Unreachable -> "unreachable" }) (verdictProfile tp)
-- ["safe","unsafe"]

-- | Is the verdict the same at every trace of nonzero weight?
constantProfile :: LTypedProgram -> Bool
constantProfile tp =
  case [ admissible (tvVerdict tv) | tv <- verdictProfile tp
       , not (all kIsZero (tvWeights tv)) ] of
    []       -> True
    (b : bs) -> all (== b) bs

-- The witness changes its ruling with the record; with the read deleted it does not.
-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> fmap constantProfile (checkLProgram liftedWitness)
-- Right False
-- >>> fmap constantProfile (checkLProgram liftedWitnessNoRead)
-- Right True
-- >>> fmap constantProfile (checkLProgram sameChannelSafe)
-- Right True

-- | Some reachable records are safe and others unsafe.
oracleSplit :: LTypedProgram -> Bool
oracleSplit = not . constantProfile

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> fmap oracleSplit (checkLProgram liftedWitness)
-- Right True
-- >>> fmap oracleSplit (checkLProgram qubitSplitAfterJointGate)
-- Right True
-- >>> fmap oracleSplit (checkLProgram classicalCoreNaiveEncoding)
-- Right False

-- | Is the profile mixed?  Then no single accept or reject is right at every record
-- of nonzero weight (paper: cor:nostatic).
everySoundStaticDisciplineRejects :: LTypedProgram -> Bool
everySoundStaticDisciplineRejects = oracleSplit

-- >>> :m + Drop.Theory.Lifted.Programs
-- >>> fmap everySoundStaticDisciplineRejects (checkLProgram liftedWitness)
-- Right True
-- >>> fmap everySoundStaticDisciplineRejects (checkLProgram sameChannelUnsafe)
-- Right False
