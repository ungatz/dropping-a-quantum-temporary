-- |
-- Module      : DQT.Lifted
--
-- A lift hands the classical bit from a run-time measurement back to the
-- host, so one program text determines a family of circuits; the semantics
-- stays unnormalised, so squared norm is exact probability.
module DQT.Lifted
  ( -- * Measurement records
    Choice(..)
  , Trace
  , allTraces
    -- * Syntax
  , PName
  , LTerm(..)
  , LProgram(..)
  , liftDepth
  , liftFree
  , embed
    -- * Typing
  , LTypeError(..)
  , checkLProgram
  , LTypedProgram(..)
    -- * Running
  , LConfig(..)
  , runLifted
  , coreMapAt
    -- * Flattening a run into statements
  , LStmt(..)
  , flattenAlong
  , runStmts
  , namesAfter
    -- * Verdicts
  , TraceVerdict(..)
  , tvWeight
  , verdictAt
  , verdictProfile
  , constantProfile
  , oracleSplit
  , everySoundStaticDisciplineRejects
  ) where

import Data.List (nub)

import DQT.Criterion (Certificate(..), Verdict(..), certificateOfCoreMap, verdictOfCoreMap)
import DQT.Algebra.Linear
import DQT.Algebra.Scalar
import DQT.Criterion.Split (canonicalLine)
import DQT.Calculus.Syntax
import DQT.Calculus.Typing (Ctx, ctxExtend, ctxLookup, ctxNames, ctxRemove, ctxRename)

-- Measurement records

-- | Which branch of a lift survives: the one inside the measured block, or the
-- one outside it.
data Choice = In | Out deriving (Eq, Show)

-- | A measurement record: one choice per lift, in run order, supplied by
-- the run, never by the text. A static analysis is a function that does
-- not receive one.
type Trace = [Choice]

-- | All @2^d@ traces at depth @d@, in a fixed order.
allTraces :: Int -> [Trace]
allTraces 0 = [[]]
allTraces n = [ c : t | c <- [In, Out], t <- allTraces (n-1) ]

-- Syntax

type PName = String

-- | The lifted calculus: the affine core plus two constructs.
data LTerm
  = LRet  Name
  | LNew  Name Int Int LTerm
  | LAct  (Name, Name) Gate (Name, Name) LTerm
  | LLift PName Name [Int] LTerm
      -- ^ @let p = lift (meas t in S) in e@: the one rule connecting the two
      -- sorts, where a state-level event creates a parameter-level binding.
  | LIf   PName LTerm LTerm
      -- ^ @if p then e1 else e0@, branching on a lifted parameter.
  | LDrop Name LTerm

data LProgram = LProgram
  { lLabel  :: String
  , lVis    :: Name
  , lVisDim :: Int
  , lTerm   :: LTerm
  }

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

-- | Lift-freeness is exactly depth zero, and on lift-free terms the verdict
-- does not depend on the trace.
liftFree :: LTerm -> Bool
liftFree e = liftDepth e == 0

-- | The measurement-free calculus sits inside the lifted one.
embed :: Term -> LTerm
embed (Ret v)         = LRet v
embed (Pair _ _)      = error "DQT.Lifted.embed: pairs are outside the lifted fragment"
embed (New t d i0 e)  = LNew t d i0 (embed e)
embed (Act o g i e)   = LAct o g i (embed e)
embed (Drop t e)      = LDrop t (embed e)

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
  deriving (Eq)

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

data LTypedProgram = LTypedProgram
  { ltProgram :: LProgram
  , ltTmpName :: Name
  , ltTmpDim  :: Int
  , ltAlloc   :: Int
  , ltVisDim  :: Int
  , ltDepth   :: Int
  }

-- | The two-sorted judgement @Delta ; Gamma |- e@.
--
-- The parameter context @Delta@ is a list of names: duplicable and
-- weakenable, so a parameter need not be used and may be read twice. The
-- state context @Gamma@ is affine, exactly as before. The @LLift@ rule is
-- the only place a state-level event reaches across.
lcheck :: [PName] -> Ctx -> LTerm -> Either LTypeError ()
lcheck _ g (LRet v) =
  case ctxLookup v g of
    Nothing -> Left (LUnbound v)
    Just _ | length g /= 1 -> Left (LLeftover (filter (/= v) (ctxNames g)))
           | otherwise     -> Right ()

lcheck ps g (LNew t d _ e)
  | t `elem` ctxNames g = Left (LUnbound t)
  | otherwise           = lcheck ps (ctxExtend t (Tmp d) g) e

lcheck ps g (LAct (t',v') _ (t,v) e) =
  case (ctxLookup t g, ctxLookup v g) of
    (Just (Tmp d), Just (Vis m)) ->
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

-- Running

-- | The machine configuration of the appendix: names and dimensions, an
-- unnormalised state, a parameter store, and the remaining measurement record.
data LConfig = LConfig
  { lcNames   :: [Name]
  , lcDims    :: [Int]
  , lcDropped :: [Name]
  , lcAmp     :: Vec
  , lcStore   :: [(PName, Int)]
  , lcTrace   :: Trace
  , lcUsed    :: Int          -- ^ how many outcomes this run actually lifted
  }

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
    pos x = maybe (error ("DQT.Lifted: no register " ++ x)) id
                  (lookup x (zip (lcNames c) [0 ..]))
    ren x | x == t = t' | x == v = v' | otherwise = x

lstep c (LDrop t e) = lstep c { lcDropped = lcDropped c ++ [t] } e

lstep c (LLift p t s e) =
  case lcTrace c of
    []          -> error "DQT.Lifted: measurement record exhausted"
    (ch : rest) ->
      let pos  = maybe (error "DQT.Lifted: no register") id
                       (lookup t (zip (lcNames c) [0 ..]))
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
    Nothing -> error ("DQT.Lifted: parameter " ++ p ++ " not in the store")

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

-- | The denotation of a lifted program /at a given trace/: @H_m -> H_d (x)
-- H_m@, the dropped register first, exactly as in the measurement-free
-- case. The map depends on the trace.
coreMapAt :: LTypedProgram -> Trace -> Mat
coreMapAt tp tr = matFromCols [ column j | j <- [0 .. m - 1] ]
  where
    m = ltVisDim tp
    column j =
      let c      = runLifted tp (vbasis m j) tr
          idxOf x = maybe (error "DQT.Lifted.coreMapAt: no register") id
                          (lookup x (zip (lcNames c) [0 ..]))
          dropIx = map idxOf (lcDropped c)
          order  = dropIx ++ [ i | i <- [0 .. length (lcDims c) - 1]
                                 , i `notElem` dropIx ]
      in matVec (reorder (lcDims c) order) (lcAmp c)

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

-- | Execute a statement list on a configuration. The residual pass uses
-- this to run a /segment/ of a program starting from a state it chose: the
-- check never re-runs the program, it runs the continuation from the
-- transferred state.
runStmts :: LConfig -> [LStmt] -> LConfig
runStmts c [] = c
runStmts c (s : ss) = case s of
  SDrop t -> runStmts c { lcDropped = lcDropped c ++ [t] } ss
  SAct (t',v') u (t,v) ->
    runStmts c { lcNames = map (ren t v t' v') (lcNames c)
               , lcAmp   = matVec (applyGateAt (lcDims c) (gateMat u)
                                     [pos c t, pos c v]) (lcAmp c) } ss
  SLift q x b -> case lcTrace c of
    []        -> error "DQT.Lifted.runStmts: measurement record exhausted"
    (ch : tl) ->
      let i    = pos c x
          d    = lcDims c !! i
          keep = case ch of
                   In  -> b
                   Out -> [ l | l <- [0 .. d-1], l `notElem` b ]
      in runStmts c { lcAmp   = projectLevels (lcDims c) i keep (lcAmp c)
                    , lcStore = (q, case ch of In -> 1; Out -> 0) : lcStore c
                    , lcTrace = tl
                    , lcUsed  = lcUsed c + 1 } ss
  where
    pos cf x = maybe (error ("DQT.Lifted.runStmts: no register " ++ x)) id
                     (lookup x (zip (lcNames cf) [0 ..]))
    ren t v t' v' x | x == t = t' | x == v = v' | otherwise = x

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

-- Verdicts

-- | The verdict at one trace, with the branch's exact weight attached.
data TraceVerdict = TraceVerdict
  { tvTrace   :: Trace
  , tvWeights :: [K]          -- ^ the branch's exact probability at each visible basis input
  , tvVerdict :: Verdict
  , tvParked  :: Maybe Vec    -- ^ the line the drop leaves the temporary constant on, when the drop is safe
  }

-- | The branch weight, when it is the same at every visible basis input:
-- true whenever the lift acts on the temporary alone.
tvWeight :: TraceVerdict -> Maybe K
tvWeight tv = case nub (tvWeights tv) of
  [w] -> Just w
  _   -> Nothing

instance Show TraceVerdict where
  show tv = show (tvTrace tv) ++ "  weight "
            ++ maybe (show (tvWeights tv)) show (tvWeight tv)
            ++ "  " ++ show (tvVerdict tv)

-- | The drop verdict on one trace.
--
-- One case is treated differently from the measurement-free code,
-- deliberately: a branch of zero weight carries no state, so the drop
-- there is about nothing and imposes no condition. The honest verdict is
-- 'Vacuous', not "unsafe".
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

-- | The verdict profile of a program: its verdict at every trace.
--
-- A sound and complete static analysis for a class of commands exists if and
-- only if the verdict is constant on each command's profile.  Both of the
-- impossibility results are instances of that statement, and this function
-- computes the object it is about.
verdictProfile :: LTypedProgram -> [TraceVerdict]
verdictProfile tp = [ verdictAt tp tr | tr <- allTraces (ltDepth tp) ]

-- | Is the verdict the same at every trace of nonzero weight?
constantProfile :: LTypedProgram -> Bool
constantProfile tp =
  case [ admissible (tvVerdict tv) | tv <- verdictProfile tp
       , not (all kIsZero (tvWeights tv)) ] of
    []       -> True
    (b : bs) -> all (== b) bs
  where
    admissible (Safe _)    = True
    admissible Vacuous     = True
    admissible (Unsafe _ _) = False

-- | The exact boundary.  A command is /outcome-dependent/ when some trace makes its
-- drop safe and some other trace does not; a command defeats every sound
-- static analysis if and only if it is outcome-dependent.
oracleSplit :: LTypedProgram -> Bool
oracleSplit = not . constantProfile

-- | The corollary a compiler writer cares about: every sound static
-- analysis must reject this command, and therefore loses its safe runs.
--
-- No quantification over disciplines in the code: the interface lemma
-- turns "for every predicate on text" into "the profile is nonconstant",
-- a finite check.
everySoundStaticDisciplineRejects :: LTypedProgram -> Bool
everySoundStaticDisciplineRejects = oracleSplit
