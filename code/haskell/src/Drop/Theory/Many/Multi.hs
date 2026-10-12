-- |
-- Module      : Drop.Theory.Many.Multi
--
-- How a theory about one temporary applies to programs with many.  'bundle'
-- reduces many temporaries to one of dimension @D = d_1 * ... * d_n@; the
-- joint verdict is strictly weaker than per-temporary ('bellPair').
module Drop.Theory.Many.Multi
  ( -- * The surface language
    MStmt(..)
  , MProgram(..)
  , mTemporaries
    -- * Composition
  , BundleError(..)
  , scopeCheck
  , bundle
  , bundlePreservesDenotation
    -- * Running the surface language directly
  , runMulti
    -- * Joint versus per-temporary
  , jointSafe
  , wireSafe
  , everyWireSafe
    -- * Examples
  , bellPair
  , wideVisible
  , nestedThree
  ) where

import Drop.Theory.Criterion (safeByRank)
import Drop.Theory.Program.Elaborate (coreMap)
import Drop.Theory.Program.Gates
import Drop.Theory.Algebra.Linear
import Drop.Theory.Criterion.Split (Split(..), factorSplit, lineEqual)
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing

-- The surface language

-- | A statement of the multi-temporary surface language.  Nesting flattens into
-- a statement list: @let t = new i0 in (body)@ becomes @MNew t d i0@ followed by
-- the body's statements, and scoping is recovered from where the matching
-- @MDrop@ sits.
data MStmt
  = MNew Name Int Int        -- ^ @let t = new i0@: name, dimension, allocation index
  | MApply String Mat [Name] -- ^ a gate, named, applied to the listed registers in order
  | MDrop Name

-- | A surface program: one visible register (of any dimension), a statement
-- list, and the promise that every temporary it allocates it also drops.
data MProgram = MProgram
  { mLabel   :: String
  , mVis     :: Name
  , mVisDim  :: Int
  , mStmts   :: [MStmt]
  }

-- | The temporaries a surface program allocates, with their dimensions and
-- allocation indices, in allocation order.
mTemporaries :: MProgram -> [(Name, Int, Int)]
mTemporaries p = [ (t,d,i0) | MNew t d i0 <- mStmts p ]

-- Running the surface language

-- | Run a surface program on a visible input, returning the final amplitude
-- vector, temporaries in allocation order then the visible register. Drops
-- are the identity: they only remove a name.
runMulti :: MProgram -> Vec -> Vec
runMulti p v0 = either (error . ("runMulti: " ++) . show) (const (go (names0, dims0, psi0) (mStmts p)))
                       (scopeCheck p)
  where
    names0 = [mVis p]
    dims0  = [mVisDim p]
    psi0   = v0
    go (_, _, psi) [] = reorderToBundleFirst psi
    go st@(ns, ds, psi) (s : ss) = case s of
      MNew t d i0 -> go (ns ++ [t], ds ++ [d], tensorV psi (vbasis d i0)) ss
      MDrop _     -> go st ss
      MApply _ g xs ->
        go (ns, ds, matVec (applyGateAt ds g (map pos xs)) psi) ss
        where pos x = maybe (error ("Drop.Theory.Many.Multi: no register " ++ x)) id
                            (lookup x (zip ns [0 ..]))
    -- the visible register was allocated first; the composite temporary convention puts the
    -- temporaries first, so one permutation at the end
    reorderToBundleFirst psi =
      let ds  = mVisDim p : [ d | (_,d,_) <- mTemporaries p ]
          n   = length ds
          ord = [1 .. n-1] ++ [0]
      in matVec (reorder ds ord) psi

-- Composition

data BundleError
  = NotAllDropped [Name]
  | DroppedButNotAllocated [Name]
  | GateOnUnknownRegister String Name
  | GateOnDeadRegister String Name
    -- ^ a gate names a temporary that has already been dropped.
  | GateBeforeAllocation String Name
    -- ^ a gate names a temporary before its @new@.
  | DroppedTwice Name
    -- ^ the same temporary is dropped twice.
  | AllocatedTwice Name
    -- ^ the same name is allocated twice without an intervening drop.
  | ReallocatedAfterDrop Name
    -- ^ the name is allocated again after being dropped; the calculus
    -- allows this, but bundling gives each allocation its own tensor
    -- factor, so rename and bundle again.
  | BadAllocation Name Int Int
    -- ^ @new@ with a dimension below 1 or an index outside @[0..d-1]@:
    -- the New rule's premises ('Drop.Theory.Program.Typing').
  | RegisterTwiceInGate String Name
    -- ^ a gate names one register twice.
  | GateWrongShape String [Name] Int
    -- ^ a gate whose matrix is not square of side the product of its
    -- registers' dimensions (the side is given).
  | GateNotUnitaryM String
    -- ^ a gate whose matrix is not unitary.
  deriving (Eq)

instance Show BundleError where
  show (NotAllDropped ts) =
    "these temporaries are never dropped, so the program does not have the "
    ++ "visible result type: " ++ show ts
  show (DroppedButNotAllocated ts) = "dropped without being allocated: " ++ show ts
  show (GateOnUnknownRegister g x) =
    "gate " ++ g ++ " names the register " ++ show x ++ ", which is not in scope"
  show (GateOnDeadRegister g x) =
    "gate " ++ g ++ " names the temporary " ++ show x ++ ", which has already "
    ++ "been dropped, and a dropped name is untouchable"
  show (GateBeforeAllocation g x) =
    "gate " ++ g ++ " names the temporary " ++ show x ++ " before it is allocated"
  show (DroppedTwice t) = "the temporary " ++ show t ++ " is dropped twice"
  show (AllocatedTwice t) =
    "the name " ++ show t ++ " is allocated twice without an intervening drop"
  show (BadAllocation t d i0) =
    "new " ++ show t ++ " has dimension " ++ show d ++ " and allocation index "
    ++ show i0 ++ "; a register has at least one level and the index is one of them"
  show (RegisterTwiceInGate g x) =
    "gate " ++ g ++ " names the register " ++ show x ++ " twice"
  show (GateWrongShape g xs n) =
    "gate " ++ g ++ " on " ++ show xs ++ " is not a square matrix of side " ++ show n
  show (GateNotUnitaryM g) = "gate " ++ g ++ " is not unitary"
  show (ReallocatedAfterDrop t) =
    "the name " ++ show t ++ " is allocated again after being dropped; "
    ++ "bundling gives each allocation its own factor, so rename the second"
    ++ " one (alpha-conversion) and bundle again"

-- | Check the statement list respects the affine discipline: a gate names a
-- temporary only between its @new@ and @drop@, no name is allocated or
-- dropped twice, and the visible register stays in scope. This is the
-- hypothesis 'bundle' needs to move every drop to the end.
--
-- It also checks the premises the core checker states for one temporary
-- (Drop.Theory.Program.Typing): an allocation index among the register's
-- levels, and a gate that is a unitary of the right size on distinct
-- registers. Bundling builds a well-shaped core gate out of any matrix it
-- is given, so after 'bundle' the core checker can no longer see these.
scopeCheck :: MProgram -> Either BundleError ()
scopeCheck p = go [] [] (mStmts p)
  where
    go _ _ [] = Right ()
    go live dead (MNew t d i0 : rest)
      | t `elem` map fst live = Left (AllocatedTwice t)
      | t `elem` dead = Left (ReallocatedAfterDrop t)
      | d < 1 || i0 < 0 || i0 >= d = Left (BadAllocation t d i0)
      | otherwise     = go ((t, d) : live) dead rest
    go live dead (MDrop t : rest)
      | t `elem` dead   = Left (DroppedTwice t)
      | t `notElem` map fst live = Left (DroppedButNotAllocated [t])
      | otherwise       = go (filter ((/= t) . fst) live) (t : dead) rest
    go live dead (MApply nm g xs : rest) =
      case [ x | x <- xs, x /= mVis p, x `notElem` map fst live ] of
        (x : _) | x `elem` dead -> Left (GateOnDeadRegister nm x)
                | otherwise     -> Left (GateBeforeAllocation nm x)
        []
          | (x : _) <- [ x | (i, x) <- zip [0 :: Int ..] xs, x `elem` take i xs ] ->
              Left (RegisterTwiceInGate nm x)
          | length g /= n || any ((/= n) . length) g -> Left (GateWrongShape nm xs n)
          | not (matIsUnitary g) -> Left (GateNotUnitaryM nm)
          | otherwise -> go live dead rest
          where
            n = product [ if x == mVis p then mVisDim p else maybe 0 id (lookup x live) | x <- xs ]

-- | The composition elaboration: many temporaries in, one temporary out.
-- Composite dimension @D = product d_i@, allocated at the mixed-radix index
-- of the individual allocations; a gate on any subset lifts to the joint
-- register @H_D (x) H_m@ (temporaries first, then the visible register, so
-- no reordering is needed); the @n@ drops become one drop at the end.
bundle :: MProgram -> Either BundleError Program
bundle p = do
  scopeCheck p
  let tmps    = mTemporaries p
      tnames  = [ t | (t,_,_) <- tmps ]
      dims    = [ d | (_,d,_) <- tmps ]
      allocs  = [ i | (_,_,i) <- tmps ]
      bigD    = dimProduct dims
      bigI0   = levelsToIndex dims allocs
      m       = mVisDim p
      dropped = [ t | MDrop t <- mStmts p ]
  mapM_ (\t -> if t `elem` tnames then Right () else Left (DroppedButNotAllocated [t]))
        dropped
  mapM_ (\t -> if t `elem` dropped then Right () else Left (NotAllDropped [t]))
        tnames
  gs <- mapM (liftGate (mVis p) tnames dims m) [ (nm,g,xs) | MApply nm g xs <- mStmts p ]
  pure Program
    { progLabel  = mLabel p ++ "  [bundled: " ++ show (length tmps)
                   ++ " temporaries of dims " ++ show dims ++ " into tmp[" ++ show bigD ++ "]]"
    , progVis    = mVis p
    , progVisDim = m
    , progTerm   = New "T" bigD bigI0 (chain (0 :: Int) "T" (mVis p) gs)
    }
  where
    chain _ t v []       = Drop t (Ret v)
    chain n t v (g : gs) =
      let t' = "T" ++ show (n+1)
          v' = "u"  ++ show (n+1)
      in Act (t', v') g (t, v) (chain (n+1) t' v' gs)

-- | Lift a gate on named registers to a gate on @tmp[D] (x) vis[m]@: one
-- call to 'applyGateAt' on dims @[d_1, ..., d_n, m]@, since the bundle order
-- (temporaries first, then visible) already makes
-- @H_{d_1} (x) ... (x) H_{d_n} (x) H_m@ equal @H_D (x) H_m@.
liftGate :: Name -> [Name] -> [Int] -> Int -> (String, Mat, [Name])
         -> Either BundleError Gate
liftGate visName tnames dims m (nm, g, xs) = do
  ps <- mapM position xs
  pure (joint nm (dimProduct dims) m (applyGateAt (dims ++ [m]) g ps))
  where
    position x
      | x == visName = Right (length tnames)
      | otherwise    = case lookup x (zip tnames [0 ..]) of
          Just i  -> Right i
          Nothing -> Left (GateOnUnknownRegister nm x)

-- | Does composition preserve the meaning?  Compare the composite core program's map
-- with the surface program's own semantics, on every visible basis input.
bundlePreservesDenotation :: MProgram -> Bool
bundlePreservesDenotation p =
  case bundle p of
    Left _  -> False
    Right b -> case checkProgram b of
      Left _   -> False
      Right tp -> and [ matVec (coreMap tp) (vbasis m j) == runMulti p (vbasis m j)
                      | j <- [0 .. m-1] ]
  where m = mVisDim p

-- Joint versus per-temporary

-- | The verdict the core can state: is the whole bundle left on one fixed ray?
jointSafe :: MProgram -> Either BundleError Bool
jointSafe p = do
  b <- bundle p
  case checkProgram b of
    Left e   -> error ("Drop.Theory.Many.Multi.jointSafe: bundled program ill-typed: " ++ show e)
    Right tp -> pure (safeByRank tp)

-- | The verdict for one named temporary: does the denotation factor across
-- the cut /this temporary/ against /everything else/, with the same factor
-- at every input?
wireSafe :: MProgram -> Name -> Either BundleError Bool
wireSafe p t = do
  b <- bundle p
  case checkProgram b of
    Left e   -> error ("Drop.Theory.Many.Multi.wireSafe: " ++ show e)
    Right tp ->
      let tmps  = mTemporaries p
          dims  = [ d | (_,d,_) <- tmps ] ++ [mVisDim p]
          pos   = maybe (error "Drop.Theory.Many.Multi.wireSafe: no such wire") id
                        (lookup t (zip [ n | (n,_,_) <- tmps ] [0 ..]))
          m     = mVisDim p
          cols  = [ matVec (coreMap tp) (vbasis m j) | j <- [0 .. m-1] ]
                  ++ [ matVec (coreMap tp) (vAllOnes m) ]
          -- The temporary is "fixed" when, at every visible input, the state
          -- factors across the cut {this temporary} | {everything else}, and
          -- the factor is the same ray every time: a temporary can factor at
          -- each input and still swing ray to ray, the phase-kickback failure.
          splits = map (factorSplit dims [pos]) cols
      in pure (case sequence splits of
                 Nothing -> False
                 Just ss -> allSameLine [ splitLeft s' | s' <- ss ])
  where
    allSameLine []       = True
    allSameLine (x : xs) = all (lineEqual x) xs

everyWireSafe :: MProgram -> Either BundleError Bool
everyWireSafe p = do
  rs <- mapM (wireSafe p) [ t | (t,_,_) <- mTemporaries p ]
  pure (and rs)

-- Examples

-- | Two temporaries prepared in a Bell state and never touched again.
--
-- Joint verdict: safe, the pair sits on the fixed ray
-- @(|00> + |11>)\/sqrt2@ independent of the visible input. Per-temporary
-- verdict: negative on both, since neither qubit is on a ray of its own:
-- conjoining per-temporary verdicts is sound but loses here.
bellPair :: MProgram
bellPair = MProgram
  { mLabel  = "Bell pair of temporaries, visible register untouched"
  , mVis    = "v"
  , mVisDim = 2
  , mStmts  =
      [ MNew "a" 2 0
      , MNew "b" 2 0
      , MApply "H" mH ["a"]
      , MApply "CX" mCX ["a","b"]
      , MDrop "a"
      , MDrop "b" ]
  }

-- | Three visible qubits, one temporary: @vis[8]@.  Deutsch--Jozsa-flavoured, to
-- show that the width of the visible register is not a parameter the theory
-- notices.
wideVisible :: MProgram
wideVisible = MProgram
  { mLabel  = "one temporary, three visible qubits (vis[8])"
  , mVis    = "v"
  , mVisDim = 8
  , mStmts  =
      [ MNew "t" 2 0
      , MApply "X" mX ["t"]
      , MApply "H" mH ["t"]
      , MApply "ctrlLow" ctrlLowBit ["t","v"]
      , MApply "ctrlLow" ctrlLowBit ["t","v"]
      , MDrop "t" ]
  }

-- | On @tmp[2] (x) vis[8]@: flip the low bit of the three-qubit visible
-- register when the temporary is @|1>@.
ctrlLowBit :: Mat
ctrlLowBit = permMat 16 (\k -> let t = k `div` 8
                                   v = k `mod` 8
                               in t * 8 + (if t == 1 then v `div` 2 * 2 + (1 - v `mod` 2) else v))

-- | Three temporaries in nested scopes, of mixed dimensions, with gates that
-- couple them.  Bundles to @tmp[12]@ and is decided by the ordinary criterion.
nestedThree :: MProgram
nestedThree = MProgram
  { mLabel  = "three nested temporaries of dims 2, 2, 3"
  , mVis    = "v"
  , mVisDim = 2
  , mStmts  =
      [ MNew "a" 2 0
      , MApply "H" mH ["a"]
      , MNew "b" 2 0
      , MApply "CX" mCX ["a","b"]
      , MNew "c" 3 0
      , MApply "tilt" mTilt ["c"]
      , MApply "CX" mCX ["b","v"]
      , MApply "CX" mCX ["b","v"]
      , MDrop "c"
      , MDrop "b"
      , MDrop "a" ]
  }
