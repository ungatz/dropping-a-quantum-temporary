-- Drop.Lang.Interp: the definitional interpreter for the command list.
--
-- Question: What does a command list do to a state, and which lists are well formed?
-- Answer:   Mach is the registers in tensor order, the exact unnormalised state over them, the
--           lifted bits, the selection still to consume and the registers dropped so far; step runs
--           one command and runStmts a list up to a site, taking one bit of the selection at each
--           lift. checkFlat is the well-formedness a command list must have before it runs: every
--           name in scope, none used after its drop, none bound twice. Nothing here judges a drop;
--           Drop.Lang.Criterion does.
-- Paper:    sec:lang:denotation (what a program denotes).
-- Shapes:   Mach a       registers, state, lifted bits, selection left, loan arrivals, dropped names.
--           FlatScope    the live registers with their dimensions, the dropped names, the lifted parameters.
--           Fragment     SurfaceFragment (what the parser writes) or ElaboratedFragment (what elab writes).
--           Site         [String], the registers one drop names, in the order it names them.

module Drop.Lang.Interp where

import Data.List (elemIndex)
import Drop.Lang.State
import Drop.Lang.Flat

-- The machine -----------------------------------------------------------------

-- | Register names and dimensions in tensor order, the exact unnormalized
-- state vector, the store of lifted classical bits, and the selection still
-- to be consumed (the oracle of measurement outcomes).
data Mach a = Mach
  { mNames :: [String]
  , mDims  :: [Int]
  , mAmp   :: StateV a
  , mStore :: [(String, Int)]
  , mSel   :: [Sel]
  , mLoans :: [(String, StateV a)]
    -- ^ the probe state each loan ('Loan', a header parameter hoisted to
    -- the head of the body) is to arrive on, keyed by name, consumed once
    -- at its own step. Empty from 'initMach', so no existing (loan-free)
    -- caller is affected; a run that reaches a 'Loan' with no entry here is
    -- a caller error (see 'initMachL').
  , mDropped :: [String]
    -- ^ the registers dropped so far. A drop is the identity on the state,
    -- so the state cannot tell a dropped register from a live one; this
    -- list is what lets the machine refuse a use after the drop.
  } deriving Show

-- Two registers in |00>: no bits lifted, no selection, no loans, nothing dropped.
-- >>> initMach [("x", 2), ("y", 2)] (ket [2, 2] [0, 0]) :: Mach Rational
-- Mach {mNames = ["x","y"], mDims = [2,2], mAmp = [1 % 1,0 % 1,0 % 1,0 % 1], mStore = [], mSel = [], mLoans = [], mDropped = []}

initMach :: VisSpec -> StateV a -> Mach a
initMach vis amp = initMachL vis amp []

-- >>> mNames (initMach [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) :: Mach Rational)
-- ["x","y"]
-- >>> mDims (initMach [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) :: Mach Rational)
-- [2,3]
-- >>> mAmp (initMach [("x", 2), ("y", 3)] (ket [2, 3] [1, 2]) :: Mach Rational)
-- [0 % 1,0 % 1,0 % 1,0 % 1,0 % 1,1 % 1]

-- | As 'initMach', but also supplying the state every loan the program
-- allocates is to arrive on for this run, keyed by name.
initMachL :: VisSpec -> StateV a -> [(String, StateV a)] -> Mach a
initMachL vis amp loans = Mach (map fst vis) (map snd vis) amp [] [] loans []

-- >>> mLoans (initMachL [("x", 2)] (ket [2] [0]) [("a", ket [2] [1])] :: Mach Rational)
-- [("a",[0 % 1,1 % 1])]

regPos :: Mach a -> String -> Int
regPos m x = case elemIndex x (mNames m) of
  Just i  -> i
  -- refusal: a register the machine never allocated (step checks its command first, so only a direct caller reaches it)
  Nothing -> error ("regPos: no register " ++ x)

-- >>> regPos (initMach [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) :: Mach Rational) "x"
-- 0
-- >>> regPos (initMach [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) :: Mach Rational) "y"
-- 1

-- | The surface language refuses a repeated binder (see Drop.Lang.Parser), but a
-- program built directly as a list of commands does not go through it. Two
-- wires with one name are indistinguishable to 'regPos', which always finds
-- the first, so the machine refuses them here as well rather than compute a
-- confident wrong answer. This is the one refusal helper for a repeated name;
-- 'stepUnchecked' calls it for 'New', 'NewState' and 'Loan'.
duplicateName :: String -> String -> a
duplicateName what x =
  -- refusal: a name allocated twice
  error (what ++ ": register " ++ x ++ " is already in scope; a name is \
         \allocated once, and reuse of the wire is the allocator's business")

-- Well-formedness of the flat form -------------------------------------------
--
-- The parser refuses an ill-formed program by name, but a 'Prog' built
-- directly as a list of commands never meets the parser, and the machine
-- below would answer on it: a drop is the identity on the state, so a gate
-- after a drop runs, and the criterion calls the drop safe. So the machine
-- checks the rules the parser enforces on every program it runs, and
-- refuses by name the way 'duplicateName' does.
--
-- Two fragments. The surface fragment is what the parser produces: no
-- binder (a new, a loan, a lift or a drop) inside an if branch. The
-- elaborated fragment is what 'Drop.Lang.Elab.elabE' produces from a typed
-- term, whose If rule lets an arm allocate, lift and drop; there each arm is
-- checked on its own path. A drop site is looked for among the top-level
-- commands only, so a run that stops at a site needs the surface fragment.

-- | What is in scope at a point of a flat program: the live registers with
-- their dimensions, the dropped ones, and the lifted parameters.
data FlatScope = FlatScope
  { fsLive    :: [(String, Int)]
  , fsDropped :: [String]
  , fsParams  :: [String]
  } deriving (Eq, Show)

-- The scope of a program that starts with one register x and has lifted nothing.
-- >>> FlatScope [("x", 2)] [] []
-- FlatScope {fsLive = [("x",2)], fsDropped = [], fsParams = []}

data Fragment = SurfaceFragment | ElaboratedFragment deriving (Eq, Show)

-- >>> SurfaceFragment == ElaboratedFragment
-- False

-- | The scope a machine is in.
machScope :: Mach a -> FlatScope
machScope m =
  FlatScope [ (x, d) | (x, d) <- zip (mNames m) (mDims m), x `notElem` mDropped m ]
            (mDropped m) (map fst (mStore m))

-- >>> machScope (initMach [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) :: Mach Rational)
-- FlatScope {fsLive = [("x",2),("y",3)], fsDropped = [], fsParams = []}

-- A dropped register leaves the live list and joins the dropped list.
-- >>> machScope (step (initMach [("x", 2), ("a", 2)] (ket [2, 2] [0, 0]) :: Mach Rational) (Drop ["a"]))
-- FlatScope {fsLive = [("x",2)], fsDropped = ["a"], fsParams = []}

-- | The scope at the start of a program with these visible registers.
visScope :: VisSpec -> FlatScope
visScope vis = FlatScope vis [] []

-- >>> visScope [("x", 2), ("y", 3)]
-- FlatScope {fsLive = [("x",2),("y",3)], fsDropped = [], fsParams = []}

-- | One command that is not an 'IfBit', checked against the scope before
-- it, giving the scope after it.
checkCmd :: FlatScope -> Cmd a -> Either String FlatScope
checkCmd sc c = case c of
  New x d          -> bind "new" x d
  NewState x d st
    | length st /= d -> Left ("new " ++ x ++ " : [" ++ show d ++ "] needs " ++ show d
                              ++ " amplitudes, got " ++ show (length st))
    | otherwise      -> bind "new" x d
  Loan x d         -> bind "loan" x d
  Gate g xs -> do
    ds <- mapM (live "gate") xs
    distinct "gate" xs
    let n = dimensionSize ds
    if length g == n && all ((== n) . length) g then Right sc
      else Left ("gate on " ++ unwords xs ++ ": a matrix of " ++ show (length g)
                 ++ " rows does not act on registers of total dimension " ++ show n)
  Drop xs -> do
    _ <- mapM (live "drop") xs
    distinct "drop" xs
    Right sc { fsLive = [ r | r@(y, _) <- fsLive sc, y `notElem` xs ]
             , fsDropped = fsDropped sc ++ xs }
  Lift p x block -> do
    d <- live "lift" x
    if p `elem` fsParams sc
      then Left ("lift: parameter " ++ p ++ " is already bound; this machine \
                 \reads the latest binding and the static pass reads the \
                 \first, so a second one would make the two disagree")
      else Right ()
    if null block || any (\l -> l < 0 || l >= d) block || length (nubS block) /= length block
         || length block >= d
      then Left ("lift " ++ x ++ ": the block " ++ show block ++ " is not a nonempty \
                 \proper set of the " ++ show d ++ " levels of " ++ x)
      else Right sc { fsParams = fsParams sc ++ [p] }
  IfBit {} -> Left "checkCmd: an if is checked by checkFlat"
  where
    bind what x d
      | x `elem` map fst (fsLive sc) = Left (what ++ ": register " ++ x ++ " is already in scope; a name is \
                                             \allocated once, and reuse of the wire is the allocator's business")
      | x `elem` fsDropped sc = Left (what ++ ": register " ++ x ++ " has been dropped; a name is \
                                      \allocated once")
      | d < 2 = Left (what ++ " " ++ x ++ " : [" ++ show d ++ "]: a register has at least 2 levels")
      | otherwise = Right sc { fsLive = fsLive sc ++ [(x, d)] }
    live what x = case lookup x (fsLive sc) of
      Just d -> Right d
      Nothing
        | x `elem` fsDropped sc -> Left (what ++ ": register " ++ x ++ " has been dropped")
        | otherwise             -> Left (what ++ ": no register " ++ x ++ " in scope")
    distinct what xs
      | length (nubS xs) /= length xs = Left (what ++ ": a register is named twice in " ++ unwords xs)
      | otherwise = Right ()

-- A new register extends the scope.
-- >>> checkCmd (visScope [("x", 2)]) (New "a" 2 :: Cmd Rational)
-- Right (FlatScope {fsLive = [("x",2),("a",2)], fsDropped = [], fsParams = []})

-- A name is allocated once.
-- >>> checkCmd (visScope [("x", 2)]) (New "x" 2 :: Cmd Rational)
-- Left "new: register x is already in scope; a name is allocated once, and reuse of the wire is the allocator's business"

-- A register has at least two levels.
-- >>> checkCmd (visScope [("x", 2)]) (New "a" 1 :: Cmd Rational)
-- Left "new a : [1]: a register has at least 2 levels"

-- A gate must name registers in scope, and its matrix must fit them.
-- >>> checkCmd (visScope [("x", 2)]) (Gate [[0, 1], [1, 0]] ["x"] :: Cmd Rational)
-- Right (FlatScope {fsLive = [("x",2)], fsDropped = [], fsParams = []})
-- >>> checkCmd (visScope [("x", 2)]) (Gate [[0, 1], [1, 0]] ["y"] :: Cmd Rational)
-- Left "gate: no register y in scope"
-- >>> checkCmd (visScope [("x", 2)]) (Gate [[0, 1], [1, 0]] ["x", "x"] :: Cmd Rational)
-- Left "gate: a register is named twice in x x"

-- A drop moves the register to the dropped list; then nothing may name it.
-- >>> checkCmd (visScope [("x", 2), ("a", 2)]) (Drop ["a"] :: Cmd Rational)
-- Right (FlatScope {fsLive = [("x",2)], fsDropped = ["a"], fsParams = []})
-- >>> checkCmd (FlatScope [("x", 2)] ["a"] []) (Drop ["a"] :: Cmd Rational)
-- Left "drop: register a has been dropped"

-- A lift binds its parameter once, and its block is a nonempty proper set of levels.
-- >>> checkCmd (visScope [("x", 2)]) (Lift "p" "x" [1] :: Cmd Rational)
-- Right (FlatScope {fsLive = [("x",2)], fsDropped = [], fsParams = ["p"]})
-- >>> checkCmd (visScope [("x", 2)]) (Lift "p" "x" [0, 1] :: Cmd Rational)
-- Left "lift x: the block [0,1] is not a nonempty proper set of the 2 levels of x"
-- >>> checkCmd (FlatScope [("x", 2)] [] ["p"]) (Lift "p" "x" [1] :: Cmd Rational)
-- Left "lift: parameter p is already bound; this machine reads the latest binding and the static pass reads the first, so a second one would make the two disagree"

nubS :: Eq b => [b] -> [b]
nubS []       = []
nubS (x : xs) = x : nubS (filter (/= x) xs)

-- >>> nubS [1, 2, 1, 3, 2 :: Int]
-- [1,2,3]
-- >>> nubS ([] :: [Int])
-- []

-- | A whole program, checked from a scope, giving the scope at the end of
-- every path (without repeats). A guard reads only parameters already
-- lifted; in the surface fragment an arm binds nothing.
checkFlat :: Fragment -> FlatScope -> Prog a -> Either String [FlatScope]
checkFlat frag sc0 prog0 = go sc0 prog0
  where
    go sc [] = Right [sc]
    go sc (IfBit g thn els : rest) = do
      case [ p | p <- guardParams g, p `notElem` fsParams sc ] of
        (p : _) -> Left ("ifbit: parameter " ++ p ++ " not lifted")
        []      -> Right ()
      if frag == SurfaceFragment
        then case [ c | c <- flatCmds (thn ++ els), binds c ] of
               (c : _) -> Left ("ifbit: " ++ cmdWord c ++ " inside an if branch; a branch \
                                \allocates, lifts and drops nothing")
               []      -> Right ()
        else Right ()
      ends <- (++) <$> go sc thn <*> go sc els
      fmap (nubS . concat) (mapM (\s -> go s rest) (nubS ends))
    go sc (c : rest) = checkCmd sc c >>= \sc' -> go sc' rest
    flatCmds = concatMap (\c -> case c of IfBit _ t e -> c : flatCmds (t ++ e); _ -> [c])
    binds c = case c of
      New {} -> True; NewState {} -> True; Loan {} -> True; Lift {} -> True; Drop {} -> True
      _ -> False
    cmdWord c = case c of
      Lift {} -> "lift"; Drop {} -> "drop"; Loan {} -> "loan"; _ -> "new"

-- The abstract's temporary AND is well formed: it ends with x, y live and a dropped.
-- >>> :m + Drop.Lang.Programs.TempAnd
-- >>> fmap (map fsDropped) (checkFlat SurfaceFragment (visScope visXY) andUncomputedByMeasurement)
-- Right [["a"]]

-- A use after the drop is refused, by name.
-- >>> checkFlat SurfaceFragment (visScope [("x", 2)]) ([New "a" 2, Drop ["a"], Gate [[0, 1], [1, 0]] ["a"]] :: Prog Rational)
-- Left "gate: register a has been dropped"

-- A guard may read only a parameter already lifted.
-- >>> checkFlat SurfaceFragment (visScope [("x", 2)]) ([IfBit (GParam "m") [] []] :: Prog Rational)
-- Left "ifbit: parameter m not lifted"

-- The surface fragment lets an if branch bind nothing; the elaborated fragment lets it.
-- >>> either id (const "accepted") (checkFlat SurfaceFragment (visScope [("x", 2)]) ([IfBit (GBit True) [New "a" 2] []] :: Prog Rational))
-- "ifbit: new inside an if branch; a branch allocates, lifts and drops nothing"
-- >>> fmap (map fsLive) (checkFlat ElaboratedFragment (visScope [("x", 2)]) ([IfBit (GBit True) [New "a" 2] []] :: Prog Rational))
-- Right [[("x",2),("a",2)],[("x",2)]]

-- | 'checkFlat', as a refusal.
requireFlat :: Fragment -> FlatScope -> Prog a -> ()
-- refusal: a command list that checkFlat refuses, with checkFlat's sentence
requireFlat frag sc prog = either error (const ()) (checkFlat frag sc prog)

-- >>> requireFlat SurfaceFragment (visScope [("x", 2)]) ([Gate [[0, 1], [1, 0]] ["x"]] :: Prog Rational)
-- ()

-- Running commands -----------------------------------------------------------

-- | One command on the machine: checked against the scope first ('checkCmd'),
-- then run.

step :: (Eq a, Num a) => Mach a -> Cmd a -> Mach a
step m c = case c of
  IfBit {} -> stepUnchecked m c
  -- refusal: a command that checkCmd refuses, with checkCmd's sentence
  _        -> either error (const (stepUnchecked m c)) (checkCmd (machScope m) c)

-- New adjoins a register in |0>.
-- >>> mAmp (step (initMach [("x", 2)] (ket [2] [1])) (New "a" 2)) :: StateV Rational
-- [0 % 1,0 % 1,1 % 1,0 % 1]
-- >>> mNames (step (initMach [("x", 2)] (ket [2] [1]) :: Mach Rational) (New "a" 2))
-- ["x","a"]

-- Gate: X on |0>.
-- >>> mAmp (step (initMach [("x", 2)] (ket [2] [0])) (Gate [[0, 1], [1, 0]] ["x"])) :: StateV Rational
-- [0 % 1,1 % 1]

-- Lift takes one bit of the selection: SIn keeps the block {1}, SOut its complement.
-- >>> let m = (initMach [("x", 2)] [1, 1] :: Mach Rational) in (mAmp (step m { mSel = [SIn] } (Lift "p" "x" [1])), mStore (step m { mSel = [SIn] } (Lift "p" "x" [1])))
-- ([0 % 1,1 % 1],[("p",1)])
-- >>> let m = (initMach [("x", 2)] [1, 1] :: Mach Rational) in (mAmp (step m { mSel = [SOut] } (Lift "p" "x" [1])), mStore (step m { mSel = [SOut] } (Lift "p" "x" [1])))
-- ([1 % 1,0 % 1],[("p",0)])

-- Drop changes no amplitude; it only records the name.
-- >>> let m = step (initMach [("x", 2), ("a", 2)] (ket [2, 2] [1, 0]) :: Mach Rational) (Drop ["a"]) in (mAmp m, mDropped m)
-- ([0 % 1,0 % 1,1 % 1,0 % 1],["a"])

-- | One command with no well-formedness check ('step' does the checking);
-- an 'IfBit' folds 'step' over the arm its guard picks.
stepUnchecked :: (Eq a, Num a) => Mach a -> Cmd a -> Mach a
stepUnchecked m c = case c of
  New x d
    | x `elem` mNames m -> duplicateName "new" x
    | otherwise ->
        m { mNames = mNames m ++ [x]
          , mDims  = mDims m ++ [d]
          , mAmp   = tensorS (mAmp m) (ket [d] [0]) }
  NewState x d st
    | x `elem` mNames m -> duplicateName "new" x
    | otherwise ->
        m { mNames = mNames m ++ [x]
          , mDims  = mDims m ++ [d]
          , mAmp   = tensorS (mAmp m) st }
  Loan x d
    | x `elem` mNames m -> duplicateName "loan" x
    | otherwise ->
        let st = case lookup x (mLoans m) of
              Just s  -> s
              -- refusal: a loan reached the machine with no arrival state (use initMachL)
              Nothing -> error ("step: no probe state assigned to the loan "
                                 ++ x ++ "; use initMachL")
        in m { mNames = mNames m ++ [x]
             , mDims  = mDims m ++ [d]
             , mAmp   = tensorS (mAmp m) st }
  Gate g xs ->
    m { mAmp = applyGate (mDims m) g (map (regPos m) xs) (mAmp m) }
  Drop xs -> m { mDropped = mDropped m ++ xs }   -- denotationally the identity
  Lift p x block
    | any ((== p) . fst) (mStore m) ->
        -- refusal: a parameter lifted twice
        error ("lift: parameter " ++ p ++ " is already bound; this machine \
               \reads the latest binding and the static pass reads the \
               \first, so a second one would make the two disagree")
    | otherwise ->
    case mSel m of
      -- refusal: the selection has fewer bits than the program has lifts
      [] -> error "lift: selection exhausted"
      (ch : rest) ->
        let pos  = regPos m x
            -- impossible: pos is regPos of a register of the machine, and mDims has one entry per name
            d    = mDims m !! pos
            keep = if ch == SIn then block
                   else [ l | l <- [0 .. d - 1], l `notElem` block ]
        in m { mAmp   = projectLevels (mDims m) pos keep (mAmp m)
             , mStore = (p, selBit ch) : mStore m
             , mSel   = rest }
  IfBit g thn els ->
    let env nm = case lookup nm (mStore m) of
          Just b  -> b == 1
          -- refusal: a guard reads a parameter no lift bound
          Nothing -> error ("ifbit: parameter " ++ nm ++ " not lifted")
    in foldl step m (if evalGuard env g then thn else els)

-- An if runs the arm its guard picks, reading the lifted bits.
-- >>> mAmp (stepUnchecked ((initMach [("x", 2)] (ket [2] [0])) { mStore = [("p", 1)] }) (IfBit (GParam "p") [Gate [[0, 1], [1, 0]] ["x"]] [])) :: StateV Rational
-- [0 % 1,1 % 1]
-- >>> mAmp (stepUnchecked ((initMach [("x", 2)] (ket [2] [0])) { mStore = [("p", 0)] }) (IfBit (GParam "p") [Gate [[0, 1], [1, 0]] ["x"]] [])) :: StateV Rational
-- [1 % 1,0 % 1]

-- A loan arrives on the state the caller assigned.
-- >>> mAmp (stepUnchecked (initMachL [("x", 2)] (ket [2] [0]) [("a", ket [2] [1])]) (Loan "a" 2)) :: StateV Rational
-- [0 % 1,1 % 1,0 % 1,0 % 1]

-- | Run a program, optionally halting just before the named drop site, the
-- point at which the criterion looks.
runStmts :: (Eq a, Num a) => Mach a -> Prog a -> [Sel] -> Maybe Site -> Mach a
runStmts m0 prog sel stop = go (m0 { mSel = sel }) prog
  where
    -- The whole program is checked once, before the run, from the scope the
    -- machine starts in: halting at a site must not hide a use after it.
    checked = requireFlat (maybe ElaboratedFragment (const SurfaceFragment) stop)
                          (machScope m0) prog `seq`
              maybe () (requireUniqueSite prog) stop
    go m _ | checked `seq` False = m
    go m [] = case stop of
      Nothing -> m
      -- refusal: the named site is not a drop of the program
      Just x  -> error ("runStmts: no drop site named " ++ show x)
    go m (c : _) | Just x <- siteNames c, Just x == stop = m
    go m (c : cs) = go (step m c) cs

-- The temporary AND from |11>, to its end, taking the bit 1 of the lift (SIn).
-- >>> :m + Drop.Lang.Programs.TempAnd
-- >>> let m = runStmts (initMach visXY (ket [2, 2] [1, 1])) andUncomputedByMeasurement [SIn] Nothing in (mNames m, mStore m, mDropped m, [ i | (i, a) <- zip [0 :: Int ..] (mAmp m), a /= 0 ])
-- (["x","y","a"],[("m",1)],["a"],[7])

-- The same, taking the bit 0 (SOut).
-- >>> let m = runStmts (initMach visXY (ket [2, 2] [1, 1])) andUncomputedByMeasurement [SOut] Nothing in (mNames m, mStore m, mDropped m, [ i | (i, a) <- zip [0 :: Int ..] (mAmp m), a /= 0 ])
-- (["x","y","a"],[("m",0)],["a"],[6])

-- Stopped just before the drop of a: nothing is dropped yet.
-- >>> let m = runStmts (initMach visXY (ket [2, 2] [1, 1])) andUncomputedByMeasurement [SIn] (Just ["a"]) in (mStore m, mDropped m)
-- ([("m",1)],[])

-- | The state at a drop site, for a record and a visible input: what every
-- form of the static pass (Drop.Lang.Pass) has to agree about.
interpSource :: (Eq a, Num a)
             => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> Mach a
interpSource vis prog x sel inp = runStmts (initMach vis inp) prog sel (Just [x])

-- The state at the site of a, for the input |11> and the bit 1: eight amplitudes, one nonzero.
-- >>> let m = interpSource visXY andUncomputedByMeasurement "a" [SIn] (ket [2, 2] [1, 1]) in [ i | (i, a) <- zip [0 :: Int ..] (mAmp m), a /= 0 ]
-- [7]

-- Reading a program: its sites, prefixes and selections ----------------------

-- | A drop site: the registers one @drop@ names, in the order it names
-- them. A tuple drop is one site (the composite-temporary proposition), so a site is a list.
type Site = [String]

-- A tuple drop is one site of two registers, in the order the drop names them.
-- >>> siteNames (Drop ["a", "b"] :: Cmd Rational)
-- Just ["a","b"]

-- | The registers a command discards, if it discards any.
siteNames :: Cmd a -> Maybe Site
siteNames (Drop xs) = Just xs
siteNames _         = Nothing

-- >>> siteNames (Drop ["a"] :: Cmd Rational)
-- Just ["a"]
-- >>> siteNames (Gate [[0, 1], [1, 0]] ["x"] :: Cmd Rational)
-- Nothing

-- | The drop sites of a program, in order. A site is a top-level command;
-- a drop inside an if branch would be no site at all, so it is refused.
dropSites :: Prog a -> [Site]
dropSites prog
  -- refusal: a drop inside an if branch
  | any inBranch prog = error "dropSites: drop inside an if branch; a branch \
                              \allocates, lifts and drops nothing"
  | otherwise = [ x | Just x <- map siteNames prog ]
  where
    inBranch (IfBit _ t e) = any isDropOrIf (t ++ e)
    inBranch _             = False
    isDropOrIf (Drop _)      = True
    isDropOrIf (IfBit _ t e) = any isDropOrIf (t ++ e)
    isDropOrIf _             = False

-- >>> dropSites andUncomputedByMeasurement
-- [["a"]]
-- >>> dropSites ([Drop ["a"], Gate [[0, 1], [1, 0]] ["x"], Drop ["b", "c"]] :: Prog Rational)
-- [["a"],["b","c"]]
-- >>> dropSites ([] :: Prog Rational)
-- []

-- | One exposed prefix per drop occurrence. Earlier drops act as identity,
-- so omitting them also keeps distinct unit drops from sharing the empty name key.
sitePrefixes :: Prog a -> [(Site, Prog a)]
sitePrefixes prog = dropSites prog `seq` go [] prog
  where
    go _ [] = []
    go before (Drop xs : rest) = (xs, before ++ [Drop xs]) : go before rest
    go before (cmd : rest) = go (before ++ [cmd]) rest

-- >>> map (\(site, pre) -> (site, length pre)) (sitePrefixes ([New "t" 2, Drop [], Lift "p" "t" [0], Drop []] :: Prog Rational))
-- [([],2),([],3)]

-- | Name-based callers must identify one occurrence; reports use sitePrefixes.
requireUniqueSite :: Prog a -> Site -> ()
requireUniqueSite prog site
  | null site && length [ () | Drop xs <- prog, xs == site ] > 1 =
      -- refusal: names alone do not identify repeated unit-drop occurrences
      error ("ambiguous drop site " ++ show site ++ "; use its exposed prefix")
  | otherwise = ()

-- >>> requireUniqueSite ([Drop ["t"]] :: Prog Rational) ["t"]
-- ()

-- | The program up to and including the drop site named @x@.
--
-- A site's verdict depends only on this prefix. Cutting there also keeps
-- the selection word honest: a site at lift depth l is indexed by an
-- l-bit word, and a whole-program walk could reach a later, deeper site
-- and consume a bit the word never had.
prefixThroughS :: Prog a -> Site -> Prog a
prefixThroughS prog x = requireUniqueSite prog x `seq` (before ++ take 1 after)
  where (before, after) = break ((== Just x) . siteNames) prog

-- >>> length (prefixThroughS ([Drop ["a"], Gate [[0, 1], [1, 0]] ["x"], Drop ["b", "c"]] :: Prog Rational) ["a"])
-- 1
-- >>> length (prefixThroughS ([Drop ["a"], Gate [[0, 1], [1, 0]] ["x"], Drop ["b", "c"]] :: Prog Rational) ["b", "c"])
-- 3

-- A site the program does not have: the whole program.
-- >>> length (prefixThroughS ([Drop ["a"], Gate [[0, 1], [1, 0]] ["x"]] :: Prog Rational) ["z"])
-- 2

prefixThrough :: Prog a -> String -> Prog a
prefixThrough prog x = prefixThroughS prog [x]

-- >>> length (prefixThrough andUncomputedByMeasurement "a")
-- 6
-- >>> last (prefixThrough andUncomputedByMeasurement "a") == Drop ["a"]
-- True

-- | The commands the machine executes strictly before a site: everything
-- up to the @drop@ that /is/ the site. Since the parser forbids an
-- allocation inside an @if@ branch, this top-level scan sees every binder.
beforeSite :: Prog a -> Site -> Prog a
beforeSite prog site = requireUniqueSite prog site `seq`
                       takeWhile ((/= Just site) . siteNames) prog

-- >>> length (beforeSite andUncomputedByMeasurement ["a"])
-- 5
-- >>> length (beforeSite andComputed ["a"])
-- 2

-- | Every selection of n lifts: SIn before SOut at each, the first lift most significant.
allSelections :: Int -> [[Sel]]
allSelections 0 = [[]]
allSelections n = [ c : r | c <- [SIn, SOut], r <- allSelections (n - 1) ]

-- >>> allSelections 0
-- [[]]
-- >>> allSelections 1
-- [[SIn],[SOut]]
-- >>> allSelections 2
-- [[SIn,SIn],[SIn,SOut],[SOut,SIn],[SOut,SOut]]

-- | Number of top-level lifts strictly before the drop at a site.
liftDepthBeforeS :: Prog a -> Site -> Int
liftDepthBeforeS prog x = length [ () | Lift {} <- beforeSite prog x ]

-- >>> liftDepthBeforeS andUncomputedByMeasurement ["a"]
-- 1
-- >>> liftDepthBeforeS andComputed ["a"]
-- 0

liftDepthBefore :: Prog a -> String -> Int
liftDepthBefore prog x = liftDepthBeforeS prog [x]

-- >>> liftDepthBefore andUncomputedByMeasurement "a"
-- 1
