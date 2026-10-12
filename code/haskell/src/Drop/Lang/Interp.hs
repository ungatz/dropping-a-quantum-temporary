-- Interp.hs: the definitional interpreter and the drop criterion.
--
-- The criterion (the criterion section): a drop of x is safe when the joint state
-- factors as a fixed temporary state tensored with a linear map of the
-- visible input, checked at dim + 1 test inputs via QState's exact minor
-- test. A zero-weight test input is skipped, not counted as a failure.

module Drop.Lang.Interp where

import Data.List (elemIndex)
import Drop.Lang.Ring
import Drop.Lang.QState
import Drop.Lang.Syntax
import Drop.Lang.Gates (daggerM)

-- Machine

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

initMach :: VisSpec -> StateV a -> Mach a
initMach vis amp = initMachL vis amp []

-- | As 'initMach', but also supplying the state every loan the program
-- allocates is to arrive on for this run, keyed by name.
initMachL :: VisSpec -> StateV a -> [(String, StateV a)] -> Mach a
initMachL vis amp loans = Mach (map fst vis) (map snd vis) amp [] [] loans []

regPos :: Mach a -> String -> Int
regPos m x = case elemIndex x (mNames m) of
  Just i  -> i
  Nothing -> error ("regPos: no register " ++ x)

-- | The surface language refuses a repeated binder (see Drop.Lang.Parser), but a
-- program built directly as a list of commands does not go through it. Two
-- wires with one name are indistinguishable to 'regPos', which always finds
-- the first, so the machine refuses them here as well rather than compute a
-- confident wrong answer.
duplicateName :: String -> String -> a
duplicateName what x =
  error (what ++ ": register " ++ x ++ " is already in scope; a name is \
         \allocated once, and reuse of the wire is the allocator's business")

-- Well-formedness of the flat form
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

data Fragment = SurfaceFragment | ElaboratedFragment deriving (Eq, Show)

-- | The scope a machine is in.
machScope :: Mach a -> FlatScope
machScope m =
  FlatScope [ (x, d) | (x, d) <- zip (mNames m) (mDims m), x `notElem` mDropped m ]
            (mDropped m) (map fst (mStore m))

-- | The scope at the start of a program with these visible registers.
visScope :: VisSpec -> FlatScope
visScope vis = FlatScope vis [] []

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
    let n = product ds
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

nubS :: Eq b => [b] -> [b]
nubS []       = []
nubS (x : xs) = x : nubS (filter (/= x) xs)

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

-- | 'checkFlat', as a refusal.
requireFlat :: Fragment -> FlatScope -> Prog a -> ()
requireFlat frag sc prog = either error (const ()) (checkFlat frag sc prog)

step :: (Eq a, Num a) => Mach a -> Cmd a -> Mach a
step m c = case c of
  IfBit {} -> stepUnchecked m c
  _        -> either error (const (stepUnchecked m c)) (checkCmd (machScope m) c)

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
        error ("lift: parameter " ++ p ++ " is already bound; this machine \
               \reads the latest binding and the static pass reads the \
               \first, so a second one would make the two disagree")
    | otherwise ->
    case mSel m of
      [] -> error "lift: selection exhausted"
      (ch : rest) ->
        let pos  = regPos m x
            d    = mDims m !! pos
            keep = if ch == SIn then block
                   else [ l | l <- [0 .. d - 1], l `notElem` block ]
        in m { mAmp   = projectLevels (mDims m) pos keep (mAmp m)
             , mStore = (p, selBit ch) : mStore m
             , mSel   = rest }
  IfBit g thn els ->
    let env nm = case lookup nm (mStore m) of
          Just b  -> b == 1
          Nothing -> error ("ifbit: parameter " ++ nm ++ " not lifted")
    in foldl step m (if evalGuard env g then thn else els)

-- | Run a program, optionally halting just before the named drop site, the
-- point at which the criterion looks.
runStmts :: (Eq a, Num a) => Mach a -> Prog a -> [Sel] -> Maybe Site -> Mach a
runStmts m0 prog sel stop = go (m0 { mSel = sel }) prog
  where
    -- The whole program is checked once, before the run, from the scope the
    -- machine starts in: halting at a site must not hide a use after it.
    checked = requireFlat (maybe ElaboratedFragment (const SurfaceFragment) stop)
                          (machScope m0) prog
    go m _ | checked `seq` False = m
    go m [] = case stop of
      Nothing -> m
      Just x  -> error ("runStmts: no drop site named " ++ show x)
    go m (c : _) | Just x <- siteNames c, Just x == stop = m
    go m (c : cs) = go (step m c) cs

-- | The state at a drop site, for a record and a visible input: what every
-- form of the static pass (Drop.Lang.Pass) has to agree about.
interpSource :: (Eq a, Num a)
             => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> Mach a
interpSource vis prog x sel inp = runStmts (initMach vis inp) prog sel (Just [x])

-- Test inputs

-- | The visible basis plus the all-ones superposition: dim + 1 test inputs.
probesFor :: Num a => VisSpec -> [(String, StateV a)]
probesFor vis =
  [ ("e" ++ show j, [ if k == j then 1 else 0 | k <- [0 .. dv - 1] ])
  | j <- [0 .. dv - 1] ]
  ++ [("sum", replicate dv 1)]
  where dv = product (map snd vis)

-- Criterion

-- | A drop site: the registers one @drop@ names, in the order it names
-- them. A tuple drop is one site (the composite-temporary proposition), so a site is a list.
type Site = [String]

data Verdict = Safe | Unsafe | Unreachable deriving (Eq, Show)

data ProbeResult a = PZero | PFail | PLine (StateV a) deriving (Eq, Show)

-- | Factor the site's registers out of the state at the drop, on one
-- visible test input and one arrival state per loan the prefix allocates.
probeResultL :: (Eq a, Fractional a)
             => VisSpec -> Prog a -> Site -> [Sel]
             -> [(String, StateV a)] -> StateV a -> ProbeResult a
probeResultL vis prog target sel env inp =
  let m = runStmts (initMachL vis inp env) prog sel (Just target)
  in if isZeroS (mAmp m) then PZero
     -- The block factor is indexed as the drop names its registers
     -- (the site definition: H_v is the tensor product of the block's spaces in the
     -- tuple's order), hence 'factorSplitOrd', not the sorted 'factorSplit'.
     else case factorSplitOrd (mDims m) (map (regPos m) target) (mAmp m) of
            Nothing       -> PFail
            Just (vA, _)  -> PLine (canonicalLine vA)

-- | 'probeResultL' on a program that allocates no loan, so there is no
-- arrival state to supply. A loan program reaches the machine through
-- 'tempVerdictS' instead, which supplies one per loan.
probeResultS :: (Eq a, Fractional a)
             => VisSpec -> Prog a -> Site -> [Sel] -> StateV a -> ProbeResult a
probeResultS vis prog target sel = probeResultL vis prog target sel []

probeResult :: (Eq a, Fractional a)
            => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> ProbeResult a
probeResult vis prog target = probeResultS vis prog [target]

-- | The temporary path of the criterion: rerun the program on every input
-- and ask whether the surviving runs all leave the site's block constant
-- on one and the same line. The inputs are the site map's whole domain
-- @[[Omega]]@ of the site definition -- the dim+1 visible probes crossed with one
-- basis arrival per loan allocated before the site ('tempProbes'), which
-- is just the dim+1 visible probes when the program has no loan.
tempVerdictS :: (Eq a, Fractional a)
             => VisSpec -> Prog a -> Site -> [Sel] -> Verdict
tempVerdictS vis prog target sel =
  let live = [ r | r <- tempProbes vis prog target sel, r /= PZero ]
  in case live of
       [] -> Unreachable
       _  | all isLine live && allEqual [ l | PLine l <- live ] -> Safe
          | otherwise -> Unsafe
  where
    isLine (PLine _) = True
    isLine _         = False

-- | Every probe the temporary path looks at, in a fixed order: one per
-- (loan arrival, visible test input) pair.
tempProbes :: (Eq a, Fractional a)
           => VisSpec -> Prog a -> Site -> [Sel] -> [ProbeResult a]
tempProbes vis prog target sel =
  [ probeResultL vis prog target sel env inp
  | env <- loanEnvs (loansBefore prog target)
  , (_, inp) <- probesFor vis ]

-- | The criterion's answer at one site under one selection: the temporary
-- path above, unless the block holds a loan, in which case the site definition clause
-- (4) decides it through 'loanResultS' -- a different theorem (the site map
-- factors as an isometry on the block's loans tensor a map on the rest, not
-- as a fixed ray tensor a map of the visible input; see the module-level
-- note below "Loans"). One loan or several, alone or beside temporaries:
-- one clause, one implementation.
semanticVerdictS :: (Eq a, Fractional a, Conj a)
                 => VisSpec -> Prog a -> Site -> [Sel] -> Verdict
semanticVerdictS vis prog target sel
  | any (isLoanTargetS prog target) target = fst (loanResultS vis prog target sel)
  | otherwise                              = tempVerdictS vis prog target sel

semanticVerdict :: (Eq a, Fractional a, Conj a)
                => VisSpec -> Prog a -> String -> [Sel] -> Verdict
semanticVerdict vis prog target = semanticVerdictS vis prog [target]

-- | The line the site's block is left constant on, when the criterion
-- accepts. Reuses the work 'tempVerdictS' already does on its way to a
-- Boolean, instead of discarding it. 'Nothing' at a loan site: a loan has
-- no fixed line to report (its certificate is the isometry B, from
-- 'semanticLoanCert').
semanticParkedS :: (Eq a, Fractional a)
                => VisSpec -> Prog a -> Site -> [Sel] -> Maybe (StateV a)
semanticParkedS vis prog target sel
  | any (isLoanTargetS prog target) target     = Nothing
  | tempVerdictS vis prog target sel /= Safe   = Nothing
  | otherwise = case [ l | PLine l <- tempProbes vis prog target sel ] of
      (l : _) -> Just l
      []      -> Nothing

semanticParked :: (Eq a, Fractional a)
               => VisSpec -> Prog a -> String -> [Sel] -> Maybe (StateV a)
semanticParked vis prog target = semanticParkedS vis prog [target]

-- | 'head' on a list this function has already shown to be non-empty: the
-- guard above rules out the empty table, and naming that here keeps the
-- module free of partial Prelude functions.
head' :: [b] -> b
head' (y : _) = y
head' []      = error "Drop.Lang.Interp: head' on an empty list (guarded above)"

allEqual :: Eq b => [b] -> Bool
allEqual []       = True
allEqual (x : xs) = all (== x) xs

-- Loans: a loan is an input register, not a fixed ket

-- | The commands the machine executes strictly before a site: everything
-- up to the @drop@ that /is/ the site. Since the parser forbids an
-- allocation inside an @if@ branch, this top-level scan sees every binder.
beforeSite :: Prog a -> Site -> Prog a
beforeSite prog site = takeWhile ((/= Just site) . siteNames) prog

-- | Every loan the program allocates before a site, dropped or not, in
-- header order. Two distinct jobs need this rather than 'liveLoansAtS':
-- the machine must be handed an arrival state for each loan it executes
-- ('initMachL' errors otherwise), and the site definition makes each loan a factor of
-- the site map's domain @[[Omega]]@, so each must be varied -- a loan
-- dropped earlier is hidden, not gone (@Drop@ is denotationally the
-- identity), and the rest of the state still depends on it.
loansBefore :: Prog a -> Site -> [(String, Int)]
loansBefore prog site = [ (n, d) | Loan n d <- beforeSite prog site ]

-- | Those of 'loansBefore' not yet dropped when the site fires: exactly the
-- registers a site can be the drop /of/ as a loan.
liveLoansAtS :: Prog a -> Site -> [(String, Int)]
liveLoansAtS prog site = go [] (beforeSite prog site)
  where
    go acc [] = acc
    go acc (Loan n d : cs)     = go (acc ++ [(n, d)]) cs
    go acc (Drop ns : cs)      = go (filter ((`notElem` ns) . fst) acc) cs
    go acc (_ : cs)            = go acc cs

-- | Is @x@ a loan still live at @site@? Keyed by the whole site, so a
-- tuple drop that happens to contain a loan is recognised as one; asking
-- with the singleton site @[x]@ would silently answer 'False' there,
-- because the scan would run past the tuple drop and see @x@ released.
isLoanTargetS :: Prog a -> Site -> String -> Bool
isLoanTargetS prog site x = x `elem` map fst (liveLoansAtS prog site)

liveLoansAt :: Prog a -> String -> [(String, Int)]
liveLoansAt prog x = liveLoansAtS prog [x]

isLoanTarget :: Prog a -> String -> Bool
isLoanTarget prog x = isLoanTargetS prog [x] x

-- | Every arrival assignment for a list of loans: each loan on one basis
-- vector of its own space, mixed radix, first loan most significant.
-- @[[]]@ for the empty list, so a loan-free program is probed exactly as
-- it was before loans existed.
loanEnvs :: Num a => [(String, Int)] -> [[(String, StateV a)]]
loanEnvs regs =
  [ [ (n, ket [d] [i]) | ((n, d), i) <- zip regs tup ] | tup <- basisTuples regs ]

-- | Every basis-index tuple of a list of (name, dim) registers, mixed
-- radix, first register most significant -- @[[]]@ for the empty list (one
-- trivial tuple, dimension 1: "no other loans" still varies the visible
-- register alone).
basisTuples :: [(String, Int)] -> [[Int]]
basisTuples regs = [ idxToLevels dims k | k <- [0 .. product dims - 1] ]
  where dims = map snd regs

-- | The loans a site's block holds, in the order the @drop@ names its
-- registers: the factors of @H_loan@ in @[[Omega]] = H_loan (x) [[Omega']]@,
-- the site definition's clause (3). Empty when the block is temporaries
-- only, which is the temporary's test ('tempVerdictS'), not this one.
blockLoansAtS :: Prog a -> Site -> [(String, Int)]
blockLoansAtS prog site =
  [ (n, d) | n <- site, Just d <- [lookup n (liveLoansAtS prog site)] ]

-- | The state at the drop site for one probe combination: the visible
-- register on its @vi@-th basis vector, every loan outside the block (in
-- @others@' order) on the basis vector @oth@ names, and the block's loans
-- on the level tuple @lk@ names in @H_loan@'s mixed radix. A genuine input
-- assignment (Drop.Lang.Machine's @cfgLoans@/'initMachL'), never a default.
blockProbeState :: (Eq a, Num a)
                => VisSpec -> Prog a -> Site -> [Sel]
                -> [(String, Int)] -> [(String, Int)] -> Int -> [Int] -> Int
                -> Mach a
blockProbeState vis prog site sel blockLoans others vi oth lk =
  runStmts (initMachL vis visProbe env) prog sel (Just site)
  where
    dv = product (map snd vis)
    visProbe = ket [dv] [vi]
    env = [ (n, ket [dd] [i]) | ((n, dd), i) <- zip others oth ]
       ++ [ (n, ket [dd] [i])
          | ((n, dd), i) <- zip blockLoans (idxToLevels (map snd blockLoans) lk) ]

-- | @B^dagger B@ is exactly @t@ times the identity, some nonzero scalar
-- @t@ -- an isometry up to scale. @B : H_loan -> H_block@ is square when
-- the block is its loans and nothing else, and rectangular (taller than
-- wide) when the block also holds temporaries; either way @B^dagger B@ is
-- the square @dim H_loan@ matrix this tests. @t@ is automatically a
-- positive real, being @sum_a |B_{a0}|^2@ over a nonzero column, so "a
-- nonzero scalar" and "a positive scalar" are the same test here; the
-- factorization below fixes @B@ only up to that scale, and no square root
-- of @t@ is taken, which would leave the exact field.
isScalarIdentity :: (Eq a, Num a) => Matrix a -> Bool
isScalarIdentity m =
  not (null m) && all ((== n) . length) m && t /= 0
  && and [ m !! i !! j == (if i == j then t else 0) | i <- [0 .. n - 1], j <- [0 .. n - 1] ]
  where
    n = length m
    t = m !! 0 !! 0

-- | the site definition's clause (3) at one site/selection, for a block holding one or
-- more loans -- alone, or beside temporaries.
--
-- Write the input space as @[[Omega]] = H_loan (x) [[Omega']]@, where
-- @H_loan@ is the tensor product of the spaces of the loans /in the block/
-- and @[[Omega']]@ is everything else the site map reads (the visible
-- register and every loan outside the block). The site is safe when the
-- site map @sigma_s : [[Omega]] -> H_block (x) H_rest@ factors as
-- @sigma_s = B (x) W@ with @B : H_loan -> H_block@ an isometry (up to
-- scale) and @W : [[Omega']] -> H_rest@ linear.
--
-- Executably: build the exact bilinear map from
-- (the visible register (x) the loans outside the block, the loans in the
-- block) to the full state at the drop site, by running on every basis
-- vector of both sides; reshape it, grouping the block output with the
-- block's loan input on one axis and everything else on the other, into a
-- single matrix; test that reshaped matrix for rank <= 1 by embedding it as
-- a two-register state and reusing 'factorSplit's own minor test verbatim
-- (the same algebraic condition, on a different index grouping); on a
-- rank-1 hit, read the block/loan factor back as the
-- @dim H_block x dim H_loan@ matrix B and accept iff @B^dagger B@ is a
-- nonzero scalar multiple of the identity ('isScalarIdentity'). A run that
-- is zero at every probe combination is unreachable, mirroring
-- 'probeResultS'/'tempVerdictS's own PZero bookkeeping.
--
-- A block of temporaries only is the case @H_loan = C@, where B is the unit
-- vector the temporaries are left on; that case is 'tempVerdictS', and this
-- function refuses it rather than answer with a one-column B whose isometry
-- test is vacuous.
loanResultS :: (Eq a, Fractional a, Conj a)
            => VisSpec -> Prog a -> Site -> [Sel] -> (Verdict, Maybe (Matrix a))
loanResultS vis prog site sel
  | null blockLoans =
      error ("loanResultS: the site " ++ show site ++ " holds no live loan; \
             \a block of temporaries is decided by tempVerdictS")
  | null table || all (isZeroS . mAmp . snd) table = (Unreachable, Nothing)
  | otherwise = case factorSplit [dBlock * dLoan, dRest * dOther] [0] bigFlat of
      Nothing -> (Unsafe, Nothing)
      Just (rowVec, _) ->
        let bMat = [ [ rowVec !! levelsToIdx [dBlock, dLoan] [a, lk]
                     | lk <- [0 .. dLoan - 1] ]
                   | a <- [0 .. dBlock - 1] ]
        in if isScalarIdentity (matMul (daggerM bMat) bMat)
             then (Safe, Just bMat)
             else (Unsafe, Nothing)
  where
    -- 'liveLoansAtS' (through 'blockLoansAtS') answers which of the block's
    -- registers are loans and gives their dimensions; 'loansBefore'
    -- additionally carries the loans already dropped, which the machine
    -- must still be handed a state for and which still vary the rest of the
    -- state, so 'others' is taken from it and not from the live list.
    blockLoans = blockLoansAtS prog site
    others     = [ nd | nd@(n, _) <- loansBefore prog site
                 , n `notElem` map fst blockLoans ]
    loanDims   = map snd blockLoans
    otherDims  = map snd others
    dLoan      = product loanDims
    dv         = product (map snd vis)
    dOther     = dv * product otherDims
    combos     = [ (vi, oth, lk)
                 | vi <- [0 .. dv - 1], oth <- basisTuples others
                 , lk <- [0 .. dLoan - 1] ]
    table      = [ (k, blockProbeState vis prog site sel blockLoans others vi oth lk)
                 | k@(vi, oth, lk) <- combos ]
    m0         = snd (head' table)
    dimsAt     = mDims m0
    posBlock   = map (regPos m0) site
    dBlock     = product [ dimsAt !! p | p <- posBlock ]
    dRest      = product [ dd | (i, dd) <- zip [0 :: Int ..] dimsAt
                         , i `notElem` posBlock ]
    ojOf vi oth = levelsToIdx (dv : otherDims) (vi : oth)
    blockMats  = [ ((vi, oth, lk), reindexABOrd dimsAt posBlock (mAmp m))
                 | ((vi, oth, lk), m) <- table ]
    entryAt a lk b oj =
      case [ mat | ((vi', oth', lk'), mat) <- blockMats
                 , lk' == lk, ojOf vi' oth' == oj ] of
        (mat : _) -> mat !! a !! b
        []        -> 0
    bigFlat =
      [ entryAt a lk b oj
      | a  <- [0 .. dBlock - 1], lk <- [0 .. dLoan - 1]
      , b  <- [0 .. dRest - 1],  oj <- [0 .. dOther - 1]
      ]

-- | 'loanResultS' at a block that is one register, the shape the corpus
-- writes.
loanResult :: (Eq a, Fractional a, Conj a)
           => VisSpec -> Prog a -> String -> [Sel] -> (Verdict, Maybe (Matrix a))
loanResult vis prog x = loanResultS vis prog [x]

-- | The isometry B a safe loan site's drop reclaims with (its adjoint is the
-- reclaiming gate): 'Nothing' when the block holds no loan, the site is not
-- reachable, or the site is unsafe.
semanticLoanCertS :: (Eq a, Fractional a, Conj a)
                  => VisSpec -> Prog a -> Site -> [Sel] -> Maybe (Matrix a)
semanticLoanCertS vis prog site sel
  | not (any (isLoanTargetS prog site) site) = Nothing
  | otherwise = case loanResultS vis prog site sel of
      (Safe, cert) -> cert
      _            -> Nothing

semanticLoanCert :: (Eq a, Fractional a, Conj a)
                 => VisSpec -> Prog a -> String -> [Sel] -> Maybe (Matrix a)
semanticLoanCert vis prog target = semanticLoanCertS vis prog [target]

-- Selections

allSelections :: Int -> [[Sel]]
allSelections 0 = [[]]
allSelections n = [ c : r | c <- [SIn, SOut], r <- allSelections (n - 1) ]

-- | Number of top-level lifts strictly before the drop at a site.
liftDepthBeforeS :: Prog a -> Site -> Int
liftDepthBeforeS prog x = length [ () | Lift {} <- before ]
  where before = takeWhile ((/= Just x) . siteNames) prog

liftDepthBefore :: Prog a -> String -> Int
liftDepthBefore prog x = liftDepthBeforeS prog [x]

-- | The registers a command discards, if it discards any.
siteNames :: Cmd a -> Maybe Site
siteNames (Drop xs) = Just xs
siteNames _         = Nothing

-- | The program up to and including the drop site named @x@.
--
-- A site's verdict depends only on this prefix. Cutting there also keeps
-- the selection word honest: a site at lift depth l is indexed by an
-- l-bit word, and a whole-program walk could reach a later, deeper site
-- and consume a bit the word never had.
prefixThroughS :: Prog a -> Site -> Prog a
prefixThroughS prog x = before ++ take 1 after
  where (before, after) = break ((== Just x) . siteNames) prog

prefixThrough :: Prog a -> String -> Prog a
prefixThrough prog x = prefixThroughS prog [x]

-- | The drop sites of a program, in order. A site is a top-level command;
-- a drop inside an if branch would be no site at all, so it is refused.
dropSites :: Prog a -> [Site]
dropSites prog
  | any inBranch prog = error "dropSites: drop inside an if branch; a branch \
                              \allocates, lifts and drops nothing"
  | otherwise = [ x | Just x <- map siteNames prog ]
  where
    inBranch (IfBit _ t e) = any isDropOrIf (t ++ e)
    inBranch _             = False
    isDropOrIf (Drop _)      = True
    isDropOrIf (IfBit _ t e) = any isDropOrIf (t ++ e)
    isDropOrIf _             = False

-- Per-site, per-selection report

data DropReport = DropReport
  { drSite :: Site
  , drRows :: [([Sel], Verdict)]
  } deriving Show

verdict :: (Eq a, Fractional a, Conj a) => VisSpec -> Prog a -> [DropReport]
verdict vis prog = requireFlat SurfaceFragment (visScope vis) prog `seq`
  [ DropReport x [ (sel, semanticVerdictS vis prog x sel)
                 | sel <- allSelections (liftDepthBeforeS prog x) ]
  | x <- dropSites prog ]

-- | Weight of the selected branch on a given test input, exact and unnormalized.
branchWeight :: (Eq a, Num a, Conj a) => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> a
branchWeight vis prog target sel inp =
  norm2S (mAmp (runStmts (initMach vis inp) prog sel (Just [target])))
