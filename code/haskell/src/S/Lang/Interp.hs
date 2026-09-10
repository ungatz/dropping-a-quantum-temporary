-- Interp.hs: the definitional interpreter and the drop criterion.
--
-- The criterion: a drop of x is safe when the joint state
-- factors as a fixed temporary state tensored with a linear map of the
-- visible input, checked at dim + 1 test inputs via QState's exact minor
-- test. A zero-weight test input is skipped, not counted as a failure.

module S.Lang.Interp where

import Data.List (elemIndex)
import S.Lang.Ring
import S.Lang.QState
import S.Lang.Syntax

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
  } deriving Show

initMach :: VisSpec -> StateV a -> Mach a
initMach vis amp = Mach (map fst vis) (map snd vis) amp [] []

regPos :: Mach a -> String -> Int
regPos m x = case elemIndex x (mNames m) of
  Just i  -> i
  Nothing -> error ("regPos: no register " ++ x)

-- | The surface language refuses a repeated binder (see S.Lang.Parser), but a
-- program built directly as a list of commands does not go through it. Two
-- wires with one name are indistinguishable to 'regPos', which always finds
-- the first, so the machine refuses them here as well rather than compute a
-- confident wrong answer.
duplicateName :: String -> String -> a
duplicateName what x =
  error (what ++ ": register " ++ x ++ " is already in scope; a name is \
         \allocated once, and reuse of the wire is the allocator's business")

step :: (Eq a, Num a) => Mach a -> Cmd a -> Mach a
step m c = case c of
  New x d
    | x `elem` mNames m -> duplicateName "new" x
    | otherwise ->
        m { mNames = mNames m ++ [x]
          , mDims  = mDims m ++ [d]
          , mAmp   = tensorS (mAmp m) (ket [d] [0]) }
  NewDirty x d st
    | x `elem` mNames m -> duplicateName "newdirty" x
    | otherwise ->
        m { mNames = mNames m ++ [x]
          , mDims  = mDims m ++ [d]
          , mAmp   = tensorS (mAmp m) st }
  Gate g xs ->
    m { mAmp = applyGate (mDims m) g (map (regPos m) xs) (mAmp m) }
  Drop _ -> m                        -- denotationally the identity
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
  IfBit p thn els ->
    case lookup p (mStore m) of
      Nothing -> error ("ifbit: parameter " ++ p ++ " not lifted")
      Just b  -> foldl step m (if b == 1 then thn else els)

-- | Run a program, optionally halting just before the named drop site, the
-- point at which the criterion looks.
runStmts :: (Eq a, Num a) => Mach a -> Prog a -> [Sel] -> Maybe String -> Mach a
runStmts m0 prog sel stop = go (m0 { mSel = sel }) prog
  where
    go m [] = case stop of
      Nothing -> m
      Just x  -> error ("runStmts: no drop site named " ++ x)
    go m (c : _) | Just x <- siteName c, Just x == stop = m
    go m (c : cs) = go (step m c) cs

-- | The state at a drop site, for a record and a visible input: what every
-- form of the static pass (S.Pass) has to agree about.
interpSource :: (Eq a, Num a)
             => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> Mach a
interpSource vis prog x sel inp = runStmts (initMach vis inp) prog sel (Just x)

-- Test inputs

-- | The visible basis plus the all-ones superposition: dim + 1 test inputs.
probesFor :: Num a => VisSpec -> [(String, StateV a)]
probesFor vis =
  [ ("e" ++ show j, [ if k == j then 1 else 0 | k <- [0 .. dv - 1] ])
  | j <- [0 .. dv - 1] ]
  ++ [("sum", replicate dv 1)]
  where dv = product (map snd vis)

-- Criterion

data Verdict = Admissible | Inadmissible | Unreachable deriving (Eq, Show)

data ProbeResult a = PZero | PFail | PLine (StateV a) deriving (Eq, Show)

-- | Factor the target register out of the state at the drop site.
probeResult :: (Eq a, Fractional a)
            => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> ProbeResult a
probeResult vis prog target sel inp =
  let m = runStmts (initMach vis inp) prog sel (Just target)
  in if isZeroS (mAmp m) then PZero
     else case factorSplit (mDims m) [regPos m target] (mAmp m) of
            Nothing       -> PFail
            Just (vA, _)  -> PLine (canonicalLine vA)

-- | Every test input's probe at one site under one selection.
probesAt :: (Eq a, Fractional a)
         => VisSpec -> Prog a -> String -> [Sel] -> [ProbeResult a]
probesAt vis prog target sel =
  [ probeResult vis prog target sel inp | (_, inp) <- probesFor vis ]

-- | The criterion read off a run of probes: the surviving ones must all leave
-- the temporary constant on one and the same line. A site with no surviving
-- input is unreachable, and an unreachable site is safe.
classify :: Eq a => [ProbeResult a] -> Verdict
classify rs = case [ r | r <- rs, r /= PZero ] of
  []   -> Unreachable
  live | all isLine live && allEqual [ l | PLine l <- live ] -> Admissible
       | otherwise -> Inadmissible
  where
    isLine (PLine _) = True
    isLine _         = False

-- | The criterion's answer at one site under one selection.
semanticVerdict :: (Eq a, Fractional a)
                => VisSpec -> Prog a -> String -> [Sel] -> Verdict
semanticVerdict vis prog target sel = classify (probesAt vis prog target sel)

-- | The line the temporary is left constant on, when the criterion accepts
-- the site. One run of the probes answers both questions, so the line is read
-- off the same results the verdict was taken from.
semanticParked :: (Eq a, Fractional a)
               => VisSpec -> Prog a -> String -> [Sel] -> Maybe (StateV a)
semanticParked vis prog target sel
  | classify rs /= Admissible = Nothing
  | otherwise = case [ l | PLine l <- rs ] of
      (l : _) -> Just l
      []      -> Nothing
  where rs = probesAt vis prog target sel

allEqual :: Eq b => [b] -> Bool
allEqual []       = True
allEqual (x : xs) = all (== x) xs

-- Selections

allSelections :: Int -> [[Sel]]
allSelections 0 = [[]]
allSelections n = [ c : r | c <- [SIn, SOut], r <- allSelections (n - 1) ]

-- | True when some command under an @if@ satisfies @q@.
--
-- 'dropSites', 'liftDepthBefore' and 'prefixThrough' read the top level only,
-- and 'runStmts' steps an 'IfBit' whole, so a drop inside a branch is walked
-- past rather than stopped at and a lift inside one has no bit in the record
-- word. Both are refused rather than answered confidently; S.Pass.Cut declines
-- the lift case by name.
nestedBy :: (Cmd a -> Bool) -> Prog a -> Bool
nestedBy q = any f
  where f (IfBit _ thn els) = any g thn || any g els
        f _                 = False
        g c                 = q c || f c

-- | Number of top-level lifts strictly before the drop of @x@.
liftDepthBefore :: Prog a -> String -> Int
liftDepthBefore prog x = length [ () | Lift {} <- before ]
  where before = takeWhile ((/= Just x) . siteName) prog

-- | The name a command discards, if it discards one.
siteName :: Cmd a -> Maybe String
siteName (Drop x) = Just x
siteName _        = Nothing

-- | The program up to and including the drop site named @x@.
--
-- A site's verdict depends only on this prefix. Cutting there also keeps
-- the selection word honest: a site at lift depth l is indexed by an
-- l-bit word, and a whole-program walk could reach a later, deeper site
-- and consume a bit the word never had.
prefixThrough :: Prog a -> String -> Prog a
prefixThrough prog x = before ++ take 1 after
  where (before, after) = break ((== Just x) . siteName) prog

dropSites :: Prog a -> [String]
dropSites prog = [ x | Just x <- map siteName prog ]

-- Per-site, per-selection report

data DropReport = DropReport
  { drSite :: String
  , drRows :: [([Sel], Verdict)]
  } deriving Show

verdict :: (Eq a, Fractional a) => VisSpec -> Prog a -> [DropReport]
verdict vis prog
  | nestedBy nestedSite prog =
      error "verdict: a drop or a lift inside an if is not read by this walk; \
            \lift the branch to the top level"
  | otherwise =
      [ DropReport x [ (sel, semanticVerdict vis prog x sel)
                     | sel <- allSelections (liftDepthBefore prog x) ]
      | x <- dropSites prog ]
  where
    nestedSite (Lift {}) = True
    nestedSite (Drop _)  = True
    nestedSite _         = False

-- | Weight of the selected branch on a given test input, exact and unnormalized.
branchWeight :: (Eq a, Num a, Conj a) => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> a
branchWeight vis prog target sel inp =
  norm2S (mAmp (runStmts (initMach vis inp) prog sel (Just target)))
