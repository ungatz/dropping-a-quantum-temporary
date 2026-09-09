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

initMach :: Num a => VisSpec -> StateV a -> Mach a
initMach vis amp = Mach (map fst vis) (map snd vis) amp [] []

regPos :: Mach a -> String -> Int
regPos m x = case elemIndex x (mNames m) of
  Just i  -> i
  Nothing -> error ("regPos: no register " ++ x)

step :: (Eq a, Num a) => Mach a -> Cmd a -> Mach a
step m c = case c of
  New x d ->
    m { mNames = mNames m ++ [x]
      , mDims  = mDims m ++ [d]
      , mAmp   = tensorS (mAmp m) (ket [d] [0]) }
  NewDirty x d st ->
    m { mNames = mNames m ++ [x]
      , mDims  = mDims m ++ [d]
      , mAmp   = tensorS (mAmp m) st }
  Gate g xs ->
    m { mAmp = applyGate (mDims m) g (map (regPos m) xs) (mAmp m) }
  Drop _ -> m                        -- denotationally the identity
  Lift p x block ->
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

-- | The criterion's answer at one site under one selection: rerun the
-- program on every test input and ask whether the surviving ones all leave
-- the temporary constant on one and the same line.
semanticVerdict :: (Eq a, Fractional a)
                => VisSpec -> Prog a -> String -> [Sel] -> Verdict
semanticVerdict vis prog target sel =
  let rs   = [ probeResult vis prog target sel inp | (_, inp) <- probesFor vis ]
      live = [ r | r <- rs, r /= PZero ]
  in case live of
       [] -> Unreachable
       _  | all isLine live && allEqual [ l | PLine l <- live ] -> Admissible
          | otherwise -> Inadmissible
  where
    isLine (PLine _) = True
    isLine _         = False

-- | The line the temporary is left constant on, when the criterion accepts
-- the site. Reuses the work 'semanticVerdict' already does on its way to a
-- Boolean, instead of discarding it.
semanticParked :: (Eq a, Fractional a)
               => VisSpec -> Prog a -> String -> [Sel] -> Maybe (StateV a)
semanticParked vis prog target sel
  | semanticVerdict vis prog target sel /= Admissible = Nothing
  | otherwise = case [ l | PLine l <- probes ] of
      (l : _) -> Just l
      []      -> Nothing
  where probes = [ probeResult vis prog target sel inp | (_, inp) <- probesFor vis ]

allEqual :: Eq b => [b] -> Bool
allEqual []       = True
allEqual (x : xs) = all (== x) xs

-- Selections

allSelections :: Int -> [[Sel]]
allSelections 0 = [[]]
allSelections n = [ c : r | c <- [SIn, SOut], r <- allSelections (n - 1) ]

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
verdict vis prog =
  [ DropReport x [ (sel, semanticVerdict vis prog x sel)
                 | sel <- allSelections (liftDepthBefore prog x) ]
  | x <- dropSites prog ]

-- | Weight of the selected branch on a given test input, exact and unnormalized.
branchWeight :: (Eq a, Num a, Conj a) => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> a
branchWeight vis prog target sel inp =
  norm2S (mAmp (runStmts (initMach vis inp) prog sel (Just target)))
