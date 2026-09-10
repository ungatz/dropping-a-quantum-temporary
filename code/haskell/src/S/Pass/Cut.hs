-- Cut.hs: pass 1 of the static pass, and the form it makes.
--
-- The verdict at a drop depends on the program up to that drop, and the
-- theorem behind the check is about what the run has already
-- measured. So the first pass throws away what cannot matter and splits
-- what is left at the first lift.

module S.Pass.Cut
  ( Cut (..), cut, interpCut
  , isLift, liftInside, allocations
  ) where

import S.Lang.QState
import S.Lang.Syntax
import S.Lang.Interp

-- | The program up to the drop, split at its first lift.
data Cut a = Cut
  { cSite   :: String
  , cPrefix :: Prog a    -- ^ everything before the first lift, so lift-free
  , cRest   :: Prog a    -- ^ the first lift onwards, up to the drop
  } deriving Show

-- | Fails when a lift sits inside an @if@ (a record allots one bit per
-- top-level lift, so a nested lift has no bit) or when the temporary is
-- allocated after the first lift, since then the prefix holds no state for
-- the check to be about.
cut :: Prog a -> String -> Either String (Cut a)
cut prog x
  | x `notElem` dropSites prog     = error ("cut: no drop site named " ++ x)
  | liftInside upTo                = Left "lifts-are-top-level"
  | x `notElem` allocations prefix = Left "target-allocated-before-lifts"
  | otherwise                      = Right (Cut x prefix rest)
  where
    upTo           = takeWhile ((/= Just x) . siteName) prog
    (prefix, rest) = break isLift upTo

-- | Running the two halves in turn is running the program to the drop.
interpCut :: (Eq a, Num a) => VisSpec -> Cut a -> [Sel] -> StateV a -> Mach a
interpCut vis c sel inp =
  runStmts (runStmts (initMach vis inp) (cPrefix c) [] Nothing) (cRest c) sel Nothing

isLift :: Cmd a -> Bool
isLift (Lift {}) = True
isLift _         = False

-- | True when some lift is nested under an @if@. One traversal, shared with
-- the machine's own refusal, so the two cannot drift apart.
liftInside :: Prog a -> Bool
liftInside = nestedBy isLift

allocations :: Prog a -> [String]
allocations seg = [ n | c <- seg, n <- alloc c ]
  where alloc (New n _)        = [n]
        alloc (NewDirty n _ _) = [n]
        alloc _                = []
