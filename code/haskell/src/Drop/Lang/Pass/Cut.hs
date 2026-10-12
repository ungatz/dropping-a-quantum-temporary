-- Cut.hs: pass 1 of the static pass, and the form it makes.
--
-- The verdict at a drop depends on the program up to that drop, and the
-- theorem behind the table (the record-dependent reclaim section) is about what the run has already
-- measured. So the first pass throws away what cannot matter and splits
-- what is left at the first lift.

module Drop.Lang.Pass.Cut
  ( Cut (..), cut, interpCut
  , isLift, liftInside, allocations
  ) where

import Drop.Lang.QState
import Drop.Lang.Syntax
import Drop.Lang.Interp

-- | The program up to the drop, split at its first lift.
data Cut a = Cut
  { cSite   :: String
  , cPrefix :: Prog a    -- ^ everything before the first lift, so lift-free
  , cRest   :: Prog a    -- ^ the first lift onwards, up to the drop
  } deriving Show

-- | Fails when a lift sits inside an @if@ (a record allots one bit per
-- top-level lift, so a nested lift has no bit), when the temporary is
-- allocated after the first lift, since then the prefix holds no state for
-- the check to be about, when some /other/ register of the program is a
-- loan (the pass runs the prefix on one visible probe at a time through
-- 'initMach', which has no arrival state to give a loan, and parking a
-- temporary that a live loan can move is anyway a statement about a wider
-- probe space than this chain carries), or when the target is a loan:
-- Theorem 7.1 (a
-- prefix that leaves the temporary constant whatever the visible input) is
-- not the loan's theorem (the site map factors as an isometry tensor a map
-- of the rest, not a fixed ray tensor a map of the visible input, see
-- Drop.Lang.Interp's "Loans" section) -- a different theorem this pass chain
-- does not state, so it declines by name rather than answering.
cut :: Prog a -> String -> Either String (Cut a)
cut prog x
  | [x] `notElem` dropSites prog   = error ("cut: no drop site named " ++ x)
  | isLoanTarget prog x            = Left "target-is-a-loan"
  | not (null (loansBefore prog [x])) = Left "program-has-a-loan"
  | liftInside upTo                = Left "lifts-are-top-level"
  | x `notElem` allocations prefix = Left "target-allocated-before-lifts"
  | otherwise                      = Right (Cut x prefix rest)
  where
    upTo           = takeWhile ((/= Just [x]) . siteNames) prog
    (prefix, rest) = break isLift upTo

-- | Running the two halves in turn is running the program to the drop.
interpCut :: (Eq a, Num a) => VisSpec -> Cut a -> [Sel] -> StateV a -> Mach a
interpCut vis c sel inp =
  runStmts (runStmts (initMach vis inp) (cPrefix c) [] Nothing) (cRest c) sel Nothing

isLift :: Cmd a -> Bool
isLift (Lift {}) = True
isLift _         = False

-- | True when some lift is nested under an @if@.
liftInside :: Prog a -> Bool
liftInside = any f
  where f (IfBit _ thn els) = any isL thn || any isL els
        f _                 = False
        isL c               = isLift c || f c

allocations :: Prog a -> [String]
allocations seg = [ n | c <- seg, n <- alloc c ]
  where alloc (New n _)        = [n]
        alloc (NewState n _ _) = [n]
        alloc (Loan n _)       = [n]
        alloc _                = []
