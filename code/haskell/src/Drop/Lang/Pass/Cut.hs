-- Drop.Lang.Pass.Cut: pass 1, the program up to the drop, split at its first lift.
--
-- Question: What does a drop depend on, and where does a measurement first enter it?
-- Answer:   A drop's verdict depends only on the commands before it, so cut keeps those and
--           nothing after. It splits them at the first lift: the prefix, which has no measurement
--           in it, and the rest, which starts at that lift. The next pass parks the prefix; the
--           one after resolves the rest. cut declines by name, rather than answering, when the
--           program is outside what the chain covers: the target is a loan, another register of
--           the program is a loan, a lift sits inside an if, or the target is not allocated in
--           the prefix. Running the two halves in turn is running the program to the drop.
-- Paper:    thm:perrecord (the criterion on one record, which the chain decides record by record),
--           sec:meas:leaf (the site read on one record), sec:residual (compiling the
--           record-dependent reclaim, which also works record by record).
-- Shapes:   Cut a  one drop site cut in two: cSite (the dropped register), cPrefix (the commands
--                   before the first lift) and cRest (the first lift on, up to the drop).

module Drop.Lang.Pass.Cut
  ( Cut (..), cut, interpCut
  , isLift, allocations
  ) where

import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion

-- The cut ---------------------------------------------------------------------

-- | The program up to the drop, split at its first lift.
data Cut a = Cut
  { cSite   :: String
  , cPrefix :: Prog a    -- ^ everything before the first lift, so lift-free
  , cRest   :: Prog a    -- ^ the first lift onwards, up to the drop
  } deriving Show

-- A cut written by hand: a temporary allocated, no lift yet, nothing after.
-- >>> Cut "a" [New "a" 2] [] :: Cut Rational
-- Cut {cSite = "a", cPrefix = [New "a" 2], cRest = []}

-- | Is this command a lift?
isLift :: Cmd a -> Bool
isLift (Lift {}) = True
isLift _         = False

-- >>> isLift (Lift "p" "t" [0] :: Cmd Rational)
-- True
-- >>> isLift (New "t" 2 :: Cmd Rational)
-- False

-- | True when some lift is nested under an @if@.
liftInside :: Prog a -> Bool
liftInside = any f
  where f (IfBit _ thn els) = any isL thn || any isL els
        f _                 = False
        isL c               = isLift c || f c

-- A lift at the top level is not inside an if, even when an if follows it.
-- >>> :m + Drop.Lang.Programs.TempAnd
-- >>> liftInside andUncomputedByMeasurement
-- False
-- >>> liftInside ([IfBit (GBit True) [Lift "q" "t" [0]] []] :: Prog Rational)
-- True
-- >>> liftInside ([IfBit (GBit True) [IfBit (GBit True) [] [Lift "q" "t" [0]]] []] :: Prog Rational)
-- True

-- | The names a stretch of commands allocates, in order: temporaries and loans.
allocations :: Prog a -> [String]
allocations seg = [ n | c <- seg, n <- alloc c ]
  where alloc (New n _)        = [n]
        alloc (NewState n _ _) = [n]
        alloc (Loan n _)       = [n]
        alloc _                = []

-- >>> allocations andComputed
-- ["a"]
-- >>> allocations ([New "a" 2, NewState "b" 2 [0, 1], Loan "l" 2, Drop ["a"]] :: Prog Rational)
-- ["a","b","l"]
-- >>> allocations ([] :: Prog Rational)
-- []

-- | Cut the program at the drop of @x@. Declines when a lift sits inside an
-- @if@ (a record allots one bit per top-level lift, so a nested lift has no
-- bit), when the temporary is allocated after the first lift, since then the
-- prefix holds no state for the check to be about, when some /other/ register
-- of the program is a loan (the pass runs the prefix on one visible probe at
-- a time through 'initMach', which has no arrival state to give a loan, and
-- parking a temporary that a live loan can move is anyway a statement about a
-- wider probe space than this chain carries), or when the target is a loan:
-- the parked-line form (a prefix that leaves the temporary constant whatever
-- the visible input) is not the loan's theorem (the site map factors as an
-- isometry tensor a map of the rest, not a fixed ray tensor a map of the
-- visible input; see the loan path of Drop.Lang.Criterion), a different
-- theorem this chain does not state, so it declines by name rather than
-- answering.
cut :: Prog a -> String -> Either String (Cut a)
cut prog x
  -- refusal: a target that is not the one register of a drop site of the program
  | [x] `notElem` dropSites prog   = error ("cut: no drop site named " ++ x)
  | isLoanTarget prog x            = Left "target-is-a-loan"
  | not (null (loansBefore prog [x])) = Left "program-has-a-loan"
  | liftInside upTo                = Left "lifts-are-top-level"
  | x `notElem` allocations prefix = Left "target-allocated-before-lifts"
  | otherwise                      = Right (Cut x prefix rest)
  where
    upTo           = takeWhile ((/= Just [x]) . siteNames) prog
    (prefix, rest) = break isLift upTo

-- The abstract's temporary AND: three commands before its lift, two from it on.
-- >>> :m + Drop.Lang.Render
-- >>> let showCmds = mapM_ (putStrLn . renderCmd)
-- >>> let showCut c = putStrLn "prefix:" >> showCmds (cPrefix c) >> putStrLn "rest:" >> showCmds (cRest c)
-- >>> either putStrLn showCut (cut andUncomputedByMeasurement "a")
-- prefix:
-- new a : [2] @ |0>;
-- CCX x y a;
-- H a;
-- rest:
-- m = lift[{1}] a;
-- if m { diag x y (1, 1, 1, -1); } else { }

-- With no lift there is nothing to split: the prefix is the whole program up to the drop.
-- >>> either putStrLn showCut (cut andComputed "a")
-- prefix:
-- new a : [2] @ |0>;
-- CCX x y a;
-- rest:

-- The repeat-until-success step: two commands each side of its lift.
-- >>> :m + Drop.Lang.Programs.RUS
-- >>> fmap (\c -> (cSite c, length (cPrefix c), length (cRest c))) (cut rusProg "t")
-- Right ("t",2,2)

-- One decline per hypothesis, each on the smallest program that makes it.
-- The target is a loan.
-- >>> fmap (const ()) (cut ([Loan "a" 2, Drop ["a"]] :: Prog Rational) "a")
-- Left "target-is-a-loan"

-- Another register is a loan.
-- >>> fmap (const ()) (cut ([Loan "l" 2, New "t" 2, Drop ["t"]] :: Prog Rational) "t")
-- Left "program-has-a-loan"

-- A lift under an if.
-- >>> fmap (const ()) (cut ([New "t" 2, IfBit (GBit True) [Lift "q" "t" [0]] [], Drop ["t"]] :: Prog Rational) "t")
-- Left "lifts-are-top-level"

-- The temporary is allocated after the first lift.
-- >>> fmap (const ()) (cut ([Lift "p" "x" [0], New "t" 2, Drop ["t"]] :: Prog Rational) "t")
-- Left "target-allocated-before-lifts"

-- | Running the two halves in turn is running the program to the drop.
interpCut :: (Eq a, Num a) => VisSpec -> Cut a -> [Sel] -> StateV a -> Mach a
interpCut vis c sel inp =
  runStmts (runStmts (initMach vis inp) (cPrefix c) [] Nothing) (cRest c) sel Nothing

-- Cut, then run: the state at the drop is the source's, under each selection.
-- >>> let same c sel = mAmp (interpCut visXY c sel (ket [2, 2] [1, 1])) == mAmp (interpSource visXY andUncomputedByMeasurement "a" sel (ket [2, 2] [1, 1]))
-- >>> either (const []) (\c -> map (same c) (allSelections 1)) (cut andUncomputedByMeasurement "a")
-- [True,True]
