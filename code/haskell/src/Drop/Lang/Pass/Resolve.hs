-- Drop.Lang.Pass.Resolve: pass 3, one lift-free residual program per record.
--
-- Question: What does the rest of the program do under one record of its lifts?
-- Answer:   One record fixes every measurement outcome in advance, so under a record no lift is
--           left to run. A lift becomes a restriction: its register keeps only the levels the
--           outcome kept (the lift's block when the bit is 1, the other levels when it is 0),
--           and the stretches of ordinary commands between lifts run as they are. resolve emits
--           one such residual program per selection of the lifts, with the lifted bits recorded
--           up front for the guards that read them. With no lift there is one record and
--           nothing to check; with a lift, resolve declines by name (B-right-invertible) when
--           the visible action B of the parked prefix is not onto.
-- Paper:    thm:perrecord (the criterion on one record), sec:meas:leaf (the site on one record),
--           app:meas-tree (lifts and the tree of runs, step by step).
-- Shapes:   Step a    one step of a residual program: Keep r levels (restrict r to those levels)
--                     or Run commands (a stretch of ordinary commands).
--           Record a  one selection of the lifts: rSel (the choices), rStore (the lifted bits,
--                     name and 0 or 1) and rSteps (the residual program).

module Drop.Lang.Pass.Resolve
  ( Step (..), Record (..), resolve, transferred, interpRecord ) where

import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Pass.Cut
import Drop.Lang.Pass.Park

-- The residual program ---------------------------------------------------------

-- | A step of a residual program: a stretch of ordinary commands, or the
-- restriction a resolved lift became.
data Step a = Keep String [Int] | Run (Prog a)
  deriving Show

-- One step of each kind: keep levels 0 and 1 of t, then run one command.
-- >>> [Keep "t" [0, 1], Run [New "u" 2]] :: [Step Rational]
-- [Keep "t" [0,1],Run [New "u" 2]]

data Record a = Record
  { rSel   :: [Sel]
  , rStore :: [(String, Int)]   -- ^ the lifted bits, all known up front
  , rSteps :: [Step a]
  } deriving Show

-- A record written by hand: the bit 1 for the lift p, which kept levels 0 and 1.
-- >>> Record [SIn] [("p", 1)] [Keep "t" [0, 1]] :: Record Rational
-- Record {rSel = [SIn], rStore = [("p",1)], rSteps = [Keep "t" [0,1]]}

-- | Resolve the lifts under every record. With no lift there is one record
-- and nothing to check; with a lift, the parked line needs the visible action
-- to be right-invertible (@B-right-invertible@).
resolve :: (Eq a, Fractional a) => VisSpec -> Parked a -> Either String [Record a]
resolve vis p
  | null (pRest p)                    = Right [Record [] [] []]
  | not (rightInvertible (pAction p)) = Left "B-right-invertible"
  | otherwise = Right [ record sel | sel <- allSelections (length lifts) ]
  where
    lifts = filter isLift (pRest p)
    env0  = vis ++ [(pSite p, pDim p)]
    record sel = Record sel [ (q, selBit ch) | (Lift q _ _, ch) <- zip lifts sel ]
                            (go env0 (pRest p) sel)
    go env cmds sel = case (break isLift cmds, sel) of
      ((seg, []), _) -> run seg
      ((seg, Lift _ y blk : more), ch : rest) ->
        let env' = env ++ [ nd | c <- seg, nd <- dimsOf c ]
            -- refusal: a lift of a register that is neither visible nor allocated before it
            d    = maybe (error ("resolve: no register " ++ y)) id (lookup y env')
            kept = if ch == SIn then blk
                   else [ l | l <- [0 .. d - 1], l `notElem` blk ]
        in run seg ++ [Keep y kept] ++ go env' more rest
      -- impossible: record is given one choice per top-level lift, and go takes one per lift it meets
      _ -> error "resolve: record and lifts do not match"
    run seg = [ Run seg | not (null seg) ]
    dimsOf (New n d)        = [(n, d)]
    dimsOf (NewState n d _) = [(n, d)]
    dimsOf (Loan n d)   = [(n, d)]
    dimsOf _                = []

-- With no lift in the rest there is one record, and it has no steps.
-- >>> :m + Drop.Lang.Programs.RUS Drop.Lang.Programs.DJ
-- >>> let parkedDj = cut (djPaper fId) "t" >>= park visDJ
-- >>> fmap (map (\r -> (rSel r, rStore r, length (rSteps r)))) (parkedDj >>= resolve visDJ)
-- Right [([],[],0)]

-- The repeat-until-success step has one lift, so two records: bit 1 keeps the block {0,1}
-- of t, bit 0 keeps the rest {2}; each then runs the if as one stretch of commands.
-- >>> let stepText s = case s of { Keep y ks -> "keep " ++ y ++ " " ++ show ks; Run seg -> "run " ++ show (length seg) ++ " commands" }
-- >>> let parkedRus = either error id (cut rusProg "t" >>= park visR)
-- >>> let recsRus = either error id (resolve visR parkedRus)
-- >>> mapM_ (\r -> print (rSel r, rStore r, map stepText (rSteps r))) recsRus
-- ([SIn],[("p",1)],["keep t [0,1]","run 1 commands"])
-- ([SOut],[("p",0)],["keep t [2]","run 1 commands"])

-- A visible action that loses information is not onto: the pass declines before resolving anything.
-- It is not reached by any corpus program; a gate that maps both basis inputs to one state does it.
-- >>> let notOnto = [New "t" 2, Gate [[1, 1], [1, 1]] ["x"], Lift "p" "t" [0], Drop ["t"]] :: Prog Rational
-- >>> fmap (const ()) (cut notOnto "t" >>= park [("x", 2)] >>= resolve [("x", 2)])
-- Left "B-right-invertible"

-- | The state the first lift hands to the continuation: @g@ cut down to the
-- block the outcome kept, or @g@ itself when that lift measured another
-- register.
transferred :: Num a => Parked a -> Record a -> StateV a
transferred p r = case rSteps r of
  Keep y ks : _ | y == pSite p ->
    [ if i `elem` ks then a else 0 | (i, a) <- zip [0 ..] (pLine p) ]
  _ -> pLine p

-- The line (1, 1, 1/2) cut to the kept levels: levels 0 and 1 under bit 1, level 2 under bit 0.
-- >>> map (transferred parkedRus) recsRus
-- [[1 % 1,1 % 1,0 % 1],[0 % 1,0 % 1,1 % 2]]

-- | A residual program, run from @w (x) g@: restrict and run as the steps
-- say. The visible argument is what the prefix delivered, so it is @B v@
-- where @v@ was the program's input.
interpRecord :: (Eq a, Num a) => VisSpec -> Parked a -> Record a -> StateV a -> Mach a
interpRecord vis p r w = foldl go m0 (rSteps r)
  where
    m0 = Mach (map fst vis ++ [pSite p]) (map snd vis ++ [pDim p])
              (tensorS w (pLine p)) (rStore r) [] [] []
    go m (Keep y ks) = m { mAmp = projectLevels (mDims m) (regPos m y) ks (mAmp m) }
    go m (Run seg)   = foldl step m seg

-- A residual program run from B v agrees with the source run from v, under each record.
-- >>> let sameAsSource r sel = mAmp (interpRecord visR parkedRus r (mulMV (pAction parkedRus) (ket [3] [0]))) == mAmp (interpSource visR rusProg "t" sel (ket [3] [0]))
-- >>> map (\r -> sameAsSource r (rSel r)) recsRus
-- [True,True]
