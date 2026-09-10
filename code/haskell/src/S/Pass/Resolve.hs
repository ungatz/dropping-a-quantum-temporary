-- Resolve.hs: pass 3 of the static pass, and the form it makes.
--
-- One record fixes every measurement outcome, so under a record no lift is
-- left to run: it is a restriction of its register to the levels the
-- outcome kept. This pass emits one lift-free residual program per record.

module S.Pass.Resolve
  ( Step (..), Record (..), resolve, transferred, interpRecord ) where

import S.Lang.QState
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass.Cut
import S.Pass.Park

-- | A step of a residual program: a stretch of ordinary commands, or the
-- restriction a resolved lift became.
data Step a = Keep String [Int] | Run (Prog a)
  deriving Show

data Record a = Record
  { rSel   :: [Sel]
  , rStore :: [(String, Int)]   -- ^ the lifted bits, all known up front
  , rSteps :: [Step a]
  } deriving Show

-- | Resolve the lifts under every record. With no lift there is one record
-- and nothing to check; with a lift, the residual is faithful only when the
-- visible action is right-invertible (@B-right-invertible@).
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
            d    = maybe (error ("resolve: no register " ++ y)) id (lookup y env')
            kept = if ch == SIn then blk
                   else [ l | l <- [0 .. d - 1], l `notElem` blk ]
        in run seg ++ [Keep y kept] ++ go env' more rest
      _ -> error "resolve: record and lifts do not match"
    run seg = [ Run seg | not (null seg) ]
    dimsOf (New n d)        = [(n, d)]
    dimsOf (NewDirty n d _) = [(n, d)]
    dimsOf _                = []

-- | The state the first lift hands to the continuation: @g@
-- cut down to the block the outcome kept, or @g@ itself when that lift
-- measured another register.
transferred :: Num a => Parked a -> Record a -> StateV a
transferred p r = case rSteps r of
  Keep y ks : _ | y == pSite p ->
    [ if i `elem` ks then a else 0 | (i, a) <- zip [0 ..] (pLine p) ]
  _ -> pLine p

-- | A residual program, run from @w (x) g@: restrict and run as the steps
-- say. The visible argument is what the prefix delivered, so it is @B v@
-- where @v@ was the program's input.
interpRecord :: (Eq a, Num a) => VisSpec -> Parked a -> Record a -> StateV a -> Mach a
interpRecord vis p r w = foldl go m0 (rSteps r)
  where
    m0 = Mach (map fst vis ++ [pSite p]) (map snd vis ++ [pDim p])
              (tensorS w (pLine p)) (rStore r) []
    go m (Keep y ks) = m { mAmp = projectLevels (mDims m) (regPos m y) ks (mAmp m) }
    go m (Run seg)   = foldl step m seg
