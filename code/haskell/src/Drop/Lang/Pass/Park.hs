-- Park.hs: pass 2 of the static pass, and the form it makes.
--
-- Theorem 7.1 is about a prefix that leaves the temporary in a fixed state
-- whatever the visible input. This pass decides whether the prefix does
-- that, and if it does it replaces the prefix by the two things the theorem
-- names: the line the temporary is left on, and the map the rest received.

module Drop.Lang.Pass.Park
  ( Parked (..), park, interpParked, rightInvertible, mulMV ) where

import Drop.Lang.QState
import Drop.Lang.Syntax
import Drop.Lang.Interp
import Drop.Lang.Pass.Cut

-- | The prefix, as the pair @(g, B)@ with @v |-> g (x) B v@: whatever comes
-- in, the temporary comes out on the line of @g@.
data Parked a = Parked
  { pSite   :: String
  , pDim    :: Int
  , pLine   :: StateV a   -- ^ g, scaled so its first nonzero entry is 1
  , pAction :: Matrix a   -- ^ B, one column per visible basis input
  , pRest   :: Prog a
  } deriving Show

-- | Run the prefix on the test inputs and factor the temporary out of each
-- result. Fails (@prefix-parks@) when one input leaves the temporary
-- entangled, when two inputs leave it on different lines, or when a second
-- temporary is still live, since then what is left beside the temporary is
-- not the visible register and the theorem's B does not exist.
park :: (Eq a, Fractional a) => VisSpec -> Cut a -> Either String (Parked a)
park vis c = case sequence splits of
  Just fs@((t0, _) : _)
    | all ((== dvis) . length . snd) fs
    , allEqual [ canonicalLine t | (t, _) <- fs ] ->
        Right (Parked x dt (canonicalLine t0) (columns fs) (cRest c))
  _ -> Left "prefix-parks"
  where
    x    = cSite c
    -- A second temporary still live at the cut leaves a factor that is not
    -- the visible register, so the theorem's B does not exist and the pass
    -- declines rather than calling that factor B.
    dvis = product (map snd vis)
    runs = [ runStmts (initMach vis inp) (cPrefix c) [] Nothing
           | (_, inp) <- probesFor vis ]
    dt   = case runs of
             (m : _) -> mDims m !! regPos m x
             []      -> error "park: no test inputs"
    splits = [ factorSplit (mDims m) [regPos m x] (mAmp m) | m <- runs ]
    -- factorSplit gives (t, r) with t (x) r the state exactly; g is t
    -- divided by its leading entry, so the column of B is r times it.
    columns fs = transposeM
      [ map (lam *) r
      | (t, r) <- take dvis fs
      , lam <- take 1 [ a | a <- t, a /= 0 ] ]

-- | Right-invertible means onto. B is square by construction, so this is
-- the determinant; a lift-free prefix is an isometry, so it fails only when
-- the prefix is not injective on the visible register.
rightInvertible :: (Eq a, Fractional a) => Matrix a -> Bool
rightInvertible b = not (null b) && all ((== length b) . length) b && detM b /= 0

-- | The parked form, run: the state after the prefix is rebuilt as
-- @B v (x) g@ instead of being computed by the prefix.
interpParked :: (Eq a, Num a) => VisSpec -> Parked a -> [Sel] -> StateV a -> Mach a
interpParked vis p sel inp = runStmts m0 (pRest p) sel Nothing
  where
    m0 = Mach (map fst vis ++ [pSite p]) (map snd vis ++ [pDim p])
              (tensorS (mulMV (pAction p) inp) (pLine p)) [] [] [] []

mulMV :: Num a => Matrix a -> StateV a -> StateV a
mulMV b v = [ sum (zipWith (*) row v) | row <- b ]
