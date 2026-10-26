-- Drop.Lang.Pass.Park: pass 2, the prefix replaced by the line it leaves the temporary on.
--
-- Question: Does everything before the first lift leave the temporary in one fixed state,
--           whatever the visible input?
-- Answer:   Run the prefix on the visible basis inputs and on the all-ones input, and factor the
--           temporary out of each result. If every run factors, the visible register is all that
--           is left beside the temporary, and every run leaves the temporary on one and the same
--           line g, then the prefix is v |-> g (x) B v: park keeps g, scaled so its first nonzero
--           entry is 1, and B, one column per visible basis input. The rest of the program is
--           then run from g and B v instead of from the prefix. If one input leaves the
--           temporary entangled, or two inputs leave it on different lines, or a second
--           temporary is still live, park declines by name (prefix-parks). rightInvertible
--           asks whether B is onto, which the next pass needs.
-- Paper:    thm:perrecord (clause 2: the site map is g (x) W), sec:meas:leaf (the site on one record).
-- Shapes:   Parked a  the temporary's name (pSite) and dimension (pDim), the line g it is left on
--                     (pLine), the visible action B (pAction, a square matrix) and the commands
--                     from the first lift on (pRest).

module Drop.Lang.Pass.Park
  ( Parked (..), park, interpParked, rightInvertible, mulMV ) where

import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass.Cut

-- The parked form ---------------------------------------------------------------

-- | The prefix, as the pair @(g, B)@ with @v |-> g (x) B v@: whatever comes
-- in, the temporary comes out on the line of @g@.
data Parked a = Parked
  { pSite   :: String
  , pDim    :: Int
  , pLine   :: StateV a   -- ^ g, scaled so its first nonzero entry is 1
  , pAction :: Matrix a   -- ^ B, one column per visible basis input
  , pRest   :: Prog a
  } deriving Show

-- A parked form written by hand: a qubit left on |1>, the visible action the identity, no rest.
-- >>> Parked "t" 2 [0, 1] [[1, 0], [0, 1]] [] :: Parked Rational
-- Parked {pSite = "t", pDim = 2, pLine = [0 % 1,1 % 1], pAction = [[1 % 1,0 % 1],[0 % 1,1 % 1]], pRest = []}

-- | A matrix times a vector: one entry per row, the row dotted with the vector.
mulMV :: Num a => Matrix a -> StateV a -> StateV a
mulMV b v = [ sum (zipWith (*) row v) | row <- b ]

-- >>> mulMV [[0, 1], [1, 0]] [3, 4 :: Int]
-- [4,3]
-- >>> mulMV [[1, 1], [1, 1]] [3, -3 :: Int]
-- [0,0]
-- >>> mulMV [[2, 0, 0], [0, 2, 0], [0, 0, 2]] [1, 2, 3 :: Int]
-- [2,4,6]

-- | Right-invertible means onto. B is square by construction, so this is
-- the determinant; a lift-free prefix is an isometry, so it fails only when
-- the prefix is not injective on the visible register.
rightInvertible :: (Eq a, Fractional a) => Matrix a -> Bool
rightInvertible b = not (null b) && all ((== length b) . length) b && detM b /= 0

-- The identity is onto; the all-ones matrix is not; an empty or a non-square matrix is refused.
-- >>> rightInvertible [[1, 0], [0, 1 :: Rational]]
-- True
-- >>> rightInvertible [[1, 1], [1, 1 :: Rational]]
-- False
-- >>> rightInvertible ([] :: Matrix Rational)
-- False
-- >>> rightInvertible [[1, 0, 0], [0, 1, 0 :: Rational]]
-- False

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
             -- impossible: regPos m x indexes mNames and mDims has one entry per name
             (m : _) -> mDims m !! regPos m x
             -- impossible: probesFor always has the all-ones probe, so runs is never empty
             []      -> error "park: no test inputs"
    splits = [ factorSplit (mDims m) [regPos m x] (mAmp m) | m <- runs ]
    -- factorSplit gives (t, r) with t (x) r the state exactly; g is t
    -- divided by its leading entry, so the column of B is r times it.
    columns fs = transposeM
      [ map (lam *) r
      | (t, r) <- take dvis fs
      , lam <- take 1 [ a | a <- t, a /= 0 ] ]

-- The repeat-until-success step parks: the tilt leaves t on the line (1, 1, 1/2) for every
-- visible input, and the visible action is two thirds of the identity.
-- >>> :m + Drop.Lang.Programs.RUS Drop.Lang.Programs.TempAnd Drop.Lang.Programs.DJ
-- >>> let parkedRus = cut rusProg "t" >>= park visR
-- >>> fmap (\p -> (pSite p, pDim p, pLine p)) parkedRus
-- Right ("t",3,[1 % 1,1 % 1,1 % 2])
-- >>> fmap pAction parkedRus
-- Right [[2 % 3,0 % 1,0 % 1],[0 % 1,2 % 3,0 % 1],[0 % 1,0 % 1,2 % 3]]
-- >>> fmap (length . pRest) parkedRus
-- Right 2

-- Deutsch-Jozsa parks the |-> temporary on [1, -1], with no lift to resolve.
-- >>> fmap pLine (cut (djPaper fId) "t" >>= park visDJ)
-- Right [1,-1]

-- The unsafe Toffoli: the temporary is entangled with x and y on the all-ones input, so park declines.
-- >>> fmap (const ()) (cut andComputed "a" >>= park visXY)
-- Left "prefix-parks"

-- The temporary AND declines too, though the criterion accepts it on both records: its prefix
-- ends with the Toffoli and H, which entangle a with x and y before the lift.
-- >>> fmap (const ()) (cut andUncomputedByMeasurement "a" >>= park visXY)
-- Left "prefix-parks"

-- | The parked form, run: the state after the prefix is rebuilt as
-- @B v (x) g@ instead of being computed by the prefix.
interpParked :: (Eq a, Num a) => VisSpec -> Parked a -> [Sel] -> StateV a -> Mach a
interpParked vis p sel inp = runStmts m0 (pRest p) sel Nothing
  where
    m0 = Mach (map fst vis ++ [pSite p]) (map snd vis ++ [pDim p])
              (tensorS (mulMV (pAction p) inp) (pLine p)) [] [] [] []

-- Parked, then run: the state at the drop is the source's, under each selection.
-- >>> let sameAsSource p sel = mAmp (interpParked visR p sel (ket [3] [0])) == mAmp (interpSource visR rusProg "t" sel (ket [3] [0]))
-- >>> fmap (\p -> map (sameAsSource p) (allSelections 1)) parkedRus
-- Right [True,True]
