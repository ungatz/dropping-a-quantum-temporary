-- |
-- Module      : DQT.Criterion
--
-- Whether a program's denotation @K : H_m -> H_d (x) H_m@ is of the form
-- @g (x) W@.  The verdict is computed twice, by cut minors and
-- by the rank of the slice matrix, and 'routesAgree' compares the two.
module DQT.Criterion
  ( -- * The verdict
    Verdict(..)
  , Certificate(..)
  , verdict
    -- * The two routes, separately
  , safeByMinors
  , safeByRank
  , routesAgree
    -- * Verdicts of a bare denotation
  , verdictOfCoreMap
  , certificateOfCoreMap
    -- * Reading the certificate off a safe program
  , certificateOf
  , parkedLine
    -- * How badly an unsafe program fails
  , readFamilyMinimaxSquared
  , productReplacementErrorSquared
  ) where

import DQT.Calculus.Elaborate (coreMap)
import DQT.Criterion.Gram
import DQT.Algebra.Linear
import DQT.Algebra.Scalar
import DQT.Criterion.Split
import DQT.Calculus.Typing (TypedProgram(..))

-- | A drop certificate for a safe drop: the vector @g@ on which the drop
-- leaves the temporary constant, and the residual visible map @W@, with
-- @K v = g (x) W v@ for every @v@.
--
-- The pair is not unique: @(lambda g, lambda^{-1} W)@ works too, so what is
-- canonical is the line @[g]@, which 'parkedLine' returns.
data Certificate = Certificate
  { certParked   :: Vec   -- ^ @g@, as returned by the split (not normalised)
  , certVisible  :: Mat   -- ^ @W@, matching that @g@
  }

-- | The verdict on a program's drop, with its evidence attached either way.
data Verdict
  = Safe Certificate
      -- ^ the denotation factors; the certificate reconstructs it exactly
  | Unsafe (Maybe ((Int,Int),(Int,Int),K,K)) Int
      -- ^ a failing 2x2 minor (when there is one) and the Kraus rank
  | Vacuous
      -- ^ the denotation is zero: no state for the drop to be about. Arises
      -- only on a zero-weight branch after a lift, where the drop imposes
      -- no condition.

instance Show Verdict where
  show (Safe c)      = "SAFE, parked on the line " ++ show (canonicalLine (certParked c))
  show Vacuous       = "VACUOUS (the zero map: no state, so no obligation)"
  show (Unsafe mn r) =
    "UNSAFE (slice rank " ++ show r ++ ", so the temporary carries "
    ++ show (r - 1) ++ " dimension(s) of information about the input)"
    ++ case mn of
         Nothing -> ""
         Just ((a,b),(a',b'),x,y) ->
           "\n  witness minor at rows " ++ show (a,a') ++ " columns " ++ show (b,b')
           ++ ": " ++ show x ++ " /= " ++ show y

-- The two routes

-- | Route 1: the cut minors vanish.
--
-- The cut is @temporary | visible-out (x) visible-in@; the coefficient
-- matrix (one row per temporary basis state, one column per (output,
-- input) pair) is the slice matrix.
safeByMinors :: TypedProgram -> Bool
safeByMinors tp = allTwoByTwoMinorsVanish (sliceMatrix (tpTmpDim tp) (tpVisDim tp) (coreMap tp))

-- | Route 2: the form the contextual theorem needs. The Kraus operators
-- span at most a line, equivalently the Gram matrix has rank at most one.
safeByRank :: TypedProgram -> Bool
safeByRank tp = slicesAreCollinear (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- | Do the two routes give the same verdict, and do the three ranks of
-- "DQT.Criterion.Gram" agree?
routesAgree :: TypedProgram -> Bool
routesAgree tp =
  safeByMinors tp == safeByRank tp
  && ranksAgree (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- The verdict

verdict :: TypedProgram -> Verdict
verdict tp = verdictOfCoreMap (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- | The verdict of a bare denotation @K : H_m -> H_d (x) H_m@. "DQT.Lifted"
-- needs this since there the denotation depends on the measurement record,
-- with no single map to attach to the program.
verdictOfCoreMap :: Int -> Int -> Mat -> Verdict
verdictOfCoreMap d m k
  | r == 0    = Vacuous
  | r == 1    = case certificateOfCoreMap d m k of
                  Just c  -> Safe c
                  Nothing -> Unsafe Nothing r     -- unreachable at rank one
  | otherwise = Unsafe (failingMinor [d, m*m] [0] (concat mm)) r
  where
    mm = sliceMatrix d m k
    r  = rank mm

-- | Read the drop certificate @(g, W)@ off a denotation of rank one.
--
-- The construction is the pivot argument of "DQT.Criterion.Split" applied to the slice
-- matrix: at rank one, @g@ is a column and @W@ is the matching row.  Rebuilding
-- @g (x) W@ and comparing it with the denotation is left to the caller,
-- 'DQT.Criterion.Witness.checkWitness'.
certificateOfCoreMap :: Int -> Int -> Mat -> Maybe Certificate
certificateOfCoreMap d m k =
  case factorSplit [d, m*m] [0] (concat (sliceMatrix d m k)) of
    Nothing -> Nothing
    Just s  -> Just Certificate { certParked  = splitLeft s
                                , certVisible = unflatten (splitRight s) }
  where
    unflatten xs = [ take m (drop (a*m) xs) | a <- [0 .. m-1] ]

certificateOf :: TypedProgram -> Maybe Certificate
certificateOf tp = certificateOfCoreMap (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- | The line on which the drop leaves the temporary constant, independent
-- of the visible input; every certificate is a vector on this ray.
parkedLine :: TypedProgram -> Maybe Vec
parkedLine tp = canonicalLine . certParked <$> certificateOf tp

-- How badly an unsafe program fails

-- | The minimax for the /read/ family, squared.
--
-- Temporary prepared in amplitude vector @u@, read by the cyclic shift
-- (Kraus operators @K_j = u_j S^j@), dropped. Least uniform error over
-- every drop-safe product replacement:
--
-- > sqrt( ||u||^2 - max_j |u_j|^2 ).
--
-- Returns the value under the root (it stays in the scalar field). Upper
-- bound checked here via 'productReplacementErrorSquared'; the matching
-- lower bound is proved by hand, not re-proved here.
--
-- @u = H|0> = (1,1)\/sqrt2@: error @1\/sqrt2@ (worst in dimension two).
-- @u = tilt|0>@ restricted to @{0,1}@, i.e. @(2\/3, 2\/3, 0)@: error @2\/3@.
readFamilyMinimaxSquared :: Vec -> K
readFamilyMinimaxSquared u = ksub (vnorm2 u) best
  where
    best = foldl (\acc x -> if krealCompare x acc == GT then x else acc)
                 kzero (map knorm2 u)

-- | The uniform squared error of replacing the read family's map by the
-- product that keeps only basis state @j@:
--
-- > K'  =  u_j |j>  (x)  S^j,
--
-- Its difference from @K@ has Kraus operators @u_l S^l@, @l /= j@; each
-- @S^l@ is unitary, so a unit @v@ maps to squared length
-- @sum_{l /= j} |u_l|^2@ everywhere, the supremum. The /construction/ half
-- of the minimax, computed exactly.
productReplacementErrorSquared :: Vec -> Int -> K
productReplacementErrorSquared u j =
  ksum [ knorm2 x | (l, x) <- zip [0 :: Int ..] u, l /= j ]
