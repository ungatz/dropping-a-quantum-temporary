-- |
-- Module      : Drop.Theory.Criterion
--
-- Whether a program's denotation @K : H_m -> H_d (x) H_m@ is of the form
-- @g (x) W@ (the criterion section). The verdict is computed twice, by cut minors and
-- by the rank of the slice matrix, and 'routesAgree' compares the two.
module Drop.Theory.Criterion
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
  ) where

import Drop.Theory.Program.Elaborate (coreMap)
import Drop.Theory.Criterion.Gram
import Drop.Theory.Algebra.Linear
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Criterion.Split
import Drop.Theory.Program.Typing (TypedProgram(..))

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
-- "Drop.Theory.Criterion.Gram" agree?
routesAgree :: TypedProgram -> Bool
routesAgree tp =
  safeByMinors tp == safeByRank tp
  && ranksAgree (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- The verdict

verdict :: TypedProgram -> Verdict
verdict tp = verdictOfCoreMap (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- | The verdict of a bare denotation @K : H_m -> H_d (x) H_m@. "Drop.Theory.Lifted"
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
-- The construction is the pivot argument of "Drop.Theory.Criterion.Split" applied to the slice
-- matrix: at rank one, @g@ is a column and @W@ is the matching row.  Rebuilding
-- @g (x) W@ and comparing it with the denotation is left to the caller,
-- 'Drop.Theory.Criterion.Witness.checkWitness'.
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

