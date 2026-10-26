-- Drop.Theory.Criterion: is a drop safe, and on which line does it leave the temporary?
--
-- Question: Is the denotation K : H_m -> H_d (x) H_m of a program of the form g (x) W?
-- Answer:   The verdict is Safe with a certificate (g, W), where K v = g (x) W v for every v;
--           or Unsafe, with a 2 x 2 minor that does not vanish and the Kraus rank; or Unreachable,
--           when K is zero and there is no state for the drop to be about. verdictOfCoreMap
--           computes it from the rank of the slice matrix, one row for each temporary basis state
--           and one column for each pair (output, input): rank 0 is Unreachable, rank 1 is Safe
--           and anything more is Unsafe. Two routes decide safety separately: safeByMinors (every
--           2 x 2 minor vanishes) and safeByRank (the Kraus operators lie on one line). routesAgree
--           compares them, and also the three ranks of Drop.Theory.Criterion.Gram. certificateOf
--           reads g and W off a safe program, and parkedLine is the line of g.
-- Paper:    sec:criterion (the criterion), sec:factor (the factorization).
-- Shapes:   Certificate   the vector g and the matrix W of a safe drop.
--           Verdict       Safe with a certificate, Unsafe with evidence, or Unreachable.

module Drop.Theory.Criterion
  ( -- * The verdict
    Verdict(..)
  , Certificate(..)
  , verdict
    -- * The two routes, separately
  , safeByRank
  , routesAgree
    -- * Verdicts of a bare denotation
  , verdictOfCoreMap
  , certificateOfCoreMap
    -- * Reading the certificate off a safe program
  , certificateOf
  , parkedLine
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

-- A safe drop leaves the temporary on g; spread-and-park parks it on (1, 1)/sqrt 2.
-- >>> :m + Drop.Theory.Corpus.Examples Drop.Theory.Program.Typing
-- >>> fmap (fmap certParked . certificateOf) (checkProgram spreadAndPark)
-- Right (Just [sqrt2/2,sqrt2/2])
-- >>> fmap (fmap certVisible . certificateOf) (checkProgram spreadAndPark)
-- Right (Just [[1,0],[0,1]])

-- | The verdict on a program's drop, with its evidence attached either way.
data Verdict
  = Safe Certificate
      -- ^ the denotation factors; the certificate reconstructs it exactly
  | Unsafe (Maybe ((Int,Int),(Int,Int),K,K)) Int
      -- ^ a failing 2x2 minor (when there is one) and the Kraus rank
  | Unreachable
      -- ^ the denotation is zero: no state for the drop to be about, so the drop
      -- imposes no condition (a record of weight zero at every input).

-- The three verdicts. An unsafe one carries a failing minor, and a safe one the line the temporary is left on.
-- >>> mapM_ print (lines (show (Unreachable :: Verdict)))
-- "UNREACHABLE (the zero map: no state, so no obligation)"
-- >>> mapM_ print (either (const []) (lines . show . verdict) (checkProgram spreadAndPark))
-- "SAFE, parked on the line [1,1]"
-- >>> mapM_ print (either (const []) (lines . show . verdict) (checkProgram spreadAndRead))
-- "UNSAFE (slice rank 2, so the temporary carries 1 dimension(s) of information about the input)"
-- "  witness minor at rows (0,1) columns (0,1): 1/2 /= 0"

instance Show Verdict where
  show (Safe c)      = "SAFE, parked on the line " ++ show (canonicalLine (certParked c))
  show Unreachable   = "UNREACHABLE (the zero map: no state, so no obligation)"
  show (Unsafe mn r) =
    "UNSAFE (slice rank " ++ show r ++ ", so the temporary carries "
    ++ show (r - 1) ++ " dimension(s) of information about the input)"
    ++ case mn of
         Nothing -> ""
         Just ((a,b),(a',b'),x,y) ->
           "\n  witness minor at rows " ++ show (a,a') ++ " columns " ++ show (b,b')
           ++ ": " ++ show x ++ " /= " ++ show y

-- >>> show (Unreachable :: Verdict)
-- "UNREACHABLE (the zero map: no state, so no obligation)"
-- >>> either show (take 5 . show . verdict) (checkProgram spreadAndPark)
-- "SAFE,"

-- The two routes

-- | Route 1: the cut minors vanish.
--
-- The cut is @temporary | visible-out (x) visible-in@; the coefficient
-- matrix (one row per temporary basis state, one column per (output,
-- input) pair) is the slice matrix.
safeByMinors :: TypedProgram -> Bool
safeByMinors tp = allTwoByTwoMinorsVanish (sliceMatrix (tpTmpDim tp) (tpVisDim tp) (coreMap tp))

-- Route 1 on the smallest safe program and the smallest unsafe one.
-- >>> fmap safeByMinors (checkProgram spreadAndPark)
-- Right True
-- >>> fmap safeByMinors (checkProgram spreadAndRead)
-- Right False

-- | Route 2: the form the contextual theorem needs. The Kraus operators
-- span at most a line, equivalently the Gram matrix has rank at most one.
safeByRank :: TypedProgram -> Bool
safeByRank tp = slicesAreCollinear (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- Route 2 gives the same two answers.
-- >>> fmap safeByRank (checkProgram spreadAndPark)
-- Right True
-- >>> fmap safeByRank (checkProgram spreadAndRead)
-- Right False

-- | Do the two routes give the same verdict, and do the three ranks of
-- "Drop.Theory.Criterion.Gram" agree?
routesAgree :: TypedProgram -> Bool
routesAgree tp =
  safeByMinors tp == safeByRank tp
  && ranksAgree (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- >>> fmap routesAgree (checkProgram spreadAndPark)
-- Right True
-- >>> fmap routesAgree (checkProgram spreadAndRead)
-- Right True
-- >>> and [ routesAgree tp | (_, p) <- catalogue, Right tp <- [checkProgram p] ]
-- True

-- The verdict

verdict :: TypedProgram -> Verdict
verdict tp = verdictOfCoreMap (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- >>> fmap (take 4 . show . verdict) (checkProgram spreadAndPark)
-- Right "SAFE"
-- >>> fmap (take 6 . show . verdict) (checkProgram spreadAndRead)
-- Right "UNSAFE"
-- >>> fmap (take 4 . show . verdict) (checkProgram doNothing)
-- Right "SAFE"

-- | The verdict of a bare denotation @K : H_m -> H_d (x) H_m@. "Drop.Theory.Lifted"
-- needs this since there the denotation depends on the measurement record,
-- with no single map to attach to the program.
verdictOfCoreMap :: Int -> Int -> Mat -> Verdict
verdictOfCoreMap d m k
  | r == 0    = Unreachable
  | r == 1    = case certificateOfCoreMap d m k of
                  Just c  -> Safe c
                  Nothing -> Unsafe Nothing r     -- cannot happen at rank one
  | otherwise = Unsafe (failingMinor [d, m*m] [0] (concat mm)) r
  where
    mm = sliceMatrix d m k
    r  = rank mm

-- The verdict of a bare denotation: rank 0, rank 1 and rank 2.
-- >>> verdictOfCoreMap 2 2 (matZero 4 2)
-- UNREACHABLE (the zero map: no state, so no obligation)
-- >>> verdictOfCoreMap 2 2 (kron [[kone], [kzero]] (matId 2))
-- SAFE, parked on the line [1,0]
-- >>> mapM_ print (lines (show (verdictOfCoreMap 2 2 [[kone, kzero], [kzero, kzero], [kzero, kzero], [kzero, kone]])))
-- "UNSAFE (slice rank 2, so the temporary carries 1 dimension(s) of information about the input)"
-- "  witness minor at rows (0,1) columns (0,3): 1 /= 0"

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

-- >>> fmap certParked (certificateOfCoreMap 2 2 (kron [[kone], [kzero]] (matId 2)))
-- Just [1,0]
-- >>> fmap certVisible (certificateOfCoreMap 2 2 (kron [[kone], [kzero]] (matId 2)))
-- Just [[1,0],[0,1]]
-- >>> fmap certParked (certificateOfCoreMap 2 2 [[kone, kzero], [kzero, kzero], [kzero, kzero], [kzero, kone]])
-- Nothing
-- >>> fmap certParked (certificateOfCoreMap 2 2 (matZero 4 2))
-- Nothing

certificateOf :: TypedProgram -> Maybe Certificate
certificateOf tp = certificateOfCoreMap (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- >>> fmap (fmap certParked . certificateOf) (checkProgram twoGateSilq)
-- Right (Just [1,0])
-- >>> fmap (fmap certParked . certificateOf) (checkProgram spreadAndRead)
-- Right Nothing

-- | The line on which the drop leaves the temporary constant, independent
-- of the visible input; every certificate is a vector on this ray.
parkedLine :: TypedProgram -> Maybe Vec
parkedLine tp = canonicalLine . certParked <$> certificateOf tp

-- The canonical line, with its first nonzero coordinate 1.
-- >>> fmap parkedLine (checkProgram spreadAndPark)
-- Right (Just [1,1])
-- >>> fmap parkedLine (checkProgram twoGateSilq)
-- Right (Just [1,0])
-- >>> fmap parkedLine (checkProgram spreadAndRead)
-- Right Nothing

