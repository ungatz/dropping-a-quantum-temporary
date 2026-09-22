-- |
-- Module      : Drop.Theory.Criterion.Context
--
-- The contextual reading of the criterion: a continuation appends one
-- gate and reads outcome statistics, extracting the Kraus operators'
-- Gram matrix (the channel's Choi matrix); rank one is a single Kraus operator.
module Drop.Theory.Criterion.Context
  ( -- * Continuations
    Client(..)
  , observe
  , observations
  , reflectionAbout
  , mixingGates
  , standardClients
  , trivialClients
    -- * Distinguishability
  , observationallyEqual
  , separatingClient
    -- * The observable object
  , observableChannel
  , observationsDetermineChannel
  , identityOnlyIsNotEnough
  ) where

import Drop.Theory.Program.Elaborate (coreMap)
import Drop.Theory.Criterion.Gram
import Drop.Theory.Algebra.Linear
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Program.Typing (TypedProgram(..))

-- | A continuation: one legal gate appended to the visible register, and one input.
data Client = Client
  { clientLabel :: String
  , clientGate  :: Mat   -- ^ @C@, unitary on @H_m@
  , clientInput :: Vec   -- ^ @v@
  }

instance Show Client where show = clientLabel

-- | The outcome statistics a continuation sees.
--
-- The temporary is gone, so outcome @j@'s probability sums over the
-- temporary's basis states, no term separately visible:
--
-- > p_j  =  sum_i | (C K_i v)_j |^2 .
--
-- The only numbers that leave the program; everything else in this module
-- is built from this one function.
observe :: TypedProgram -> Client -> [K]
observe tp cl = case observations tp [cl] of
  (o : _) -> o
  []      -> []

-- | The same, for a whole family, elaborating the program once.  Every check in
-- this module goes through here, so no check can accidentally read information a
-- continuation does not have.
observations :: TypedProgram -> [Client] -> [[K]]
observations tp = map one
  where
    ks = slices (tpTmpDim tp) m (coreMap tp)
    m  = tpVisDim tp
    one cl =
      [ ksum [ knorm2 (out ki !! j) | ki <- ks ] | j <- [0 .. m-1] ]
      where out ki = matVec (clientGate cl) (matVec ki (clientInput cl))

-- | The reflection about the hyperplane perpendicular to a nonzero vector
-- @u@:
--
-- > R_u = I - 2 u u^dagger / ||u||^2 .
--
-- One gate for every direction: the realisation step of the contextual
-- theorem, the same construction as "Drop.Theory.Criterion.Witness"'s preparation gate.
reflectionAbout :: Vec -> Mat
reflectionAbout u =
  [ [ ksub (delta a b) (kdiv (kmul ktwo (kmul (u !! a) (kconj (u !! b)))) n2)
    | b <- [0 .. m-1] ]
  | a <- [0 .. m-1] ]
  where
    m  = length u
    n2 = vnorm2 u
    delta a b = if a == b then kone else kzero

-- | Gates that mix a pair of visible basis states, in the two phases.
--
-- On the span of basis states @a@ and @b@:
--
-- > (1/sqrt2) [[1, 1], [1, -1]]     and     (1/sqrt2) [[1, -i], [-i, 1]],
--
-- identity elsewhere. Together they turn the off-diagonal entry of the
-- observable into a probability (real part, then imaginary part):
-- polarisation, since without a mixing gate only diagonal entries show.
mixingGates :: Int -> [(String, Mat)]
mixingGates m =
  [ ("mixR" ++ show (a,b), block a b kinvsqrt2 kinvsqrt2 kinvsqrt2 (kneg kinvsqrt2))
  | a <- [0 .. m-1], b <- [a+1 .. m-1] ]
  ++
  [ ("mixI" ++ show (a,b), block a b kinvsqrt2 mi mi kinvsqrt2)
  | a <- [0 .. m-1], b <- [a+1 .. m-1] ]
  where
    mi = kneg (kmul kimag kinvsqrt2)
    block a b xaa xab xba xbb =
      [ [ entry i j | j <- [0 .. m-1] ] | i <- [0 .. m-1] ]
      where
        entry i j
          | i == a && j == a = xaa
          | i == a && j == b = xab
          | i == b && j == a = xba
          | i == b && j == b = xbb
          | i == j && i /= a && i /= b = kone
          | otherwise = kzero

-- | The finite continuation family used for every check: the identity and
-- all the mixing gates, run on every basis input, the all-ones input, and
-- every basis pair sum and @i@-weighted pair sum.
--
-- The theorem quantifies over all continuations; since the observable is
-- bilinear, agreement on this spanning family is agreement everywhere.
standardClients :: Int -> [Client]
standardClients m =
  [ Client (gl ++ "@" ++ vl) g v | (gl, g) <- gates, (vl, v) <- inputs ]
  where
    gates  = ("id", matId m) : mixingGates m
    inputs = [ ("e" ++ show j, vbasis m j) | j <- [0 .. m-1] ]
             ++ [ ("ones", vAllOnes m) ]
             ++ [ ("e" ++ show a ++ "+e" ++ show b
                  , vadd (vbasis m a) (vbasis m b))
                | a <- [0 .. m-1], b <- [a+1 .. m-1] ]
             ++ [ ("e" ++ show a ++ "+ie" ++ show b
                  , vadd (vbasis m a) (vscale kimag (vbasis m b)))
                | a <- [0 .. m-1], b <- [a+1 .. m-1] ]

-- | The degenerate class: continuations that append nothing.  Kept because the
-- theorem's hypothesis is that the class contains the reflections, and this is
-- the class that shows the hypothesis cannot be dropped.
trivialClients :: Int -> [Client]
trivialClients m =
  [ Client ("id@e" ++ show j) (matId m) (vbasis m j) | j <- [0 .. m-1] ]
  ++ [ Client "id@ones" (matId m) (vAllOnes m) ]

-- Distinguishability

observationallyEqual :: [Client] -> TypedProgram -> TypedProgram -> Bool
observationallyEqual cls p q = observations p cls == observations q cls

-- | A continuation that tells the two programs apart, if the family contains one.
separatingClient :: [Client] -> TypedProgram -> TypedProgram -> Maybe Client
separatingClient cls p q =
  case [ c | (c, op, oq) <- zip3 cls (observations p cls) (observations q cls)
           , op /= oq ] of
    []      -> Nothing
    (c : _) -> Just c

-- The observable object

-- | The observable object: the Choi matrix of
-- @Phi(X) = sum_i K_i X K_i^dagger@.
--
-- Everything a continuation can learn is a value of this map, and nothing
-- else. Its rank is the Gram rank of the Kraus operators:
--
-- > what continuations can see   =   Phi
-- > safe to drop           <=>  rank(Choi Phi) <= 1
-- >                        <=>  Phi(X) = W X W^dagger for a single W.
observableChannel :: TypedProgram -> Mat
observableChannel tp = choiMatrix (tpTmpDim tp) (tpVisDim tp) (coreMap tp)

-- | Realisation and polarisation, checked:
--
-- > same numbers to every continuation in the standard family   <=>   same channel.
--
-- Right to left is immediate; left to right needs both, and
-- 'identityOnlyIsNotEnough' shows it fails for the trivial family.
observationsDetermineChannel :: TypedProgram -> TypedProgram -> Bool
observationsDetermineChannel p q =
  observationallyEqual (standardClients (tpVisDim p)) p q
    == (observableChannel p == observableChannel q)

-- | The boundary: two programs with different channels, one safe and one
-- not, that no continuation of the trivial family can tell apart.
--
-- 'True' when the pair is trivially indistinguishable yet differs: right
-- extension cannot be dropped from the theorem's hypothesis.
identityOnlyIsNotEnough :: TypedProgram -> TypedProgram -> Bool
identityOnlyIsNotEnough p q =
  observationallyEqual (trivialClients (tpVisDim p)) p q
    && observableChannel p /= observableChannel q
