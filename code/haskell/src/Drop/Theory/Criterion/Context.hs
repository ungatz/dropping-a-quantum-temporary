-- Drop.Theory.Criterion.Context: what a continuation of a program can observe.
--
-- Question: Can a continuation that appends one gate and reads outcomes tell two programs apart, and
--           what is the one object it sees?
-- Answer:   A client appends one unitary gate to the visible register and reads the outcome
--           probabilities p_j = sum_i |(C K_i v)_j|^2 on one input. The family
--           standardClients (the identity and the mixing gates, on the basis inputs, the all-ones
--           input and every pair sum, plain and i-weighted) is the one every check uses;
--           observationallyEqual compares two programs on a family. What
--           every client can learn is the Choi matrix of Phi(X) = sum_i K_i X K_i^dagger
--           (observableChannel); observationsDetermineChannel checks that equal numbers on the
--           standard family mean equal channels, and identityOnlyIsNotEnough that clients which
--           append nothing (trivialClients) can fail to tell two different channels apart.
-- Paper:    sec:ctxequiv (the criterion, and contextual equivalence).
-- Shapes:   Client   a label, a unitary gate C on the visible register, and an input v.

module Drop.Theory.Criterion.Context
  ( -- * Continuations
    Client(..)
  , observations
  , standardClients
    -- * Distinguishability
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

-- A client has a label, a gate on the visible register and an input.
-- >>> :m + Drop.Theory.Corpus.Examples Drop.Theory.Program.Typing
-- >>> let Right park = checkProgram spreadAndPark
-- >>> let Right rd = checkProgram spreadAndRead
-- >>> let Right rd2 = checkProgram spreadAndReadTwice
-- >>> let Right noth = checkProgram doNothing
-- >>> let Right calone = checkProgram computeAlone
-- >>> Client "id@e0" (matId 2) (vbasis 2 0)
-- id@e0
-- >>> clientLabel (Client "id@e0" (matId 2) (vbasis 2 0))
-- "id@e0"

instance Show Client where show = clientLabel

-- A client prints as its label.
-- >>> show (Client "id@e0" (matId 2) (vbasis 2 0))
-- "id@e0"

-- | The same, for a whole family, elaborating the program once.  Every check in
-- this module goes through here, so no check can accidentally read information a
-- continuation does not have.
observations :: TypedProgram -> [Client] -> [[K]]
observations tp = map one
  where
    ks = slices (tpTmpDim tp) m (coreMap tp)
    m  = tpVisDim tp
    one cl =
      -- impossible: out ki has m entries
      [ ksum [ knorm2 (out ki !! j) | ki <- ks ] | j <- [0 .. m-1] ]
      where out ki = matVec (clientGate cl) (matVec ki (clientInput cl))

-- >>> observations park [Client "id@e0" (matId 2) (vbasis 2 0), Client "id@e1" (matId 2) (vbasis 2 1)]
-- [[1,0],[0,1]]
-- >>> observations park []
-- []

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

-- For each pair of basis states, a real mixing gate and an i-weighted one.
-- >>> map fst (mixingGates 2)
-- ["mixR(0,1)","mixI(0,1)"]
-- >>> map fst (mixingGates 3)
-- ["mixR(0,1)","mixR(0,2)","mixR(1,2)","mixI(0,1)","mixI(0,2)","mixI(1,2)"]
-- >>> mixingGates 1
-- []
-- >>> map matIsUnitary (map snd (mixingGates 3))
-- [True,True,True,True,True,True]

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

-- The identity and the mixing gates, each on every basis input, the all-ones input and the pair sums.
-- >>> length (standardClients 2)
-- 15
-- >>> take 5 (standardClients 2)
-- [id@e0,id@e1,id@ones,id@e0+e1,id@e0+ie1]
-- >>> length (standardClients 3)
-- 70

-- | The degenerate class: continuations that append nothing.  Kept because the
-- theorem's hypothesis is that the class contains the reflections, and this is
-- the class that shows the hypothesis cannot be dropped.
trivialClients :: Int -> [Client]
trivialClients m =
  [ Client ("id@e" ++ show j) (matId m) (vbasis m j) | j <- [0 .. m-1] ]
  ++ [ Client "id@ones" (matId m) (vAllOnes m) ]

-- >>> trivialClients 2
-- [id@e0,id@e1,id@ones]
-- >>> length (trivialClients 3)
-- 4

-- Distinguishability

observationallyEqual :: [Client] -> TypedProgram -> TypedProgram -> Bool
observationallyEqual cls p q = observations p cls == observations q cls

-- Spread-and-park and do-nothing both act as the identity on the visible register, so no client tells them apart; spread-and-read differs from spread-and-park.
-- >>> observationallyEqual (standardClients 2) rd rd
-- True
-- >>> observationallyEqual (standardClients 2) park noth
-- True
-- >>> observationallyEqual (standardClients 2) rd park
-- False

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

-- The Choi matrix of a program: spread-and-park acts as the identity channel; spread-and-read applies I or X with probability 1/2 each.
-- >>> observableChannel park
-- [[1,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,1]]
-- >>> observableChannel rd
-- [[1/2,0,0,1/2],[0,1/2,1/2,0],[0,1/2,1/2,0],[1/2,0,0,1/2]]

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

-- >>> observationsDetermineChannel park noth
-- True
-- >>> observationsDetermineChannel rd park
-- True
-- >>> observationsDetermineChannel rd rd2
-- True

-- | The boundary: two programs with different channels, one safe and one
-- not, that no continuation of the trivial family can tell apart.
--
-- 'True' when the pair is trivially indistinguishable yet differs: right
-- extension cannot be dropped from the theorem's hypothesis.
identityOnlyIsNotEnough :: TypedProgram -> TypedProgram -> Bool
identityOnlyIsNotEnough p q =
  observationallyEqual (trivialClients (tpVisDim p)) p q
    && observableChannel p /= observableChannel q

-- Copying the visible register into the temporary and doing nothing: clients that append nothing cannot tell them apart, yet the channels differ.
-- >>> identityOnlyIsNotEnough calone noth
-- True
-- >>> observationallyEqual (trivialClients 2) calone noth
-- True
-- >>> identityOnlyIsNotEnough park noth
-- False
