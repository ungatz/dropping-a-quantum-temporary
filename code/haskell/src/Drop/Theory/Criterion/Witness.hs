-- Drop.Theory.Criterion.Witness: the criterion in both directions, by a program of the shape sep(R, W).
--
-- Question: Is a safe program equal to a program that prepares its temporary once, computes on the rest
--           and drops, and can that program be built?
-- Answer:   sep(R, W) is the program `new; R on the temporary; W on the visible register; drop`
--           (sepProgram), and its denotation is (R e_i0) (x) W (sepCoreMap). forwardDirection checks
--           that the elaborator agrees with that formula. Backwards, synthesize reads g and W off a
--           safe program, scales g to a unit vector (the square root of its squared norm must lie in
--           K), requires W unitary, builds the real Householder reflection R that carries e_i0 to g
--           (householder), emits sep(R, W) and checks that it types and denotes the same map entry by
--           entry. If a step fails the result is a Reason, one for each hypothesis the construction
--           needs. checkWitness repeats the check on its own; inSepShape tests whether a program is
--           literally of the shape; explainWitness is the account the command line prints.
-- Paper:    def:sw (the independent witness), sec:ctxequiv.
-- Shapes:   Witness   the unit vector g, the unitary W, the reflection R, the emitted program and
--                     whether R is the identity.
--           Reason    why no witness was built: one constructor for each failing hypothesis.

module Drop.Theory.Criterion.Witness
  ( -- * The shape itself
    inSepShape
    -- * Direction 1
  , forwardDirection
    -- * The reflection
  , householder
    -- * Direction 2
  , Witness(..)
  , Reason(..)
  , synthesize
  , checkWitness
    -- * Reporting
  , explainWitness
  ) where

import Data.List (intercalate)
import Drop.Theory.Criterion
import Drop.Theory.Program.Elaborate (coreMap)
import Drop.Theory.Program.Gates (mId)
import Drop.Theory.Algebra.Linear
import Drop.Theory.Pretty
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Criterion.Split (canonicalLine)
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing

-- the shape, as a syntactic property

-- | Is this program /literally/ of the shape @sep(R, W)@: allocate, one
-- gate on the temporary, one gate on the visible register, drop, return?
--
-- Not the criterion: almost no real program is literally in the shape.
-- /Source-weakenable/ is weaker: 'synthesize' finds a program of the
-- shape with the same denotation.
inSepShape :: Program -> Bool
inSepShape p = case progTerm p of
  New _ _ _ (Act _ g1 _ (Act _ g2 _ (Drop _ (Ret _)))) ->
    gateKind g1 == OnTmp && gateKind g2 == OnVis
  _ -> False

-- Literally of the shape: one gate on the temporary, one on the visible register. Spread-and-park has only the first.
-- >>> :m + Drop.Theory.Corpus.Examples Drop.Theory.Program.Gates
-- >>> inSepShape sepHX
-- True
-- >>> inSepShape spreadAndPark
-- False
-- >>> inSepShape doNothing
-- True

-- direction 1: the shape is manifestly a product

-- | Build the source term @sep(R, W)@ as an actual program.
--
-- > let t = new i0 in
-- >   let (t1, v1) = (R (x) 1)(t, v) in
-- >   let (t2, v2) = (1 (x) W)(t1, v1) in
-- >   drop t2; v2
sepProgram :: String     -- ^ label
           -> Name       -- ^ the visible register's name
           -> Int        -- ^ @m@
           -> Int        -- ^ @d@
           -> Int        -- ^ @i0@
           -> Mat        -- ^ @R@, on the temporary
           -> Mat        -- ^ @W@, on the visible register
           -> Program
sepProgram lbl v m d i0 r w =
  Program { progLabel  = lbl
          , progVis    = v
          , progVisDim = m
          , progTerm   =
              New "t" d i0 $
                Act ("t1","v1") (onTmp "R" r m) ("t", v) $
                  Act ("t2","v2") (onVis "W" d w) ("t1","v1") $
                    Drop "t2" (Ret "v2") }

-- sep(H, X) written as a program.
-- >>> mapM_ print (lines (prettySugared (sepProgram "sep(H,X)" "v" 2 2 0 mH mX)))
-- "-- sep(H,X)"
-- "let t = new |0> in"
-- "  t1 := R t;  v1 := v"
-- "  v2 := W v1;  t2 := t1"
-- "  drop t2;"
-- "  return v2"
-- >>> inSepShape (sepProgram "sep(H,X)" "v" 2 2 0 mH mX)
-- True

-- | The denotation of @sep(R, W)@, written down without running the
-- elaborator: @(R e_{i0}) (x) W@.
sepCoreMap :: Int -> Int -> Mat -> Mat -> Mat
sepCoreMap d i0 r w = kron (matFromCols [matVec r (vbasis d i0)]) w

-- (R e_i0) (x) W: the column H e_0 = (1, 1)/sqrt 2 beside X.
-- >>> sepCoreMap 2 0 mH mX
-- [[0,sqrt2/2],[sqrt2/2,0],[0,sqrt2/2],[sqrt2/2,0]]
-- >>> sepCoreMap 2 1 mX mZ
-- [[1,0],[0,-1],[0,0],[0,0]]

-- | The forward direction, checked: elaborate @sep(R, W)@ with the
-- elaborator and compare with the one-line answer. Any @(R, W)@ may be
-- passed, including non-unitary ones, in which case the program is
-- ill-typed and the check reports 'Nothing' rather than a false success.
forwardDirection :: Int -> Int -> Int -> Mat -> Mat -> Either TypeError Bool
forwardDirection m d i0 r w = do
  tp <- checkProgram (sepProgram "sep(R,W)" "v" m d i0 r w)
  pure (coreMap tp == sepCoreMap d i0 r w)

-- The elaborator agrees with the formula; a gate that is not unitary is refused by typing, not accepted.
-- >>> forwardDirection 2 2 0 mH mX
-- Right True
-- >>> forwardDirection 2 2 1 mX mZ
-- Right True
-- >>> forwardDirection 2 2 0 [[kone, kone], [kone, kone]] mX
-- Left gate R is not unitary; the Gate rule's premise U^dagger U = U U^dagger = I fails exactly

-- the reflection

-- | The Householder reflection carrying @e_{i0}@ to the unit vector @g@.
--
-- > R  =  I - 2 w w^T / ||w||^2,     w = e_{i0} - g,
--
-- @R = I@ when @w = 0@. Real entries only: over C a reflection carries
-- @e_{i0}@ to @g@ only up to a phase, so this refuses rather than guessing.
householder :: Int   -- ^ dimension @d@
            -> Int   -- ^ @i0@
            -> Vec   -- ^ @g@, expected to be a real unit vector
            -> Either Reason Mat
householder d i0 g
  | not (all kIsReal g)    = Left (ComplexParkedState g)
  | vnorm2 g /= kone       = Left (ParkedStateNotUnit (vnorm2 g))
  | vIsZero w              = Right (mId d)                       -- g = e_{i0}
  | otherwise              =
      let n2   = vnorm2 w
          -- impossible: a and b are positions of w, which has d entries
          refl = [ [ ksub (delta a b) (kdiv (kmul ktwo (kmul (w !! a) (w !! b))) n2)
                   | b <- [0 .. d-1] ]
                 | a <- [0 .. d-1] ]
      in if matIsUnitary refl && matVec refl (vbasis d i0) == g
           then Right refl
           else Left (ReflectionFailed refl)
  where
    w = vsub (vbasis d i0) g
    delta a b = if a == b then kone else kzero

-- The reflection carrying e_0 to a real unit vector g; the identity when g = e_0; a refusal otherwise.
-- >>> householder 2 0 [kinvsqrt2, kinvsqrt2]
-- Right [[sqrt2/2,sqrt2/2],[sqrt2/2,-sqrt2/2]]
-- >>> householder 2 0 [kone, kzero]
-- Right [[1,0],[0,1]]
-- >>> fmap (== mId 2) (householder 2 1 [kzero, kone])
-- Right True
-- >>> either show (const "reflection") (householder 2 0 [kimag, kzero])
-- "the parked state is not real; the Householder witness is real-only (over C the factors are determined only up to a compensating phase)"
-- >>> either show (const "reflection") (householder 2 0 [kone, kone])
-- "internal: normalised parked state has norm^2 2"

-- direction 2: synthesis

-- | Why the construction could not produce a witness.  Each constructor is a
-- hypothesis of the theorem, failing out loud.
data Reason
  = DoesNotFactor Int (Maybe ((Int,Int),(Int,Int),K,K))
      -- ^ the Kraus rank exceeds one; the drop is genuinely unsafe.  The
      -- optional payload is a 2x2 minor that fails to vanish.
  | ZeroMap
      -- ^ the denotation is zero; there is no state for the drop to be about.
  | ParkedNormNotInGateRing K
      -- ^ @||g||^2@ has no square root in the coefficient field, so the
      -- preparation gate is not expressible over it: the relativised form of
      -- the criterion, reached.
  | ComplexParkedState Vec
      -- ^ the temporary's constant state is not real; the source witness is real-only.
  | ParkedStateNotUnit K
      -- ^ internal: normalisation did not produce a unit vector.
  | ReflectionFailed Mat
      -- ^ internal: the constructed reflection failed its own check.
  | NormClauseFails Mat
      -- ^ @W@ is not unitary.  For a typed program this cannot happen; for an
      -- arbitrary term of the grammar it can, and it is the extra clause the
      -- untyped statement of the criterion carries.
  | WitnessIllTyped TypeError
  | WitnessDenotationDiffers

-- One constructor for each hypothesis of the construction.
-- >>> ZeroMap
-- the core map is zero: no state, hence no obligation
-- >>> DoesNotFactor 2 Nothing
-- the drop is unsafe: the slices span 2 dimensions, not one
-- >>> ParkedNormNotInGateRing (fromInt 3)
-- the parked state has squared norm 3, which has no square root in the coefficient field, so no gate over that field prepares it; the drop is semantically safe but the source witness does not exist over this ring
-- >>> ComplexParkedState [kimag, kzero]
-- the parked state is not real; the Householder witness is real-only (over C the factors are determined only up to a compensating phase)

instance Show Reason where
  show (DoesNotFactor r mn) =
    "the drop is unsafe: the slices span " ++ show r ++ " dimensions, not one"
    ++ case mn of
         Nothing -> ""
         Just ((a,b),(a',b'),x,y) ->
           "\n    the 2x2 minor at rows " ++ show (a,a') ++ ", columns "
           ++ show (b,b') ++ " does not vanish: " ++ show x ++ " /= " ++ show y
  show ZeroMap = "the core map is zero: no state, hence no obligation"
  show (ParkedNormNotInGateRing n) =
    "the parked state has squared norm " ++ show n
    ++ ", which has no square root in the coefficient field, so no gate over "
    ++ "that field prepares it; the drop is semantically safe but the source "
    ++ "witness does not exist over this ring"
  show (ComplexParkedState _) =
    "the parked state is not real; the Householder witness is real-only "
    ++ "(over C the factors are determined only up to a compensating phase)"
  show (ParkedStateNotUnit n) = "internal: normalised parked state has norm^2 " ++ show n
  show (ReflectionFailed _)   = "internal: the reflection failed its own unitarity check"
  show (NormClauseFails _) =
    "the residual visible map is not unitary, so it is not a legal gate; this is "
    ++ "the norm clause the untyped criterion carries and typing discharges"
  show (WitnessIllTyped e)    = "the emitted witness does not type: " ++ show e
  show WitnessDenotationDiffers =
    "the emitted witness types but denotes a different map (this would be a bug)"

-- >>> show ZeroMap
-- "the core map is zero: no state, hence no obligation"
-- >>> show (ComplexParkedState [kimag])
-- "the parked state is not real; the Householder witness is real-only (over C the factors are determined only up to a compensating phase)"

-- | A successful synthesis: the mathematical data, the emitted program, and the
-- flag saying whether the construction was in its degenerate case.
data Witness = Witness
  { wParked     :: Vec       -- ^ @g@, a unit vector
  , wVisible    :: Mat       -- ^ @W@, unitary
  , wPrepare    :: Mat       -- ^ @R@, the reflection (or the identity)
  , wProgram    :: Program   -- ^ @sep(R, W)@: the certificate, as source text
  , wTyped      :: TypedProgram
  , wDegenerate :: Bool      -- ^ @g = e_{i0}@, so @R = I@ and no reflection was needed
  }

-- A witness for spread-and-park: g = (1, 1)/sqrt 2, W = I, R the reflection (not the identity).
-- >>> :m + Drop.Theory.Program.Typing
-- >>> let Right park = checkProgram spreadAndPark
-- >>> let Right wit = synthesize park
-- >>> let Right silq = checkProgram twoGateSilq
-- >>> let Right rd = checkProgram spreadAndRead
-- >>> let Right noth = checkProgram doNothing
-- >>> (wParked wit, wVisible wit, wDegenerate wit)
-- ([sqrt2/2,sqrt2/2],[[1,0],[0,1]],False)
-- >>> wPrepare wit
-- [[sqrt2/2,sqrt2/2],[sqrt2/2,-sqrt2/2]]
-- >>> mapM_ print (lines (prettySugared (wProgram wit)))
-- "-- witness for program (a): spread and park"
-- "let t = new |0> in"
-- "  t1 := R t;  v1 := v"
-- "  v2 := W v1;  t2 := t1"
-- "  drop t2;"
-- "  return v2"

-- | The converse direction, as an algorithm.  Returns the witness program, or
-- the hypothesis that failed.
synthesize :: TypedProgram -> Either Reason Witness
synthesize tp = do
  cert <- case verdict tp of
            Unreachable     -> Left ZeroMap
            Unsafe mn r -> Left (DoesNotFactor r mn)
            Safe c      -> Right c
  -- 1. normalise so that ||g|| = 1
  let g0 = certParked cert
      w0 = certVisible cert
      n2 = vnorm2 g0
  c <- maybe (Left (ParkedNormNotInGateRing n2)) Right (ksqrtReal n2)
  let g = map (`kdiv` c) g0
      w = matScale c w0
  -- 2. the type system's one clause
  _ <- if matIsUnitary w then Right () else Left (NormClauseFails w)
  -- 3. the preparation gate
  r <- householder d i0 g
  -- 4. emit and verify
  let prog = sepProgram ("witness for " ++ progLabel (tpProgram tp))
                        (progVis (tpProgram tp)) m d i0 r w
  wtp <- either (Left . WitnessIllTyped) Right (checkProgram prog)
  if coreMap wtp /= coreMap tp
    then Left WitnessDenotationDiffers
    else Right Witness { wParked     = g
                       , wVisible    = w
                       , wPrepare    = r
                       , wProgram    = prog
                       , wTyped      = wtp
                       , wDegenerate = matIsIdentity r }
  where
    d  = tpTmpDim tp
    m  = tpVisDim tp
    i0 = tpAlloc tp

-- Three outcomes. A safe program has a witness; an unsafe one is refused with its rank; the two-gate program needs no reflection.
-- >>> either (const "refused") (const "witness") (synthesize park)
-- "witness"
-- >>> fmap wDegenerate (synthesize park)
-- Right False
-- >>> fmap wDegenerate (synthesize silq)
-- Right True
-- >>> mapM_ print (either (lines . show) (const []) (synthesize rd))
-- "the drop is unsafe: the slices span 2 dimensions, not one"
-- "    the 2x2 minor at rows (0,1), columns (0,1) does not vanish: 1/2 /= 0"
-- >>> [ n | (n, p) <- catalogue, Right tp <- [checkProgram p], Left _ <- [synthesize tp] ]
-- ["example-B","tilt-read","kickback","cz-copy","compute-alone"]

-- | Independent re-check of a witness: it must type, and its denotation must
-- equal the original's exactly.  'synthesize' already runs this; it is
-- exported separately so that a witness produced by hand or by another tool
-- can be verified the same way.
checkWitness :: TypedProgram -> Witness -> Bool
checkWitness tp wit =
  case checkProgram (wProgram wit) of
    Left _     -> False
    Right wtp  -> coreMap wtp == coreMap tp

-- A witness for one program is not a witness for another.
-- >>> checkWitness park wit
-- True
-- >>> checkWitness noth wit
-- False

-- | A human-readable account of what the construction did, for the CLI.
explainWitness :: TypedProgram -> Either Reason Witness -> [String]
explainWitness tp (Left rsn) =
  kv "no source witness for" (progLabel (tpProgram tp))
  ++ kv "reason" (show rsn)
explainWitness tp (Right wit) =
  kvs [ ("parked state  g",  showVecW (wParked wit))
      , ("its ray  [g]",     showVecW (canonicalLine (wParked wit))) ]
  ++ blank
  ++ boxedMat "W" (map (map showK) (wVisible wit))
  ++ blank
  ++ boxedMat "R" (map (map showK) (wPrepare wit))
  ++ blank
  ++ para (if wDegenerate wit
             then "R is the identity here: g is the allocated basis state, so \
                  \no reflection is needed."
             else "R is a Householder reflection exchanging e_{i0} and g. It \
                  \is one gate, and there is never a second.")
  ++ blank
  ++ para "The witness, as source text:"
  ++ blank
  ++ gutter (prettySugared (wProgram wit))
  ++ blank
  ++ para ("The witness types, and its core map is equal to the original's "
           ++ "entry by entry in exact arithmetic, so the acceptance is a "
           ++ "program you can run, not an existence claim about matrices. "
           ++ okBad "checked" "the check failed" (checkWitness tp wit))

-- >>> explainWitness park (synthesize park) == explainWitness park (Right wit)
-- True
-- >>> mapM_ print (take 2 (explainWitness rd (synthesize rd)))
-- "  no source witness for           : example (B) = program (b): spread and read"
-- "  reason                          : the drop is unsafe: the slices span 2"

-- | A vector, in the notation the printed tables use.
showVecW :: Vec -> String
showVecW v = "[" ++ intercalate ", " (map showK v) ++ "]"

-- >>> showVecW [kone, khalf, kimag]
-- "[1, 1/2, i]"
-- >>> showVecW []
-- "[]"
