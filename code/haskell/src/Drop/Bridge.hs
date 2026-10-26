{-# OPTIONS_GHC -Wno-orphans #-}
-- Drop.Bridge: the matrix checker and the state-vector checker, run against each other.
--
-- Question: Do the two checkers of this package, which reach a drop's verdict by different algorithms,
--           agree on every program of the matrix checker's catalogue?
-- Answer:   The matrix checker (Drop.Theory) builds the site map as a matrix and takes an exact rank; the
--           state-vector checker (Drop.Lang) tests dim + 1 inputs and compares lines. toS translates a
--           program of the matrix checker's syntax into the state-vector checker's, bridgeVerdict runs the
--           state-vector checker on it, and bridgeAgrees compares its verdict with the matrix checker's
--           by name. bridgeDisagreements lists the catalogue programs where they differ, and must be
--           empty. The two share the scalar field K (the orphan instances below run the state-vector
--           checker, which is polymorphic over a fractional field, at K), so the comparison holds
--           arithmetic and equality fixed and varies only the algorithm. residualAgreesWithItsCriterion is
--           a separate check inside the matrix checker: on the two lifted programs, its per-record table
--           agrees with its own criterion at every record and has an entry for every record.
-- Paper:    sec:eval (the implementation), app:implementation (the finite checks).
-- Shapes:   SProgram   a program of the state-vector checker: the visible frame, the statements, and the
--                      name of the temporary the drop is about.

module Drop.Bridge
  ( -- * Translation
    toS
  , SProgram(..)
    -- * Cross-checking the two implementations
  , bridgeReport
  , bridgeDisagreements
    -- * Cross-checking the per-record table against its criterion
  , residualAgreesWithItsCriterion
  , residualBridgeReport
  ) where

import Drop.Theory.Criterion (Verdict(..), verdict)
import Drop.Theory.Corpus.Examples (catalogue)
import Drop.Theory.Algebra.Linear (Mat)
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing (checkProgram)

import Drop.Theory.Lifted (LProgram(..), checkLProgram, ltDepth)
import Drop.Theory.Lifted.Programs (liftedWitness, liftedWitnessNoRead)
import Drop.Theory.Residual (ResidualTable(..), residualAgrees, residualCheck)

import qualified Drop.Lang.Criterion as SC
import qualified Drop.Lang.Scalar as SR
import qualified Drop.Lang.Flat as SS

-- One Scalar Field, Two Implementations

-- | @K@ is a field, so it is a 'Num' and a 'Fractional'.  The language implementation
-- is polymorphic over @(Eq a, Fractional a)@ and never calls 'abs' or
-- 'signum'.  They are defined here on the real subfield, where they mean
-- something, and refuse elsewhere rather than returning a wrong answer
-- quietly.  These are orphan instances by design: neither layer depends on
-- the other, and a bridge is where an orphan belongs.
instance Num K where
  (+)         = kadd
  (-)         = ksub
  (*)         = kmul
  negate      = kneg
  fromInteger = fromInt
  abs x
    | kIsReal x = if krealCompare x kzero == LT then kneg x else x
    -- refusal: abs of a non-real element
    | otherwise = error "Drop.Bridge: abs of a non-real element of the field"
  signum x
    | kIsZero x   = kzero
    | kIsReal x   = if krealCompare x kzero == LT then kneg kone else kone
    -- refusal: signum of a non-real element
    | otherwise   = error "Drop.Bridge: signum of a non-real element of the field"

-- >>> 2 + 3 * 4 :: K
-- 14
-- >>> (abs (-2) :: K, signum (-2) :: K, signum 0 :: K)
-- (2,-1,0)
-- >>> abs (kmul kimag kimag) :: K
-- 1

instance Fractional K where
  recip        = kinv
  fromRational = fromRat

-- >>> 1 / 3 :: K
-- 1/3
-- >>> 0.5 :: K
-- 1/2

-- | Conjugation sends @w@ to @w^{-1}@; "Drop.Theory.Algebra.Scalar" already has it as
-- 'kconj', and the language implementation's probability sites all go through it.
instance SR.Conj K where
  conj = kconj

-- >>> SR.conj kimag
-- -1i
-- >>> SR.conj kone
-- 1

instance SR.Amp K where
  showAmp = showK

-- >>> SR.showAmp (kdiv kone ktwo)
-- "1/2"

-- Translation

-- | A program of the language implementation: the visible frame, the statement list,
-- and the name of the temporary the drop is about.
data SProgram = SProgram
  { spVis    :: SS.VisSpec
  , spProg   :: SS.Prog K
  , spTarget :: String
  }

-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> fmap (\sp -> (spVis sp, spTarget sp, length (spProg sp))) (toS spreadAndPark)
-- Just ([("v",2)],"t",3)

-- | Translate an affine "Drop.Theory.Program.Syntax" program into an imperative
-- "Drop.Lang.Flat" one: names are consumed there but registers act in
-- place here, so the translation is a renaming substitution.
--
-- Allocation index handled, not assumed away: @i0 /= 0@ gets a
-- transposition carrying @0@ to @i0@ right after allocation.
--
-- A program the theory's checker refuses has no translation: the flat
-- engine would answer on it, and its answer would be about a program the
-- theory says is not one.
toS :: Program -> Maybe SProgram
toS p | Left _ <- checkProgram p = Nothing
toS p = case progTerm p of
  New t d i0 body ->
    Just SProgram
      { spVis    = [(progVis p, progVisDim p)]
      , spProg   = SS.New t d
                   : ([ SS.Gate (transposition d 0 i0) [t] | i0 /= 0 ])
                   ++ go [(t, t), (progVis p, progVis p)] body
      , spTarget = t }
  _ -> Nothing
  where
    go _ (Ret _)       = []
    go _ (Pair _ _)    = []
    go _ (New _ _ _ _) = []          -- allocFree forbids this; typing rejects it
    go sub (Act (t', v') g (t, v) e) =
      SS.Gate (gateMat g) [look sub t, look sub v]
        : go (rename (rename sub t t') v v') e
    go sub (Drop t e) = SS.Drop [look sub t] : go sub e

    look sub x = maybe x id (lookup x sub)
    rename sub old new' = [ (if a == old then new' else a, b) | (a, b) <- sub ]

-- A program the matrix checker accepts has a translation; one it refuses has none.
-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> fmap (\sp -> (spVis sp, spTarget sp, length (spProg sp))) (toS spreadAndRead)
-- Just ([("v",2)],"t",4)
-- >>> fmap (const ()) (toS (Program "bare" "v" 2 (Ret "v")))
-- Nothing

-- | The permutation matrix exchanging basis states @i@ and @j@ of a @d@-dimensional
-- register.  Its own inverse, and a legal gate.
transposition :: Int -> Int -> Int -> Mat
transposition d i j =
  [ [ entry r c | c <- [0 .. d-1] ] | r <- [0 .. d-1] ]
  where
    swap k | k == i    = j
           | k == j    = i
           | otherwise = k
    entry r c = if r == swap c then kone else kzero

-- >>> transposition 3 0 2
-- [[0,0,1],[0,1,0],[1,0,0]]
-- >>> transposition 2 0 0
-- [[1,0],[0,1]]
-- >>> :m + Drop.Theory.Algebra.Linear
-- >>> matIsUnitary (transposition 4 1 3)
-- True

-- The Comparison

-- | The language implementation's verdict on a program, reached by testing.
bridgeVerdict :: Program -> Maybe SC.Verdict
bridgeVerdict p = do
  sp <- toS p
  pure (SC.semanticVerdict (spVis sp) (spProg sp) (spTarget sp) [])

-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> bridgeVerdict spreadAndPark
-- Just Safe
-- >>> bridgeVerdict spreadAndRead
-- Just Unsafe
-- >>> bridgeVerdict (Program "bare" "v" 2 (Ret "v"))
-- Nothing

-- | The theory implementation's verdict, as a name.
theoryName :: Verdict -> String
theoryName (Safe _)     = "Safe"
theoryName (Unsafe _ _) = "Unsafe"
theoryName Unreachable  = "Unreachable"

-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> fmap (theoryName . verdict) (checkProgram spreadAndPark)
-- Right "Safe"
-- >>> fmap (theoryName . verdict) (checkProgram spreadAndRead)
-- Right "Unsafe"
-- >>> theoryName Unreachable
-- "Unreachable"

-- | The language implementation's verdict, as a name.  Both layers use the words
-- Safe, Unsafe and Unreachable.
languageName :: SC.Verdict -> String
languageName = show

-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> fmap languageName (bridgeVerdict spreadAndPark)
-- Just "Safe"
-- >>> fmap languageName (bridgeVerdict spreadAndRead)
-- Just "Unsafe"

-- | Do the two implementations agree on this program?
bridgeAgrees :: Program -> Bool
bridgeAgrees p = case (checkProgram p, bridgeVerdict p) of
  (Right tp, Just sv) -> theoryName (verdict tp) == languageName sv
  _ -> False

-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> bridgeAgrees spreadAndPark
-- True
-- >>> bridgeAgrees spreadAndRead
-- True
-- >>> bridgeAgrees (Program "bare" "v" 2 (Ret "v"))
-- False

-- | Every catalogue program on which the two implementations differ.  Must be empty.
bridgeDisagreements :: [String]
bridgeDisagreements = [ n | (n, p) <- catalogue, not (bridgeAgrees p) ]

-- The catalogue has seventeen programs and the two checkers agree on all of them.
-- >>> bridgeDisagreements
-- []
-- >>> length catalogue
-- 17

-- | The two verdicts, printed side by side as a table.
bridgeReport :: String
bridgeReport = unlines $
  [ "  the theory engine builds K and takes a rank; the language engine probes"
  , "  dim+1 inputs and compares lines. They must agree everywhere."
  , ""
  , "  " ++ pad 16 "program" ++ pad 20 "theory engine" ++ "language engine" ]
  ++ [ "  " ++ pad 16 n ++ pad 20 (theory p) ++ language p | (n, p) <- catalogue ]
  ++ [ "", "  disagreements: " ++ show bridgeDisagreements ]
  where
    pad k s = s ++ replicate (max 0 (k - length s)) ' '
    theory p = case checkProgram p of
      Left _   -> "ill-typed"
      Right tp -> theoryName (verdict tp)
    language p = maybe "untranslatable" languageName (bridgeVerdict p)

-- The first lines of the table, shown as strings.
-- >>> mapM_ print (take 5 (lines bridgeReport))
-- "  the theory engine builds K and takes a rank; the language engine probes"
-- "  dim+1 inputs and compares lines. They must agree everywhere."
-- ""
-- "  program         theory engine       language engine"
-- "  example-A       Safe                Safe"
-- >>> length (lines bridgeReport)
-- 23

-- The Table Against Its Criterion

-- | The matrix checker's per-record table ("Drop.Theory.Residual"), on the two lifted
-- programs: for each program, does the table agree with the matrix checker's own
-- criterion at every record, and does it have an entry for every record?  A table
-- that abstains does not agree.
residualAgreesWithItsCriterion :: [(String, Bool, Bool)]
residualAgreesWithItsCriterion =
  [ ( lLabel p
    , agreesAtEveryRecord p
    , hasEveryRecord p )
  | p <- [liftedWitness, liftedWitnessNoRead] ]
  where
    agreesAtEveryRecord p = case checkLProgram p of
      Left _   -> False
      Right tp -> residualAgrees tp == Just []
    hasEveryRecord p = case checkLProgram p of
      Left _   -> False
      Right tp -> length (rtEntries (residualCheck tp)) == 2 ^ ltDepth tp

-- >>> residualAgreesWithItsCriterion
-- [("the witness: tilt, lift {0,1}, read under a vacuous conditional, drop",True,True),("the witness with the read deleted: tilt, lift, drop",True,True)]

-- | The same two facts, printed.
residualBridgeReport :: String
residualBridgeReport = unlines $
  [ "  the runtime check, checked twice over: it must agree with the criterion"
  , "  at every entry, and its table must have an entry for every measurement record."
  , "" ]
  ++ [ "  " ++ lbl ++ "\n      agrees with the criterion everywhere : " ++ show a
       ++ "\n      table covers every measurement record       : " ++ show b
     | (lbl, a, b) <- residualAgreesWithItsCriterion ]

-- >>> mapM_ print (lines residualBridgeReport)
-- "  the runtime check, checked twice over: it must agree with the criterion"
-- "  at every entry, and its table must have an entry for every measurement record."
-- ""
-- "  the witness: tilt, lift {0,1}, read under a vacuous conditional, drop"
-- "      agrees with the criterion everywhere : True"
-- "      table covers every measurement record       : True"
-- "  the witness with the read deleted: tilt, lift, drop"
-- "      agrees with the criterion everywhere : True"
-- "      table covers every measurement record       : True"
