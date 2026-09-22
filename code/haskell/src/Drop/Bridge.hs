{-# OPTIONS_GHC -Wno-orphans #-}
-- |
-- Module      : Drop.Bridge
--
-- The cross-check of the implementation section: the theory layer builds the denotation as
-- a matrix and takes an exact rank; the language layer instead tests
-- @dim + 1@ inputs and compares lines.  The two decision procedures share no
-- code.  They do share a backend: the orphan instances below run the
-- language layer, which is polymorphic over @(Eq a, Fractional a)@, at the
-- theory layer's exact scalar field @K@, so the comparison holds arithmetic
-- and equality fixed and varies only the algorithm.  That is what the paper
-- claims and it is less than two wholly independent implementations.
module Drop.Bridge
  ( -- * Translation
    toS
  , SProgram(..)
    -- * The two vocabularies
  , verdictDictionary
    -- * Cross-checking the two implementations
  , bridgeVerdict
  , bridgeAgrees
  , bridgeReport
  , bridgeDisagreements
    -- * Cross-checking the two runtime checks
  , residualAgreesAcrossEngines
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

import qualified Drop.Lang.Interp as SI
import qualified Drop.Lang.Ring as SR
import qualified Drop.Lang.Syntax as SS

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
    | otherwise = error "Drop.Bridge: abs of a non-real element of the field"
  signum x
    | kIsZero x   = kzero
    | kIsReal x   = if krealCompare x kzero == LT then kneg kone else kone
    | otherwise   = error "Drop.Bridge: signum of a non-real element of the field"

instance Fractional K where
  recip        = kinv
  fromRational = fromRat

-- | Conjugation sends @w@ to @w^{-1}@; "Drop.Theory.Algebra.Scalar" already has it as
-- 'kconj', and the language implementation's probability sites all go through it.
instance SR.Conj K where
  conj = kconj

instance SR.Amp K where
  showAmp = showK

-- Translation

-- | A program of the language implementation: the visible frame, the statement list,
-- and the name of the temporary the drop is about.
data SProgram = SProgram
  { spVis    :: SS.VisSpec
  , spProg   :: SS.Prog K
  , spTarget :: String
  }

-- | Translate an affine "Drop.Theory.Program.Syntax" program into an imperative
-- "Drop.Lang.Syntax" one: names are consumed there but registers act in
-- place here, so the translation is a renaming substitution.
--
-- Allocation index handled, not assumed away: @i0 /= 0@ gets a
-- transposition carrying @0@ to @i0@ right after allocation.
toS :: Program -> Maybe SProgram
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

-- The Comparison

-- | The language implementation's verdict on a program, reached by testing.
bridgeVerdict :: Program -> Maybe SI.Verdict
bridgeVerdict p = do
  sp <- toS p
  pure (SI.semanticVerdict (spVis sp) (spProg sp) (spTarget sp) [])

-- | The two vocabularies, side by side.  The layers now share the word for
-- two of the three verdicts (both say Safe, both say Unsafe); stating the
-- correspondence as data rather than burying it in a @case@ still means
-- there is one place to look and one place to change, for the one name that
-- does differ: theory's Vacuous and language's Unreachable are the same
-- verdict, no state so no obligation.
verdictDictionary :: [(String, String)]
verdictDictionary =
  [ ("Safe",    "Safe")
  , ("Unsafe",  "Unsafe")
  , ("Vacuous", "Unreachable") ]

-- | The theory implementation's verdict, as the name the dictionary uses.
theoryName :: Verdict -> String
theoryName (Safe _)     = "Safe"
theoryName (Unsafe _ _) = "Unsafe"
theoryName Vacuous      = "Vacuous"

-- | The language implementation's verdict, as the name the dictionary uses.
languageName :: SI.Verdict -> String
languageName = show

-- | Do the two implementations agree on this program?
bridgeAgrees :: Program -> Bool
bridgeAgrees p = case (checkProgram p, bridgeVerdict p) of
  (Right tp, Just sv) ->
    lookup (theoryName (verdict tp)) verdictDictionary == Just (languageName sv)
  _ -> False

-- | Every catalogue program on which the two implementations differ.  Must be empty.
bridgeDisagreements :: [String]
bridgeDisagreements = [ n | (n, p) <- catalogue, not (bridgeAgrees p) ]

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

-- The Second Cross-Check: Two Runtime Checks

-- | Two runtime checks, sharing no code: "Drop.Theory.Residual" over the lifted
-- language, "Drop.Lang.Pass" over the machine.
--
-- Each compares itself against its own criterion at every table entry;
-- this asks what those miss: do the two decline in the same places,
-- where a check is most easily wrong?
residualAgreesAcrossEngines :: [(String, Bool, Bool)]
residualAgreesAcrossEngines =
  [ ( lLabel p
    , decidesEverything p
    , tableIsExhaustive p )
  | p <- [liftedWitness, liftedWitnessNoRead] ]
  where
    decidesEverything p = case checkLProgram p of
      Left _   -> False
      Right tp -> residualAgrees tp == Just []
    tableIsExhaustive p = case checkLProgram p of
      Left _   -> False
      Right tp -> length (rtEntries (residualCheck tp)) == 2 ^ ltDepth tp

-- | The same two facts, printed.
residualBridgeReport :: String
residualBridgeReport = unlines $
  [ "  the runtime check, checked twice over: it must agree with the criterion"
  , "  at every entry, and its table must have an entry for every measurement record."
  , "" ]
  ++ [ "  " ++ lbl ++ "\n      agrees with the criterion everywhere : " ++ show a
       ++ "\n      table covers every measurement record       : " ++ show b
     | (lbl, a, b) <- residualAgreesAcrossEngines ]
