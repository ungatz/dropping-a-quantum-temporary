-- |
-- Module      : DQT.Corpus.Producer
--
-- Two producer rules compared with the criterion over the
-- catalogue: R1 ('qfreeAccepts') is unsound; R2 ('producerAccepts') adds a
-- no-inflow clause and is sound but strictly incomplete.
module DQT.Corpus.Producer
  ( -- * The criterion, for rules to be compared against
    criterionAdmits
    -- * R1: gate classicality
  , isQfreeMat
  , qfreeAccepts
  , qfreeIsSound
  , qfreeUnsoundnessWitnesses
    -- * R2: classicality and no inflow
  , noInflowGate
  , producerAccepts
  , producerIsSound
  , producerIncompletenessWitnesses
    -- * The counts the tables print
  , r1Count
  , r2Count
  , safeCount
    -- * Reporting
  , producerReport
  , catalogueTex
  ) where

import DQT.Criterion (Verdict (..), verdict)
import DQT.Calculus.Elaborate (coreMap)
import DQT.Corpus.Examples  (catalogue)
import DQT.Algebra.Linear    (Mat, matRows)
import DQT.Algebra.Scalar    (kIsZero, showK)
import DQT.Calculus.Syntax    (Gate (..), GateKind (..), Program (..), Term (..),
                      prettySugared)
import DQT.Calculus.Typing    (TypedProgram, checkProgram)

typed :: Program -> Maybe TypedProgram
typed p = either (const Nothing) Just (checkProgram p)

-- | Is the drop of this program accepted by the criterion?  A vacuous verdict
-- counts as accepted: there is no state for the drop to be about.
criterionAdmits :: Program -> Bool
criterionAdmits p = case typed p >>= (Just . verdict) of
  Just (Safe _) -> True
  Just Vacuous  -> True
  _             -> False

-- R1: gate classicality

-- | Creates-no-superposition, as a predicate on a matrix: every column has
-- at most one nonzero entry (monomial), sending each basis state to a
-- basis state up to a scalar.
isQfreeMat :: Mat -> Bool
isQfreeMat m = all colOk [0 .. n - 1]
  where
    n = matRows m
    colOk j = length [ () | i <- [0 .. n - 1], not (kIsZero (m !! i !! j)) ] <= 1

-- | R1 accepts the automatic drop exactly when every gate that touched the
-- temporary is classical in the sense of 'isQfreeMat'.
qfreeAccepts :: Program -> Bool
qfreeAccepts p = go (progTerm p)
  where
    go (New _ _ _ e) = go e
    go (Act _ g _ e) = (gateKind g == OnVis || isQfreeMat (gateMat g)) && go e
    go (Drop _ e)    = go e
    go _             = True

-- | Is gate classicality alone a sound discard discipline? It is not:
-- 'qfreeUnsoundnessWitnesses' names the counterexamples, since a leak can
-- be carried by a permutation, which creates no superposition.
qfreeIsSound :: Bool
qfreeIsSound = null qfreeUnsoundnessWitnesses

-- | Programs R1 accepts whose drop is unsafe.  Each is a permutation program
-- that moves information from the visible register into the temporary.
qfreeUnsoundnessWitnesses :: [String]
qfreeUnsoundnessWitnesses =
  [ nm | (nm, p) <- catalogue, qfreeAccepts p, not (criterionAdmits p) ]

-- R2: classicality and no inflow

-- | The missing clause: no information flows into the temporary.
--
-- For a gate on @tmp (x) vis@: the output temporary basis state depends
-- only on the input one, not the visible one. On a monomial gate
-- @U(e_i (x) e_j) = c . e_{a(i,j)} (x) e_{b(i,j)}@, @a(i,j)@ must be
-- independent of @j@ (the executable stand-in for a producer's @const@ use).
noInflowGate :: Gate -> Bool
noInflowGate g
  | gateKind g == OnVis = True
  | otherwise           = all sameRow [0 .. d - 1]
  where
    d = gateTmpDim g
    m = gateVisDim g
    u = gateMat g
    -- the temporary basis state(s) reachable from tmp basis state i and visible input j
    tmpOut i j = [ r `div` m | r <- [0 .. d * m - 1]
                 , not (kIsZero (u !! r !! (i * m + j))) ]
    sameRow i = case map (tmpOut i) [0 .. m - 1] of
      []       -> True
      (x : xs) -> all (== x) xs

-- | R2: every gate touching the temporary is classical, and no gate writes
-- visible data into the temporary.
producerAccepts :: Program -> Bool
producerAccepts p = qfreeAccepts p && go (progTerm p)
  where
    go (New _ _ _ e) = go e
    go (Act _ g _ e) = noInflowGate g && go e
    go (Drop _ e)    = go e
    go _             = True

-- | With the dataflow clause restored the rule is sound: every program R2
-- accepts, the criterion accepts.
producerIsSound :: Bool
producerIsSound = and [ criterionAdmits p | (_, p) <- catalogue, producerAccepts p ]

-- | Where R2 is still incomplete: the safe drops it refuses.
producerIncompletenessWitnesses :: [String]
producerIncompletenessWitnesses =
  [ nm | (nm, p) <- catalogue, not (producerAccepts p), criterionAdmits p ]

-- The counts

-- | How many catalogue programs R1 accepts.
r1Count :: Int
r1Count = length [ () | (_, p) <- catalogue, qfreeAccepts p ]

-- | How many catalogue programs R2 accepts.
r2Count :: Int
r2Count = length [ () | (_, p) <- catalogue, producerAccepts p ]

-- | How many catalogue programs the criterion accepts.
safeCount :: Int
safeCount = length [ () | (_, p) <- catalogue, criterionAdmits p ]

-- LaTeX emitters

verdictWord :: Program -> String
verdictWord p = case typed p >>= (Just . verdict) of
  Just (Safe _) -> "SAFE"
  Just Vacuous  -> "VACUOUS"
  _             -> "UNSAFE"

-- | Why the criterion said what it said, in one clause.
reasonOf :: Program -> String
reasonOf p = case typed p >>= (Just . verdict) of
  Just (Safe _)      -> "slices collinear: the temporary carries nothing about $v$"
  Just Vacuous       -> "the zero map: no state, so no obligation"
  Just (Unsafe _ r)  -> "slice rank " ++ show r ++ ": the temporary carries "
                        ++ show (r - 1) ++ " dimension(s) about $v$"
  Nothing            -> "does not typecheck"

-- | Every catalogue program: its source, and what each rule says.  A table of
-- verdicts is generated from this, so no verdict is a second copy of a fact
-- the code already decides.
catalogueTex :: String
catalogueTex = unlines (concatMap block catalogue)
  where
    -- Two pairs of catalogue programs print identical source (dj-constant
    -- / dj-balanced both read @Uf@; bv-0 / bv-1 both read @Us@), so where
    -- source does not separate two programs, print the denotation instead
    -- (what the criterion reads). The label line is dropped first, since
    -- what is compared is what is printed.
    printed         = drop 1 . lines . prettySugared
    collides (_, q) = length [ () | (_, r) <- catalogue
                                  , printed r == printed q ] > 1
    coreLines pr    = maybe [] coreMap (typed pr)
    separator e@(_, q)
      | not (collides e) = []
      | otherwise =
          [ "{\\scriptsize The source above does not distinguish this program"
          , "from the other one printing it; the elaborated core map does,"
          , "and it is what the criterion reads:\\par}"
          , "\\begin{lstlisting}[style=xlang]"
          ] ++ map (("  " ++) . unwords . map showK) (coreLines q) ++
          [ "\\end{lstlisting}" ]
    block e@(nm, p) =
      [ "\\begin{tcolorbox}[colback=white,colframe=black!45,boxrule=0.5pt,"
      , "  arc=1.5pt,left=5pt,right=5pt,top=2pt,bottom=2pt,before skip=3pt,"
      , "  after skip=3pt,fonttitle=\\footnotesize,"
      -- \hfill collapses to zero width in a narrow two-column box, which runs
      -- the name into the first verdict; the 5pt is the floor that survives it.
      , "  title={\\ttfamily " ++ tex nm ++ "\\hfill\\hspace{5pt}"
          ++ "R1 " ++ ans (qfreeAccepts p) ++ "\\enspace R2 "
          ++ ans (producerAccepts p) ++ "\\enspace criterion "
          ++ mark (verdictWord p) ++ "}]"
      , "\\begin{lstlisting}[style=xlang]"
      ] ++ drop 1 (lines (prettySugared p)) ++
      [ "\\end{lstlisting}"
      , "{\\scriptsize " ++ reasonOf p ++ ".\\par}"
      ] ++ separator e ++
      [ "\\end{tcolorbox}"
      ]
    ans True  = "\\textcolor{black!60!green}{accept}"
    ans False = "\\textcolor{red!65!black}{refuse}"
    mark "SAFE" = "\\textcolor{black!60!green}{\\textbf{SAFE}}"
    mark w      = "\\textcolor{red!65!black}{\\textbf{" ++ w ++ "}}"
    tex = concatMap (\c -> if c == '_' then "\\_" else [c])

-- Report

producerReport :: String
producerReport = unlines $
  [ "  two producer rules, run over the catalogue"
  , ""
  , "  R1 accepts when every gate touching the temporary creates no"
  , "  superposition, read as: the gate matrix is monomial. R2 adds that no"
  , "  gate writes visible data into the temporary. Both are readings of"
  , "  documented rules, not runs of any implementation, so this table is a"
  , "  comparison of rules over one catalogue."
  , ""
  , "  R1: gate classicality alone."
  , "    never accepts an unsafe drop : " ++ show qfreeIsSound
  ] ++
  [ "      unsound, witness: " ++ nm | nm <- qfreeUnsoundnessWitnesses ] ++
  [ "    A permutation can move visible data into the temporary while creating"
  , "    no superposition at all: the obstruction is classical, so no"
  , "    no-superposition test can see it. A rule about the producer of a"
  , "    value rather than about gate matrices does not have this hole, and R2"
  , "    restores that clause."
  , ""
  , "  R2: classicality and no inflow into the temporary."
  , "    never accepts an unsafe drop (sound) : " ++ show producerIsSound
  , "    safe drops it refuses (incomplete)   : "
      ++ show (length producerIncompletenessWitnesses)
  ] ++
  [ "      - " ++ nm | nm <- producerIncompletenessWitnesses ] ++
  [ ""
  , "  counts over the " ++ show (length catalogue) ++ " catalogue programs:"
  , "    R1 accepts        : " ++ show r1Count
  , "    R2 accepts        : " ++ show r2Count
  , "    criterion admits  : " ++ show safeCount
  , ""
  , "    Sound and incomplete, computed rather than asserted, which is the gap"
  , "    between a producer rule and the criterion, and the reason the criterion"
  , "    is not a reformulation of any producer test."
  ]
