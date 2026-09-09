-- |
-- Module      : DQT.Corpus.Examples
--
-- The catalogue: small programs, each a value of type 'Program', typed, run,
-- elaborated, judged and, when safe, rewritten into the shape @sep(R, W)@.
-- 'catalogue' lists them in the order Appendix B tabulates.
module DQT.Corpus.Examples
  ( -- * The catalogue
    catalogue
  , byName
    -- * The three worked programs
  , addTwiceNoRotate
  , spreadAndRead
  , spreadAndReadTwice
    -- * Programs (a), (b) and (c)
  , spreadAndPark
  , twoGateSilq
  , tiltThenRead
  , sepHX
    -- * Textbook algorithms
  , deutschJozsa
  , bernsteinVazirani
  , groverOracleComputeUncompute
  , czAfterSpread
    -- * The separator pair of the summary no-go
  , copyThenCopy
  , czThenCopy
    -- * The boundary witness for the contextual theorem
  , computeAlone
  , computeAloneAt
  , doNothing
  ) where

import DQT.Calculus.Gates
import DQT.Calculus.Syntax

-- Helpers

-- | Build a straight-line program: allocate a @d@-dimensional temporary in @|i0>@,
-- apply the listed gates in order, drop, return the visible register.
--
-- Names are generated, so the source text reads like the printed tables
-- rather than like a de Bruijn exercise.
straightLine :: String -> Int -> Int -> Int -> [Gate] -> Program
straightLine lbl m d i0 gs =
  Program { progLabel  = lbl
          , progVis    = "v"
          , progVisDim = m
          , progTerm   = New "t" d i0 (body (0 :: Int) "t" "v" gs) }
  where
    body _ t v []       = Drop t (Ret v)
    body n t v (g : gs') =
      let t' = "t" ++ show (n+1)
          v' = "v" ++ show (n+1)
      in Act (t', v') g (t, v) (body (n+1) t' v' gs')

-- The three worked programs

-- | @
-- let t = new |0> in
--   v := v + t;
--   v := v + t;
--   drop t;
--   return v
-- @
--
-- Safe, trivial shape: the temporary stays on @|0>@, each read adds zero,
-- so the denotation is @|0> (x) v@, @g = e_0@, @W = I@. Witness is
-- @sep(I, I)@; the two reads are simply deleted.
addTwiceNoRotate :: Program
addTwiceNoRotate =
  straightLine "example (A): read twice, never rotate" 2 2 0 [gRead 2, gRead 2]

-- | @
-- let t = new |0> in
--   t := H t;
--   v := v + t;
--   drop t; v
-- @
--
-- Unsafe (program (b)): after @H@ the temporary is @(|0>+|1>)\/sqrt2@, the
-- read correlates it with @v@, giving @(|0>|v> + |1>|v+1>)\/sqrt2@, rank
-- two across the cut. No product replacement beats @1\/sqrt2@ of the input
-- norm, the worst value in dimension two.
spreadAndRead :: Program
spreadAndRead =
  straightLine "example (B) = program (b): spread and read" 2 2 0 [gHt 2, gRead 2]

-- | @
-- let t = new |0> in
--   t := H t;
--   v := v + t;
--   v := v + t;
--   drop t; v
-- @
--
-- Safe: same producing code as the unsafe program above, but reads twice;
-- at dimension two @2t = 0 (mod 2)@, so the reads cancel and the
-- denotation is @((|0>+|1>)\/sqrt2) (x) v@, shape @sep(H, I)@.
--
-- The witness text differs from the source ('source-weakenable');
-- 'DQT.Criterion.Witness.synthesize' produces one that shows @sep@.
spreadAndReadTwice :: Program
spreadAndReadTwice =
  straightLine "example (C): spread and read twice" 2 2 0 [gHt 2, gRead 2, gRead 2]

-- Programs (a), (b) and (c)

-- | Program (a): rotate the temporary, never touch the visible register,
-- drop. Safe. It does not restore the temporary, refuting the guess that
-- the rule is to put it back as found.
spreadAndPark :: Program
spreadAndPark = straightLine "program (a): spread and park" 2 2 0 [gHt 2]

-- | The two-gate program the introduction opens with: @H@ twice, then discard.
-- @H H = I@, so the temporary is handed back exactly as allocated.  Safe, with
-- the degenerate witness, and refused by a producer-based discipline, because
-- the producer of the value is @H@.
twoGateSilq :: Program
twoGateSilq = straightLine "the two-gate Silq program: H, H, drop" 2 2 0 [gHt 2, gHt 2]

-- | A program literally of the shape @sep(R, W)@: one gate on the
-- temporary, one gate on the visible register, then the drop.
-- 'DQT.Criterion.Witness.inSepShape' is @True@ here and @False@ elsewhere
-- in the catalogue, including safe programs that are /source-weakenable/
-- to this shape without being in it.
sepHX :: Program
sepHX = straightLine "sep(H, X): literally of the separable shape" 2 2 0
          [gHt 2, onVis "X" 2 mX]

-- | Program (c) without its measurement: tilt the three-dimensional
-- temporary, then read. Unsafe as it stands; the measurement that makes
-- the verdict depend on the run lives in "DQT.Lifted".
tiltThenRead :: Program
tiltThenRead =
  straightLine "program (c), unlifted: tilt then read" 3 3 0
    [gTiltT 3, gRead 3]

-- Textbook algorithms

-- | Deutsch–Jozsa on a one-bit domain, with the phase-kickback ancilla.
--
-- > t := new |0>; t := X t; t := H t;   (ancilla prepared on |->)
-- > v := H v;
-- > (v,t) := Uf(v,t);                   (phase kickback)
-- > v := H v;
-- > drop t; v
--
-- Safe: after @Uf@ the state is @(sum_j (-1)^{f(j)} c_j |j>) (x) |->@ at
-- every input, so the denotation is @|-> (x) (H D_f H)@. The ancilla is
-- never restored to @|0>@, spread-and-park with an algorithm attached.
deutschJozsa :: (Int -> Int) -> Program
deutschJozsa f =
  straightLine ("Deutsch-Jozsa, f = " ++ show (map f [0,1])) 2 2 0
    [ gXt 2, gHt 2
    , onVis "H" 2 mH
    , joint "Uf" 2 2 (uf f)
    , onVis "H" 2 mH ]
  where
    -- U_f |t, v> = |t (+) f(v), v>, with the temporary first, by convention.
    uf fn = permMat 4 (\k -> let t = k `div` 2
                                 v = k `mod` 2
                             in (if fn v == 1 then 1 - t else t) * 2 + v)

-- | Bernstein–Vazirani at one hidden bit: the same shape, with @W = X^s@.
bernsteinVazirani :: Int -> Program
bernsteinVazirani s =
  straightLine ("Bernstein-Vazirani, s = " ++ show s) 2 2 0
    [ gXt 2, gHt 2
    , onVis "H" 2 mH
    , joint "Us" 2 2 (us s)
    , onVis "H" 2 mH ]
  where
    us sb = permMat 4 (\k -> let t = k `div` 2
                                 v = k `mod` 2
                             in (if sb * v `mod` 2 == 1 then 1 - t else t) * 2 + v)

-- | The compute–uncompute pattern: entangle the temporary with the visible
-- register, do visible work, run the entangling gate backwards.
--
-- Safe: the drop leaves the temporary constant on @|0>@. The one place
-- where this criterion and a producer discipline agree on an automatic
-- discard.
groverOracleComputeUncompute :: Program
groverOracleComputeUncompute =
  straightLine "Grover oracle, compute-uncompute" 2 2 0
    [ gCompute, gZt 2, gCompute ]

-- | Phase kickback, unsafe. Spread the temporary, then apply @cZ@:
--
-- > |0>|v>  --H-->  (|0>+|1>)/sqrt2 (x) |v>  --cZ-->  ((|0> + (-1)^v |1>)/sqrt2) (x) |v>.
--
-- The state factors at every input, yet the drop stays unsafe: the
-- temporary's line depends on the input, @|+>@ at @v = 0@ and @|->@ at
-- @v = 1@. Discard safety is a property of the map, not of the state at a
-- point: the state at one input is a product, the map has rank two.
czAfterSpread :: Program
czAfterSpread = straightLine "phase kickback: spread, then cZ" 2 2 0 [gHt 2, gCZ]

-- The separator pair

-- | @copy ; copy@: safe.  Two @CNOT@s compose to the identity.
copyThenCopy :: Program
copyThenCopy = borrowed "copy ; copy" [gCopy, gCopy]

-- | @cZ ; copy@: unsafe. Same input-to-basis-state correspondence as
-- @copy ; copy@ (both leave the temporary on its own basis state per
-- input), yet one is safe and the other makes a Bell state: the no-go
-- for summaries that forget the visible action.
czThenCopy :: Program
czThenCopy = borrowed "cZ ; copy" [gCZ, gCopy]

-- | The separator pair lends the temporary in the balanced state, so the
-- allocation is followed by an @H@ on the temporary: in a calculus whose @new@
-- allocates a basis state, preparing the balanced state is one gate.
borrowed :: String -> [Gate] -> Program
borrowed lbl gs = straightLine lbl 2 2 0 (gHt 2 : gs)

-- The boundary witness: why right extension is necessary

-- | @let t = new |0> in (t,v) := compute(t,v); drop t; v@: copy the visible
-- register into the temporary and drop it.
--
-- Unsafe, maximally: denotation @v |-> sum_j v_j |j>|j>@, Kraus rank two.
-- A continuation appending nothing cannot tell: outcomes are @|v_j|^2@ at
-- every input, exactly 'doNothing'; a mixing gate is needed to see it.
computeAlone :: Program
computeAlone = straightLine "compute alone (copy the visible register)" 2 2 0 [gCompute]

-- | 'computeAlone' at every dimension: @d@-dimensional temporary and
-- visible register, single permutation @|t, v> |-> |t + v mod d, v>@.
--
-- Separates a gate-classicality rule from the criterion: every member is a
-- permutation (accepted by a superposition-only rule) yet writes @v@ into
-- the temporary (refused by the criterion, at rank @d@).
computeAloneAt :: Int -> Program
computeAloneAt d =
  straightLine ("compute alone at dimension " ++ show d) d d 0 [gComputeAt d]

-- | @let t = new |0> in drop t; v@, written with two identity gates so that it
-- is literally of the shape @sep(1, 1)@.  The separable program the previous one
-- cannot be told apart from, without a mixing continuation.
doNothing :: Program
doNothing = straightLine "sep(1,1): allocate and drop" 2 2 0
              [onTmp "1" (mId 2) 2, gIdent 2 2]

-- The catalogue

catalogue :: [(String, Program)]
catalogue =
  [ ("example-A",       addTwiceNoRotate)
  , ("example-B",       spreadAndRead)
  , ("example-C",       spreadAndReadTwice)
  , ("park",            spreadAndPark)
  , ("silq-two-gate",   twoGateSilq)
  , ("tilt-read",       tiltThenRead)
  , ("in-shape",        sepHX)
  , ("dj-constant",     deutschJozsa (const 0))
  , ("dj-balanced",     deutschJozsa id)
  , ("bv-0",            bernsteinVazirani 0)
  , ("bv-1",            bernsteinVazirani 1)
  , ("grover-oracle",   groverOracleComputeUncompute)
  , ("kickback",        czAfterSpread)
  , ("copy-copy",       copyThenCopy)
  , ("cz-copy",         czThenCopy)
  , ("compute-alone",   computeAlone)
  , ("do-nothing",      doNothing)
  ]

byName :: String -> Maybe Program
byName n = lookup n catalogue
