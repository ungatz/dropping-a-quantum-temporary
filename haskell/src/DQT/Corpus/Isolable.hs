-- |
-- Module      : DQT.Corpus.Isolable
--
-- R3: the lifetime discipline of Qutes, run against the criterion over the
-- catalogue.
--
-- WHAT THE RULE IS, AND WHERE IT COMES FROM.  Faro, Marino and Messina
-- (arXiv:2603.14538) reclaim a temporary at a lifetime boundary when the
-- subcomputation is /output-isolable/.  Their Definition 5 (p.7) asks for a
-- decomposition of the subcomputation's unitary
--
-- > U = U_L . V_T
--
-- with @U_L@ acting only on the live outputs and @V_T@ acting only on the
-- temporaries; their Definition 6 (p.8) then reclaims by inserting the
-- adjoint of the temporary's history, \"restoring it to its initial state\".
-- Lemma 11 (p.15) makes output-isolability exactly the condition for
-- restoration across a boundary.
--
-- Because @U_L@ and @V_T@ act on disjoint registers, that decomposition says
-- precisely that the gate product is a /product unitary/ @A (x) B@.  So the
-- rule is decidable by the same shape of test the criterion uses -- a rank-one
-- test on a reshaping -- but of a different object: the criterion reshapes the
-- Kraus family, this reshapes the whole unitary.  See 'isProductUnitary'.
--
-- WHICH READING THIS IS, AND WHY IT MATTERS.  We implement Definition 5 /as
-- written/.  Their own worked example (p.8) does not satisfy it: the
-- subcomputation p1-p4 is decomposed there as
--
-- >   CX(t2,y1)  .  [ CX(t1,t2) ; g(x1,t2) ; f(x1,t1) ]
--
-- whose left factor acts on the temporary @t2@, not only on the live output,
-- and whose right factor reads the input @x1@, which is in neither set.  So
-- the definition admits a stricter reading (this one) and a looser one (the
-- example's), and under the looser reading the condition moves together with
-- drop safety instead of being strictly stronger.  Every number below is a
-- measurement of the STRICT reading, and no claim here should be reported as
-- "what Qutes decides" without that qualifier.
--
-- WHERE IT IS EVALUATED.  Qutes computes a semantic lifetime and may reclaim
-- early.  The catalogue's programs name their drop site, so the subcomputation
-- between allocation and that drop is the whole gate product, and that is what
-- we test.  This is the most generous reading: an earlier boundary can only
-- have less history to factor.
--
-- WHAT WE EXPECT, AND WHY (strict reading).  The rule is sound and strictly
-- incomplete.  Sound
-- because @U = A (x) B@ sends @i0 (x) v@ to @(A i0) (x) (B v)@, which is the
-- shape @g (x) W@ of the criterion.  Incomplete because a program may reach
-- that shape /on the allocated state/ without the unitary factoring at all:
-- phase kickback is the standard case, and the witnesses are named by
-- 'isolableIncompletenessWitnesses'.
module DQT.Corpus.Isolable
  ( -- * The test
    isProductUnitary
  , gateProduct
    -- * R3: output-isolability at the drop site
  , isolableAccepts
  , isolableIsSound
  , isolableIncompletenessWitnesses
  , r3Count
    -- * Reporting
  , isolableReport
  ) where

import DQT.Algebra.Linear   (Mat, matMul, matId, rank)
import DQT.Calculus.Syntax  (Gate (..), Program (..), Term (..))
import DQT.Corpus.Examples  (catalogue)
import DQT.Corpus.Producer  (criterionAdmits)

-- | Is @u@, a unitary on @H_d (x) H_m@ with the temporary most significant,
-- a product @A (x) B@?
--
-- The test is a rank-one test on the realignment.  Index @u@ by row @(i,j)@
-- and column @(k,l)@ with @i,k@ over the temporary and @j,l@ over the visible
-- register, and form the @d^2 x m^2@ matrix
--
-- > R[(i,k), (j,l)] = u[(i,j), (k,l)] .
--
-- If @u = A (x) B@ then @u[(i,j),(k,l)] = A[i][k] * B[j][l]@, so @R@ is the
-- outer product of the flattenings of @A@ and @B@ and has rank one; and
-- conversely a rank-one @R@ factors as such an outer product, which is a
-- decomposition of @u@.  Rank is exact, over the same scalar field as the
-- criterion, so the verdict is a decision and not an estimate.
isProductUnitary :: Int -> Int -> Mat -> Bool
isProductUnitary d m u = rank realign <= 1
  where
    realign = [ [ u !! (i * m + j) !! (k * m + l)
                | j <- [0 .. m - 1], l <- [0 .. m - 1] ]
              | i <- [0 .. d - 1], k <- [0 .. d - 1] ]

-- | The product of a program's gates, on @H_d (x) H_m@, in the order the
-- denotation applies them (later gates on the left).  'Nothing' when the
-- program allocates no temporary, where the rule has nothing to say.
gateProduct :: Program -> Maybe (Int, Int, Mat)
gateProduct p = go (progTerm p)
  where
    m = progVisDim p
    go (New _ d _ e) = Just (d, m, walk (matId (d * m)) e)
    go _             = Nothing
    walk acc (Act _ g _ e) = walk (matMul (gateMat g) acc) e
    walk acc (Drop _ e)    = walk acc e
    walk acc (New _ _ _ e) = walk acc e
    walk acc _             = acc

-- | R3 accepts the drop exactly when the subcomputation is output-isolable,
-- that is, when the gate product factors as @A (x) B@.
isolableAccepts :: Program -> Bool
isolableAccepts p = case gateProduct p of
  Just (d, m, u) -> isProductUnitary d m u
  Nothing        -> True      -- no temporary: nothing to reclaim

-- | Is the rule sound?  It is: every program R3 accepts, the criterion
-- accepts.  This is the executable form of the implication argued in the
-- module header, and it is checked over the catalogue rather than assumed.
isolableIsSound :: Bool
isolableIsSound =
  and [ criterionAdmits p | (_, p) <- catalogue, isolableAccepts p ]

-- | Where R3 is incomplete: the safe drops it refuses.
isolableIncompletenessWitnesses :: [String]
isolableIncompletenessWitnesses =
  [ nm | (nm, p) <- catalogue
       , not (isolableAccepts p), criterionAdmits p ]

-- | How many catalogue programs R3 accepts.
r3Count :: Int
r3Count = length [ () | (_, p) <- catalogue, isolableAccepts p ]

-- | The paragraph the evaluation section prints.
isolableReport :: [String]
isolableReport =
  [ "R3, output-isolability at the drop site (Qutes, arXiv:2603.14538 Def. 5, Lem. 11)"
  , "  accepts             : " ++ show r3Count ++ " of " ++ show (length catalogue)
  , "  sound               : " ++ show isolableIsSound
  , "  safe drops refused  : " ++ show (length isolableIncompletenessWitnesses)
  ] ++ [ "    " ++ nm | nm <- isolableIncompletenessWitnesses ]
