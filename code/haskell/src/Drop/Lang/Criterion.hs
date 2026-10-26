-- Drop.Lang.Criterion: is this drop safe?
--
-- Question: When is a drop safe, and how is that decided exactly, with no rounding?
-- Answer:   At a site the state must factor as a fixed state of the dropped block tensored with a
--           linear map of the rest. For a block of temporaries, probeResult runs dim + 1 test inputs
--           and asks State's exact minor test whether the block's factor is the same line each time;
--           a zero-weight probe is skipped, not failed. For a block that holds a loan, the fixed
--           state is replaced by an isometry B from the loan's space to the block: loanResultS builds
--           the bilinear map from every basis input, reshapes it and tests B^dagger B for a scalar
--           multiple of the identity. verdict reports every site under every selection.
-- Paper:    fig:criterion (the criterion), sec:factor (the factorization), fig:loan-return (the loan),
--           prop:loangram (Gram rank refutes a loan), app:criterion:proofs (the proofs).
-- Shapes:   Verdict        Safe, Unsafe or Unreachable (no probe reached the site with weight).
--           ProbeResult a  PZero (zero weight), PFail (the block does not factor) or PLine l (it does, on line l).
--           DropReport     one site with its verdict under each selection of the lifts before it.

module Drop.Lang.Criterion where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Gates (daggerM)
import Drop.Lang.Interp

-- The probes ------------------------------------------------------------------

-- | The visible basis plus the all-ones superposition: dim + 1 test inputs.
probesFor :: Num a => VisSpec -> [(String, StateV a)]
probesFor vis =
  [ ("e" ++ show j, [ if k == j then 1 else 0 | k <- [0 .. dv - 1] ])
  | j <- [0 .. dv - 1] ]
  ++ [("sum", replicate dv 1)]
  where dv = product (map snd vis)

-- The visible basis plus the all-ones vector: dim + 1 test inputs.
-- >>> map fst (probesFor [("x", 2), ("y", 2)] :: [(String, StateV Rational)])
-- ["e0","e1","e2","e3","sum"]
-- >>> probesFor [("x", 2)] :: [(String, StateV Rational)]
-- [("e0",[1 % 1,0 % 1]),("e1",[0 % 1,1 % 1]),("sum",[1 % 1,1 % 1])]

-- | The criterion's answer at one site under one selection: the block can be
-- dropped ('Safe'), cannot ('Unsafe'), or no probe reaches the site with
-- nonzero weight ('Unreachable').
data Verdict = Safe | Unsafe | Unreachable deriving (Eq, Show)

-- >>> [Safe, Unsafe, Unreachable]
-- [Safe,Unsafe,Unreachable]

-- | What one test input says of the block: the run has zero weight at the
-- site, the block does not factor, or it factors and is left on this line.
data ProbeResult a = PZero | PFail | PLine (StateV a) deriving (Eq, Show)

-- >>> [PZero, PFail, PLine [1, 0 :: Rational]]
-- [PZero,PFail,PLine [1 % 1,0 % 1]]

-- | Factor the site's registers out of the state at the drop, on one
-- visible test input and one arrival state per loan the prefix allocates.
probeResultL :: (Eq a, Fractional a)
             => VisSpec -> Prog a -> Site -> [Sel]
             -> [(String, StateV a)] -> StateV a -> ProbeResult a
probeResultL vis prog target sel env inp =
  let m = runStmts (initMachL vis inp env) prog sel (Just target)
  in if isZeroS (mAmp m) then PZero
     -- The block factor is indexed as the drop names its registers
     -- (the site definition: H_v is the tensor product of the block's spaces in the
     -- tuple's order), hence 'factorSplitOrd', not the sorted 'factorSplit'.
     else case factorSplitOrd (mDims m) (map (regPos m) target) (mAmp m) of
            Nothing       -> PFail
            Just (vA, _)  -> PLine (canonicalLine vA)

-- The temporary AND, uncomputed by measurement: on |00>, bit 1, the block a is left on the line |1>.
-- >>> :m + Drop.Lang.Programs.TempAnd
-- >>> probeResultL visXY andUncomputedByMeasurement ["a"] [SIn] [] (ket [2, 2] [0, 0]) == PLine [0, 1]
-- True

-- Without the measurement the Toffoli entangles a with x, y: on the all-ones input the block does not factor.
-- >>> probeResultL visXY andComputed ["a"] [] [] [1, 1, 1, 1]
-- PFail

-- A selection that has no weight on the input is a zero probe, skipped and not failed.
-- >>> probeResultL [("x", 2)] [Lift "p" "x" [1], Drop ["x"]] ["x"] [SIn] [] (ket [2] [0])
-- PZero

-- | 'probeResultL' on a program that allocates no loan, so there is no
-- arrival state to supply. A loan program reaches the machine through
-- 'tempVerdictS' instead, which supplies one per loan.
probeResultS :: (Eq a, Fractional a)
             => VisSpec -> Prog a -> Site -> [Sel] -> StateV a -> ProbeResult a
probeResultS vis prog target sel = probeResultL vis prog target sel []

-- >>> probeResultS visXY andUncomputedByMeasurement ["a"] [SOut] (ket [2, 2] [1, 1]) == PLine [1, 0]
-- True

probeResult :: (Eq a, Fractional a)
            => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> ProbeResult a
probeResult vis prog target = probeResultS vis prog [target]

-- >>> probeResult visXY andUncomputedByMeasurement "a" [SIn] (ket [2, 2] [0, 1]) == PLine [0, 1]
-- True

-- On the unsafe program only the all-ones test input exposes the entanglement.
-- >>> map (\(n, inp) -> (n, probeResult visXY andComputed "a" [] inp == PFail)) (probesFor visXY)
-- [("e0",False),("e1",False),("e2",False),("e3",False),("sum",True)]

-- The path for a block of temporaries ---------------------------------------

-- | Every probe the temporary path looks at, in a fixed order: one per
-- (loan arrival, visible test input) pair.
tempProbes :: (Eq a, Fractional a)
           => VisSpec -> Prog a -> Site -> [Sel] -> [ProbeResult a]
tempProbes vis prog target sel =
  [ probeResultL vis prog target sel env inp
  | env <- loanEnvs (loansBefore prog target)
  , (_, inp) <- probesFor vis ]

-- One probe per test input when the program has no loan.
-- >>> length (tempProbes visXY andUncomputedByMeasurement ["a"] [SIn])
-- 5
-- >>> tempProbes visXY andUncomputedByMeasurement ["a"] [SIn] == replicate 5 (PLine [0, 1])
-- True
-- >>> map (== PFail) (tempProbes visXY andComputed ["a"] [])
-- [False,False,False,False,True]

-- | The temporary path of the criterion: rerun the program on every input
-- and ask whether the surviving runs all leave the site's block constant
-- on one and the same line. The inputs are the site map's whole domain
-- @[[Omega]]@ of the site definition -- the dim+1 visible probes crossed with one
-- basis arrival per loan allocated before the site ('tempProbes'), which
-- is just the dim+1 visible probes when the program has no loan.
tempVerdictS :: (Eq a, Fractional a)
             => VisSpec -> Prog a -> Site -> [Sel] -> Verdict
tempVerdictS vis prog target sel =
  let live = [ r | r <- tempProbes vis prog target sel, r /= PZero ]
  in case live of
       [] -> Unreachable
       _  | all isLine live && allEqual [ l | PLine l <- live ] -> Safe
          | otherwise -> Unsafe
  where
    isLine (PLine _) = True
    isLine _         = False

-- The paper's program, under both selections: the same line each time, so safe.
-- >>> tempVerdictS visXY andUncomputedByMeasurement ["a"] [SIn]
-- Safe
-- >>> tempVerdictS visXY andUncomputedByMeasurement ["a"] [SOut]
-- Safe

-- Dropped right after the Toffoli, the block is entangled with the input: unsafe.
-- >>> tempVerdictS visXY andComputed ["a"] []
-- Unsafe

-- A temporary allocated in |0> and measured against the block {1} has no weight under the bit 1: unreachable.
-- >>> tempVerdictS [("x", 2)] [New "a" 2, Lift "p" "a" [1], Drop ["a"]] ["a"] [SIn]
-- Unreachable
-- >>> tempVerdictS [("x", 2)] [New "a" 2, Lift "p" "a" [1], Drop ["a"]] ["a"] [SOut]
-- Safe

-- The verdict at one site ------------------------------------------------------

-- | The criterion's answer at one site under one selection: the temporary
-- path above, unless the block holds a loan, in which case the site definition clause
-- (4) decides it through 'loanResultS' -- a different theorem (the site map
-- factors as an isometry on the block's loans tensor a map on the rest, not
-- as a fixed ray tensor a map of the visible input; see the section on
-- loans below). One loan or several, alone or beside temporaries:
-- one clause, one implementation.
semanticVerdictS :: (Eq a, Fractional a, Conj a)
                 => VisSpec -> Prog a -> Site -> [Sel] -> Verdict
semanticVerdictS vis prog target sel
  | any (isLoanTargetS prog target) target = fst (loanResultS vis prog target sel)
  | otherwise                              = tempVerdictS vis prog target sel

-- >>> semanticVerdictS visXY andUncomputedByMeasurement ["a"] [SIn]
-- Safe
-- >>> semanticVerdictS visXY andComputed ["a"] []
-- Unsafe

-- A block that holds a loan goes to the loan path: mcx-dirty-x.s drops its loan a with B = X.
-- >>> :m + Drop.Lang.Parser
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> semanticVerdictS vis prog ["a"] []) (parseProgram src))
-- Right Safe

semanticVerdict :: (Eq a, Fractional a, Conj a)
                => VisSpec -> Prog a -> String -> [Sel] -> Verdict
semanticVerdict vis prog target = semanticVerdictS vis prog [target]

-- The paper's three programs at the drop of a.
-- >>> semanticVerdict visXY andUncomputedByMeasurement "a" [SIn]
-- Safe
-- >>> semanticVerdict visXY andUncomputedByMeasurement "a" [SOut]
-- Safe
-- >>> semanticVerdict visXY andComputed "a" []
-- Unsafe
-- >>> semanticVerdict visXY andNoCorrection "a" [SIn]
-- Safe
-- >>> semanticVerdict visXY andNoCorrection "a" [SOut]
-- Safe

-- | The line the site's block is left constant on, when the criterion
-- accepts. Reuses the work 'tempVerdictS' already does on its way to a
-- Boolean, instead of discarding it. 'Nothing' at a loan site: a loan has
-- no fixed line to report (its certificate is the isometry B, from
-- 'semanticLoanCert').
semanticParkedS :: (Eq a, Fractional a)
                => VisSpec -> Prog a -> Site -> [Sel] -> Maybe (StateV a)
semanticParkedS vis prog target sel
  | any (isLoanTargetS prog target) target     = Nothing
  | tempVerdictS vis prog target sel /= Safe   = Nothing
  | otherwise = case [ l | PLine l <- tempProbes vis prog target sel ] of
      (l : _) -> Just l
      []      -> Nothing

-- The line the block is left on when the criterion accepts: |1> under the bit 1, |0> under the bit 0.
-- >>> semanticParkedS visXY andUncomputedByMeasurement ["a"] [SIn] == Just [0, 1]
-- True
-- >>> semanticParkedS visXY andUncomputedByMeasurement ["a"] [SOut] == Just [1, 0]
-- True

-- Nothing when the drop is unsafe.
-- >>> semanticParkedS visXY andComputed ["a"] []
-- Nothing

semanticParked :: (Eq a, Fractional a)
               => VisSpec -> Prog a -> String -> [Sel] -> Maybe (StateV a)
semanticParked vis prog target = semanticParkedS vis prog [target]

-- >>> semanticParked visXY andUncomputedByMeasurement "a" [SIn] == Just [0, 1]
-- True

-- Nothing at a loan: its certificate is the isometry B.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> semanticParked vis prog "a" []) (parseProgram src))
-- Right Nothing

-- | 'head' on a list this function has already shown to be non-empty: the
-- guard above rules out the empty table, and naming that here keeps the
-- module free of partial Prelude functions.
head' :: [b] -> b
head' (y : _) = y
-- impossible: every caller has tested for the empty list first (loanReshaped is called on a nonempty table)
head' []      = error "Drop.Lang.Criterion: head' on an empty list (guarded above)"

-- >>> head' [3, 4, 5 :: Int]
-- 3
-- >>> head' "a"
-- 'a'

allEqual :: Eq b => [b] -> Bool
allEqual []       = True
allEqual (x : xs) = all (== x) xs

-- >>> allEqual [1, 1, 1 :: Int]
-- True
-- >>> allEqual [1, 2 :: Int]
-- False
-- >>> allEqual ([] :: [Int])
-- True

-- Loans: a loan is an input register, not a fixed ket -------------------------

-- | Every loan the program allocates before a site, dropped or not, in
-- header order. Two distinct jobs need this rather than 'liveLoansAtS':
-- the machine must be handed an arrival state for each loan it executes
-- ('initMachL' errors otherwise), and the site definition makes each loan a factor of
-- the site map's domain @[[Omega]]@, so each must be varied -- a loan
-- dropped earlier is hidden, not gone (@Drop@ is denotationally the
-- identity), and the rest of the state still depends on it.
loansBefore :: Prog a -> Site -> [(String, Int)]
loansBefore prog site = [ (n, d) | Loan n d <- beforeSite prog site ]

-- mcx-dirty-x.s: the loan a is allocated before the drop of a.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> (vis, loansBefore prog ["a"])) (parseProgram src))
-- Right ([("q1",2),("q2",2),("q3",2),("q",2)],[("a",2)])

-- The temporary AND has no loan.
-- >>> loansBefore andUncomputedByMeasurement ["a"]
-- []

-- | Those of 'loansBefore' not yet dropped when the site fires: exactly the
-- registers a site can be the drop /of/ as a loan.
liveLoansAtS :: Prog a -> Site -> [(String, Int)]
liveLoansAtS prog site = go [] (beforeSite prog site)
  where
    go acc [] = acc
    go acc (Loan n d : cs)     = go (acc ++ [(n, d)]) cs
    go acc (Drop ns : cs)      = go (filter ((`notElem` ns) . fst) acc) cs
    go acc (_ : cs)            = go acc cs

-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(_, prog) -> liveLoansAtS prog ["a"]) (parseProgram src))
-- Right [("a",2)]

-- A loan already dropped is no longer live.
-- >>> liveLoansAtS [Loan "a" 2, Drop ["a"], Gate [[0, 1], [1, 0]] ["x"], Drop ["x"]] ["x"] :: [(String, Int)]
-- []

-- | Is @x@ a loan still live at @site@? Keyed by the whole site, so a
-- tuple drop that happens to contain a loan is recognised as one; asking
-- with the singleton site @[x]@ would silently answer 'False' there,
-- because the scan would run past the tuple drop and see @x@ released.
isLoanTargetS :: Prog a -> Site -> String -> Bool
isLoanTargetS prog site x = x `elem` map fst (liveLoansAtS prog site)

-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(_, prog) -> isLoanTargetS prog ["a"] "a") (parseProgram src))
-- Right True
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(_, prog) -> isLoanTargetS prog ["a"] "q1") (parseProgram src))
-- Right False

liveLoansAt :: Prog a -> String -> [(String, Int)]
liveLoansAt prog x = liveLoansAtS prog [x]

-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(_, prog) -> liveLoansAt prog "a") (parseProgram src))
-- Right [("a",2)]

isLoanTarget :: Prog a -> String -> Bool
isLoanTarget prog x = isLoanTargetS prog [x] x

-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(_, prog) -> isLoanTarget prog "a") (parseProgram src))
-- Right True
-- >>> isLoanTarget andUncomputedByMeasurement "a"
-- False

-- | Every arrival assignment for a list of loans: each loan on one basis
-- vector of its own space, mixed radix, first loan most significant.
-- @[[]]@ for the empty list: a loan-free program is probed once, with no
-- loan to place.
loanEnvs :: Num a => [(String, Int)] -> [[(String, StateV a)]]
loanEnvs regs =
  [ [ (n, ket [d] [i]) | ((n, d), i) <- zip regs tup ] | tup <- basisTuples regs ]

-- No loans: one empty assignment, so a loan-free program is probed once.
-- >>> loanEnvs [] :: [[(String, StateV Rational)]]
-- [[]]
-- >>> loanEnvs [("a", 2)] :: [[(String, StateV Rational)]]
-- [[("a",[1 % 1,0 % 1])],[("a",[0 % 1,1 % 1])]]

-- Two loans: mixed radix, the first most significant.
-- >>> loanEnvs [("a", 2), ("b", 2)] :: [[(String, StateV Rational)]]
-- [[("a",[1 % 1,0 % 1]),("b",[1 % 1,0 % 1])],[("a",[1 % 1,0 % 1]),("b",[0 % 1,1 % 1])],[("a",[0 % 1,1 % 1]),("b",[1 % 1,0 % 1])],[("a",[0 % 1,1 % 1]),("b",[0 % 1,1 % 1])]]

-- | Every basis-index tuple of a list of (name, dim) registers, mixed
-- radix, first register most significant -- @[[]]@ for the empty list (one
-- trivial tuple, dimension 1: "no other loans" still varies the visible
-- register alone).
basisTuples :: [(String, Int)] -> [[Int]]
basisTuples regs = [ idxToLevels dims k | k <- [0 .. product dims - 1] ]
  where dims = map snd regs

-- >>> basisTuples []
-- [[]]
-- >>> basisTuples [("a", 2)]
-- [[0],[1]]
-- >>> basisTuples [("a", 2), ("b", 3)]
-- [[0,0],[0,1],[0,2],[1,0],[1,1],[1,2]]

-- | The loans a site's block holds, in the order the @drop@ names its
-- registers: the factors of @H_loan@ in @[[Omega]] = H_loan (x) [[Omega']]@,
-- the site definition's clause (3). Empty when the block is temporaries
-- only, which is the temporary's test ('tempVerdictS'), not this one.
blockLoansAtS :: Prog a -> Site -> [(String, Int)]
blockLoansAtS prog site =
  [ (n, d) | n <- site, Just d <- [lookup n (liveLoansAtS prog site)] ]

-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(_, prog) -> blockLoansAtS prog ["a"]) (parseProgram src))
-- Right [("a",2)]

-- A block of temporaries holds no loan.
-- >>> blockLoansAtS andUncomputedByMeasurement ["a"]
-- []

-- | The state at the drop site for one probe combination: the visible
-- register on its @vi@-th basis vector, every loan outside the block (in
-- @others@' order) on the basis vector @oth@ names, and the block's loans
-- on the level tuple @lk@ names in @H_loan@'s mixed radix. A genuine input
-- assignment (Drop.Lang.Machine's @cfgLoans@/'initMachL'), never a default.
blockProbeState :: (Eq a, Num a)
                => VisSpec -> Prog a -> Site -> [Sel]
                -> [(String, Int)] -> [(String, Int)] -> Int -> [Int] -> Int
                -> Mach a
blockProbeState vis prog site sel blockLoans others vi oth lk =
  runStmts (initMachL vis visProbe env) prog sel (Just site)
  where
    dv = product (map snd vis)
    visProbe = ket [dv] [vi]
    env = [ (n, ket [dd] [i]) | ((n, dd), i) <- zip others oth ]
       ++ [ (n, ket [dd] [i])
          | ((n, dd), i) <- zip blockLoans (idxToLevels (map snd blockLoans) lk) ]

-- mcx-dirty-x.s at its drop: the loan a on level 1, the visible registers on their basis vector 0.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> (mNames (blockProbeState vis prog ["a"] [] [("a", 2)] [] 0 [] 1), [ i | (i, c) <- zip [0 :: Int ..] (mAmp (blockProbeState vis prog ["a"] [] [("a", 2)] [] 0 [] 1)), c /= 0 ])) (parseProgram src))
-- Right (["q1","q2","q3","q","a"],[0])

-- | @B^dagger B@ is exactly @t@ times the identity, some nonzero scalar
-- @t@ -- an isometry up to scale. @B : H_loan -> H_block@ is square when
-- the block is its loans and nothing else, and rectangular (taller than
-- wide) when the block also holds temporaries; either way @B^dagger B@ is
-- the square @dim H_loan@ matrix this tests. @t@ is automatically a
-- positive real, being @sum_a |B_{a0}|^2@ over a nonzero column, so "a
-- nonzero scalar" and "a positive scalar" are the same test here; the
-- factorization below fixes @B@ only up to that scale, and no square root
-- of @t@ is taken, which would leave the exact field.
isScalarIdentity :: (Eq a, Num a) => Matrix a -> Bool
isScalarIdentity m =
  not (null m) && all ((== n) . length) m && t /= 0
  -- impossible: m is nonempty and square (tested above), so every index is in range
  && and [ m !! i !! j == (if i == j then t else 0) | i <- [0 .. n - 1], j <- [0 .. n - 1] ]
  where
    n = length m
    -- impossible: m is nonempty (tested above)
    t = m !! 0 !! 0

-- >>> isScalarIdentity [[1, 0], [0, 1 :: Rational]]
-- True
-- >>> isScalarIdentity [[3, 0], [0, 3 :: Rational]]
-- True
-- >>> isScalarIdentity [[1, 0], [0, 2 :: Rational]]
-- False
-- >>> isScalarIdentity [[0, 0], [0, 0 :: Rational]]
-- False
-- >>> isScalarIdentity [[1, 1], [0, 1 :: Rational]]
-- False
-- >>> isScalarIdentity ([] :: Matrix Rational)
-- False

-- | the site definition's clause (3) at one site/selection, for a block holding one or
-- more loans -- alone, or beside temporaries.
--
-- Write the input space as @[[Omega]] = H_loan (x) [[Omega']]@, where
-- @H_loan@ is the tensor product of the spaces of the loans /in the block/
-- and @[[Omega']]@ is everything else the site map reads (the visible
-- register and every loan outside the block). The site is safe when the
-- site map @sigma_s : [[Omega]] -> H_block (x) H_rest@ factors as
-- @sigma_s = B (x) W@ with @B : H_loan -> H_block@ an isometry (up to
-- scale) and @W : [[Omega']] -> H_rest@ linear.
--
-- Executably: build the exact bilinear map from
-- (the visible register (x) the loans outside the block, the loans in the
-- block) to the full state at the drop site, by running on every basis
-- vector of both sides; reshape it, grouping the block output with the
-- block's loan input on one axis and everything else on the other, into a
-- single matrix; test that reshaped matrix for rank <= 1 by embedding it as
-- a two-register state and reusing 'factorSplit's own minor test verbatim
-- (the same algebraic condition, on a different index grouping); on a
-- rank-1 hit, read the block/loan factor back as the
-- @dim H_block x dim H_loan@ matrix B and accept iff @B^dagger B@ is a
-- nonzero scalar multiple of the identity ('isScalarIdentity'). A run that
-- is zero at every probe combination is unreachable, mirroring
-- 'probeResultS'/'tempVerdictS's own PZero bookkeeping.
--
-- A block of temporaries only is the case @H_loan = C@, where B is the unit
-- vector the temporaries are left on; that case is 'tempVerdictS', and this
-- function refuses it rather than answer with a one-column B whose isometry
-- test is vacuous.
loanResultS :: (Eq a, Fractional a, Conj a)
            => VisSpec -> Prog a -> Site -> [Sel] -> (Verdict, Maybe (Matrix a))
loanResultS vis prog site sel
  | null blockLoans =
      -- refusal: a block of temporaries only is decided by tempVerdictS, not here
      error ("loanResultS: the site " ++ show site ++ " holds no live loan; \
             \a block of temporaries is decided by tempVerdictS")
  | null table || all (isZeroS . mAmp . snd) table = (Unreachable, Nothing)
  | otherwise = loanIsometryTest dBlock dLoan cols flat
  where
    -- 'liveLoansAtS' (through 'blockLoansAtS') answers which of the block's
    -- registers are loans and gives their dimensions; 'loansBefore'
    -- additionally carries the loans already dropped, which the machine
    -- must still be handed a state for and which still vary the rest of the
    -- state, so 'others' is taken from it and not from the live list.
    blockLoans           = blockLoansAtS prog site
    others               = [ nd | nd@(n, _) <- loansBefore prog site
                           , n `notElem` map fst blockLoans ]
    dLoan                = product (map snd blockLoans)
    table                = loanProbeTable vis prog site sel blockLoans others
    (dBlock, cols, flat) = loanReshaped vis site blockLoans others table

-- A loan site: mcx-dirty-x.s, B = X (an isometry), so safe.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> (fst (loanResultS vis prog ["a"] []), fmap (== [[0, 1], [1, 0]]) (snd (loanResultS vis prog ["a"] [])))) (parseProgram src))
-- Right (Safe,Just True)

-- mcx-dirty.s drops its loan with B = I.
-- >>> readFile "programs/mcx-dirty.s" >>= \src -> print (fmap (\(vis, prog) -> (fst (loanResultS vis prog ["a"] []), fmap (== [[1, 0], [0, 1]]) (snd (loanResultS vis prog ["a"] [])))) (parseProgram src))
-- Right (Safe,Just True)

-- mcx-dirty-half.s deletes the fourth Toffoli, so the loan is not handed back: unsafe, and no certificate.
-- >>> readFile "programs/mcx-dirty-half.s" >>= \src -> print (fmap (\(vis, prog) -> fst (loanResultS vis prog ["a"] [])) (parseProgram src))
-- Right Unsafe
-- >>> readFile "programs/mcx-dirty-half.s" >>= \src -> print (fmap (\(vis, prog) -> null (snd (loanResultS vis prog ["a"] []))) (parseProgram src))
-- Right True

-- | The probe table of 'loanResultS': the machine run to the site on every
-- basis vector of both sides -- the visible register (x) the loans outside
-- the block, and the loans in the block -- each combination keyed
-- @(visible index, outside-loan levels, block-loan index)@.
loanProbeTable :: (Eq a, Num a)
               => VisSpec -> Prog a -> Site -> [Sel]
               -> [(String, Int)] -> [(String, Int)]
               -> [((Int, [Int], Int), Mach a)]
loanProbeTable vis prog site sel blockLoans others =
  [ (k, blockProbeState vis prog site sel blockLoans others vi oth lk)
  | k@(vi, oth, lk) <- combos ]
  where
    dv     = product (map snd vis)
    dLoan  = product (map snd blockLoans)
    combos = [ (vi, oth, lk)
             | vi <- [0 .. dv - 1], oth <- basisTuples others
             , lk <- [0 .. dLoan - 1] ]

-- mcx-dirty-x.s: 16 visible basis vectors times the 2 levels of the loan.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> length (loanProbeTable vis prog ["a"] [] [("a", 2)] [])) (parseProgram src))
-- Right 32
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> take 3 (map fst (loanProbeTable vis prog ["a"] [] [("a", 2)] []))) (parseProgram src))
-- Right [(0,[],0),(0,[],1),(1,[],0)]

-- | The reshaped matrix of 'loanResultS': the probe table with the block's
-- output grouped with the block's loan input on one axis and everything
-- else on the other, flattened row by row. It returns @dim H_block@, the
-- number of columns (@dim H_rest * dim [[Omega']]@) and the flat matrix. The
-- table must not be empty ('loanResultS' has checked).
loanReshaped :: Num a
             => VisSpec -> Site -> [(String, Int)] -> [(String, Int)]
             -> [((Int, [Int], Int), Mach a)] -> (Int, Int, StateV a)
loanReshaped vis site blockLoans others table = (dBlock, dRest * dOther, bigFlat)
  where
    otherDims  = map snd others
    dLoan      = product (map snd blockLoans)
    dv         = product (map snd vis)
    dOther     = dv * product otherDims
    m0         = snd (head' table)
    dimsAt     = mDims m0
    posBlock   = map (regPos m0) site
    -- impossible: posBlock holds indices of dimsAt, one per register of the site
    dBlock     = product [ dimsAt !! p | p <- posBlock ]
    dRest      = product [ dd | (i, dd) <- zip [0 :: Int ..] dimsAt
                         , i `notElem` posBlock ]
    ojOf vi oth = levelsToIdx (dv : otherDims) (vi : oth)
    blockMats  = [ ((vi, oth, lk), reindexABOrd dimsAt posBlock (mAmp m))
                 | ((vi, oth, lk), m) <- table ]
    entryAt a lk b oj =
      case [ mat | ((vi', oth', lk'), mat) <- blockMats
                 , lk' == lk, ojOf vi' oth' == oj ] of
        -- impossible: a and b index the block and rest axes the matrix was built with
        (mat : _) -> mat !! a !! b
        []        -> 0
    bigFlat =
      [ entryAt a lk b oj
      | a  <- [0 .. dBlock - 1], lk <- [0 .. dLoan - 1]
      , b  <- [0 .. dRest - 1],  oj <- [0 .. dOther - 1]
      ]

-- Rows: the block output (dim 2) times the loan input (dim 2); columns: the rest of the state times the visible input.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> (\(dBlock, cols, flat) -> (dBlock, cols, length flat)) (loanReshaped vis ["a"] [("a", 2)] [] (loanProbeTable vis prog ["a"] [] [("a", 2)] []))) (parseProgram src))
-- Right (2,256,1024)

-- | The isometry test of 'loanResultS': the reshaped matrix (the arguments
-- are @dim H_block@, @dim H_loan@, the column count and the flat matrix) must
-- have rank at most one, by 'factorSplit's own minor test; the block/loan
-- factor read back is B, and the site is safe when @B^dagger B@ is a
-- nonzero scalar multiple of the identity ('isScalarIdentity').
loanIsometryTest :: (Eq a, Fractional a, Conj a)
                 => Int -> Int -> Int -> StateV a -> (Verdict, Maybe (Matrix a))
loanIsometryTest dBlock dLoan cols flat =
  case factorSplit [dBlock * dLoan, cols] [0] flat of
    Nothing -> (Unsafe, Nothing)
    Just (rowVec, _) ->
      -- impossible: rowVec has dBlock * dLoan entries and every index below is in range
      let bMat = [ [ rowVec !! levelsToIdx [dBlock, dLoan] [a, lk]
                   | lk <- [0 .. dLoan - 1] ]
                 | a <- [0 .. dBlock - 1] ]
      in if isScalarIdentity (matMul (daggerM bMat) bMat)
           then (Safe, Just bMat)
           else (Unsafe, Nothing)

-- B = I (one column): an isometry, so safe, and B is read back.
-- >>> loanIsometryTest 2 2 1 [1, 0, 0, 1 :: Rational]
-- (Safe,Just [[1 % 1,0 % 1],[0 % 1,1 % 1]])

-- B = diag(1, 2): B-dagger B = diag(1, 4) is not a scalar multiple of I.
-- >>> loanIsometryTest 2 2 1 [1, 0, 0, 2 :: Rational]
-- (Unsafe,Nothing)

-- A matrix of rank 2 does not factor at all.
-- >>> loanIsometryTest 1 2 2 [1, 0, 0, 1 :: Rational]
-- (Unsafe,Nothing)

-- | 'loanResultS' at a block that is one register, the shape the corpus
-- writes.
loanResult :: (Eq a, Fractional a, Conj a)
           => VisSpec -> Prog a -> String -> [Sel] -> (Verdict, Maybe (Matrix a))
loanResult vis prog x = loanResultS vis prog [x]

-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> fst (loanResult vis prog "a" [])) (parseProgram src))
-- Right Safe

-- | The isometry B a safe loan site's drop reclaims with (its adjoint is the
-- reclaiming gate): 'Nothing' when the block holds no loan, the site is not
-- reachable, or the site is unsafe.
semanticLoanCertS :: (Eq a, Fractional a, Conj a)
                  => VisSpec -> Prog a -> Site -> [Sel] -> Maybe (Matrix a)
semanticLoanCertS vis prog site sel
  | not (any (isLoanTargetS prog site) site) = Nothing
  | otherwise = case loanResultS vis prog site sel of
      (Safe, cert) -> cert
      _            -> Nothing

-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> fmap (== [[0, 1], [1, 0]]) (semanticLoanCertS vis prog ["a"] [])) (parseProgram src))
-- Right (Just True)

-- A block of temporaries has no certificate.
-- >>> semanticLoanCertS visXY andUncomputedByMeasurement ["a"] [SIn]
-- Nothing

semanticLoanCert :: (Eq a, Fractional a, Conj a)
                 => VisSpec -> Prog a -> String -> [Sel] -> Maybe (Matrix a)
semanticLoanCert vis prog target = semanticLoanCertS vis prog [target]

-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (\(vis, prog) -> fmap (== [[0, 1], [1, 0]]) (semanticLoanCert vis prog "a" [])) (parseProgram src))
-- Right (Just True)

-- The report for a whole program -------------------------------------------

data DropReport = DropReport
  { drSite :: Site
  , drRows :: [([Sel], Verdict)]
  } deriving Show

-- A report is built by verdict; this one is written by hand to show its two fields.
-- >>> DropReport ["a"] [([SIn], Safe), ([SOut], Unsafe)]
-- DropReport {drSite = ["a"], drRows = [([SIn],Safe),([SOut],Unsafe)]}

verdict :: (Eq a, Fractional a, Conj a) => VisSpec -> Prog a -> [DropReport]
verdict vis prog = requireFlat SurfaceFragment (visScope vis) prog `seq`
  [ DropReport x [ (sel, semanticVerdictS vis prog x sel)
                 | sel <- allSelections (liftDepthBeforeS prog x) ]
  | x <- dropSites prog ]

-- Every site under every selection of the lifts before it.
-- >>> verdict visXY andUncomputedByMeasurement
-- [DropReport {drSite = ["a"], drRows = [([SIn],Safe),([SOut],Safe)]}]
-- >>> verdict visXY andComputed
-- [DropReport {drSite = ["a"], drRows = [([],Unsafe)]}]
-- >>> verdict visXY andNoCorrection
-- [DropReport {drSite = ["a"], drRows = [([SIn],Safe),([SOut],Safe)]}]

-- No drop, no site.
-- >>> verdict visXY ([] :: Prog Cyclo)
-- []

-- | Weight of the selected branch on a given test input, exact and unnormalized.
branchWeight :: (Eq a, Num a, Conj a) => VisSpec -> Prog a -> String -> [Sel] -> StateV a -> a
branchWeight vis prog target sel inp =
  norm2S (mAmp (runStmts (initMach vis inp) prog sel (Just [target])))



-- The branch weight of the lift in the temporary AND, from |11>: one half under each bit.
-- >>> branchWeight visXY andUncomputedByMeasurement "a" [SIn] (ket [2, 2] [1, 1]) == 1 / 2
-- True
-- >>> branchWeight visXY andUncomputedByMeasurement "a" [SOut] (ket [2, 2] [1, 1]) == 1 / 2
-- True
