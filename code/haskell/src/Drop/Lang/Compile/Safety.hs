-- Drop.Lang.Compile.Safety: which drops are safe on which record, decided exactly.
--
-- Question: Which drops are safe on which record, decided exactly?
-- Answer:   The decision is made over exact scalars, never over inexact numbers. For a drop of
--           temporaries, computeSafety runs the machine on every probe of Criterion.probesFor (the
--           visible basis and the all-ones vector), crossed with every basis arrival of the loans,
--           to reach every leaf; at each leaf's recorded site state it factors the dropped block out
--           (State.factorSplitOrd) and reads its line (canonicalLine), as Criterion's
--           probeResultL does. The outcome is indexed by the record prefix, the lift outcomes
--           crossed before the site, by name, and not by a selection word: a drop inside an if
--           branch already has some of those bits fixed by the branch, and the reclaiming gate may
--           still depend on the rest. A drop that names a loan is decided by Criterion's own loan
--           criterion (semanticVerdictS and semanticLoanCertS on the elaborated program), at the
--           empty record only. fragmentSafety then refuses a program that drops a loan after a
--           lift or an if, or drops an input not marked loan at a site that is safe, with a
--           nonzero site map, on some record; the refusal names the drop.
-- Paper:    sec:lang:compile (what the emitter inserts at a drop), app:emitter-contract.
-- Shapes:   SafetyOutcome  a site's verdict on one record: SafeCert (the line a temporary is left
--                          on), SafeIso (the isometry B a block holding a loan is returned
--                          with), UnsafeOutcome, or UnreachableOutcome (no probe reaches it).
--           SafetyInfo     per site, per record prefix, one SafetyOutcome.

module Drop.Lang.Compile.Safety
  ( SafetyOutcome (..)
  , SafetyInfo
  , loanBindersOf
  , fragmentSafety
  ) where

import Data.List (nub)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Drop.Lang.Compile.Layout
import Drop.Lang.Criterion (ProbeResult (..), probesFor, loanEnvs, semanticVerdictS, semanticLoanCertS, Verdict (..))
import Drop.Lang.Elab (elabE)
import Drop.Lang.Machine
import Drop.Lang.Scalar (Cyclo)
import Drop.Lang.State
import Drop.Lang.Syntax

-- The outcomes ----------------------------------------------------------------

-- | A temporary's certificate is the line it is left constant on
-- ('SafeCert'); a block holding a
-- loan carries instead the isometry B its drop reclaims with ('SafeIso',
-- B : H_loan -> H_block of the site definition's clause (3) -- square when the block is
-- its loans and nothing else, taller than wide when temporaries sit beside
-- them).
data SafetyOutcome = SafeCert (StateV Cyclo) | SafeIso (Matrix Cyclo)
                   | UnsafeOutcome | UnreachableOutcome
  deriving (Eq, Show)

-- The four outcomes: a line, an isometry (here X), no verdict, and no probe at all.
-- >>> [SafeCert [1, 0], SafeIso [[0, 1], [1, 0]], UnsafeOutcome, UnreachableOutcome]
-- [SafeCert [Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]],SafeIso [[Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]],[Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]],UnsafeOutcome,UnreachableOutcome]

-- | Per drop site, per record prefix (the lift outcomes crossed before the
-- site, by name, 1 = survived), the site's outcome.
type SafetyInfo = Map SiteId (Map [(Name, Int)] SafetyOutcome)

-- Site 0 is safe on the record where lift m survived, and unsafe where it did not.
-- >>> Map.singleton 0 (Map.fromList [([("m", 1)], SafeCert [0, 1]), ([("m", 0)], UnsafeOutcome)]) :: SafetyInfo
-- fromList [(0,fromList [([("m",0)],UnsafeOutcome),([("m",1)],SafeCert [Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]])])]

-- One site, one record --------------------------------------------------------

-- | What the machine's record of one drop says: the whole state at the drop,
-- with the dropped block factored out of it. The block is read in the order
-- the drop names it.
probeOutcome :: SiteRecord Cyclo -> ProbeResult Cyclo
probeOutcome rec_
  | isZeroS (srAmp rec_) = PZero
  | otherwise = case factorSplitOrd (srDims rec_) regsA (srAmp rec_) of
      Nothing      -> PFail
      Just (vA, _) -> PLine (canonicalLine vA)
  where
    -- The block's machine positions in the order the drop names its
    -- registers ('srHidden'), so the certificate is indexed as the
    -- allocation state 'psi' and the qubit list of 'compileDrop' are: a
    -- tuple dropped out of allocation order reads the same way everywhere.
    regsA = [ i | n <- srHidden rec_, (i, nm) <- zip [0 ..] (srNames rec_), nm == n ]

-- A block alone in a state: it is left on its own line.
-- >>> probeOutcome (SiteRecord 0 ["a"] ["a"] [2] [0, 1])
-- PLine [Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]]

-- A state of weight zero: the probe does not reach the site.
-- >>> probeOutcome (SiteRecord 0 ["a"] ["a"] [2] [0, 0])
-- PZero

-- A Bell pair with the block a dropped: it does not factor.
-- >>> probeOutcome (SiteRecord 0 ["a"] ["x", "a"] [2, 2] [1, 0, 0, 1])
-- PFail

-- The block a beside a register x in the state |x=1>|a=0> + |x=1>|a=1>: a is left on the line (1, 1), whatever x is.
-- >>> probeOutcome (SiteRecord 0 ["a"] ["x", "a"] [2, 2] [0, 0, 1, 1])
-- PLine [Cyclo 1 [1 % 1],Cyclo 1 [1 % 1]]

-- | One site on one record, from what every probe says: unreachable when every
-- probe has weight zero there, safe on a line when all the others leave the
-- block on one and the same line, unsafe otherwise.
aggregate :: [ProbeResult Cyclo] -> SafetyOutcome
aggregate prs = case live of
  []                                        -> UnreachableOutcome
  _ | all isLine live, (l : _) <- lns, allSameLine lns -> SafeCert l
    | otherwise                             -> UnsafeOutcome
  where
    live = [ p | p <- prs, p /= PZero ]
    isLine (PLine _) = True
    isLine _          = False
    lns = [ l | PLine l <- live ]
    allSameLine [] = True
    allSameLine (x : xs) = all (== x) xs

-- >>> aggregate []
-- UnreachableOutcome
-- >>> aggregate [PZero, PZero]
-- UnreachableOutcome
-- >>> aggregate [PLine [1, 0], PZero, PLine [1, 0]]
-- SafeCert [Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]
-- >>> aggregate [PLine [1, 0], PLine [0, 1]]
-- UnsafeOutcome
-- >>> aggregate [PLine [1, 0], PFail]
-- UnsafeOutcome

-- | Every name a loan binds, with its dimension (structural scan; an
-- @if@'s branches are resource-invariant -- 'compileFragment' -- so
-- either one, or their union, sees every loan).
loanBindersOf :: Term a -> [(Name, Int)]
loanBindersOf term = case term of
  Return _             -> []
  Do (StLoan x d) m    -> (x, d) : loanBindersOf m
  Do _ m               -> loanBindersOf m
  If _ m1 m2           -> loanBindersOf m1 ++ loanBindersOf m2

-- >>> loanBindersOf (Return VUnit :: Term Int)
-- []
-- >>> loanBindersOf (Do (StLoan "a" 2) (Do (StNew "t" 2 [1, 0]) (Return VUnit)) :: Term Int)
-- [("a",2)]
-- >>> :m + Drop.Lang.Parser
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (loanBindersOf (toTerm (progTerm prog)))) (parseTyped src)
-- [("a",2)]

-- | The registers each 'drop' occurrence names, by site id, in the order it
-- names them -- a tuple drop is ONE site (the composite-temporary proposition), so the entry is a
-- list, and a block that holds a loan is recognised as a loan site below
-- whether it is that loan alone or that loan beside other registers.
dropTargetsOf :: Term a -> Map SiteId [Name]
dropTargetsOf term = case term of
  Return _ -> Map.empty
  Do (StDrop site v) m -> Map.insert site (valueNames v) (dropTargetsOf m)
  Do _ m -> dropTargetsOf m
  If _ m1 m2 -> Map.union (dropTargetsOf m1) (dropTargetsOf m2)

-- >>> dropTargetsOf (Return VUnit :: Term Int)
-- fromList []
-- >>> dropTargetsOf (Do (StDrop 0 (VPair (VVar "a") (VVar "b"))) (Do (StDrop 1 (VVar "t")) (Return VUnit)) :: Term Int)
-- fromList [(0,["a","b"]),(1,["t"])]
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (dropTargetsOf (toTerm (progTerm prog)))) (parseTyped src)
-- fromList [(0,["a"])]

-- The table -------------------------------------------------------------------

-- | The safety table of a program: the temporary sites and the loan sites
-- side by side. The depth map says how many lifts precede each drop
-- ('liSiteDepth').
computeSafety :: Program Cyclo -> Term Cyclo -> Map SiteId Int -> SafetyInfo
computeSafety prog core siteDepthMap =
  Map.unionWith Map.union (temporarySafety prog core siteDepthMap) (loanSafety prog core)

-- The temporary AND of the paper: two records, each with its own line.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> computeSafety prog (toTerm (progTerm prog)) (liSiteDepth l)) (layoutProgram prog))) (parseTyped src)
-- Right (fromList [(0,fromList [([("m",0)],SafeCert [Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]),([("m",1)],SafeCert [Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]])])])

-- Two temporaries dropped one after the other are two sites, 0 and 1.
-- >>> readFile "programs/two-phases.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> Map.keys (computeSafety prog (toTerm (progTerm prog)) (liSiteDepth l))) (layoutProgram prog))) (parseTyped src)
-- Right [0,1]

-- | The sites that drop temporaries only, never a loan. A program mixing a loan with a temporary needs the
-- loan's own value run through to reach every temp site at all, and
-- the site definition makes that loan a factor of the site map's domain
-- [[Omega]], so the probe space is every basis arrival of every loan
-- crossed with the dim+1 visible probes -- exactly
-- Drop.Lang.Criterion.tempProbes' space, so the two engines decide these
-- sites alike. Seeding every loan at |0> instead would call a temporary
-- safe whenever it is safe on a |0> loan, and `new t; CX a t; drop t`
-- is safe on a |0> loan and unsafe on any other.
temporarySafety :: Program Cyclo -> Term Cyclo -> Map SiteId Int -> SafetyInfo
temporarySafety prog core siteDepthMap = tempInfo
  where
    vis = progCtx prog
    loanNames = map fst (loanBindersOf core)
    dTargets  = dropTargetsOf core
    isLoanSite s = maybe False (any (`elem` loanNames)) (Map.lookup s dTargets)
    loanEnvs0 = loanEnvs (loanBindersOf core) :: [[(Name, StateV Cyclo)]]
    probes = map snd (probesFor vis) :: [StateV Cyclo]
    raw =
      [ (site, prefix, probeOutcome rec_)
      | loanEnv <- loanEnvs0
      , inp <- probes
      , leaf <- run (initConfigL vis inp loanEnv core)
      , rec_ <- cfgSites leaf
      , let site = srSite rec_
      , not (isLoanSite site)
      , Just depth <- [Map.lookup site siteDepthMap]
      , let prefix = take depth (cfgBits leaf)
      , length prefix == depth
      ]
    grouped = Map.fromListWith (++) [ ((site, prefix), [pr]) | (site, prefix, pr) <- raw ]
    tempInfo = Map.fromListWith Map.union
      [ (site, Map.singleton prefix (aggregate prs))
      | ((site, prefix), prs) <- Map.toList grouped
      ]

-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> temporarySafety prog (toTerm (progTerm prog)) (liSiteDepth l)) (layoutProgram prog))) (parseTyped src)
-- Right (fromList [(0,fromList [([("m",0)],SafeCert [Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]),([("m",1)],SafeCert [Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]])])])

-- A program with a loan only: no temporary site at all.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> temporarySafety prog (toTerm (progTerm prog)) (liSiteDepth l)) (layoutProgram prog))) (parseTyped src)
-- Right (fromList [])

-- | The loan path: reuses Drop.Lang.Criterion's own loan criterion exactly
-- (via 'elabE'; in this domain a loan is dropped before the first lift
-- and the first if, so its verdict at the empty record prefix is its
-- verdict on every record), so the emitted
-- circuit's safety decision is the one and only implementation of the
-- criterion, not a second one that could drift from it. Only the
-- depth-0 (no lift before the loan) case is populated: 'fragmentSafety'
-- refuses every program that drops a loan after a lift or an if before
-- this map is asked for, and 'compileDrop' only ever looks up the prefix
-- matching the site's own (structural) depth.
loanSafety :: Program Cyclo -> Term Cyclo -> SafetyInfo
loanSafety prog core = loanInfo
  where
    vis = progCtx prog
    loanNames = map fst (loanBindersOf core)
    dTargets  = dropTargetsOf core
    loanInfo = Map.fromList
      [ (site, Map.singleton ([] :: [(Name, Int)]) (loanOutcomeFor names))
      | (site, names) <- Map.toList dTargets, any (`elem` loanNames) names
      ]
    loanOutcomeFor names = case elabE core of
      Left _ -> UnsafeOutcome
      Right flatProg -> case semanticVerdictS vis flatProg names [] of
        Safe -> case semanticLoanCertS vis flatProg names [] of
          Just b  -> SafeIso b
          Nothing -> UnsafeOutcome
        Unreachable -> UnreachableOutcome
        Unsafe -> UnsafeOutcome

-- The loan is handed back flipped by the X the program applied to it: B = X.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (loanSafety prog (toTerm (progTerm prog)))) (parseTyped src)
-- fromList [(0,fromList [([],SafeIso [[Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]],[Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]])])]

-- With the fourth Toffoli deleted the loan is not handed back: unsafe.
-- >>> readFile "programs/mcx-dirty-half.s" >>= \src -> either putStrLn (\prog -> print (loanSafety prog (toTerm (progTerm prog)))) (parseTyped src)
-- fromList [(0,fromList [([],UnsafeOutcome)])]

-- A program without a loan has no loan site.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (loanSafety prog (toTerm (progTerm prog)))) (parseTyped src)
-- fromList []

-- The fragment's conditions on drops ------------------------------------------

-- | Every drop naming a loan that follows a lift or sits in an arm of an
-- if, once each. The loan criterion ('computeSafety', through
-- Drop.Lang.Criterion.loanResultS) runs the expanded term with no lift
-- outcomes, and the expansion copies an if's continuation into both arms,
-- where Drop.Lang.Interp.runStmts does not look for the site; so these
-- drops have no verdict here, and asking for one stops the program.
lateLoanDrops :: [Name] -> Term a -> [[Name]]
lateLoanDrops loans = nub . go False
  where
    go _ (Return _) = []
    go late (Do (StDrop _ v) m)
      | late, any (`elem` loans) (valueNames v) = valueNames v : go late m
    go _ (Do (StLift {}) m) = go True m
    go late (Do _ m) = go late m
    go _ (If _ m1 m2) = go True m1 ++ go True m2

-- A loan dropped before any lift is on time.
-- >>> lateLoanDrops ["a"] (Do (StDrop 0 (VVar "a")) (Return VUnit) :: Term Int)
-- []

-- The same drop after a lift is late.
-- >>> lateLoanDrops ["a"] (Do (StLift "p" [1] "x") (Do (StDrop 0 (VVar "a")) (Return VUnit)) :: Term Int)
-- [["a"]]

-- A drop in an arm of an if counts as late; a register that is not a loan does not.
-- >>> lateLoanDrops ["a"] (If (BParam "p") (Do (StDrop 0 (VVar "a")) (Return VUnit)) (Do (StDrop 1 (VVar "t")) (Return VUnit)) :: Term Int)
-- [["a"]]

-- | Every drop naming an input not marked @loan@ whose site is safe, with a
-- nonzero site map, on some record: 'isSafe' counts 'SafeCert' and 'SafeIso' only, and a
-- record on which the site map is zero is 'UnreachableOutcome', which does not
-- count (unmunreach.s compiles). A reclaiming gate returns a temporary to its allocation state and
-- hands a loan back to the caller; such an input has neither, so no
-- reclaiming gate is defined for it. An unsafe drop of one emits no gate,
-- like any unsafe drop, and is not refused.
unmarkedSafeDrops :: [(Name, Int)] -> Term a -> SafetyInfo -> [[Name]]
unmarkedSafeDrops vis core safety =
  [ names
  | (site, names) <- Map.toList (dropTargetsOf core)
  , any (`elem` map fst vis) names
  , any isSafe (Map.elems (Map.findWithDefault Map.empty site safety)) ]
  where
    isSafe (SafeCert _) = True
    isSafe (SafeIso _)  = True
    isSafe _            = False

-- copy-input.s drops its input, and the criterion calls that drop unsafe: nothing to refuse.
-- >>> readFile "programs/copy-input.s" >>= \src -> either putStrLn (\prog -> let core = toTerm (progTerm prog) in print (fmap (\l -> unmarkedSafeDrops (progCtx prog) core (computeSafety prog core (liSiteDepth l))) (layoutProgram prog))) (parseTyped src)
-- Right []

-- An input swapped into a temporary and then dropped is safe: it needs a reclaiming gate it cannot have.
-- >>> either putStrLn (\prog -> let core = toTerm (progTerm prog) in print (fmap (\l -> unmarkedSafeDrops (progCtx prog) core (computeSafety prog core (liSiteDepth l))) (layoutProgram prog))) (parseTyped "prog unmarked_safe (x : [2]) : [2] { new t : [2] @ |0>; Swap x t; X x; drop x; return t }")
-- Right [["x"]]

-- | The safety map of a program in the fragment, or the refusal of its
-- first drop outside it. The late loans are refused first, before the map
-- is built: the map is strict, and building it asks for their verdicts.
fragmentSafety :: Program Cyclo -> Term Cyclo -> LayoutInfo -> Either CompileError SafetyInfo
fragmentSafety prog core layout =
  case lateLoanDrops (map fst (loanBindersOf core)) core of
    (xs : _) -> Left (DropOutsideFragment xs
                  "it drops a loan after a lift or an if, and this compiler decides a loan's drop only before both")
    [] ->
      let safety = computeSafety prog core (liSiteDepth layout)
      in case unmarkedSafeDrops (progCtx prog) core safety of
           (xs : _) -> Left (DropOutsideFragment xs
                         "it drops an input not marked loan at a site that is safe, with a nonzero site \
                         \map, on some record, and a reclaiming gate is defined only for temporaries and loans")
           [] -> Right safety

-- The temporary AND is safe on both records and nothing in it is refused.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (layoutProgram prog >>= fragmentSafety prog (toTerm (progTerm prog)))) (parseTyped src)
-- Right (fromList [(0,fromList [([("m",0)],SafeCert [Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]),([("m",1)],SafeCert [Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]])])])

-- The borrowed qubit of the three-control Toffoli is returned by X: a SafeIso.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (layoutProgram prog >>= fragmentSafety prog (toTerm (progTerm prog)))) (parseTyped src)
-- Right (fromList [(0,fromList [([],SafeIso [[Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]],[Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]])])])

-- An unsafe drop is not refused: copy-input.s has the outcome UnsafeOutcome.
-- >>> readFile "programs/copy-input.s" >>= \src -> either putStrLn (\prog -> print (layoutProgram prog >>= fragmentSafety prog (toTerm (progTerm prog)))) (parseTyped src)
-- Right (fromList [(0,fromList [([],UnsafeOutcome)])])

-- A loan dropped after a lift is refused, with the drop it names.
-- >>> either putStrLn (\prog -> putStrLn (either showCompileError (const "decided") (layoutProgram prog >>= fragmentSafety prog (toTerm (progTerm prog))))) (parseTyped "prog loan_after_lift (loan a : [2], x : [2]) : [2] { new t : [2] @ |0>; H t; p = lift[{0}] t; X a; drop a; drop t; return x }")
-- drop a is outside the compilation fragment: it drops a loan after a lift or an if, and this compiler decides a loan's drop only before both

-- A safe drop of an input not marked loan is refused too.
-- >>> either putStrLn (\prog -> putStrLn (either showCompileError (const "decided") (layoutProgram prog >>= fragmentSafety prog (toTerm (progTerm prog))))) (parseTyped "prog unmarked_safe (x : [2]) : [2] { new t : [2] @ |0>; Swap x t; X x; drop x; return t }")
-- drop x is outside the compilation fragment: it drops an input not marked loan at a site that is safe, with a nonzero site map, on some record, and a reclaiming gate is defined only for temporaries and loans
