-- Drop.Lang.Machine: the paper's machine, one rule at a time.
--
-- Question: How does a typed term run, and what does a run leave behind at a drop?
-- Answer:   A configuration is <Delta, sigma || M>: the registers allocated so far in allocation
--           order, the unnormalised state over them, and the term (the record also keeps the
--           lifted bits, the drop sites and the loan arrivals, which the rules only append to or
--           look up). Five rules fire at the head of M, one function each: a gate applies U to the
--           registers it names; new allocates a name not in Delta and not bound in M; drop applies
--           nothing and records the site (the names, the registers and the state at that moment,
--           which is what the criterion reads); lift is the one labelled rule, two successors for
--           the two bits; if takes a branch by its closed guard. A loan allocates as new does, on
--           the state the caller assigned. run follows every label to a leaf; termSize shrinks at
--           each step.
-- Paper:    fig:machine (the rules), sec:lang:dynamics (the dynamics).
-- Shapes:   Config a      names, dims and amplitudes of Delta and sigma, the term M, the lifted bits,
--                         the site records, the loan arrivals.
--           SiteRecord a  one drop: its site id, the names it hid, and the whole state at that moment.

module Drop.Lang.Machine
  ( Config (..)
  , SiteRecord (..)
  , initConfig
  , initConfigL
  , isFinal
  , cfgHidden
  , ctxOf
  , step
  , stepNewAt
  , run
  ) where

import Data.List (elemIndex, nub, (\\))
import Drop.Lang.State
import Drop.Lang.Syntax

-- The configuration ----------------------------------------------------------
--
-- There is no hidden set. The hidden registers are the allocated ones the
-- term no longer names ('cfgHidden'), which along any run are exactly the
-- ones the run has dropped (the type-safety theorem's clause (5), checked in
-- TypedSpec (o)).

-- | The state recorded at one `drop` occurrence on one leaf's path: the site
-- id, the names it hid, and the full (names, dims, amplitude) triple at the
-- moment of the drop -- exactly what the criterion (Drop.Lang.Criterion, for
-- the flat engine) needs to factor.
data SiteRecord a = SiteRecord
  { srSite   :: SiteId
  , srHidden :: [Name]
  , srNames  :: [Name]
  , srDims   :: [Int]
  , srAmp    :: StateV a
  } deriving (Eq, Show)

-- @<Delta, sigma || M>@: 'cfgNames' / 'cfgDims' are Delta, the registers
-- allocated so far in allocation order, 'cfgAmp' is sigma in [[Delta]],
-- unnormalised, and 'cfgTerm' is M. The other three fields are bookkeeping:
-- the rules append to them or look them up and the term never reads them.
data Config a = Config
  { cfgNames  :: [Name]        -- Delta, allocation order
  , cfgDims   :: [Int]
  , cfgAmp    :: StateV a      -- sigma in [[Delta]], unnormalised
  , cfgTerm   :: Term a        -- M
  , cfgBits   :: [(Name, Int)] -- the record so far: one entry per lift fired
  , cfgSites  :: [SiteRecord a]
  , cfgLoans  :: [(Name, StateV a)]
    -- ^ the probe state a loan ('Drop.Lang.Syntax.StLoan') is to arrive on, one
    -- entry consumed per loan, keyed by the name the header gave it. Empty
    -- on every configuration built by 'initConfig', so no existing caller is
    -- affected: only a term containing a loan ever consults it.
  } deriving Show

initConfig :: [(Name, Int)] -> StateV a -> Term a -> Config a
initConfig vis amp m = initConfigL vis amp [] m

-- The smallest configuration: one register x in |0>, and the term that flips it and returns it.
-- >>> initConfig [("x", 2)] (ket [2] [0]) (Do (StGate [[0,1],[1,0]] (VVar "x")) (Return (VVar "x"))) :: Config Rational
-- Config {cfgNames = ["x"], cfgDims = [2], cfgAmp = [1 % 1,0 % 1], cfgTerm = Do (StGate [[0 % 1,1 % 1],[1 % 1,0 % 1]] (VVar "x")) (Return (VVar "x")), cfgBits = [], cfgSites = [], cfgLoans = []}

-- >>> cfgNames (initConfig [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) (Return VUnit) :: Config Rational)
-- ["x","y"]
-- >>> cfgDims (initConfig [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) (Return VUnit) :: Config Rational)
-- [2,3]
-- >>> cfgLoans (initConfig [("x", 2)] (ket [2] [0]) (Return VUnit) :: Config Rational)
-- []

-- | As 'initConfig', but also supplying the state each loan the term
-- allocates is to arrive on, keyed by the loan's name. (Every name is bound
-- once in this language, so the key is unambiguous.)
initConfigL :: [(Name, Int)] -> StateV a -> [(Name, StateV a)] -> Term a -> Config a
initConfigL vis amp loans m = Config (map fst vis) (map snd vis) amp m [] [] loans

-- >>> cfgLoans (initConfigL [("x", 2)] (ket [2] [0]) [("a", ket [2] [1])] (Return VUnit) :: Config Rational)
-- [("a",[0 % 1,1 % 1])]

isFinal :: Config a -> Bool
isFinal cfg = case cfgTerm cfg of
  Return _ -> True
  _        -> False

-- >>> isFinal (initConfig [("x", 2)] (ket [2] [0]) (Return (VVar "x")) :: Config Rational)
-- True
-- >>> isFinal (initConfig [("x", 2)] (ket [2] [0]) (Do (StGate [[0,1],[1,0]] (VVar "x")) (Return (VVar "x"))) :: Config Rational)
-- False

-- | The term's own register context: the allocated registers the term still
-- names. The type-safety theorem's clause (5) says this is the allocated registers minus the
-- ones the run has dropped.
ctxOf :: Config a -> [(Name, Int)]
ctxOf cfg = [ (x, d) | (x, d) <- zip (cfgNames cfg) (cfgDims cfg), x `elem` live ]
  where live = freeTerm (cfgTerm cfg)

-- >>> ctxOf (initConfig [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) (Return (VVar "x")) :: Config Rational)
-- [("x",2)]

-- A register the term no longer names is not in its context.
-- >>> ctxOf (initConfig [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) (Return VUnit) :: Config Rational)
-- []

-- | The hidden registers: the allocated ones the term no longer names. Not a
-- component of the configuration -- it is read off the two that are.
cfgHidden :: Config a -> [Name]
cfgHidden cfg = cfgNames cfg \\ map fst (ctxOf cfg)

-- >>> cfgHidden (initConfig [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) (Return (VVar "x")) :: Config Rational)
-- ["y"]

-- After a drop the dropped register is hidden.
-- >>> map cfgHidden (step (initConfig [("x", 2), ("a", 2)] (ket [2, 2] [0, 0]) (Do (StDrop 0 (VVar "a")) (Return (VVar "x"))) :: Config Rational))
-- [["a"]]

-- The registers' places -------------------------------------------------------

posOf :: Config a -> Name -> Int
posOf cfg x = case elemIndex x (cfgNames cfg) of
  Just i  -> i
  -- impossible: a typed term names only allocated registers, and 'usable' refuses the rest first
  Nothing -> error ("Drop.Lang.Machine: no register " ++ x ++ " in scope")

-- >>> posOf (initConfig [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) (Return VUnit) :: Config Rational) "y"
-- 1

dimOf :: Config a -> Name -> Int
-- impossible: posOf is an index into cfgNames, and cfgDims has one entry per name
dimOf cfg x = cfgDims cfg !! posOf cfg x

-- >>> dimOf (initConfig [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) (Return VUnit) :: Config Rational) "y"
-- 3

-- The guards of a step ---------------------------------------------------------
--
-- A term that never met the checker may name a register the run has
-- already dropped. A drop changes nothing in sigma, so the step would go
-- through and a later criterion would read a state the program was not
-- allowed to touch; the machine refuses such a step by name instead, and
-- also a drop that names one register twice and a lift whose block is not
-- a nonempty proper set of the register's levels.

-- | The registers a gate, a drop or a lift names are in scope, not yet
-- dropped, and named once each: 'True', or a refusal by name.
usable :: Config a -> String -> [Name] -> Bool
usable cfg what xs
  | (x : _) <- [ x | x <- xs, x `elem` dropped ] =
      -- refusal: a register is named after its drop
      error ("Drop.Lang.Machine: " ++ what ++ " names register " ++ x
             ++ ", which has been dropped")
  | (x : _) <- [ x | x <- xs, x `notElem` cfgNames cfg ] =
      -- refusal: a register is named that was never allocated
      error ("Drop.Lang.Machine: " ++ what ++ " names register " ++ x
             ++ ", which is not in scope")
  | length (nub xs) /= length xs =
      -- refusal: one register is named twice by one statement
      error ("Drop.Lang.Machine: " ++ what ++ " names a register twice in "
             ++ unwords xs)
  | otherwise = True
  where dropped = concatMap srHidden (cfgSites cfg)

-- >>> usable (initConfig [("x", 2), ("y", 3)] (ket [2, 3] [0, 0]) (Return VUnit) :: Config Rational) "gate" ["x", "y"]
-- True

-- | The block of a lift is a nonempty proper set of the register's levels:
-- 'True', or a refusal by name.
goodBlock :: Config a -> Name -> [Int] -> Bool
goodBlock cfg x s
  | null s || any (\l -> l < 0 || l >= d) s || length (nub s) /= length s
      || length s >= d =
      -- refusal: the block of a lift is not a nonempty proper set of levels
      error ("Drop.Lang.Machine: the block " ++ show s ++ " of a lift is not a \
             \nonempty proper set of the " ++ show d ++ " levels of " ++ x)
  | otherwise = True
  where d = dimOf cfg x

-- >>> goodBlock (initConfig [("x", 3)] (ket [3] [0]) (Return VUnit) :: Config Rational) "x" [0, 2]
-- True

-- The five rules ---------------------------------------------------------------

-- | \\textsc{Step-New} at an EXPLICITLY CHOSEN name @w@: 'Nothing' when
-- either side condition fails -- @w@ already in Delta, or @w@ bound in the
-- continuation. The second keeps a name from being cloned: on
-- @new 5; new 7; return (5,7)@, choosing @w = 7@ at the first allocation
-- makes @M[7/5]@ name one register twice, and this returns 'Nothing' rather
-- than cloning it.
stepNewAt :: Num a => Name -> Config a -> Maybe (Config a)
stepNewAt w cfg = case cfgTerm cfg of
  Do (StNew t d psi) m
    | w `elem` cfgNames cfg  -> Nothing
    | w `elem` boundIn m      -> Nothing
    | otherwise -> Just cfg
        { cfgNames = cfgNames cfg ++ [w]
        , cfgDims  = cfgDims cfg ++ [d]
        , cfgAmp   = tensorS (cfgAmp cfg) psi
        , cfgTerm  = renameTerm t w m
        }
  Do (StLoan a d) m
    | w `elem` cfgNames cfg  -> Nothing
    | w `elem` boundIn m      -> Nothing
    | otherwise ->
        let psi = case lookup a (cfgLoans cfg) of
              Just st -> st
              -- refusal: a loan reached the machine with no arrival state (use initConfigL)
              Nothing -> error ("Drop.Lang.Machine: no probe state assigned to the loan "
                                 ++ a ++ "; use initConfigL")
        in Just cfg
             { cfgNames = cfgNames cfg ++ [w]
             , cfgDims  = cfgDims cfg ++ [d]
             , cfgAmp   = tensorS (cfgAmp cfg) psi
             , cfgTerm  = renameTerm a w m
             }
  _ -> Nothing

-- The term allocates u, then v, and returns both.
-- >>> fmap cfgNames (stepNewAt "w" (initConfig [] [1] (Do (StNew "u" 2 (ket [2] [0])) (Do (StNew "v" 2 (ket [2] [0])) (Return (VPair (VVar "u") (VVar "v"))))) :: Config Rational))
-- Just ["w"]

-- The name v is bound later in the term: choosing it at the first allocation would clone a register.
-- >>> fmap cfgNames (stepNewAt "v" (initConfig [] [1] (Do (StNew "u" 2 (ket [2] [0])) (Do (StNew "v" 2 (ket [2] [0])) (Return (VPair (VVar "u") (VVar "v"))))) :: Config Rational))
-- Nothing

-- The name x is already in Delta.
-- >>> fmap cfgNames (stepNewAt "x" (initConfig [("x", 2)] (ket [2] [0]) (Do (StNew "u" 2 (ket [2] [0])) (Return (VVar "u"))) :: Config Rational))
-- Nothing

-- A term that does not allocate has no such step.
-- >>> fmap cfgNames (stepNewAt "w" (initConfig [("x", 2)] (ket [2] [0]) (Return (VVar "x")) :: Config Rational))
-- Nothing

-- | The name \\textsc{Step-New} takes when the machine is left to choose:
-- the one the program wrote, when the side conditions allow it, and
-- otherwise the first fresh variant of it that does.
allocName :: Config a -> Name -> Term a -> Name
allocName cfg t m = fresh (cfgNames cfg ++ boundIn m) t

-- >>> allocName (initConfig [("x", 2)] (ket [2] [0]) (Return (VVar "x")) :: Config Rational) "a" (Return (VVar "a"))
-- "a"

-- The name the program wrote is taken, so the machine picks a fresh variant.
-- >>> allocName (initConfig [("a", 2)] (ket [2] [0]) (Return (VVar "a")) :: Config Rational) "a" (Return (VVar "a"))
-- "a_1"

-- | Step-Gate applies U to the factors v names, in the order v lists them;
-- the registers keep their names, since a gate binds nothing.
stepGate :: Num a => Config a -> Matrix a -> Value -> Term a -> [Config a]
stepGate cfg g v m = [ cfg { cfgAmp = amp', cfgTerm = m } ]
  where
    positions = map (posOf cfg) (valueNames v)
    amp'      = applyGate (cfgDims cfg) g positions (cfgAmp cfg)

-- The gate X on the register x, in |0>.
-- >>> map cfgTerm (stepGate (initConfig [("x", 2)] (ket [2] [0]) (Return VUnit)) [[0,1],[1,0]] (VVar "x") (Return (VVar "x"))) :: [Term Rational]
-- [Return (VVar "x")]
-- >>> map cfgAmp (stepGate (initConfig [("x", 2)] (ket [2] [0]) (Return VUnit)) [[0,1],[1,0]] (VVar "x") (Return (VVar "x"))) :: [StateV Rational]
-- [[0 % 1,1 % 1]]

-- | Step-New allocates a name w with w not in Delta AND w not bound in M,
-- tensors psi on, and continues with M[w/t]. The second side condition is
-- not decoration: without it the renaming captures a binder of M and the
-- successor clones a register ('stepNewAt' refuses such a w; TypedSpec (n)
-- is the witness). The machine picks the name with 'allocName'.
stepNew :: Num a => Config a -> Name -> Term a -> [Config a]
stepNew cfg t m = maybe [] (: []) (stepNewAt (allocName cfg t m) cfg)

-- >>> map cfgTerm (stepNew (initConfig [("x", 2)] (ket [2] [0]) (Do (StNew "a" 2 (ket [2] [0])) (Return (VPair (VVar "x") (VVar "a")))) :: Config Rational) "a" (Return (VPair (VVar "x") (VVar "a"))))
-- [Return (VPair (VVar "x") (VVar "a"))]
-- >>> map cfgNames (stepNew (initConfig [("x", 2)] (ket [2] [0]) (Do (StNew "a" 2 (ket [2] [0])) (Return (VPair (VVar "x") (VVar "a")))) :: Config Rational) "a" (Return (VPair (VVar "x") (VVar "a"))))
-- [["x","a"]]
-- >>> map cfgAmp (stepNew (initConfig [("x", 2)] (ket [2] [1]) (Do (StNew "a" 2 (ket [2] [0])) (Return (VPair (VVar "x") (VVar "a")))) :: Config Rational) "a" (Return (VPair (VVar "x") (VVar "a"))))
-- [[0 % 1,0 % 1,1 % 1,0 % 1]]

-- The name the program wrote is taken: the register is allocated under a fresh variant.
-- >>> map cfgNames (stepNew (initConfig [("a", 2)] (ket [2] [1]) (Do (StNew "a" 2 (ket [2] [0])) (Return (VVar "a"))) :: Config Rational) "a" (Return (VVar "a")))
-- [["a","a_1"]]

-- | A loan is an input register, hoisted to the head of the body, so it
-- arrives on the state 'initConfigL' assigned it rather than on a psi the
-- text names; it allocates under its header name exactly as `new` does.
stepLoan :: Num a => Config a -> Name -> Term a -> [Config a]
stepLoan cfg a m = maybe [] (: []) (stepNewAt (allocName cfg a m) cfg)

-- >>> map cfgNames (stepLoan (initConfigL [("x", 2)] (ket [2] [0]) [("a", ket [2] [1])] (Do (StLoan "a" 2) (Return (VVar "a"))) :: Config Rational) "a" (Return (VVar "a")))
-- [["x","a"]]
-- >>> map cfgAmp (stepLoan (initConfigL [("x", 2)] (ket [2] [0]) [("a", ket [2] [1])] (Do (StLoan "a" 2) (Return (VVar "a"))) :: Config Rational) "a" (Return (VVar "a")))
-- [[0 % 1,1 % 1,0 % 1,0 % 1]]

-- | Step-Drop deletes the statement: it applies nothing to sigma and
-- allocates nothing. It appends the site (the names, the registers and the
-- state at this moment) to the record the criterion reads.
stepDrop :: Config a -> SiteId -> Value -> Term a -> [Config a]
stepDrop cfg site v m = [ cfg { cfgSites = cfgSites cfg ++ [rec_], cfgTerm = m } ]
  where
    names = valueNames v
    rec_  = SiteRecord site names (cfgNames cfg) (cfgDims cfg) (cfgAmp cfg)

-- The drop records its site: the id, the names it hid and the registers then in scope.
-- >>> map (map srSite . cfgSites) (stepDrop (initConfig [("x", 2), ("a", 2)] (ket [2, 2] [0, 0]) (Return VUnit) :: Config Rational) 7 (VVar "a") (Return (VVar "x")))
-- [[7]]
-- >>> map (map srHidden . cfgSites) (stepDrop (initConfig [("x", 2), ("a", 2)] (ket [2, 2] [0, 0]) (Return VUnit) :: Config Rational) 7 (VVar "a") (Return (VVar "x")))
-- [[["a"]]]
-- >>> map (map srNames . cfgSites) (stepDrop (initConfig [("x", 2), ("a", 2)] (ket [2, 2] [0, 0]) (Return VUnit) :: Config Rational) 7 (VVar "a") (Return (VVar "x")))
-- [[["x","a"]]]

-- Nothing is applied to the state.
-- >>> map cfgAmp (stepDrop (initConfig [("x", 2), ("a", 2)] (ket [2, 2] [1, 0]) (Return VUnit) :: Config Rational) 7 (VVar "a") (Return (VVar "x")))
-- [[0 % 1,0 % 1,1 % 1,0 % 1]]

-- | Step-Lift fires in two labelled instances, b = 1 then b = 0, applying
-- (P^b_S)_x to sigma and continuing with M[b/p]; the register keeps its
-- name. It is the only labelled rule and the only one that does not
-- preserve the norm of sigma.
stepLift :: Num a => Config a -> Name -> [Int] -> Name -> Term a -> [Config a]
stepLift cfg p s x m = [ mkBranch 1 s, mkBranch 0 ([0 .. d - 1] \\ s) ]
  where
    pos = posOf cfg x
    -- impossible: pos indexes cfgNames, and cfgDims has one entry per name
    d   = cfgDims cfg !! pos
    mkBranch bit keep = cfg
      { cfgAmp  = projectLevels (cfgDims cfg) pos keep (cfgAmp cfg)
      , cfgBits = cfgBits cfg ++ [(p, bit)]
      , cfgTerm = substParam p (bit == 1) m
      }

-- Measure x, in an equal superposition, against the block {1}: two successors, the bit 1 first.
-- >>> map cfgBits (stepLift (initConfig [("x", 2)] [1, 1] (Return VUnit) :: Config Rational) "p" [1] "x" (Return (VVar "x")))
-- [[("p",1)],[("p",0)]]
-- >>> map cfgAmp (stepLift (initConfig [("x", 2)] [1, 1] (Return VUnit) :: Config Rational) "p" [1] "x" (Return (VVar "x")))
-- [[0 % 1,1 % 1],[1 % 1,0 % 1]]

-- The bit replaces the parameter in the rest of the term.
-- >>> map cfgTerm (stepLift (initConfig [("x", 2)] [1, 1] (Return VUnit) :: Config Rational) "p" [1] "x" (If (BParam "p") (Return (VVar "x")) (Return (VVar "x"))))
-- [If (BLit True) (Return (VVar "x")) (Return (VVar "x")),If (BLit False) (Return (VVar "x")) (Return (VVar "x"))]

-- | Step-If replaces the `if` by one branch, by the value of the CLOSED
-- guard e (closed because Step-Lift substituted its bit).
stepIf :: Config a -> BExpr -> Term a -> Term a -> [Config a]
stepIf cfg e m1 m2 = [ cfg { cfgTerm = if evalB env e then m1 else m2 } ]
  where
    -- The record is consulted only for a parameter a caller bound outside this term.
    env nm = case lookup nm (cfgBits cfg) of
      Just b  -> b == 1
      -- refusal: a guard reads a parameter no lift bound
      Nothing -> error ("Drop.Lang.Machine: parameter " ++ nm ++ " not bound")

-- >>> map cfgTerm (stepIf (initConfig [("x", 2)] (ket [2] [0]) (Return VUnit) :: Config Rational) (BLit True) (Return (VVar "x")) (Return VUnit))
-- [Return (VVar "x")]
-- >>> map cfgTerm (stepIf (initConfig [("x", 2)] (ket [2] [0]) (Return VUnit) :: Config Rational) (BNot (BLit True)) (Return (VVar "x")) (Return VUnit))
-- [Return VUnit]

-- A parameter an earlier lift fired is read from the record.
-- >>> map cfgTerm (stepIf ((initConfig [("x", 2)] (ket [2] [0]) (Return VUnit) :: Config Rational) { cfgBits = [("p", 1)] }) (BParam "p") (Return (VVar "x")) (Return VUnit))
-- [Return (VVar "x")]

-- One machine step -------------------------------------------------------------

-- | One machine step. [] at a value (final); one successor at a gate, an
-- allocation, a drop or an `if`; two labelled successors (b = 1 then b = 0)
-- at a lift. The head of the term picks the rule.
step :: Num a => Config a -> [Config a]
step cfg = case cfgTerm cfg of
  Return _ -> []
  Do (StGate g v) m   | usable cfg "gate" (valueNames v) -> stepGate cfg g v m
  Do (StNew t _ _) m  -> stepNew cfg t m
  Do (StLoan a _) m   -> stepLoan cfg a m
  Do (StDrop site v) m | usable cfg "drop" (valueNames v) -> stepDrop cfg site v m
  Do (StLift p s x) m | usable cfg "lift" [x] && goodBlock cfg x s -> stepLift cfg p s x m
  If e m1 m2          -> stepIf cfg e m1 m2
  -- impossible: every guard above either holds or calls 'error'
  _ -> error "Drop.Lang.Machine.step: refused"

-- One step per rule, on the smallest term that fires it. A value is final: no successor.
-- >>> length (step (initConfig [("x", 2)] (ket [2] [0]) (Return (VVar "x")) :: Config Rational))
-- 0

-- Gate: X flips |0> to |1>.
-- >>> map cfgTerm (step (initConfig [("x", 2)] (ket [2] [0]) (Do (StGate [[0,1],[1,0]] (VVar "x")) (Return (VVar "x"))) :: Config Rational))
-- [Return (VVar "x")]
-- >>> map cfgAmp (step (initConfig [("x", 2)] (ket [2] [0]) (Do (StGate [[0,1],[1,0]] (VVar "x")) (Return (VVar "x"))) :: Config Rational))
-- [[0 % 1,1 % 1]]

-- New: the register a joins Delta, and the term continues with a.
-- >>> map cfgTerm (step (initConfig [("x", 2)] (ket [2] [0]) (Do (StNew "a" 2 (ket [2] [0])) (Return (VPair (VVar "x") (VVar "a")))) :: Config Rational))
-- [Return (VPair (VVar "x") (VVar "a"))]
-- >>> map cfgNames (step (initConfig [("x", 2)] (ket [2] [0]) (Do (StNew "a" 2 (ket [2] [0])) (Return (VPair (VVar "x") (VVar "a")))) :: Config Rational))
-- [["x","a"]]

-- Loan: the same, on the state the caller assigned.
-- >>> map cfgAmp (step (initConfigL [("x", 2)] (ket [2] [0]) [("a", ket [2] [1])] (Do (StLoan "a" 2) (Return (VPair (VVar "x") (VVar "a")))) :: Config Rational))
-- [[0 % 1,1 % 1,0 % 1,0 % 1]]

-- Drop: the term continues and the site is recorded.
-- >>> map (map srHidden . cfgSites) (step (initConfig [("x", 2), ("a", 2)] (ket [2, 2] [0, 0]) (Do (StDrop 0 (VVar "a")) (Return (VVar "x"))) :: Config Rational))
-- [[["a"]]]
-- >>> map cfgTerm (step (initConfig [("x", 2), ("a", 2)] (ket [2, 2] [0, 0]) (Do (StDrop 0 (VVar "a")) (Return (VVar "x"))) :: Config Rational))
-- [Return (VVar "x")]

-- Lift: two successors, the bit 1 first.
-- >>> map cfgAmp (step (initConfig [("x", 2)] [1, 1] (Do (StLift "p" [1] "x") (Return (VVar "x"))) :: Config Rational))
-- [[0 % 1,1 % 1],[1 % 1,0 % 1]]
-- >>> map cfgBits (step (initConfig [("x", 2)] [1, 1] (Do (StLift "p" [1] "x") (Return (VVar "x"))) :: Config Rational))
-- [[("p",1)],[("p",0)]]

-- If: the closed guard picks the first branch.
-- >>> map cfgTerm (step (initConfig [("x", 2)] (ket [2] [0]) (If (BLit True) (Return (VVar "x")) (Return VUnit)) :: Config Rational))
-- [Return (VVar "x")]

-- | Run to every leaf (a root-to-leaf path through the lift labels).
-- Terminates because every rule strictly shortens the term: the number of
-- statements along the longest branch, an `if` counting as one
-- ('Drop.Lang.Syntax.termSize'), drops by one at each step.
run :: (Eq a, Num a) => Config a -> [Config a]
run cfg = case step cfg of
  []    -> [cfg]
  succs -> concatMap run succs

-- The abstract's temporary AND, uncomputed by measurement, from |11>: one leaf per bit of the lift.
-- >>> :m + Drop.Lang.Programs.TempAnd Drop.Lang.Elab
-- >>> length (run (initConfig visXY (ket [2, 2] [1, 1]) (toTerm (progTerm (flatToProgram visXY andUncomputedByMeasurement)))))
-- 2

-- Each leaf carries the sites its path crossed: the one drop of a.
-- >>> map (map srHidden . cfgSites) (run (initConfig visXY (ket [2, 2] [1, 1]) (toTerm (progTerm (flatToProgram visXY andUncomputedByMeasurement)))))
-- [[["a"]],[["a"]]]

-- The bits of the two leaves.
-- >>> map cfgBits (run (initConfig visXY (ket [2, 2] [1, 1]) (toTerm (progTerm (flatToProgram visXY andUncomputedByMeasurement)))))
-- [[("m",1)],[("m",0)]]

-- A term with no lift has one leaf.
-- >>> length (run (initConfig [("x", 2)] (ket [2] [0]) (Do (StGate [[0,1],[1,0]] (VVar "x")) (Return (VVar "x"))) :: Config Rational))
-- 1
