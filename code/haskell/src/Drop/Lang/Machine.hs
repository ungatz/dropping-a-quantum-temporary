-- Machine.hs: the machine figure, and the two rules the measurement section adds.
--
-- A configuration is @<Delta, sigma || M>@ and NOTHING ELSE: 'cfgNames' /
-- 'cfgDims' are Delta, the registers allocated so far in allocation order,
-- 'cfgAmp' is sigma in [[Delta]], unnormalised, and 'cfgTerm' is M. There is
-- no hidden set. The hidden registers are the allocated ones the term no
-- longer names ('cfgHidden'), which along any run are exactly the ones the
-- run has dropped (the type-safety theorem's clause (5), checked in TypedSpec (o)).
--
-- Five rules fire, each at the head of M:
--
--   Step-Gate  applies U to the factors v names, in the order v lists them;
--              the registers keep their names, since a gate binds nothing.
--   Step-New   allocates a name w with w not in Delta AND w not bound in M,
--              tensors psi on, and continues with M[w/t]. The second side
--              condition is not decoration: without it the renaming captures
--              a binder of M and the successor clones a register
--              ('stepNewAt' refuses such a w; TypedSpec (n) is the witness).
--   Step-Drop  deletes the statement: it applies nothing to sigma and
--              allocates nothing.
--   Step-Lift  fires in two labelled instances, b = 1 then b = 0, applying
--              (P^b_S)_x to sigma and continuing with M[b/p]; the register
--              keeps its name. It is the only labelled rule and the only one
--              that does not preserve the norm of sigma.
--   Step-If    replaces the `if` by one branch, by the value of the CLOSED
--              guard e (closed because Step-Lift substituted its bit).
--
-- 'run' collects the leaf configurations, one per root-to-leaf path through
-- the lift labels, each carrying its own record ('cfgBits') and its own list
-- of site states (one entry per `drop` the leaf's path crossed).

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
  , finalType
  ) where

import Data.List (elemIndex, nub, (\\))
import Drop.Lang.QState
import Drop.Lang.Typed

-- | The state recorded at one `drop` occurrence on one leaf's path: the site
-- id, the names it hid, and the full (names, dims, amplitude) triple at the
-- moment of the drop -- exactly what the criterion (Drop.Lang.Interp, for the
-- flat engine) needs to factor.
data SiteRecord a = SiteRecord
  { srSite   :: SiteId
  , srHidden :: [Name]
  , srNames  :: [Name]
  , srDims   :: [Int]
  , srAmp    :: StateV a
  } deriving (Eq, Show)

data Config a = Config
  { cfgNames  :: [Name]        -- Delta, allocation order
  , cfgDims   :: [Int]
  , cfgAmp    :: StateV a      -- sigma in [[Delta]], unnormalised
  , cfgTerm   :: Term a        -- M
  , cfgBits   :: [(Name, Int)] -- the record so far: one entry per lift fired
  , cfgSites  :: [SiteRecord a]
  , cfgLoans  :: [(Name, StateV a)]
    -- ^ the probe state a loan ('Drop.Lang.Typed.StLoan') is to arrive on, one
    -- entry consumed per loan, keyed by the name the header gave it. Empty
    -- on every configuration built by 'initConfig', so no existing caller is
    -- affected: only a term containing a loan ever consults it.
  } deriving Show

initConfig :: [(Name, Int)] -> StateV a -> Term a -> Config a
initConfig vis amp m = initConfigL vis amp [] m

-- | As 'initConfig', but also supplying the state each loan the term
-- allocates is to arrive on, keyed by the loan's name. (Every name is bound
-- once in this language, so the key is unambiguous.)
initConfigL :: [(Name, Int)] -> StateV a -> [(Name, StateV a)] -> Term a -> Config a
initConfigL vis amp loans m = Config (map fst vis) (map snd vis) amp m [] [] loans

isFinal :: Config a -> Bool
isFinal cfg = case cfgTerm cfg of
  Return _ -> True
  _        -> False

-- | The term's own register context: the allocated registers the term still
-- names. The type-safety theorem's clause (5) says this is the allocated registers minus the
-- ones the run has dropped.
ctxOf :: Config a -> [(Name, Int)]
ctxOf cfg = [ (x, d) | (x, d) <- zip (cfgNames cfg) (cfgDims cfg), x `elem` live ]
  where live = freeTerm (cfgTerm cfg)

-- | The hidden registers: the allocated ones the term no longer names. Not a
-- component of the configuration -- it is read off the two that are.
cfgHidden :: Config a -> [Name]
cfgHidden cfg = cfgNames cfg \\ map fst (ctxOf cfg)

-- | The type of a final configuration's value, read off its live registers
-- and returned value shape (used by preservation checks in the test suite).
finalType :: Config a -> Maybe Ty
finalType cfg = case cfgTerm cfg of
  Return v -> Just (go v)
  _        -> Nothing
  where
    go (VVar x) = TReg (dimOf cfg x)
    go VUnit    = TUnit
    go (VPair a b) = TTensor (go a) (go b)

posOf :: Config a -> Name -> Int
posOf cfg x = case elemIndex x (cfgNames cfg) of
  Just i  -> i
  Nothing -> error ("Drop.Lang.Machine: no register " ++ x ++ " in scope")

dimOf :: Config a -> Name -> Int
dimOf cfg x = cfgDims cfg !! posOf cfg x

-- | \\textsc{Step-New} at an EXPLICITLY CHOSEN name @w@: 'Nothing' when
-- either side condition fails -- @w@ already in Delta, or @w@ bound in the
-- continuation. The second is the one the printed rule used to lack: on
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
              Nothing -> error ("Drop.Lang.Machine: no probe state assigned to the loan "
                                 ++ a ++ "; use initConfigL")
        in Just cfg
             { cfgNames = cfgNames cfg ++ [w]
             , cfgDims  = cfgDims cfg ++ [d]
             , cfgAmp   = tensorS (cfgAmp cfg) psi
             , cfgTerm  = renameTerm a w m
             }
  _ -> Nothing

-- | The name \\textsc{Step-New} takes when the machine is left to choose:
-- the one the program wrote, when the side conditions allow it, and
-- otherwise the first fresh variant of it that does.
allocName :: Config a -> Name -> Term a -> Name
allocName cfg t m = fresh (cfgNames cfg ++ boundIn m) t

-- | One machine step. [] at a value (final); one successor at a gate, an
-- allocation, a drop or an `if`; two labelled successors (b = 1 then b = 0)
-- at a lift.
--
-- A term that never met the checker may name a register the run has
-- already dropped. A drop changes nothing in sigma, so the step would go
-- through and a later criterion would read a state the program was not
-- allowed to touch; the machine refuses such a step by name instead, and
-- also a drop that names one register twice and a lift whose block is not
-- a nonempty proper set of the register's levels.
step :: Num a => Config a -> [Config a]
step cfg = case cfgTerm cfg of
  Return _ -> []

  Do (StGate g v) m | usable "gate" (valueNames v) ->
    let positions = map (posOf cfg) (valueNames v)
        amp'      = applyGate (cfgDims cfg) g positions (cfgAmp cfg)
    in [ cfg { cfgAmp = amp', cfgTerm = m } ]

  Do (StNew t _ _) m -> maybe [] (: []) (stepNewAt (allocName cfg t m) cfg)

  -- A loan is an input register, hoisted to the head of the body, so it
  -- arrives on the state 'initConfigL' assigned it rather than on a psi the
  -- text names; it allocates under its header name exactly as `new` does.
  Do (StLoan a _) m -> maybe [] (: []) (stepNewAt (allocName cfg a m) cfg)

  Do (StDrop site v) m | usable "drop" (valueNames v) ->
    let names = valueNames v
        rec_  = SiteRecord site names (cfgNames cfg) (cfgDims cfg) (cfgAmp cfg)
    in [ cfg { cfgSites = cfgSites cfg ++ [rec_], cfgTerm = m } ]

  Do (StLift p s x) m | usable "lift" [x] && goodBlock x s ->
    let pos = posOf cfg x
        d   = cfgDims cfg !! pos
        mkBranch bit keep = cfg
          { cfgAmp  = projectLevels (cfgDims cfg) pos keep (cfgAmp cfg)
          , cfgBits = cfgBits cfg ++ [(p, bit)]
          , cfgTerm = substParam p (bit == 1) m
          }
    in [ mkBranch 1 s, mkBranch 0 ([0 .. d - 1] \\ s) ]

  If e m1 m2 ->
    -- Step-Lift substituted its bit, so e is closed; the record is consulted
    -- only for a parameter a caller bound outside this term.
    let env nm = case lookup nm (cfgBits cfg) of
          Just b  -> b == 1
          Nothing -> error ("Drop.Lang.Machine: parameter " ++ nm ++ " not bound")
    in [ cfg { cfgTerm = if evalB env e then m1 else m2 } ]

  -- unreachable: every guard above either holds or calls 'error'
  _ -> error "Drop.Lang.Machine.step: refused"
  where
    dropped = concatMap srHidden (cfgSites cfg)
    usable what xs
      | (x : _) <- [ x | x <- xs, x `elem` dropped ] =
          error ("Drop.Lang.Machine: " ++ what ++ " names register " ++ x
                 ++ ", which has been dropped")
      | (x : _) <- [ x | x <- xs, x `notElem` cfgNames cfg ] =
          error ("Drop.Lang.Machine: " ++ what ++ " names register " ++ x
                 ++ ", which is not in scope")
      | length (nub xs) /= length xs =
          error ("Drop.Lang.Machine: " ++ what ++ " names a register twice in "
                 ++ unwords xs)
      | otherwise = True
    goodBlock x s
      | null s || any (\l -> l < 0 || l >= d) s || length (nub s) /= length s
          || length s >= d =
          error ("Drop.Lang.Machine: the block " ++ show s ++ " of a lift is not a \
                 \nonempty proper set of the " ++ show d ++ " levels of " ++ x)
      | otherwise = True
      where d = dimOf cfg x

-- | Run to every leaf (a root-to-leaf path through the lift labels).
-- Terminates because every rule strictly shortens the term: the number of
-- statements along the longest branch, an `if` counting as one
-- ('Drop.Lang.Typed.termSize'), drops by one at each step.
run :: (Eq a, Num a) => Config a -> [Config a]
run cfg = case step cfg of
  []    -> [cfg]
  succs -> concatMap run succs
