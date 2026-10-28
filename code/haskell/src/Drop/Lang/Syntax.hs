-- Drop.Lang.Syntax: the language the paper prints, as data.
--
-- Question: What is a program, and what does a term look like before anything is checked or run?
-- Answer:   A sequence of statements ending in return: a gate on named registers, new (the one
--           binder), drop, lift, and if in tail position. Types are 1, [d] and tensor products;
--           values are names, unit and pairs. A block ybar = { M1 }; M2 and a non-tail if are
--           surface forms; seqTerm, M1 (+)_ybar M2 in three clauses, spells them out before typing.
-- Paper:    fig:syntax (the grammar), sec:lang:syntax (the language), app:surface (the surface
--           forms and the renaming).
-- Shapes:   Name, SiteId  a register or parameter name (a String); the number of a drop site.
--           Ty            1, [d] or A (x) B: TUnit, TReg d, TTensor.
--           Value         a name, unit or a pair: VVar, VUnit, VPair.
--           BExpr         a guard over lifted bits; BLit is the bit Step-Lift leaves behind.
--           Stmt a        one statement: StGate, StNew, StLoan, StDrop, StLift; none is a term.
--           Term a        statements ending in Return, with If in tail position.
--           Surface a     a Term and SBlock, the one extra production that seqTerm expands.
--           Program a     the header's registers, as (name, dimension), and a Surface.

module Drop.Lang.Syntax where

import Data.List (nub, (\\))
import Drop.Lang.State (Matrix, StateV)

-- The data -----------------------------------------------------------------
--
-- A term is a SEQUENCE OF STATEMENTS ending in `return`, and that is the
-- spelling a program file uses: there is no second grammar and no
-- abbreviation. 'Term' is that sequence, 'Stmt' one of its statements, and
-- `if` is a term former in tail position.
--
-- The scalar field is left polymorphic: 'StNew' names psi as a StateV a, so a
-- clean allocation is 'StNew t d (ket [d] [i])' and a dirty one any other
-- unit vector.

type Name = String

-- | A site is an occurrence of `drop v` in the surface program. The
-- sequencing operator's `if` clause may copy it into several occurrences of
-- the expanded term; they carry the same SiteId, assigned once when the
-- surface term is built.
type SiteId = Int

-- Types: A ::= 1 | [d] | A (x) B
data Ty
  = TUnit
  | TReg Int              -- [d], d >= 2
  | TTensor Ty Ty
  deriving (Eq, Show)

-- Values: v ::= x | () | (v1, v2)
data Value
  = VVar Name
  | VUnit
  | VPair Value Value
  deriving (Eq, Show)

-- | Boolean guards over lifted bits: the syntax figure's
-- @e ::= b | p | not e | e1 and e2 | e1 or e2@.
--
-- 'BLit' is a bit constant a program file writes as 0 or 1. It is also what
-- \\textsc{Step-Lift}'s substitution @M[b/p]@ puts in place of the parameter
-- it consumes, so that \\textsc{Step-If}'s guard is CLOSED, as the machine's
-- rule requires. A bit constant needs no parameter in scope.
data BExpr
  = BParam Name
  | BNot BExpr
  | BAnd BExpr BExpr
  | BOr BExpr BExpr
  | BLit Bool
  deriving (Eq, Show)

-- | A statement: one of the syntax figure's four measurement-free forms, plus the
-- lift the measurement section adds. Each one prefixes a term; none of them
-- is a term, and nothing types one alone (the language definition).
--
-- `new` is the only binder. A gate binds nothing ("CX x t;" applies CX to
-- the two registers, which keep their names); a drop binds nothing; a lift
-- binds its PARAMETER and leaves the register live under its own name.
data Stmt a
  = StGate (Matrix a) Value
    -- ^ @U v;@ --- a gate on the registers v names, in that order. Binds
    -- nothing: the registers keep their names.
  | StNew Name Int (StateV a)
    -- ^ @new t : [d] \@ psi;@ --- the only binder of the language.
  | StLoan Name Int
    -- ^ a header @loan a : [d]@, hoisted to the head of the body: an input
    -- register handed over in a state the program does not know. It types
    -- and runs as an input; only the site definition and the compiler read the marker.
  | StDrop SiteId Value
    -- ^ @drop v;@ --- forget the registers v names. Binds nothing. A tuple
    -- drop is ONE site (the composite-temporary proposition), which is why it carries one id.
  | StLift Name [Int] Name
    -- ^ @p = lift_S x;@ --- binds the parameter p; the register x stays
    -- live under its own name.
  deriving (Eq, Show)

-- | Terms: a sequence of statements ending in @return@, with @if@ in tail
-- position. This is the syntax figure, and it is also the file format.
--
-- @M ::= return v | U v; M | new t : [d] \@ psi; M | drop v; M
--       | p = lift_S x; M | if e { M1 } else { M2 }@
data Term a
  = Return Value
  | Do (Stmt a) (Term a)
  | If BExpr (Term a) (Term a)
  deriving (Eq, Show)

-- >>> Do (StDrop 0 (VVar "t")) (Return VUnit) :: Term Int
-- Do (StDrop 0 (VVar "t")) (Return VUnit)

-- | The surface: the terms, plus the ONE extra production that spells the
-- two forms expanded before typing. @SBlock ybar M1 M2@ is the block
-- @ybar = { M1 }; M2@, and a non-tail @if@ is the same production with M1
-- an @SIf@ --- so no separate constructor is needed for it.
data Surface a
  = SReturn Value
  | SDo (Stmt a) (Surface a)
  | SIf BExpr (Surface a) (Surface a)
  | SBlock Value (Surface a) (Surface a)
  deriving (Eq, Show)

-- | A program: an input register context (names with their dimensions, in a
-- fixed order) plus a surface term. @prog f (x1:[d1], ..., xn:[dn]) : A { M }@
-- is the judgement @x1:[d1], ..., xn:[dn] |- M : A@.
data Program a = Program
  { progCtx  :: [(Name, Int)]
  , progTerm :: Surface a
  } deriving (Eq, Show)

-- >>> progCtx (Program [("x", 2)] (SReturn (VVar "x")) :: Program Int)
-- [("x",2)]

-- Names ------------------------------------------------------------------

-- | The names of a value, left to right.
valueNames :: Value -> [Name]
valueNames (VVar x)    = [x]
valueNames VUnit       = []
valueNames (VPair a b) = valueNames a ++ valueNames b

-- >>> valueNames VUnit
-- []
-- >>> valueNames (VVar "x")
-- ["x"]
-- >>> valueNames (VPair (VVar "x") (VPair VUnit (VVar "y")))
-- ["x","y"]

-- | Is this value a TUPLE OF NAMES -- a value all of whose leaves are
-- names? That is the only binder the language has (the syntax figure's ybar), and
-- 'substTuple' is defined exactly on it.
isTupleOfNames :: Value -> Bool
isTupleOfNames (VVar _)    = True
isTupleOfNames VUnit       = True
isTupleOfNames (VPair a b) = isTupleOfNames a && isTupleOfNames b

-- >>> isTupleOfNames (VPair (VVar "x") VUnit)
-- True

-- | The parameters a guard reads, each once.
freeB :: BExpr -> [Name]
freeB (BParam p)  = [p]
freeB (BNot e)    = freeB e
freeB (BAnd a b)  = nub (freeB a ++ freeB b)
freeB (BOr a b)   = nub (freeB a ++ freeB b)
freeB (BLit _)    = []

-- >>> freeB (BLit True)
-- []
-- >>> freeB (BAnd (BParam "p") (BNot (BParam "p")))
-- ["p"]
-- >>> freeB (BOr (BParam "p") (BParam "q"))
-- ["p","q"]

-- | A guard's value, given the bits in scope.
evalB :: (Name -> Bool) -> BExpr -> Bool
evalB env (BParam p)  = env p
evalB env (BNot e)    = not (evalB env e)
evalB env (BAnd a b)  = evalB env a && evalB env b
evalB env (BOr a b)   = evalB env a || evalB env b
evalB _   (BLit b)    = b

-- >>> evalB (const False) (BLit True)
-- True
-- >>> evalB (== "p") (BAnd (BParam "p") (BNot (BParam "q")))
-- True
-- >>> evalB (const False) (BOr (BParam "p") (BParam "q"))
-- False

-- | The register names a statement READS (it binds them nowhere).
stmtReads :: Stmt a -> [Name]
stmtReads (StGate _ v) = valueNames v
stmtReads (StNew {})   = []
stmtReads (StLoan {})  = []
stmtReads (StDrop _ v) = valueNames v
stmtReads (StLift _ _ x) = [x]

-- >>> stmtReads (StGate [[0,1],[1,0]] (VVar "x") :: Stmt Int)
-- ["x"]
-- >>> stmtReads (StNew "t" 2 [1,0] :: Stmt Int)
-- []
-- >>> stmtReads (StDrop 0 (VPair (VVar "a") (VVar "b")) :: Stmt Int)
-- ["a","b"]
-- >>> stmtReads (StLift "p" [1] "x" :: Stmt Int)
-- ["x"]

-- | The name a statement binds, if any: a register for @new@ and for a
-- loan, a parameter for a lift, nothing for a gate or a drop.
stmtBinds :: Stmt a -> Maybe Name
stmtBinds (StNew t _ _)  = Just t
stmtBinds (StLoan a _)   = Just a
stmtBinds (StLift p _ _) = Just p
stmtBinds (StGate _ _)   = Nothing
stmtBinds (StDrop _ _)   = Nothing

-- >>> stmtBinds (StNew "t" 2 [1,0] :: Stmt Int)
-- Just "t"
-- >>> stmtBinds (StLoan "a" 2 :: Stmt Int)
-- Just "a"
-- >>> stmtBinds (StLift "p" [1] "x" :: Stmt Int)
-- Just "p"
-- >>> stmtBinds (StDrop 0 (VVar "t") :: Stmt Int)
-- Nothing

-- | Free register and parameter names of a term (the two share one
-- namespace here, as the concrete syntax does).
freeTerm :: Term a -> [Name]
freeTerm (Return v) = valueNames v
freeTerm (Do st m)  = nub (stmtReads st ++ rest)
  where rest = case stmtBinds st of
                 Just b  -> freeTerm m \\ [b]
                 Nothing -> freeTerm m
freeTerm (If e m1 m2) = nub (freeB e ++ freeTerm m1 ++ freeTerm m2)

-- >>> freeTerm (Return (VVar "x") :: Term Int)
-- ["x"]
-- >>> freeTerm (Do (StNew "t" 2 [1,0]) (Return (VVar "t")) :: Term Int)
-- []
-- >>> freeTerm (Do (StLift "p" [1] "x") (If (BParam "p") (Return (VVar "x")) (Return (VVar "y"))) :: Term Int)
-- ["x","y"]

-- | Every name BOUND in a term -- registers (@new@, a loan) and parameters
-- (a lift) alike. \\textsc{Step-New}'s second side condition reads this list:
-- the name it allocates must not be bound in the continuation, or the
-- renaming captures a binder and the successor clones a register.
boundIn :: Term a -> [Name]
boundIn (Return _) = []
boundIn (Do st m)  = maybe id (:) (stmtBinds st) (boundIn m)
boundIn (If _ m1 m2) = boundIn m1 ++ boundIn m2

-- >>> boundIn (Return (VVar "x") :: Term Int)
-- []
-- >>> boundIn (Do (StNew "t" 2 [1,0]) (Do (StLift "p" [1] "t") (Return (VVar "t"))) :: Term Int)
-- ["t","p"]
-- >>> boundIn (If (BParam "p") (Do (StLoan "a" 2) (Return VUnit)) (Return VUnit) :: Term Int)
-- ["a"]

-- Substitution: renaming, and nothing else -------------------------------
--
-- Every table this section builds maps names to names, so a substitution is a
-- RENAMING: the language has no substitution beyond renaming. There is no
-- pattern grammar: the only tuple that ever binds is the tuple of names ybar
-- of a block, and substituting a tuple of names for a tuple of names is
-- 'substTuple'.

-- | Replace each name the table mentions; a name it does not mention stays.
substValue :: [(Name, Value)] -> Value -> Value
substValue tbl (VVar y)    = maybe (VVar y) id (lookup y tbl)
substValue _   VUnit       = VUnit
substValue tbl (VPair a b) = VPair (substValue tbl a) (substValue tbl b)

-- >>> substValue [("x", VVar "y")] (VVar "x")
-- VVar "y"
-- >>> substValue [("x", VVar "y")] (VVar "z")
-- VVar "z"
-- >>> substValue [("x", VVar "y"), ("z", VVar "x")] (VPair (VVar "x") (VPair VUnit (VVar "z")))
-- VPair (VVar "y") (VPair VUnit (VVar "x"))

-- | The same through a guard: a parameter is renamed when the table sends it
-- to a name, and left alone otherwise.
substBExpr :: [(Name, Value)] -> BExpr -> BExpr
substBExpr tbl (BParam p) = case lookup p tbl of
  Just (VVar q) -> BParam q
  _             -> BParam p
substBExpr tbl (BNot e)   = BNot (substBExpr tbl e)
substBExpr tbl (BAnd a b) = BAnd (substBExpr tbl a) (substBExpr tbl b)
substBExpr tbl (BOr a b)  = BOr (substBExpr tbl a) (substBExpr tbl b)
substBExpr _   (BLit b)   = BLit b

-- >>> substBExpr [("p", VVar "q")] (BAnd (BParam "p") (BParam "r"))
-- BAnd (BParam "q") (BParam "r")
-- >>> substBExpr [("p", VUnit)] (BParam "p")
-- BParam "p"
-- >>> substBExpr [("p", VVar "q")] (BLit True)
-- BLit True

-- | The same through a statement. A binder is left as it is, and so is the
-- state a @new@ carries.
substStmt :: [(Name, Value)] -> Stmt a -> Stmt a
substStmt tbl (StGate g v)   = StGate g (substValue tbl v)
substStmt _   (StNew t d ps) = StNew t d ps
substStmt _   (StLoan a d)   = StLoan a d
substStmt tbl (StDrop s v)   = StDrop s (substValue tbl v)
substStmt tbl (StLift p s x) = StLift p s (case lookup x tbl of
                                             Just (VVar y) -> y
                                             _             -> x)

-- >>> substStmt [("x", VVar "y")] (StGate [[0,1],[1,0]] (VVar "x") :: Stmt Int)
-- StGate [[0,1],[1,0]] (VVar "y")
-- >>> substStmt [("t", VVar "u")] (StNew "t" 2 [1,0] :: Stmt Int)
-- StNew "t" 2 [1,0]
-- >>> substStmt [("x", VVar "y")] (StDrop 3 (VVar "x") :: Stmt Int)
-- StDrop 3 (VVar "y")
-- >>> substStmt [("x", VVar "y")] (StLift "p" [1] "x" :: Stmt Int)
-- StLift "p" [1] "y"

-- | A simultaneous substitution through a term, stopping at a binder that
-- shadows the name being substituted.
substTerm :: [(Name, Value)] -> Term a -> Term a
substTerm tbl (Return v) = Return (substValue tbl v)
substTerm tbl (Do st m)  = Do (substStmt tbl st) (substTerm tbl' m)
  where tbl' = case stmtBinds st of
                 Just b  -> filter ((/= b) . fst) tbl
                 Nothing -> tbl
substTerm tbl (If e m1 m2) =
  If (substBExpr tbl e) (substTerm tbl m1) (substTerm tbl m2)

-- >>> substTerm [("x", VVar "y")] (Return (VVar "x") :: Term Int)
-- Return (VVar "y")
-- >>> substTerm [("x", VVar "y")] (Do (StNew "x" 2 [1,0]) (Return (VVar "x")) :: Term Int)
-- Do (StNew "x" 2 [1,0]) (Return (VVar "x"))
-- >>> substTerm [("p", VVar "q")] (If (BParam "p") (Return (VVar "x")) (Return (VVar "z")) :: Term Int)
-- If (BParam "q") (Return (VVar "x")) (Return (VVar "z"))

-- | @M[w/x]@: rename one name throughout a term.
renameTerm :: Name -> Name -> Term a -> Term a
renameTerm x w = substTerm [(x, VVar w)]

-- >>> renameTerm "x" "y" (Do (StGate [[0,1],[1,0]] (VVar "x")) (Return (VVar "x")) :: Term Int)
-- Do (StGate [[0,1],[1,0]] (VVar "y")) (Return (VVar "y"))

-- | @M[b/p]@: \\textsc{Step-Lift}'s substitution of the bit it took for the
-- parameter it bound, which is what leaves \\textsc{Step-If}'s guard closed.
-- A parameter occurs only in a guard, so this touches nothing else.
substParam :: Name -> Bool -> Term a -> Term a
substParam _ _ t@(Return _) = t
substParam p b (Do st m)
  | stmtBinds st == Just p = Do st m          -- shadowed: an inner lift rebinds p
  | otherwise              = Do st (substParam p b m)
substParam p b (If e m1 m2) =
  If (litFor e) (substParam p b m1) (substParam p b m2)
  where
    litFor (BParam q) | q == p = BLit b
    litFor (BParam q)          = BParam q
    litFor (BNot e')           = BNot (litFor e')
    litFor (BAnd a c)          = BAnd (litFor a) (litFor c)
    litFor (BOr a c)           = BOr (litFor a) (litFor c)
    litFor (BLit c)            = BLit c

-- >>> substParam "p" True (If (BParam "p") (Return VUnit) (Return VUnit) :: Term Int)
-- If (BLit True) (Return VUnit) (Return VUnit)
-- >>> substParam "p" False (If (BAnd (BParam "p") (BParam "q")) (Return VUnit) (Return VUnit) :: Term Int)
-- If (BAnd (BLit False) (BParam "q")) (Return VUnit) (Return VUnit)
-- >>> substParam "p" True (Do (StLift "p" [1] "x") (If (BParam "p") (Return VUnit) (Return VUnit)) :: Term Int)
-- Do (StLift "p" [1] "x") (If (BParam "p") (Return VUnit) (Return VUnit))

-- | @M[v/ybar]@: the substitution of \\textsc{(+)}'s first clause. @ybar@ is
-- a tuple of NAMES and @v@ a value of the same shape, so zipping their
-- leaves is exact and the result is a renaming.
substTuple :: Value -> Value -> Term a -> Term a
substTuple ybar v m = substTerm (zip (valueNames ybar) (leaves v)) m
  where
    leaves (VVar x)    = [VVar x]
    leaves VUnit       = []
    leaves (VPair a b) = leaves a ++ leaves b

-- >>> substTuple (VVar "y") (VVar "x") (Return (VVar "y") :: Term Int)
-- Return (VVar "x")
-- >>> substTuple (VPair (VVar "y") (VVar "z")) (VPair (VVar "a") (VVar "b")) (Return (VPair (VVar "z") (VVar "y")) :: Term Int)
-- Return (VPair (VVar "b") (VVar "a"))

-- Fresh names ------------------------------------------------------------

-- | A name not among the given ones, built from a base name by appending
-- @_1@, @_2@, ...; deterministic, so renaming is reproducible in tests.
fresh :: [Name] -> Name -> Name
fresh avoid base
  | base `notElem` avoid = base
  | otherwise = case [ c | n <- [(1 :: Int) ..], let c = base ++ "_" ++ show n
                         , c `notElem` avoid ] of
      (c : _) -> c
      -- impossible: the candidate stream is infinite and avoid is finite
      []      -> error "fresh: unreachable (infinite candidate stream)"

-- >>> fresh [] "t"
-- "t"
-- >>> fresh ["t"] "t"
-- "t_1"
-- >>> fresh ["t", "t_1", "t_2"] "t"
-- "t_3"

-- The sequencing operator -------------------------------------------------
--
-- Two surface forms are expanded before typing, and one operator expands
-- them: 'seqTerm' is M1 (+)_ybar M2 as the syntax figure prints it, three
-- clauses and no more. A block `ybar = { M1 }; M2` is M1 (+)_ybar M2, and a
-- non-tail `if` is (if e {M1} else {M2}) (+)_ybar M.

-- | @M1 (+)_ybar M2@, the syntax figure verbatim: three clauses, by recursion on
-- M1, one clause per statement and the same clause for all of them.
--
-- @
--   (return v)                  (+)_ybar M = M[v\/ybar]
--   (stmt; M')                  (+)_ybar M = stmt; (M' (+)_ybar M)
--   (if e {M1} else {M2})       (+)_ybar M = if e {M1 (+)_ybar M}
--                                            else {M2 (+)_ybar M}
-- @
--
-- The last clause copies the continuation into both branches, which is why
-- the expanded term can be 2^k times the size of the file under k nested
-- blocks; no run, site or verdict changes.
--
-- This is the operator alone. The desugaring lemma states it under a freshness
-- hypothesis on the names M1 binds; 'seqFresh' establishes that hypothesis
-- and then calls this.
seqTerm :: Value -> Term a -> Term a -> Term a
seqTerm ybar (Return v)   m = substTuple ybar v m
seqTerm ybar (Do st m')   m = Do st (seqTerm ybar m' m)
seqTerm ybar (If e a b)   m = If e (seqTerm ybar a m) (seqTerm ybar b m)

-- First clause: M1 is a return, so y becomes x in the continuation.
-- >>> seqTerm (VVar "y") (Return (VVar "x")) (Return (VVar "y")) :: Term Int
-- Return (VVar "x")

-- Second clause: the statement stays in front, and the clause goes on under it.
-- >>> seqTerm (VVar "y") (Do (StDrop 0 (VVar "t")) (Return (VVar "x"))) (Return (VVar "y")) :: Term Int
-- Do (StDrop 0 (VVar "t")) (Return (VVar "x"))

-- Third clause: the continuation is copied into both branches.
-- >>> seqTerm (VVar "y") (If (BParam "p") (Return (VVar "a")) (Return (VVar "b"))) (Return (VPair (VVar "y") (VVar "y"))) :: Term Int
-- If (BParam "p") (Return (VPair (VVar "a") (VVar "a"))) (Return (VPair (VVar "b") (VVar "b")))

-- | The desugaring lemma's freshness bundle, then 'seqTerm': the names M1 binds ---
-- registers and parameters alike --- are renamed fresh for M2 and for
-- @ybar@ before the operator is applied. Terms are identified up to
-- renaming of the names @new@ binds, so this changes nothing the paper
-- distinguishes; without it the componentwise renaming can clone a register.
seqFresh :: Value -> Term a -> Term a -> Term a
seqFresh ybar m1 m2 = seqTerm ybar (refreshBinders avoid m1) m2
  where avoid = nub (freeTerm m2 ++ valueNames ybar ++ boundIn m2)


-- M1 and M2 both bind t; the operator alone would let M1's t capture M2's.
-- >>> seqTerm (VVar "y") (Do (StNew "t" 2 [1,0]) (Return (VVar "t"))) (Do (StNew "t" 2 [1,0]) (Return (VPair (VVar "y") (VVar "t")))) :: Term Int
-- Do (StNew "t" 2 [1,0]) (Do (StNew "t" 2 [1,0]) (Return (VPair (VVar "t") (VVar "t"))))
-- >>> seqFresh (VVar "y") (Do (StNew "t" 2 [1,0]) (Return (VVar "t"))) (Do (StNew "t" 2 [1,0]) (Return (VPair (VVar "y") (VVar "t")))) :: Term Int
-- Do (StNew "t_1" 2 [1,0]) (Do (StNew "t" 2 [1,0]) (Return (VPair (VVar "t_1") (VVar "t"))))

-- | Rename every binder of a term away from the given names (and away from
-- the ones already chosen), leaving free names alone.
refreshBinders :: [Name] -> Term a -> Term a
refreshBinders avoid0 = go avoid0
  where
    go _ t@(Return _) = t
    go avoid (Do st m) = case stmtBinds st of
      Nothing -> Do st (go avoid m)
      Just b
        | b `notElem` avoid -> Do st (go (b : avoid) m)
        | otherwise ->
            let b'  = fresh (avoid ++ boundIn m ++ freeTerm m) b
                st' = renameBinder b' st
            in Do st' (go (b' : avoid) (renameTerm b b' m))
    go avoid (If e m1 m2) = If e (go avoid m1) (go avoid m2)

    renameBinder b' (StNew _ d ps) = StNew b' d ps
    renameBinder b' (StLoan _ d)   = StLoan b' d
    renameBinder b' (StLift _ s x) = StLift b' s x
    renameBinder _  st             = st

-- >>> refreshBinders [] (Do (StNew "t" 2 [1,0]) (Return (VVar "t"))) :: Term Int
-- Do (StNew "t" 2 [1,0]) (Return (VVar "t"))
-- >>> refreshBinders ["t"] (Do (StNew "t" 2 [1,0]) (Return (VVar "t"))) :: Term Int
-- Do (StNew "t_1" 2 [1,0]) (Return (VVar "t_1"))
-- >>> refreshBinders ["x"] (Do (StGate [[0,1],[1,0]] (VVar "x")) (Return (VVar "x"))) :: Term Int
-- Do (StGate [[0,1],[1,0]] (VVar "x")) (Return (VVar "x"))

-- | Expand the surface's one extra production: a block is the sequencing
-- operator, and so is a non-tail @if@.
toTerm :: Surface a -> Term a
toTerm (SReturn v)      = Return v
toTerm (SDo st m)       = Do st (toTerm m)
toTerm (SIf e m1 m2)    = If e (toTerm m1) (toTerm m2)
toTerm (SBlock ybar m1 m2)
  | not (isTupleOfNames ybar) =
      -- impossible: every Value is a tuple of names, so isTupleOfNames holds
      error "Drop.Lang.Syntax.toTerm: a block's binder must be a tuple of names"
  | otherwise = seqFresh ybar (toTerm m1) (toTerm m2)

-- >>> toTerm (SReturn (VVar "x")) :: Term Int
-- Return (VVar "x")
-- >>> toTerm (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "x"))) :: Term Int
-- Do (StDrop 0 (VVar "t")) (Return (VVar "x"))

-- A block: y = { drop t; return x }; return y.
-- >>> toTerm (SBlock (VVar "y") (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "x"))) (SReturn (VVar "y"))) :: Term Int
-- Do (StDrop 0 (VVar "t")) (Return (VVar "x"))

-- A non-tail if: (if p { return a } else { return b }) (+)_y return y copies the continuation.
-- >>> toTerm (SBlock (VVar "y") (SIf (BParam "p") (SReturn (VVar "a")) (SReturn (VVar "b"))) (SReturn (VVar "y"))) :: Term Int
-- If (BParam "p") (Return (VVar "a")) (Return (VVar "b"))

-- | The number of statements along the longest branch, an @if@ counting as
-- one: the type-safety theorem's termination measure.
termSize :: Term a -> Int
termSize (Return _)   = 0
termSize (Do _ m)     = 1 + termSize m
termSize (If _ m1 m2) = 1 + max (termSize m1) (termSize m2)

-- >>> termSize (Return VUnit :: Term Int)
-- 0
-- >>> termSize (Do (StDrop 0 (VVar "t")) (Return VUnit) :: Term Int)
-- 1
-- >>> termSize (Do (StDrop 0 (VVar "t")) (If (BParam "p") (Return VUnit) (Do (StDrop 1 (VVar "u")) (Return VUnit))) :: Term Int)
-- 3

-- Alpha-equivalence -------------------------------------------------------
--
-- Terms are identified up to renaming of the names `new` binds (and of the
-- parameters a lift binds). 'seqFresh' renames M1's binders away from M2,
-- so the desugaring lemma is a statement up to this relation and not up to '(==)'.
-- Two names, one on each side, that were bound together get the same number;
-- a name bound on neither side is free and is compared by its spelling.

data ACtx = ACtx { acLeft :: [(Name, Int)], acRight :: [(Name, Int)], acNext :: Int }

acEmpty :: ACtx
acEmpty = ACtx [] [] 0

-- >>> acNext acEmpty
-- 0

acBind :: Name -> Name -> ACtx -> ACtx
acBind x y (ACtx ls rs n) = ACtx ((x, n) : ls) ((y, n) : rs) (n + 1)

-- >>> acNext (acBind "x" "y" acEmpty)
-- 1

acVar :: ACtx -> Bool -> Name -> Either Name Int
acVar ctx isLeft x = case lookup x (if isLeft then acLeft ctx else acRight ctx) of
  Just i  -> Right i
  Nothing -> Left x   -- free: compared by name

-- >>> acVar (acBind "x" "y" acEmpty) True "x"
-- Right 0
-- >>> acVar (acBind "x" "y" acEmpty) False "y"
-- Right 0
-- >>> acVar (acBind "x" "y" acEmpty) True "z"
-- Left "z"

alphaEqValue :: ACtx -> Value -> Value -> Bool
alphaEqValue ctx (VVar x) (VVar y) = acVar ctx True x == acVar ctx False y
alphaEqValue _ VUnit VUnit = True
alphaEqValue ctx (VPair a b) (VPair c d) = alphaEqValue ctx a c && alphaEqValue ctx b d
alphaEqValue _ _ _ = False

-- >>> alphaEqValue (acBind "x" "y" acEmpty) (VVar "x") (VVar "y")
-- True
-- >>> alphaEqValue acEmpty (VVar "x") (VVar "y")
-- False
-- >>> alphaEqValue acEmpty (VPair (VVar "x") VUnit) (VVar "x")
-- False

alphaEqB :: ACtx -> BExpr -> BExpr -> Bool
alphaEqB ctx (BParam p) (BParam q) = acVar ctx True p == acVar ctx False q
alphaEqB ctx (BNot a) (BNot b) = alphaEqB ctx a b
alphaEqB ctx (BAnd a b) (BAnd c d) = alphaEqB ctx a c && alphaEqB ctx b d
alphaEqB ctx (BOr a b) (BOr c d) = alphaEqB ctx a c && alphaEqB ctx b d
alphaEqB _ (BLit a) (BLit b) = a == b
alphaEqB _ _ _ = False

-- >>> alphaEqB (acBind "p" "q" acEmpty) (BNot (BParam "p")) (BNot (BParam "q"))
-- True
-- >>> alphaEqB acEmpty (BLit True) (BLit False)
-- False

alphaEqStmt :: Eq a => ACtx -> Stmt a -> Stmt a -> Bool
alphaEqStmt ctx (StGate g v) (StGate g' v') = g == g' && alphaEqValue ctx v v'
alphaEqStmt _   (StNew _ d ps) (StNew _ d' ps') = d == d' && ps == ps'
alphaEqStmt _   (StLoan _ d)   (StLoan _ d')    = d == d'
alphaEqStmt ctx (StDrop s v)   (StDrop s' v')   = s == s' && alphaEqValue ctx v v'
alphaEqStmt ctx (StLift _ s x) (StLift _ s' x') =
  s == s' && acVar ctx True x == acVar ctx False x'
alphaEqStmt _ _ _ = False

-- >>> alphaEqStmt acEmpty (StNew "t" 2 [1,0]) (StNew "u" 2 [1,0] :: Stmt Int)
-- True
-- >>> alphaEqStmt acEmpty (StNew "t" 2 [1,0]) (StNew "t" 3 [1,0,0] :: Stmt Int)
-- False
-- >>> alphaEqStmt acEmpty (StDrop 0 (VVar "x")) (StDrop 1 (VVar "x") :: Stmt Int)
-- False

-- | Alpha-equivalence of terms, as a decision procedure.
alphaEq :: Eq a => Term a -> Term a -> Bool
alphaEq = go acEmpty
  where
    go ctx (Return v) (Return v') = alphaEqValue ctx v v'
    go ctx (Do st m) (Do st' m') =
      alphaEqStmt ctx st st' &&
      case (stmtBinds st, stmtBinds st') of
        (Just b, Just b') -> go (acBind b b' ctx) m m'
        (Nothing, Nothing) -> go ctx m m'
        _ -> False
    go ctx (If e m1 m2) (If e' m1' m2') =
      alphaEqB ctx e e' && go ctx m1 m1' && go ctx m2 m2'
    go _ _ _ = False

-- >>> alphaEq (Return (VVar "x")) (Return (VVar "x") :: Term Int)
-- True
-- >>> alphaEq (Do (StNew "t" 2 [1,0]) (Return (VVar "t"))) (Do (StNew "u" 2 [1,0]) (Return (VVar "u")) :: Term Int)
-- True
-- >>> alphaEq (Do (StNew "t" 2 [1,0]) (Return (VVar "t"))) (Do (StNew "u" 2 [1,0]) (Return (VVar "t")) :: Term Int)
-- False

-- The desugaring lemma's case: the fresh expansion of a block is alpha-equal to the capture-avoiding one.
-- >>> alphaEq (seqFresh (VVar "y") (Do (StNew "t" 2 [1,0]) (Return (VVar "t"))) (Do (StNew "t" 2 [1,0]) (Return (VPair (VVar "y") (VVar "t"))))) (Do (StNew "a" 2 [1,0]) (Do (StNew "b" 2 [1,0]) (Return (VPair (VVar "a") (VVar "b")))) :: Term Int)
-- True
