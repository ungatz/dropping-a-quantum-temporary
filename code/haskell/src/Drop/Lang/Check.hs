-- Check.hs: the statics of the language definition, exactly.
--
-- TWO judgements share one context: @Omega |- v : A@ for values
-- ('checkValue') and @Pi; Omega |- M : A@ for terms ('checkTerm'). There is
-- no pattern judgement and no operation judgement: a statement is not a term
-- of the language, and nothing types one alone. 'checkStmt' below is not a
-- third judgement -- it is the shared premise-and-conclusion bookkeeping of
-- the four statement rules (Gate, New, Drop, Lift), each of which is a rule
-- about the TERM it prefixes.
--
-- A register context Omega is a finite set of typed register names with
-- pairwise distinct names, and the comma is defined only when the two have
-- disjoint domains ('mergeCtx'). That one convention is the whole
-- discipline: no register is named twice, and none is discarded without a
-- `drop`. The parameter context Pi is a set of names, not a linear context.
--
-- Errors name the construct and the register, as "the types catch six
-- mistakes and let the seventh through" lists them.

module Drop.Lang.Check
  ( Ctx
  , emptyCtx
  , ctxFromList
  , ctxToList
  , TypeError (..)
  , showTypeError
  , Pi
  , checkValue
  , checkStmt
  , checkTerm
  , checkTermP
  , checkSurface
  , check
  , checkProgram
  , loanDiscipline
  , loanPaths
  ) where

import qualified Data.Map.Strict as M
import Drop.Lang.Typed

-- | A linear register context: a finite map name -> dimension. The comma of
-- the statics is 'mergeCtx', defined only when the two contexts' domains are
-- disjoint; a name appearing in both is exactly the "register used twice"
-- error, caught before any rule fires on the merged context.
newtype Ctx = Ctx (M.Map Name Int) deriving (Eq, Show)

emptyCtx :: Ctx
emptyCtx = Ctx M.empty

ctxFromList :: [(Name, Int)] -> Ctx
ctxFromList = Ctx . M.fromList

ctxToList :: Ctx -> [(Name, Int)]
ctxToList (Ctx m) = M.toList m

ctxSingle :: Name -> Int -> Ctx
ctxSingle x d = Ctx (M.singleton x d)

ctxDom :: Ctx -> [Name]
ctxDom (Ctx m) = M.keys m

ctxLookup :: Name -> Ctx -> Maybe Int
ctxLookup x (Ctx m) = M.lookup x m

data TypeError
  = UsedTwice Name                     -- comma on overlapping domains
  | UnknownWire Name                   -- Var rule miss, or a dropped/unbound register
  | GateDim String Int Int             -- gate name, expected dim, actual dim
  | LeftoverWires [Name]               -- a temporary neither dropped nor returned
  | BranchMismatch Ty Ty               -- if branches return different registers/types
  | ParamOutOfScope Name                -- a guard over a parameter not in Pi
  | ParamAlreadyBound Name              -- a lift binds a parameter Pi already has
  | BadLiftBlock Name                   -- lift block not nonempty-proper
  | LoanReturned Name                   -- a loan named by the program's return value
  | LoanNotDroppedOnce Name             -- a loan not dropped exactly once on some path
  | Other String
  deriving (Eq, Show)

showTypeError :: TypeError -> String
showTypeError e = case e of
  UsedTwice x           -> "wire " ++ x ++ " used twice"
  UnknownWire x          -> "wire " ++ x ++ " used after drop, or never bound"
  GateDim nm expect got  -> "gate " ++ nm ++ " expects [" ++ show expect ++ "], got [" ++ show got ++ "]"
  LeftoverWires xs       -> "wire(s) " ++ show xs ++ " neither dropped nor returned"
  BranchMismatch a b     -> "if branches return different wires: " ++ show a ++ " vs " ++ show b
  ParamOutOfScope p      -> "parameter " ++ p ++ " out of scope"
  ParamAlreadyBound p    -> "parameter " ++ p ++ " is already bound"
  BadLiftBlock x         -> "lift: block for " ++ x ++ " is not a nonempty proper subset"
  LoanReturned x         -> "a loan is dropped, not returned (the language definition): the \
                            \return value names the loan " ++ x
  LoanNotDroppedOnce x   -> "the loan " ++ x ++ " must be dropped exactly once"
  Other s                -> s

-- | The comma: disjoint union, or the first repeated name as an error.
mergeCtx :: Ctx -> Ctx -> Either TypeError Ctx
mergeCtx c1 c2 = case [ x | x <- ctxDom c1, x `elem` ctxDom c2 ] of
  (x : _) -> Left (UsedTwice x)
  []      -> let Ctx m1 = c1; Ctx m2 = c2 in Right (Ctx (M.union m1 m2))

-- | The sub-context of exactly the named registers; fails if one is missing.
restrictCtx :: Ctx -> [Name] -> Either TypeError Ctx
restrictCtx ctx ns = do
  ds <- mapM (\x -> maybe (Left (UnknownWire x)) Right (ctxLookup x ctx)) ns
  Right (ctxFromList (zip ns ds))

-- | The context with the named registers removed.
dropFromCtx :: Ctx -> [Name] -> Ctx
dropFromCtx ctx ns = ctxFromList [ (x, d) | (x, d) <- ctxToList ctx, x `notElem` ns ]

-- The value judgement: Omega |- v : A ------------------------------------
--
-- Var / Unit / Pair. 'checkValue' requires ctx's domain to be exactly v's
-- free names (the singleton/product contexts the rules read off); a caller
-- restricts the ambient context to those names first.
checkValue :: Ctx -> Value -> Either TypeError Ty
checkValue ctx (VVar x) = case ctxToList ctx of
  [(y, d)] | y == x -> Right (TReg d)
  _                 -> case ctxLookup x ctx of
    Nothing -> Left (UnknownWire x)
    Just _  -> Left (UsedTwice x)   -- x present, but with other names alongside it
checkValue ctx VUnit
  | null (ctxDom ctx) = Right TUnit
  | otherwise          = Left (LeftoverWires (ctxDom ctx))
checkValue ctx (VPair v1 v2) = do
  let ns1 = valueNames v1
      ns2 = valueNames v2
  c1 <- restrictCtx ctx ns1
  c2 <- restrictCtx ctx ns2
  _  <- mergeCtx c1 c2                -- disjointness, i.e. no shared register
  a  <- checkValue c1 v1
  b  <- checkValue c2 v2
  Right (TTensor a b)

-- | A square matrix of size n is read as acting on total dimension n.
gateDimOf :: [[a]] -> Int
gateDimOf = length

tyTotalDim :: Ty -> Int
tyTotalDim TUnit         = 1
tyTotalDim (TReg d)      = d
tyTotalDim (TTensor a b) = tyTotalDim a * tyTotalDim b

-- | The parameter context Pi: the names of the lifted bits in scope. A set,
-- not a linear context: parameters are classical and may go unread.
type Pi = [Name]

checkB :: Pi -> BExpr -> Either TypeError ()
checkB pi_ (BParam p) = if p `elem` pi_ then Right () else Left (ParamOutOfScope p)
checkB pi_ (BNot e)   = checkB pi_ e
checkB pi_ (BAnd a b) = checkB pi_ a >> checkB pi_ b
checkB pi_ (BOr a b)  = checkB pi_ a >> checkB pi_ b
checkB _   (BLit _)   = Right ()   -- a bit Step-Lift substituted: no parameter to look up

-- | The premises of the four statement rules, and the context each one
-- hands to the term it prefixes.
--
--   Gate  reads Omega_1 |- v : A with U on [[A]], and leaves Omega_1,Omega_2
--         unchanged: the registers are in the context before the statement
--         and after it, under the same names, which is why the rule has no
--         binder.
--   New   extends the context by one fresh name.
--   Drop  consumes the context that named its value, and carries no premise
--         about safety.
--   Lift  extends Pi by its parameter and leaves Omega alone: the register
--         stays live under its own name.
checkStmt :: Pi -> Ctx -> Stmt a -> Either TypeError (Pi, Ctx)
checkStmt pi_ ctx (StGate g v) = do
  opCtx <- restrictCtx ctx (valueNames v)
  a <- checkValue opCtx v
  let expect = gateDimOf g
      got    = tyTotalDim a
  if expect == got then Right (pi_, ctx) else Left (GateDim "U" expect got)
checkStmt pi_ ctx (StNew t d _psi) = do
  ctx' <- mergeCtx ctx (ctxSingle t d)
  Right (pi_, ctx')
-- A loan types exactly like `new`: it introduces a register and reads none,
-- the difference (no declared state) being invisible to the statics, which
-- never look inside the state a register carries. What a loan IS -- an input
-- the caller lends and gets back -- is 'loanDiscipline' below.
checkStmt pi_ ctx (StLoan a d) = do
  ctx' <- mergeCtx ctx (ctxSingle a d)
  Right (pi_, ctx')
checkStmt pi_ ctx (StDrop _ v) = do
  opCtx <- restrictCtx ctx (valueNames v)
  _ <- checkValue opCtx v
  Right (pi_, dropFromCtx ctx (valueNames v))
checkStmt pi_ ctx (StLift p s x) = do
  d <- maybe (Left (UnknownWire x)) Right (ctxLookup x ctx)
  if null s || length (filter (\l -> l >= 0 && l < d) s) /= length s || length s >= d
    then Left (BadLiftBlock x) else Right ()
  if p `elem` pi_ then Left (ParamAlreadyBound p) else Right ()
  Right (pi_ ++ [p], ctx)

-- The term judgement: Pi; Omega |- M : A ---------------------------------

checkTermP :: Pi -> Ctx -> Term a -> Either TypeError Ty
checkTermP _ ctx (Return v) =
  let extra = [ x | x <- ctxDom ctx, x `notElem` valueNames v ]
  in if not (null extra) then Left (LeftoverWires extra) else checkValue ctx v
checkTermP pi_ ctx (Do st m) = do
  (pi', ctx') <- checkStmt pi_ ctx st
  checkTermP pi' ctx' m
checkTermP pi_ ctx (If e m1 m2) = do
  checkB pi_ e
  a1 <- checkTermP pi_ ctx m1
  a2 <- checkTermP pi_ ctx m2
  if a1 == a2 then Right a1 else Left (BranchMismatch a1 a2)

-- | The measurement-free fragment carries Pi = [].
checkTerm :: Term a -> Ctx -> Either TypeError Ty
checkTerm = flip (checkTermP [])

-- | A surface term is typed after its blocks are expanded (the desugaring lemma).
checkSurface :: Surface a -> Ctx -> Either TypeError Ty
checkSurface m ctx = checkTerm (toTerm m) ctx

-- | @check :: Program -> Either TypeError Ty@, i.e. the judgement
-- @x1:[d1], ..., xn:[dn] |- M : A@ the program header states.
check :: Program a -> Either TypeError Ty
check (Program vis m) = checkSurface m (ctxFromList vis)

-- The loan discipline
--
-- Not a typing rule: the statics above never look at what a register
-- carries, and a loan types exactly like a `new`. What a loan is -- an input
-- the caller lends and gets back -- is a well-formedness condition on the
-- whole program, checked here after 'check' has established that the term is
-- well typed, so that the rules of the language stay as the paper prints
-- them.
--
-- Two obligations, both from the language definition: a loan is DROPPED, not returned
-- (returning it would hand the caller a register the program never gave back
-- at a site, so no B certifies it), and every loan input is dropped EXACTLY
-- ONCE. "Exactly once" is read per execution path, so a loan dropped in one
-- branch of an `if` and not the other is an error: 'loanPaths' splits at
-- 'If' and each branch must discharge every loan on its own. (Dropping a
-- loan twice is already a linearity error, 'UnknownWire'; it is still
-- reported here, under its own name, for a program built directly rather
-- than parsed.)

-- | Every execution path of a term, as (the loans it binds; the loans it
-- drops, with multiplicity; the loans its return value names).
--
-- No statement renames a register any more -- a gate keeps its registers'
-- names and a lift keeps the measured register's -- so the walk is by name
-- throughout, and the only binder it has to follow is the loan's own.
loanPaths :: [Name] -> Term a -> [([Name], [Name], [Name])]
loanPaths ls term = case term of
  Return v -> [(ls, [], [ x | x <- valueNames v, x `elem` ls ])]
  Do (StDrop _ v) m ->
    [ (bs, [ x | x <- valueNames v, x `elem` ls ] ++ ds, rs)
    | (bs, ds, rs) <- loanPaths ls m ]
  Do (StLoan a _) m -> loanPaths (ls ++ [a]) m
  Do _ m            -> loanPaths ls m
  If _ m1 m2        -> loanPaths ls m1 ++ loanPaths ls m2

-- | The loan discipline of the language definition, on a program the statics have
-- already accepted.
loanDiscipline :: Program a -> Either TypeError ()
loanDiscipline (Program _ m) = mapM_ onePath (loanPaths [] (toTerm m))
  where
    onePath (bound, dropped, returned) = case returned of
      (x : _) -> Left (LoanReturned x)
      []      -> case [ x | x <- bound, length (filter (== x) dropped) /= 1 ] of
        (x : _) -> Left (LoanNotDroppedOnce x)
        []      -> Right ()

-- | The statics, then the loan discipline: a program is accepted when it
-- types and every loan it takes is dropped exactly once and never returned.
checkProgram :: Program a -> Either TypeError Ty
checkProgram p = do
  ty <- check p
  loanDiscipline p
  Right ty
