-- Drop.Lang.Check: the two judgements of the language definition.
--
-- Question: Which programs are programs, and which mistakes do the types catch?
-- Answer:   Omega |- v : A for values and Pi; Omega |- M : A for terms, over one register context
--           whose comma is defined only on disjoint domains: no register is named twice and none
--           is discarded without a drop. checkStmt is the bookkeeping the four statement rules
--           share, not a third judgement. loanDiscipline adds the loan rule: a loan is dropped
--           exactly once on every path and never returned. Every TypeError names the construct
--           and the register, and showTypeError prints the sentence the user reads.
-- Paper:    def:calculus (the typing rules), sec:lang:statics (the statics).
-- Shapes:   Ctx          a finite map from register names to dimensions (Omega); the comma is mergeCtx.
--           Pi           the parameter names in scope, a list used as a set.
--           TypeError    one constructor per refusal.
--           check, checkProgram   a Program to its type, or to its first error.

module Drop.Lang.Check
  ( Ctx
  , ctxFromList
  , TypeError (..)
  , showTypeError
  , checkTerm
  , checkSurface
  , check
  , checkProgram
  , checkCapacity
  , loanDiscipline
  ) where

import Data.List (nub)
import qualified Data.Map.Strict as M
import Drop.Lang.State (isUnitary, norm2S, dimensionSize)
import Drop.Lang.Scalar (Conj)
import Drop.Lang.Syntax

-- The context ------------------------------------------------------------
--
-- Errors name the construct and the register, as "the types catch six
-- mistakes and let the seventh through" lists them. The examples below show
-- each refusal in the sentence the user reads.

-- | A linear register context: a finite map name -> dimension. The comma of
-- the statics is 'mergeCtx', defined only when the two contexts' domains are
-- disjoint; a name appearing in both is exactly the "register used twice"
-- error, caught before any rule fires on the merged context.
newtype Ctx = Ctx (M.Map Name Int) deriving (Eq, Show)

ctxFromList :: [(Name, Int)] -> Ctx
ctxFromList = Ctx . M.fromList

-- >>> ctxFromList [("y", 3), ("x", 2)]
-- Ctx (fromList [("x",2),("y",3)])

ctxToList :: Ctx -> [(Name, Int)]
ctxToList (Ctx m) = M.toList m

-- >>> ctxToList (ctxFromList [("y", 3), ("x", 2)])
-- [("x",2),("y",3)]
-- >>> ctxToList (ctxFromList [])
-- []

ctxSingle :: Name -> Int -> Ctx
ctxSingle x d = Ctx (M.singleton x d)

-- >>> ctxSingle "x" 2
-- Ctx (fromList [("x",2)])

ctxDom :: Ctx -> [Name]
ctxDom (Ctx m) = M.keys m

-- >>> ctxDom (ctxFromList [("y", 3), ("x", 2)])
-- ["x","y"]

ctxLookup :: Name -> Ctx -> Maybe Int
ctxLookup x (Ctx m) = M.lookup x m

-- >>> ctxLookup "x" (ctxFromList [("x", 2)])
-- Just 2
-- >>> ctxLookup "y" (ctxFromList [("x", 2)])
-- Nothing

-- The refusals ------------------------------------------------------------

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
  | GateNotUnitary [Name]               -- Gate's premise U in the gate set, a set of unitaries
  | BadDimension Name Int               -- a register of dimension below 2 (d >= 2)
  | StateLength Name Int Int            -- New's premise psi in K^d: register, d, length of psi
  | StateNotUnit Name Int               -- New's premise ||psi|| = 1
  | Other String
  deriving (Eq, Show)

-- | The sentence the user reads.
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
  GateNotUnitary xs      -> "gate on " ++ showNames xs ++ " is not unitary (U U^H is not I); the \
                            \Gate rule asks for U in the gate set, a set of unitaries"
  BadDimension x d       -> "register " ++ x ++ " has dimension " ++ show d
                            ++ "; a register has at least 2 levels"
  StateLength x d n      -> "new " ++ x ++ " : [" ++ show d ++ "] needs " ++ show d
                            ++ " amplitudes, got " ++ show n
  StateNotUnit x d       -> "new " ++ x ++ " : [" ++ show d ++ "] must name a unit state"
  Other s                -> s
  where
    showNames [x] = x
    showNames xs  = "(" ++ commas xs ++ ")"   -- the unit value () names no register
    commas []       = ""
    commas [x]      = x
    commas (x : xs) = x ++ ", " ++ commas xs

-- >>> showTypeError (UsedTwice "x")
-- "wire x used twice"
-- >>> showTypeError (UnknownWire "t")
-- "wire t used after drop, or never bound"
-- >>> showTypeError (GateDim "U" 4 2)
-- "gate U expects [4], got [2]"
-- >>> showTypeError (LeftoverWires ["a", "b"])
-- "wire(s) [\"a\",\"b\"] neither dropped nor returned"
-- >>> showTypeError (BranchMismatch (TReg 2) TUnit)
-- "if branches return different wires: TReg 2 vs TUnit"
-- >>> showTypeError (GateNotUnitary ["x", "y"])
-- "gate on (x, y) is not unitary (U U^H is not I); the Gate rule asks for U in the gate set, a set of unitaries"
-- >>> showTypeError (GateNotUnitary [])
-- "gate on () is not unitary (U U^H is not I); the Gate rule asks for U in the gate set, a set of unitaries"
-- >>> showTypeError (Other "anything else")
-- "anything else"

-- The comma ---------------------------------------------------------------

-- | The comma: disjoint union, or the first repeated name as an error.
mergeCtx :: Ctx -> Ctx -> Either TypeError Ctx
mergeCtx c1 c2 = case [ x | x <- ctxDom c1, x `elem` ctxDom c2 ] of
  (x : _) -> Left (UsedTwice x)
  []      -> let Ctx m1 = c1; Ctx m2 = c2 in Right (Ctx (M.union m1 m2))

-- Disjoint domains merge.
-- >>> mergeCtx (ctxFromList [("x", 2)]) (ctxFromList [("y", 3)])
-- Right (Ctx (fromList [("x",2),("y",3)]))
-- >>> mergeCtx (ctxFromList []) (ctxFromList [("y", 3)])
-- Right (Ctx (fromList [("y",3)]))

-- Overlapping domains are the error "register used twice", whatever the dimensions.
-- >>> mergeCtx (ctxFromList [("x", 2)]) (ctxFromList [("x", 2)])
-- Left (UsedTwice "x")
-- >>> mergeCtx (ctxFromList [("x", 2), ("y", 2)]) (ctxFromList [("y", 3), ("x", 3)])
-- Left (UsedTwice "x")
-- >>> either showTypeError (const "merged") (mergeCtx (ctxFromList [("x", 2)]) (ctxFromList [("x", 2)]))
-- "wire x used twice"

-- | The sub-context of exactly the named registers; fails if one is missing.
restrictCtx :: Ctx -> [Name] -> Either TypeError Ctx
restrictCtx ctx ns = do
  ds <- mapM (\x -> maybe (Left (UnknownWire x)) Right (ctxLookup x ctx)) ns
  Right (ctxFromList (zip ns ds))

-- >>> restrictCtx (ctxFromList [("x", 2), ("y", 3)]) ["y"]
-- Right (Ctx (fromList [("y",3)]))
-- >>> restrictCtx (ctxFromList [("x", 2)]) ["x", "z"]
-- Left (UnknownWire "z")

-- | The context with the named registers removed.
dropFromCtx :: Ctx -> [Name] -> Ctx
dropFromCtx ctx ns = ctxFromList [ (x, d) | (x, d) <- ctxToList ctx, x `notElem` ns ]

-- >>> dropFromCtx (ctxFromList [("x", 2), ("y", 3)]) ["x"]
-- Ctx (fromList [("y",3)])
-- >>> dropFromCtx (ctxFromList [("x", 2)]) ["z"]
-- Ctx (fromList [("x",2)])

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

-- The Var rule: the context is exactly the one register.
-- >>> checkValue (ctxFromList [("x", 2)]) (VVar "x")
-- Right (TReg 2)

-- A name not in the context is refused, and so is one with company.
-- >>> checkValue (ctxFromList []) (VVar "x")
-- Left (UnknownWire "x")
-- >>> either showTypeError show (checkValue (ctxFromList []) (VVar "x"))
-- "wire x used after drop, or never bound"
-- >>> either showTypeError show (checkValue (ctxFromList [("x", 2), ("y", 2)]) (VVar "x"))
-- "wire x used twice"

-- The Unit rule: the empty context.
-- >>> checkValue (ctxFromList []) VUnit
-- Right TUnit
-- >>> either showTypeError show (checkValue (ctxFromList [("x", 2)]) VUnit)
-- "wire(s) [\"x\"] neither dropped nor returned"

-- The Pair rule: two disjoint contexts, a tensor type.
-- >>> checkValue (ctxFromList [("x", 2), ("y", 3)]) (VPair (VVar "x") (VVar "y"))
-- Right (TTensor (TReg 2) (TReg 3))
-- >>> either showTypeError show (checkValue (ctxFromList [("x", 2)]) (VPair (VVar "x") (VVar "x")))
-- "wire x used twice"

-- | A square matrix of size n is read as acting on total dimension n.
gateDimOf :: [[a]] -> Int
gateDimOf = length

-- >>> gateDimOf [[0, 1], [1, 0 :: Int]]
-- 2

tyTotalDim :: Ty -> Int
tyTotalDim = dimensionSize . dims
  where
    dims TUnit = []
    dims (TReg d) = [d]
    dims (TTensor a b) = dims a ++ dims b

-- >>> tyTotalDim TUnit
-- 1
-- >>> tyTotalDim (TReg 3)
-- 3
-- >>> tyTotalDim (TTensor (TReg 2) (TTensor (TReg 3) TUnit))
-- 6

-- | The parameter context Pi: the names of the lifted bits in scope. A set,
-- not a linear context: parameters are classical and may go unread.
type Pi = [Name]

checkB :: Pi -> BExpr -> Either TypeError ()
checkB pi_ (BParam p) = if p `elem` pi_ then Right () else Left (ParamOutOfScope p)
checkB pi_ (BNot e)   = checkB pi_ e
checkB pi_ (BAnd a b) = checkB pi_ a >> checkB pi_ b
checkB pi_ (BOr a b)  = checkB pi_ a >> checkB pi_ b
checkB _   (BLit _)   = Right ()   -- a bit Step-Lift substituted: no parameter to look up

-- >>> checkB ["p"] (BNot (BParam "p"))
-- Right ()
-- >>> checkB [] (BLit True)
-- Right ()
-- >>> either showTypeError (const "ok") (checkB ["p"] (BAnd (BParam "p") (BParam "q")))
-- "parameter q out of scope"

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
--
-- The premises the rules print about the data a statement carries are
-- checked here too: Gate's U is in the gate set, a set of unitaries, so a
-- square matrix of the right side that is not unitary is refused; New's psi
-- is a unit vector of K^d; and a register has d >= 2 levels, in a New, a
-- loan and the header alike.
checkStmt :: (Eq a, Num a, Conj a) => Pi -> Ctx -> Stmt a -> Either TypeError (Pi, Ctx)
checkStmt pi_ ctx (StGate g v) = do
  opCtx <- restrictCtx ctx (valueNames v)
  a <- checkValue opCtx v
  let expect = gateDimOf g
      got    = tyTotalDim a
  if expect == got then Right () else Left (GateDim "U" expect got)
  if isUnitary g then Right (pi_, ctx) else Left (GateNotUnitary (valueNames v))
checkStmt pi_ ctx (StNew t d psi) = do
  checkDim t d
  if length psi /= d then Left (StateLength t d (length psi)) else Right ()
  if norm2S psi /= 1 then Left (StateNotUnit t d) else Right ()
  ctx' <- mergeCtx ctx (ctxSingle t d)
  Right (pi_, ctx')
-- A loan types exactly like `new`: it introduces a register and reads none,
-- the difference (no declared state) being invisible to the statics, which
-- never look inside the state a register carries. What a loan IS -- an input
-- the caller lends and gets back -- is 'loanDiscipline' below.
checkStmt pi_ ctx (StLoan a d) = do
  checkDim a d
  ctx' <- mergeCtx ctx (ctxSingle a d)
  Right (pi_, ctx')
checkStmt pi_ ctx (StDrop _ v) = do
  opCtx <- restrictCtx ctx (valueNames v)
  _ <- checkValue opCtx v
  Right (pi_, dropFromCtx ctx (valueNames v))
checkStmt pi_ ctx (StLift p s x) = do
  d <- maybe (Left (UnknownWire x)) Right (ctxLookup x ctx)
  if null s || length (nub s) /= length s
       || length (filter (\l -> l >= 0 && l < d) s) /= length s || length s >= d
    then Left (BadLiftBlock x) else Right ()
  if p `elem` pi_ then Left (ParamAlreadyBound p) else Right ()
  Right (pi_ ++ [p], ctx)

-- Gate: the registers keep their names, and the matrix must be unitary of the right side.
-- >>> checkStmt [] (ctxFromList [("x", 2)]) (StGate [[0, 1], [1, 0]] (VVar "x") :: Stmt Rational)
-- Right ([],Ctx (fromList [("x",2)]))
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList [("x", 3)]) (StGate [[0, 1], [1, 0]] (VVar "x") :: Stmt Rational))
-- "gate U expects [2], got [3]"
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList [("x", 2)]) (StGate [[1, 1], [0, 1]] (VVar "x") :: Stmt Rational))
-- "gate on x is not unitary (U U^H is not I); the Gate rule asks for U in the gate set, a set of unitaries"
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList []) (StGate [[0, 1], [1, 0]] (VVar "x") :: Stmt Rational))
-- "wire x used after drop, or never bound"

-- A gate on the unit value acts on total dimension 1; a 1 x 1 matrix that is not unitary is refused too.
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList []) (StGate [[2]] VUnit :: Stmt Rational))
-- "gate on () is not unitary (U U^H is not I); the Gate rule asks for U in the gate set, a set of unitaries"

-- New: one fresh name, a unit state of the right length, at least two levels.
-- >>> checkStmt [] (ctxFromList []) (StNew "t" 2 [1, 0] :: Stmt Rational)
-- Right ([],Ctx (fromList [("t",2)]))
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList [("t", 2)]) (StNew "t" 2 [1, 0] :: Stmt Rational))
-- "wire t used twice"
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList []) (StNew "t" 1 [1] :: Stmt Rational))
-- "register t has dimension 1; a register has at least 2 levels"
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList []) (StNew "t" 2 [1] :: Stmt Rational))
-- "new t : [2] needs 2 amplitudes, got 1"
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList []) (StNew "t" 2 [1, 1] :: Stmt Rational))
-- "new t : [2] must name a unit state"

-- Loan: typed like new, minus the state.
-- >>> checkStmt [] (ctxFromList []) (StLoan "a" 2 :: Stmt Rational)
-- Right ([],Ctx (fromList [("a",2)]))
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList []) (StLoan "a" 1 :: Stmt Rational))
-- "register a has dimension 1; a register has at least 2 levels"

-- Drop: the named registers leave the context.
-- >>> checkStmt [] (ctxFromList [("a", 2), ("x", 2)]) (StDrop 0 (VVar "a") :: Stmt Rational)
-- Right ([],Ctx (fromList [("x",2)]))
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList [("x", 2)]) (StDrop 0 (VVar "a") :: Stmt Rational))
-- "wire a used after drop, or never bound"

-- Lift: Pi gains the parameter, the register stays.
-- >>> checkStmt [] (ctxFromList [("x", 2)]) (StLift "p" [1] "x" :: Stmt Rational)
-- Right (["p"],Ctx (fromList [("x",2)]))
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList [("x", 2)]) (StLift "p" [] "x" :: Stmt Rational))
-- "lift: block for x is not a nonempty proper subset"
-- >>> either showTypeError (const "ok") (checkStmt [] (ctxFromList [("x", 2)]) (StLift "p" [0, 1] "x" :: Stmt Rational))
-- "lift: block for x is not a nonempty proper subset"
-- >>> either showTypeError (const "ok") (checkStmt ["p"] (ctxFromList [("x", 2)]) (StLift "p" [1] "x" :: Stmt Rational))
-- "parameter p is already bound"

-- | "The restriction d >= 2": a register of one level carries no quantum
-- data, and every register the language names has at least two.
checkDim :: Name -> Int -> Either TypeError ()
checkDim x d = if d >= 2 then Right () else Left (BadDimension x d)

-- >>> checkDim "x" 2
-- Right ()
-- >>> checkDim "x" 1
-- Left (BadDimension "x" 1)

-- The term judgement: Pi; Omega |- M : A ---------------------------------

checkTermP :: (Eq a, Num a, Conj a) => Pi -> Ctx -> Term a -> Either TypeError Ty
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

-- Return: the context is exactly what the value names.
-- >>> checkTermP [] (ctxFromList [("x", 2)]) (Return (VVar "x") :: Term Rational)
-- Right (TReg 2)
-- >>> either showTypeError show (checkTermP [] (ctxFromList [("x", 2), ("y", 2)]) (Return (VVar "x") :: Term Rational))
-- "wire(s) [\"y\"] neither dropped nor returned"

-- A statement, then the rest of the term in the context it hands over.
-- >>> checkTermP [] (ctxFromList [("x", 2), ("y", 2)]) (Do (StDrop 0 (VVar "y")) (Return (VVar "x")) :: Term Rational)
-- Right (TReg 2)
-- >>> either showTypeError show (checkTermP [] (ctxFromList [("x", 2)]) (Do (StDrop 0 (VVar "x")) (Return (VVar "x")) :: Term Rational))
-- "wire x used after drop, or never bound"

-- If: the guard reads parameters in Pi, and the two branches have one type.
-- >>> checkTermP ["p"] (ctxFromList [("x", 2)]) (If (BParam "p") (Return (VVar "x")) (Return (VVar "x")) :: Term Rational)
-- Right (TReg 2)
-- >>> either showTypeError show (checkTermP [] (ctxFromList [("x", 2)]) (If (BParam "p") (Return (VVar "x")) (Return (VVar "x")) :: Term Rational))
-- "parameter p out of scope"
-- >>> either showTypeError show (checkTermP [] (ctxFromList [("x", 2), ("y", 3)]) (If (BLit True) (Do (StDrop 0 (VVar "y")) (Return (VVar "x"))) (Do (StDrop 1 (VVar "x")) (Return (VVar "y"))) :: Term Rational))
-- "if branches return different wires: TReg 2 vs TReg 3"

-- | The measurement-free fragment carries Pi = [].
checkTerm :: (Eq a, Num a, Conj a) => Term a -> Ctx -> Either TypeError Ty
checkTerm = flip (checkTermP [])

-- >>> checkTerm (Return VUnit :: Term Rational) (ctxFromList [])
-- Right TUnit
-- >>> checkTerm (Do (StNew "t" 2 [1, 0]) (Do (StDrop 0 (VVar "t")) (Return VUnit)) :: Term Rational) (ctxFromList [])
-- Right TUnit

-- A lift binds a parameter inside the term, so the measurement-free entry point still types it.
-- >>> checkTerm (Do (StLift "p" [1] "x") (If (BParam "p") (Return (VVar "x")) (Return (VVar "x"))) :: Term Rational) (ctxFromList [("x", 2)])
-- Right (TReg 2)

-- | A surface term is typed after its blocks are expanded (the desugaring lemma).
checkSurface :: (Eq a, Num a, Conj a) => Surface a -> Ctx -> Either TypeError Ty
checkSurface m ctx = checkTerm (toTerm m) ctx

-- A block is expanded, and then typed.
-- >>> checkSurface (SBlock (VVar "y") (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "x"))) (SReturn (VVar "y")) :: Surface Rational) (ctxFromList [("t", 2), ("x", 2)])
-- Right (TReg 2)

-- | @check :: Program -> Either TypeError Ty@, i.e. the judgement
-- @x1:[d1], ..., xn:[dn] |- M : A@ the program header states.
check :: (Eq a, Num a, Conj a) => Program a -> Either TypeError Ty
check p@(Program vis m) = do
  mapM_ (uncurry checkDim) vis
  case [ x | (i, (x, _)) <- zip [0 :: Int ..] vis, x `elem` map fst (take i vis) ] of
    x : _ -> Left (UsedTwice x)
    [] -> Right ()
  checkCapacity p
  checkSurface m (ctxFromList vis)

-- | Bound the exposed state before any amplitude list is evaluated.
-- Earlier drops retain their factors; alternatives contribute the larger path.
checkCapacity :: Program a -> Either TypeError ()
checkCapacity (Program vis body)
  | total > toInteger (maxBound :: Int) =
      Left (Other ("implementation limit: exposed state dimension " ++ show total
                   ++ " exceeds the index range"))
  | otherwise = Right ()
  where
    total = product (map (toInteger . snd) vis) * allocated body
    allocated (SReturn _) = 1
    allocated (SDo st rest) = factor st * allocated rest
    allocated (SIf _ yes no) = max (allocated yes) (allocated no)
    allocated (SBlock _ first rest) = allocated first * allocated rest
    factor (StNew _ d _) = toInteger (max 1 d)
    factor (StLoan _ d) = toInteger (max 1 d)
    factor _ = 1

-- >>> checkCapacity (Program [] (SReturn VUnit) :: Program Rational)
-- Right ()
-- >>> let huge = Program [("x", maxBound), ("y", 2)] (SReturn VUnit) :: Program Rational
-- >>> case checkCapacity huge of { Left (Other _) -> True; _ -> False }
-- True

-- >>> check (Program [("x", 2)] (SReturn (VVar "x")) :: Program Rational)
-- Right (TReg 2)
-- >>> either showTypeError show (check (Program [("x", 1)] (SReturn (VVar "x")) :: Program Rational))
-- "register x has dimension 1; a register has at least 2 levels"
-- >>> either showTypeError show (check (Program [("x", 2)] (SReturn VUnit) :: Program Rational))
-- "wire(s) [\"x\"] neither dropped nor returned"

-- The loan rule -------------------------------------------------------------
--
-- Not a typing rule: the statics above never look at what a register
-- carries, and a loan types exactly like a `new`. What a loan is -- an input
-- the caller lends and gets back -- is a well-formedness condition on the
-- whole program, checked here after 'check' has established that the term is
-- well typed, so that the rules of the calculus stay as the paper prints
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
-- No statement renames a register: a gate keeps its registers'
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

-- >>> loanPaths [] (Return VUnit :: Term Rational)
-- [([],[],[])]

-- A loan, dropped once: bound a, dropped a, returned nothing.
-- >>> loanPaths [] (Do (StLoan "a" 2) (Do (StDrop 0 (VVar "a")) (Return VUnit)) :: Term Rational)
-- [(["a"],["a"],[])]

-- A loan returned: it shows up in the third list.
-- >>> loanPaths [] (Do (StLoan "a" 2) (Return (VVar "a")) :: Term Rational)
-- [(["a"],[],["a"])]

-- Each branch of an if is a path of its own.
-- >>> loanPaths [] (Do (StLoan "a" 2) (If (BLit True) (Do (StDrop 0 (VVar "a")) (Return VUnit)) (Return VUnit)) :: Term Rational)
-- [(["a"],["a"],[]),(["a"],[],[])]

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

-- >>> loanDiscipline (Program [] (SReturn VUnit) :: Program Rational)
-- Right ()
-- >>> loanDiscipline (Program [] (SDo (StLoan "a" 2) (SDo (StDrop 0 (VVar "a")) (SReturn VUnit))) :: Program Rational)
-- Right ()
-- >>> either showTypeError (const "ok") (loanDiscipline (Program [] (SDo (StLoan "a" 2) (SReturn (VVar "a"))) :: Program Rational))
-- "a loan is dropped, not returned (the language definition): the return value names the loan a"
-- >>> either showTypeError (const "ok") (loanDiscipline (Program [] (SDo (StLoan "a" 2) (SReturn VUnit)) :: Program Rational))
-- "the loan a must be dropped exactly once"
-- >>> either showTypeError (const "ok") (loanDiscipline (Program [] (SDo (StLoan "a" 2) (SDo (StDrop 0 (VVar "a")) (SDo (StDrop 1 (VVar "a")) (SReturn VUnit)))) :: Program Rational))
-- "the loan a must be dropped exactly once"

-- Per path: dropped in one branch of an if and not in the other is refused.
-- >>> either showTypeError (const "ok") (loanDiscipline (Program [] (SDo (StLoan "a" 2) (SIf (BLit True) (SDo (StDrop 0 (VVar "a")) (SReturn VUnit)) (SReturn VUnit))) :: Program Rational))
-- "the loan a must be dropped exactly once"

-- The whole program --------------------------------------------------------

-- | The statics, then the loan discipline: a program is accepted when it
-- types and every loan it takes is dropped exactly once and never returned.
checkProgram :: (Eq a, Num a, Conj a) => Program a -> Either TypeError Ty
checkProgram p = do
  ty <- check p
  loanDiscipline p
  Right ty

-- The paper's programs: the abstract's temporary AND, uncomputed by measurement, and the same
-- program with its drop right after the Toffoli. The types accept both: whether the drop is
-- safe is the criterion's question, not the statics'.
-- >>> :m + Drop.Lang.Elab Drop.Lang.Programs.TempAnd
-- >>> checkProgram (flatToProgram visXY andUncomputedByMeasurement)
-- Right (TTensor (TReg 2) (TReg 2))
-- >>> checkProgram (flatToProgram visXY andComputed)
-- Right (TTensor (TReg 2) (TReg 2))
-- >>> checkProgram (flatToProgram visXY andNoCorrection)
-- Right (TTensor (TReg 2) (TReg 2))
