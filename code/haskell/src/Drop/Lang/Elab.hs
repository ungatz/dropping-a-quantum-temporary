-- Drop.Lang.Elab: the typed term and the command list are the same programs.
--
-- Question: How does a command list become a term, and a term a command list?
-- Answer:   flatToProgram reads a command list as a Program, one line per construct, because the
--           two syntaxes share their constructs; the one command that is not already a term, an if,
--           becomes a block the sequencing operator expands. elab goes back, a term to its command
--           list, and is total on every term a program file can name. The check is the round trip:
--           elab after flatToProgram gives the list back, except that the commands after an if come
--           back copied into both of its arms, and the machine on the term agrees with the
--           interpreter on the list, leaf for leaf.
-- Paper:    sec:lang:denotation (what a program denotes), lem:desugar (the block the sequencing
--           operator expands).
-- Shapes:   flatToProgram, flatToProgramR   a command list (and the value its return names) to a Program.
--           elab, elabE                     a Term back to its command list; elabE is the total form.
--           denote                          the interpreter's final Mach for one selection.

module Drop.Lang.Elab
  ( flatToProgram
  , flatToProgramR
  , elabE
  , elab
  , denote
  ) where

import Data.List ((\\))
import Drop.Lang.State
import Drop.Lang.Flat
import Drop.Lang.Syntax
import qualified Drop.Lang.Interp as I

-- Reading a command list as a term -----------------------------------------
--
-- 'flatToProgramR' reads an existing flat engine program (Drop.Lang.Flat.Cmd,
-- as parsed from a .s corpus file) as a typed 'Program'. The reading is
-- one line per construct, because the two syntaxes are the same syntax:
-- "U v;" is 'StGate', "new t : [d] @ psi;" is 'StNew', "drop v;" is
-- 'StDrop', "p = lift[S] x;" is 'StLift'. The one construct that is not
-- already flat is the `if`: an 'IfBit' is the surface form
-- @(if e {M1} else {M2}) (+)_ybar M@, built here as an 'SBlock' and
-- expanded by 'Drop.Lang.Syntax.toTerm' -- so every corpus program with an
-- `if` exercises the sequencing operator, and none of them has to have its
-- continuation copied by hand.

tupleVal :: [Name] -> Value
tupleVal []       = VUnit
tupleVal [x]      = VVar x
tupleVal (x : xs) = VPair (VVar x) (tupleVal xs)

-- >>> tupleVal []
-- VUnit
-- >>> tupleVal ["x"]
-- VVar "x"
-- >>> tupleVal ["x", "y", "z"]
-- VPair (VVar "x") (VPair (VVar "y") (VVar "z"))

-- | A guard to the term syntax's boolean expression.
guardToB :: Guard -> BExpr
guardToB (GBit b)   = BLit b
guardToB (GParam p) = BParam p
guardToB (GNot e)   = BNot (guardToB e)
guardToB (GAnd a b) = BAnd (guardToB a) (guardToB b)
guardToB (GOr a b)  = BOr (guardToB a) (guardToB b)

-- >>> guardToB (GParam "p")
-- BParam "p"
-- >>> guardToB (GAnd (GParam "p") (GNot (GBit False)))
-- BAnd (BParam "p") (BNot (BLit False))

-- | And back. Total: every boolean expression of the typed syntax, including
-- the 'BLit' that Step-Lift puts in place of the parameter it consumed, is a
-- guard of the surface syntax.
bToGuard :: BExpr -> Guard
bToGuard (BLit b)   = GBit b
bToGuard (BParam p) = GParam p
bToGuard (BNot e)   = GNot (bToGuard e)
bToGuard (BAnd a b) = GAnd (bToGuard a) (bToGuard b)
bToGuard (BOr a b)  = GOr (bToGuard a) (bToGuard b)

-- >>> bToGuard (BLit True)
-- GBit True

-- Back is the inverse, on a guard with every connective.
-- >>> let g = GOr (GAnd (GParam "p") (GNot (GParam "q"))) (GBit True) in bToGuard (guardToB g) == g
-- True

-- | Read a flat program as a surface term, assigning increasing 'SiteId's to
-- the `drop` occurrences in program order. A loan is an input register, so
-- it is bound by 'StLoan' at the head, where the parser put it.
--
-- @live@ is the registers in scope at each point, which the non-tail `if`
-- needs: the block's binder @ybar@ is the tuple of names the branches return.
flatToSurface :: forall a. Num a => [Name] -> Value -> Prog a -> Surface a
flatToSurface live0 ret prog = fst (go live0 0 prog)
  where
    go :: [Name] -> Int -> Prog a -> (Surface a, Int)
    go _ sid [] = (SReturn ret, sid)
    go live sid (c : cs) = case c of
      New x d          -> push (StNew x d (ket [d] [0])) (live ++ [x])
      NewState x d psi -> push (StNew x d psi) (live ++ [x])
      Loan x d         -> push (StLoan x d) (live ++ [x])
      Gate g xs        -> push (StGate g (tupleVal xs)) live
      Lift p x block   -> push (StLift p block x) live
      Drop xs ->
        let (rest, sid') = go (live \\ xs) (sid + 1) cs
        in (SDo (StDrop sid (tupleVal xs)) rest, sid')
      IfBit g thn els ->
        let (cont, sid') = go live sid cs
            ybar = tupleVal live
        in ( SBlock ybar
               (SIf (guardToB g) (branch thn ybar) (branch els ybar))
               cont
           , sid' )
      where
        push st live' = let (rest, sid') = go live' sid cs in (SDo st rest, sid')

    -- The branches of a surface `if` bind nothing (Drop.Lang.Parser.branchBinder
    -- rejects a binder there), so a branch is a list of gates and nested
    -- `if`s only, and it returns exactly the registers it was handed.
    branch :: Prog a -> Value -> Surface a
    branch cs ybar = wrap cs
      where
        wrap [] = SReturn ybar
        wrap (Gate g xs : rest) = SDo (StGate g (tupleVal xs)) (wrap rest)
        wrap (IfBit g thn els : rest) =
          SBlock ybar (SIf (guardToB g) (branch thn ybar) (branch els ybar))
                 (wrap rest)
        -- refusal: an if-branch that binds a wire (the parser excludes it; a built Prog can reach it)
        wrap (_ : _) = error "flatToSurface: an if-branch binds a wire (excluded by the parser)"

-- A gate, then a drop: the first drop is site 0.
-- >>> flatToSurface ["x", "a"] (VVar "x") ([Gate [[0,1],[1,0]] ["x"], Drop ["a"]] :: Prog Rational)
-- SDo (StGate [[0 % 1,1 % 1],[1 % 1,0 % 1]] (VVar "x")) (SDo (StDrop 0 (VVar "a")) (SReturn (VVar "x")))

-- Sites are numbered in program order.
-- >>> flatToSurface ["a", "b"] VUnit ([Drop ["a"], Drop ["b"]] :: Prog Rational)
-- SDo (StDrop 0 (VVar "a")) (SDo (StDrop 1 (VVar "b")) (SReturn VUnit))

-- A tuple drop is one site.
-- >>> flatToSurface ["a", "b"] VUnit ([Drop ["a", "b"]] :: Prog Rational)
-- SDo (StDrop 0 (VPair (VVar "a") (VVar "b"))) (SReturn VUnit)

-- An if becomes a block binding the live registers (x, y); the commands after it are its continuation.
-- >>> flatToSurface ["x", "y"] (VVar "y") ([IfBit (GParam "m") [Gate [[0,1],[1,0]] ["y"]] [], Drop ["x"]] :: Prog Rational)
-- SBlock (VPair (VVar "x") (VVar "y")) (SIf (BParam "m") (SDo (StGate [[0 % 1,1 % 1],[1 % 1,0 % 1]] (VVar "y")) (SReturn (VPair (VVar "x") (VVar "y")))) (SReturn (VPair (VVar "x") (VVar "y")))) (SDo (StDrop 0 (VVar "x")) (SReturn (VVar "y")))

-- | As 'flatToProgram', with the value the file's `return` names.
--
-- A header @loan a : [d]@ is an input register of the program (the paper's
-- Omega holds it), and the parser hoists it to a 'Loan' at the head of the
-- body; here it becomes an 'StLoan' at the head of the term rather than an
-- entry of 'progCtx'. The two readings agree construct for construct -- a
-- statement that reads no register and binds a fresh one, at the very head
-- of a term, is a context extension -- and this one keeps the loan
-- distinguishable from an ordinary input, which is what the site verdict
-- (the block-factor test) and the compiler (prepare nothing) have to read.
flatToProgramR :: Num a => VisSpec -> Value -> Prog a -> Program a
flatToProgramR vis ret prog = Program vis (flatToSurface (map fst vis) ret prog)

-- >>> progCtx (flatToProgramR [("x", 2)] (VVar "x") ([] :: Prog Rational))
-- [("x",2)]
-- >>> progTerm (flatToProgramR [("x", 2), ("y", 2)] (VVar "y") ([Drop ["x"]] :: Prog Rational))
-- SDo (StDrop 0 (VVar "x")) (SReturn (VVar "y"))

-- | A command list as a Program, returning the registers still live at its end.
flatToProgram :: Num a => VisSpec -> Prog a -> Program a
flatToProgram vis prog = flatToProgramR vis (tupleVal (map fst live)) prog
  where
    live = foldl stepLive vis prog
    stepLive acc c = case c of
      New x d        -> acc ++ [(x, d)]
      NewState x d _ -> acc ++ [(x, d)]
      Loan x d       -> acc ++ [(x, d)]
      Drop xs        -> filter ((`notElem` xs) . fst) acc
      _              -> acc

-- Nothing to do: the program returns its visible register.
-- >>> progTerm (flatToProgram [("x", 2)] ([] :: Prog Rational))
-- SReturn (VVar "x")

-- A temporary allocated and dropped is not returned.
-- >>> progTerm (flatToProgram [("x", 2)] ([New "a" 2, Drop ["a"]] :: Prog Rational))
-- SDo (StNew "a" 2 [1 % 1,0 % 1]) (SDo (StDrop 0 (VVar "a")) (SReturn (VVar "x")))

-- An if with a statement after it is an SBlock: the if, then the rest.
-- >>> progTerm (flatToProgram [("x", 2), ("y", 2)] [Lift "m" "x" [1], IfBit (GParam "m") [Gate [[0,1],[1,0]] ["y"]] [], Drop ["x"]] :: Program Rational)
-- SDo (StLift "m" [1] "x") (SBlock (VPair (VVar "x") (VVar "y")) (SIf (BParam "m") (SDo (StGate [[0 % 1,1 % 1],[1 % 1,0 % 1]] (VVar "y")) (SReturn (VPair (VVar "x") (VVar "y")))) (SReturn (VPair (VVar "x") (VVar "y")))) (SDo (StDrop 0 (VVar "x")) (SReturn (VVar "y"))))

-- The abstract's temporary AND: expanded to a term, its longest branch has seven statements.
-- >>> :m + Drop.Lang.Programs.TempAnd
-- >>> termSize (toTerm (progTerm (flatToProgram visXY andUncomputedByMeasurement)))
-- 7

-- A term back to its command list ------------------------------------------
--
-- 'elab' goes the other way: a term back to the flat command list, so the
-- existing two engines (Drop.Lang.Interp's interpreter and its criterion
-- in Drop.Lang.Criterion, and Drop.Lang.Report.Trace) run the typed term
-- unchanged. It is total on every term a program file can name: no gate
-- renames its registers and no lift renames the measured one, since neither
-- binds.

-- | A unit vector's basis index, if it is exactly one: the clean-allocation
-- case ('New'); any other unit vector elaborates to 'NewState'.
basisIndex :: (Eq a, Num a) => StateV a -> Maybe Int
basisIndex psi = case [ i | (i, c) <- zip [0 ..] psi, c /= 0 ] of
  -- impossible: i came from zip [0 ..] psi, so it indexes psi
  [i] | (psi !! i) == 1 -> Just i
  _                     -> Nothing

-- >>> basisIndex [1, 0 :: Rational]
-- Just 0
-- >>> basisIndex [0, 1 :: Rational]
-- Just 1

-- A superposition, a zero vector and a scaled basis vector are not basis vectors.
-- >>> basisIndex [1, 1 :: Rational]
-- Nothing
-- >>> basisIndex [0, 0 :: Rational]
-- Nothing
-- >>> basisIndex [2, 0 :: Rational]
-- Nothing

-- | A term to its command list. A statement is one command, an `if` is an
-- 'IfBit' with the two arms elaborated; the answer is always 'Right'.
elabE :: (Eq a, Num a) => Term a -> Either String (Prog a)
elabE (Return _) = Right []
elabE (Do st m) = case st of
  StGate g v     -> (Gate g (valueNames v) :) <$> elabE m
  StNew x d psi  -> (cmd :) <$> elabE m
    where cmd = case basisIndex psi of
            Just 0 -> New x d
            _      -> NewState x d psi
  StLoan x d     -> (Loan x d :) <$> elabE m
  StDrop _ v     -> (Drop (valueNames v) :) <$> elabE m
  StLift p s x   -> (Lift p x s :) <$> elabE m
elabE (If e m1 m2) = do
  c1 <- elabE m1
  c2 <- elabE m2
  Right [IfBit (bToGuard e) c1 c2]

-- >>> elabE (Return VUnit :: Term Rational)
-- Right []

-- |0> is the clean allocation New; any other unit vector is NewState.
-- >>> elabE (Do (StNew "a" 2 [1, 0]) (Return VUnit) :: Term Rational)
-- Right [New "a" 2]
-- >>> elabE (Do (StNew "a" 2 [0, 1]) (Return VUnit) :: Term Rational)
-- Right [NewState "a" 2 [0 % 1,1 % 1]]
-- >>> elabE (Do (StDrop 0 (VPair (VVar "a") (VVar "b"))) (Return VUnit) :: Term Rational)
-- Right [Drop ["a","b"]]
-- >>> elabE (Do (StLift "p" [1] "x") (If (BParam "p") (Return VUnit) (Return VUnit)) :: Term Rational)
-- Right [Lift "p" "x" [1],IfBit (GParam "p") [] []]

-- | 'elabE' without the 'Either'.
elab :: (Eq a, Num a) => Term a -> Prog a
-- impossible: elabE has no Left case, every term elaborates
elab = either error id . elabE

-- The programs of the abstract come back as written, except the one with an if followed by a drop.
-- >>> elab (toTerm (progTerm (flatToProgram visXY andComputed))) == andComputed
-- True
-- >>> elab (toTerm (progTerm (flatToProgram visXY andNoCorrection))) == andNoCorrection
-- True
-- >>> elab (toTerm (progTerm (flatToProgram visXY andUncomputedByMeasurement))) == andUncomputedByMeasurement
-- False

-- There the sequencing operator copied the drop into both arms of the if.
-- >>> length andUncomputedByMeasurement
-- 6
-- >>> length (elab (toTerm (progTerm (flatToProgram visXY andUncomputedByMeasurement))))
-- 5
-- >>> [ (g, length t, length e) | IfBit g t e <- elab (toTerm (progTerm (flatToProgram visXY andUncomputedByMeasurement))) ]
-- [(GParam "m",2,1)]

-- A NewState of |0> comes back as New.
-- >>> elab (toTerm (progTerm (flatToProgram [("x", 2)] [NewState "a" 2 [1, 0], Drop ["a"]] :: Program Rational)))
-- [New "a" 2,Drop ["a"]]

-- The interpreter's meaning of a command list --------------------------------

-- | The final machine state for one selection (one leaf of the flat engine),
-- from a basis or arbitrary input on the visible registers.
denote :: (Eq a, Num a) => VisSpec -> Prog a -> [Sel] -> StateV a -> I.Mach a
denote vis prog sel inp = I.runStmts (I.initMach vis inp) prog sel Nothing

-- The interpreter on one gate: X on |0>.
-- >>> I.mAmp (denote [("x", 2)] [Gate [[0,1],[1,0]] ["x"]] [] (ket [2] [0]) :: I.Mach Rational)
-- [0 % 1,1 % 1]

-- A lift consumes one bit of the selection.
-- >>> I.mAmp (denote [("x", 2)] [Lift "p" "x" [1]] [SIn] [1, 1] :: I.Mach Rational)
-- [0 % 1,1 % 1]
-- >>> I.mAmp (denote [("x", 2)] [Lift "p" "x" [1]] [SOut] [1, 1] :: I.Mach Rational)
-- [1 % 1,0 % 1]
-- >>> I.mDropped (denote visXY andUncomputedByMeasurement [SIn] (ket [2, 2] [1, 1]))
-- ["a"]

-- The lemma: the machine on the term and the interpreter on the list agree, leaf for leaf, on every basis input.
-- >>> :m + Drop.Lang.Machine
-- >>> and [ map cfgAmp (run (initConfig visXY inp (toTerm (progTerm (flatToProgram visXY andUncomputedByMeasurement))))) == [ I.mAmp (denote visXY andUncomputedByMeasurement sel inp) | sel <- I.allSelections 1 ] | (_, inp) <- basisXY ]
-- True
