-- Elab.hs: Lemma E, both directions.
--
-- 'flatToProgramR' reads an existing flat engine program (Drop.Lang.Syntax.Cmd,
-- as parsed from a .s corpus file) as a typed 'Program'. The reading is now
-- one line per construct, because the two syntaxes are the same syntax:
-- "U v;" is 'StGate', "new t : [d] @ psi;" is 'StNew', "drop v;" is
-- 'StDrop', "p = lift[S] x;" is 'StLift'. The one construct that is not
-- already flat is the NON-TAIL `if`: an 'IfBit' with statements after it is
-- the surface form @(if e {M1} else {M2}) (+)_ybar M@, built here as an
-- 'SBlock' and expanded by 'Drop.Lang.Typed.toTerm' -- so every corpus program
-- with an `if` exercises the sequencing operator, and none of them has to
-- have its continuation copied by hand.
--
-- 'elab' goes the other way: a term back to the flat command list, so the
-- existing two engines (Drop.Lang.Interp's semantic criterion and
-- Drop.Lang.Report.Trace) run the typed term unchanged. It is now total on every
-- term a program file can name: the shapes it used to refuse -- a gate that
-- renames its registers, a lift that renames the measured one -- do not
-- exist in this language, since neither binds.

module Drop.Lang.Elab
  ( flatToProgram
  , flatToProgramR
  , elabE
  , elab
  , denote
  , denoteLeaves
  ) where

import Data.List ((\\))
import Drop.Lang.QState
import Drop.Lang.Syntax
import Drop.Lang.Typed
import qualified Drop.Lang.Interp as I

-- Flat -> typed

tupleVal :: [Name] -> Value
tupleVal []       = VUnit
tupleVal [x]      = VVar x
tupleVal (x : xs) = VPair (VVar x) (tupleVal xs)

-- | A guard to the term syntax's boolean expression.
guardToB :: Guard -> BExpr
guardToB (GBit b)   = BLit b
guardToB (GParam p) = BParam p
guardToB (GNot e)   = BNot (guardToB e)
guardToB (GAnd a b) = BAnd (guardToB a) (guardToB b)
guardToB (GOr a b)  = BOr (guardToB a) (guardToB b)

-- | And back. Total: every boolean expression of the typed syntax, including
-- the 'BLit' that Step-Lift puts in place of the parameter it consumed, is a
-- guard of the surface syntax.
bToGuard :: BExpr -> Guard
bToGuard (BLit b)   = GBit b
bToGuard (BParam p) = GParam p
bToGuard (BNot e)   = GNot (bToGuard e)
bToGuard (BAnd a b) = GAnd (bToGuard a) (bToGuard b)
bToGuard (BOr a b)  = GOr (bToGuard a) (bToGuard b)

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
        wrap (_ : _) = error "flatToSurface: an if-branch binds a wire (excluded by the parser)"

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

-- Typed -> flat (Lemma E, the elaboration direction)

-- | A unit vector's basis index, if it is exactly one: the clean-allocation
-- case ('New'); any other unit vector elaborates to 'NewState'.
basisIndex :: (Eq a, Num a) => StateV a -> Maybe Int
basisIndex psi = case [ i | (i, c) <- zip [0 ..] psi, c /= 0 ] of
  [i] | (psi !! i) == 1 -> Just i
  _                     -> Nothing

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

elab :: (Eq a, Num a) => Term a -> Prog a
elab = either error id . elabE

-- Denotation via the existing interpreter

-- | The final machine state for one selection (one leaf of the flat engine),
-- from a basis or arbitrary input on the visible registers.
denote :: (Eq a, Num a) => VisSpec -> Prog a -> [Sel] -> StateV a -> I.Mach a
denote vis prog sel inp = I.runStmts (I.initMach vis inp) prog sel Nothing

-- | Every leaf (one per selection word), paired with its selection.
denoteLeaves :: (Eq a, Num a) => VisSpec -> Prog a -> StateV a -> [([Sel], I.Mach a)]
denoteLeaves vis prog inp =
  [ (sel, denote vis prog sel inp) | sel <- I.allSelections (numLifts prog) ]
  where
    numLifts [] = 0
    numLifts (Lift {} : cs) = 1 + numLifts cs
    numLifts (IfBit _ t e : cs) = numLifts t + numLifts e + numLifts cs
    numLifts (_ : cs) = numLifts cs
