-- Drop.Lang.Compile.Layout: where every wire and every bit goes.
--
-- Question: Where does each register, each lift and each drop of a program sit in the circuit?
-- Answer:   compileFragment first refuses what the compiler does not cover: a program that fails
--           the statics or the loan discipline, a new, loan, lift or drop inside an if branch, a
--           name bound twice, two drops with one site id, and two arms of an if whose allocations,
--           lifts and drops differ. layoutProgram then walks the program in order. Every input (a
--           loan too) and every allocation gets ilog2 d consecutive qubits, most significant bit
--           first, and a dimension that is not a power of two (at least 2) is refused by name.
--           Every lift gets the next classical bit; a lift of a one-qubit register on {0} or {1}
--           is measured directly, any other lift gets one ancilla qubit (the block form). Every
--           drop is given its depth, the number of lifts before it: a structural count, the same
--           in both arms of an if, because the arms never allocate or lift.
-- Paper:    sec:lang:compile (the compiler's domain), app:emitter-contract (the supported fragment).
-- Shapes:   CompileError  the six ways compile refuses a program, each with its reason.
--           LayoutInfo    per name its qubits (most significant first), dimension and allocation
--                         vector; per lift its classical bit, the measured value that means
--                         "survived" and its ancilla qubit if any; per drop site its depth;
--                         the totals of qubits and bits; the qubits a pooled drop clears.
--           LayoutSt      the same while the walk is unfinished, with the next free qubit and bit.

module Drop.Lang.Compile.Layout
  ( CompileError (..)
  , showCompileError
  , LayoutInfo (..)
  , ilog2
  , layoutProgram
  , statements
  , wireQubits
  , bitsOfIndex
  , basisIndexOfExact
  ) where

import Data.Bits (testBit, (.&.))
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Drop.Lang.Check (checkProgram, showTypeError)
import Drop.Lang.Scalar (Cyclo)
import Drop.Lang.State
import Drop.Lang.Syntax


-- Refusals --------------------------------------------------------------------

-- | The six ways compile refuses a program, each with its reason: a register
-- whose dimension is not a power of two, a gate the emitter has no circuit for,
-- a drop the fragment excludes, a type error, a construct outside the fragment,
-- and anything else with its own message.
data CompileError
  = NonPowerOfTwo Name Int
  | GateNotInDomain [Name] String
  | DropOutsideFragment [Name] String
  | NotWellTyped String
  | OutsideFragment String
  | Other String
  deriving (Eq, Show)

-- The smallest refusal: a register of dimension 3 has no whole number of qubits.
-- >>> NonPowerOfTwo "x" 3
-- NonPowerOfTwo "x" 3
-- >>> OutsideFragment "lift inside an if branch"
-- OutsideFragment "lift inside an if branch"
-- >>> [GateNotInDomain ["x", "y"] "not diagonal", DropOutsideFragment ["t"] "it drops a loan after a lift"]
-- [GateNotInDomain ["x","y"] "not diagonal",DropOutsideFragment ["t"] "it drops a loan after a lift"]

-- | The text a refusal prints, as @dqt compile@ shows it after @REFUSED: @.
showCompileError :: CompileError -> String
showCompileError e = case e of
  NonPowerOfTwo x d -> "register " ++ x ++ " has dimension " ++ show d ++ ", not a power of two"
  GateNotInDomain xs msg -> "gate on " ++ unwords xs ++ " is not in the compile domain (" ++ msg ++ ")"
  DropOutsideFragment xs msg -> "drop " ++ tupleText xs ++ " is outside the compilation fragment: " ++ msg
  NotWellTyped msg -> "type error: " ++ msg
  OutsideFragment msg -> "outside the compilation fragment: " ++ msg
  Other s -> s
  where
    tupleText [x] = x
    tupleText xs = "(" ++ intercalate ", " xs ++ ")"

-- >>> showCompileError (NonPowerOfTwo "x" 3)
-- "register x has dimension 3, not a power of two"
-- >>> showCompileError (GateNotInDomain ["x", "y"] "not diagonal")
-- "gate on x y is not in the compile domain (not diagonal)"
-- >>> showCompileError (NotWellTyped "wire t used twice")
-- "type error: wire t used twice"
-- >>> showCompileError (OutsideFragment "new inside an if branch")
-- "outside the compilation fragment: new inside an if branch"
-- >>> showCompileError (Other "the branches return values of different sizes")
-- "the branches return values of different sizes"

-- A tuple drop names its registers in parentheses; a single register stands alone.
-- >>> showCompileError (DropOutsideFragment ["t"] "it drops a loan after a lift")
-- "drop t is outside the compilation fragment: it drops a loan after a lift"
-- >>> showCompileError (DropOutsideFragment ["a", "b"] "it drops a loan after a lift")
-- "drop (a, b) is outside the compilation fragment: it drops a loan after a lift"

-- | What every entry point of the compiler asks of a program before it lays
-- it out. First the statics and the loan discipline ('checkProgram'): a term
-- that was built directly, not parsed, may name a dropped wire or return a
-- loan, and the layout below would give it qubits all the same. Then three
-- rules of the parser that the statics do not impose, because the paper's
-- If rule lets a branch allocate, lift and drop: the compiler lays out one
-- branch for both, keys its layout by name and its safety table by site id,
-- so it needs no binder in a branch, every name bound once, and a site id
-- per surface drop.
compileFragment :: Program Cyclo -> Either CompileError ()
compileFragment prog = do
  either (Left . NotWellTyped . showTypeError) (const (Right ())) (checkProgram prog)
  case [ st | st <- inBranch False (progTerm prog), binder st ] of
    (st : _) -> Left (OutsideFragment (stmtWord st ++ " inside an if branch"))
    []       -> Right ()
  let names = map fst (progCtx prog) ++ [ x | st <- inBranch True (progTerm prog), Just x <- [stmtBinds st] ]
  case [ x | (i, x) <- zip [0 :: Int ..] names, x `elem` take i names ] of
    (x : _) -> Left (OutsideFragment ("the name " ++ x ++ " is bound twice"))
    []      -> Right ()
  let sites = [ i | StDrop i _ <- inBranch True (progTerm prog) ]
  case [ i | (k, i) <- zip [0 :: Int ..] sites, i `elem` take k sites ] of
    (i : _) -> Left (OutsideFragment ("two drops carry the site id " ++ show i))
    []      -> Right ()
  _ <- resourcePlan (toTerm (progTerm prog))
  Right ()
  where
    -- One static layout must serve every expanded branch.
    resourcePlan (Return _) = Right []
    resourcePlan (Do st m) = do
      rest <- resourcePlan m
      Right (case st of StGate {} -> rest; _ -> st : rest)
    resourcePlan (If _ a b) = do
      left <- resourcePlan a
      right <- resourcePlan b
      if left == right then Right left
        else Left (OutsideFragment ("resource layout differs between if arms: " ++
                                          resourceDifference left right))
    resourceDifference (x:xs) (y:ys)
      | x == y = resourceDifference xs ys
      | otherwise = show x ++ " versus " ++ show y
    resourceDifference [] (y:_) = "end of arm versus " ++ show y
    resourceDifference (x:_) [] = show x ++ " versus end of arm"
    resourceDifference [] [] = "equal resource lists"
    -- the statements of a surface term: with True all of them, with False
    -- only those under an if
    inBranch top t = case t of
      SReturn _      -> []
      SDo st m       -> [ st | top ] ++ inBranch top m
      SIf _ m1 m2    -> inBranch True m1 ++ inBranch True m2
      SBlock _ m1 m2 -> inBranch top m1 ++ inBranch top m2
    binder st = case st of
      StGate {} -> False
      _         -> True
    stmtWord st = case st of
      StNew {}  -> "new"
      StLoan {} -> "loan"
      StLift {} -> "lift"
      StDrop {} -> "drop"
      StGate {} -> "gate"

-- A program that parses and types is in the fragment.
-- >>> :m + Drop.Lang.Parser
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (compileFragment prog)) (parseTyped src)
-- Right ()
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (compileFragment prog)) (parseTyped src)
-- Right ()

-- A term built directly, not parsed, may break the statics: t is allocated and never dropped.
-- >>> compileFragment (Program [("x", 2)] (SDo (StNew "t" 2 [1, 0]) (SReturn (VVar "x"))))
-- Left (NotWellTyped "wire(s) [\"t\"] neither dropped nor returned")

-- The if rule of the paper lets a branch allocate; the compiler does not: a new inside an arm is refused.
-- >>> compileFragment (Program [("x", 2)] (SDo (StLift "p" [1] "x") (SIf (BParam "p") (SDo (StNew "t" 2 [1, 0]) (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "x")))) (SReturn (VVar "x")))))
-- Left (OutsideFragment "new inside an if branch")
-- >>> either showCompileError (const "in the fragment") (compileFragment (Program [("x", 2)] (SDo (StLift "p" [1] "x") (SIf (BParam "p") (SDo (StNew "t" 2 [1, 0]) (SDo (StDrop 0 (VVar "t")) (SReturn (VVar "x")))) (SReturn (VVar "x"))))))
-- "outside the compilation fragment: new inside an if branch"

-- A drop in an arm is refused too, whatever it drops.
-- >>> either showCompileError (const "in the fragment") (compileFragment (Program [("x", 2)] (SDo (StLift "p" [1] "x") (SIf (BParam "p") (SDo (StDrop 0 (VVar "x")) (SReturn VUnit)) (SDo (StDrop 1 (VVar "x")) (SReturn VUnit))))))
-- "outside the compilation fragment: drop inside an if branch"

-- The layout ------------------------------------------------------------------

-- | Where everything went: per name its qubits, most significant first, its
-- dimension and (for a @new@) its allocation vector; per lift its classical bit
-- and the measured value that means "survived", with the ancilla qubit of the
-- block form; per drop site its depth; the totals; and the qubits a pooled
-- drop clears (empty here, filled in by Drop.Lang.Compile.Reuse).
data LayoutInfo = LayoutInfo
  { liWireQ       :: Map Name [Int]         -- MSB-first physical qubit indices
  , liWireDim     :: Map Name Int
  , liWireAlloc   :: Map Name (StateV Cyclo)  -- exact allocation vectors
  , liLiftInfo    :: Map Name (Int, Int)    -- param -> (classical bit index, qasm value meaning "survived")
  , liLiftAncilla :: Map Name Int           -- param -> ancilla qubit index (block-lift form only)
  , liSiteDepth   :: Map SiteId Int
  , liTotalQubits :: Int
  , liTotalBits   :: Int
  , liPoolClears  :: Map SiteId [Int] -- X gates taking restored basis blocks to zero
  } deriving Show

-- The temporary AND of the paper (programs/temp-and.s), as (qubits, classical bits).
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> (liTotalQubits l, liTotalBits l)) (layoutProgram prog))) (parseTyped src)
-- Right (3,1)

-- | The walk's state: 'LayoutInfo' while it is unfinished, plus the next free
-- qubit and the next free classical bit.
data LayoutSt = LayoutSt
  { lsNextQubit   :: Int
  , lsNextBit     :: Int
  , lsWireQ       :: Map Name [Int]
  , lsWireDim     :: Map Name Int
  , lsWireAlloc   :: Map Name (StateV Cyclo)
  , lsLiftInfo    :: Map Name (Int, Int)
  , lsLiftAncilla :: Map Name Int
  , lsSiteDepth   :: Map SiteId Int
  }

-- | The walk's state before anything is laid out: no qubit, no bit, no name.
startSt :: LayoutSt
startSt = LayoutSt 0 0 Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

-- >>> lsNextQubit startSt
-- 0
-- >>> Map.null (lsWireQ startSt)
-- True

-- | A dimension that is a whole number of qubits: a power of two, at least 2.
isPow2 :: Int -> Bool
isPow2 n = n >= 2 && (n .&. (n - 1)) == 0

-- >>> map isPow2 [1, 2, 4, 3]
-- [False,True,True,False]
-- >>> isPow2 0
-- False
-- >>> isPow2 1024
-- True

-- | The number of qubits of a register of dimension @n@; meant for 'isPow2'
-- dimensions, where it is exact.
ilog2 :: Int -> Int
ilog2 n = go n 0 where go 1 acc = acc; go m acc = go (m `div` 2) (acc + 1)

-- >>> map ilog2 [2, 4, 8]
-- [1,2,3]
-- >>> ilog2 1
-- 0

-- | The layout of a program in the fragment, or the refusal that stops it:
-- the fragment first, then each input, then the statements in order.
layoutProgram :: Program Cyclo -> Either CompileError LayoutInfo
layoutProgram prog = do
  compileFragment prog
  st1 <- foldEither wireLaidOut startSt (progCtx prog)
  stF <- termLaidOut 0 st1 (toTerm (progTerm prog))
  Right (layoutInfoOf stF)
  where
    foldEither f = go where go st [] = Right st; go st (x : xs) = f st x >>= \st' -> go st' xs

-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (fmap liWireQ (layoutProgram prog))) (parseTyped src)
-- Right (fromList [("a",[2]),("x",[0]),("y",[1])])

-- The drop of a is at depth 1, after the one lift; the lift m reads qubit a directly: bit 0, survived when it reads 1.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> (liSiteDepth l, liLiftInfo l)) (layoutProgram prog))) (parseTyped src)
-- Right (fromList [(0,1)],fromList [("m",(0,1))])

-- A loan is laid out like an input: mcx-dirty-x.s has five registers, so five qubits, and its drop is at depth 0.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> (liTotalQubits l, liSiteDepth l)) (layoutProgram prog))) (parseTyped src)
-- Right (5,fromList [(0,0)])

-- A lift on a register of 16 levels is the block form: shor.s gives it an ancilla qubit (7), the indicator, and the bit means survived when it reads 1.
-- >>> readFile "programs/shor.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> (liLiftInfo l, liLiftAncilla l)) (layoutProgram prog))) (parseTyped src)
-- Right (fromList [("s",(0,1))],fromList [("s",7)])

-- rus.s has a register of dimension three: refused by dimension, not approximated.
-- >>> readFile "programs/rus.s" >>= \src -> either putStrLn (\prog -> putStrLn (either showCompileError (const "laid out") (layoutProgram prog))) (parseTyped src)
-- register x has dimension 3, not a power of two

-- | The finished 'LayoutInfo' of a finished walk; nothing is pooled yet.
layoutInfoOf :: LayoutSt -> LayoutInfo
layoutInfoOf stF = LayoutInfo
  { liWireQ = lsWireQ stF, liWireDim = lsWireDim stF, liWireAlloc = lsWireAlloc stF
  , liLiftInfo = lsLiftInfo stF, liLiftAncilla = lsLiftAncilla stF, liSiteDepth = lsSiteDepth stF
  , liTotalQubits = lsNextQubit stF, liTotalBits = lsNextBit stF
  , liPoolClears = Map.empty
  }

-- >>> liTotalQubits (layoutInfoOf (startSt { lsNextQubit = 3, lsNextBit = 1 }))
-- 3
-- >>> liPoolClears (layoutInfoOf (startSt { lsNextQubit = 3, lsNextBit = 1 }))
-- fromList []

-- | The state after one register (an input, a loan or an allocation) is given
-- its qubits, or the refusal of a dimension that is not a power of two.
wireLaidOut :: LayoutSt -> (Name, Int) -> Either CompileError LayoutSt
wireLaidOut st (n, d)
  | not (isPow2 d) = Left (NonPowerOfTwo n d)
  | otherwise =
      let k = ilog2 d
          qs = [lsNextQubit st .. lsNextQubit st + k - 1]
      in Right st { lsNextQubit = lsNextQubit st + k
                  , lsWireQ = Map.insert n qs (lsWireQ st)
                  , lsWireDim = Map.insert n d (lsWireDim st) }

-- >>> fmap lsWireQ (wireLaidOut startSt ("x", 4))
-- Right (fromList [("x",[0,1])])
-- >>> fmap lsNextQubit (wireLaidOut (startSt { lsNextQubit = 3 }) ("y", 2))
-- Right 4
-- >>> either showCompileError (const "laid out") (wireLaidOut startSt ("z", 3))
-- "register z has dimension 3, not a power of two"

-- | The state after the statements of a term are laid out, one clause per
-- term former. @depth@ is the number of lifts passed so far.
termLaidOut :: Int -> LayoutSt -> Term Cyclo -> Either CompileError LayoutSt
termLaidOut depth st term = case term of
  Return _ -> Right st
  Do (StGate _ _) m -> termLaidOut depth st m
  Do (StNew nm d psi) m -> do
    st' <- wireLaidOut st (nm, d)
    termLaidOut depth st' { lsWireAlloc = Map.insert nm psi (lsWireAlloc st') } m
  -- A loan has no allocation vector to record: it is a genuine input
  -- register (Drop.Lang.Criterion's "Loans" section), laid out like one.
  Do (StLoan nm d) m -> do
    st' <- wireLaidOut st (nm, d)
    termLaidOut depth st' m
  Do (StDrop site _) m ->
    termLaidOut depth (st { lsSiteDepth = Map.insert site depth (lsSiteDepth st) }) m
  -- A lift binds no register: x stays live under its own name, so there
  -- is no second wire to give the first one's qubits to.
  Do (StLift pname s x) m -> do
    d <- maybe (Left (Other ("Drop.Lang.Compile: unknown wire " ++ x))) Right (Map.lookup x (lsWireDim st))
    let direct = d == 2 && (s == [0] || s == [1])
        sv = if s == [1] then 1 else 0
        bitIdx = lsNextBit st
        st1 = st { lsNextBit = bitIdx + 1 }
    let (anc, st2) = if direct
                       then (Nothing, st1)
                       else (Just (lsNextQubit st1), st1 { lsNextQubit = lsNextQubit st1 + 1 })
        st3 = st2 { lsLiftInfo = Map.insert pname (bitIdx, if direct then sv else 1) (lsLiftInfo st2) }
        st4 = case anc of
                Just a  -> st3 { lsLiftAncilla = Map.insert pname a (lsLiftAncilla st3) }
                Nothing -> st3
    termLaidOut (depth + 1) st4 m
  If _ m1 _ -> termLaidOut depth st m1  -- resources are branch-invariant ('compileFragment': no alloc/lift/drop in a branch)

-- A new on four levels takes two qubits; the drop after it is at depth 0.
-- >>> fmap (\s -> (lsWireQ s, lsSiteDepth s)) (termLaidOut 0 startSt (Do (StNew "t" 4 [1, 0, 0, 0]) (Do (StDrop 0 (VVar "t")) (Return VUnit))))
-- Right (fromList [("t",[0,1])],fromList [(0,0)])

-- Helpers the later decisions share --------------------------------------------

-- | The statements of a term in order. Resource-bearing statements are outside
-- branches in the compiler fragment, so an @if@ is read through its first arm.
statements :: Term a -> [Stmt a]
statements (Return _) = []
statements (Do st m) = st : statements m
statements (If _ a _) = statements a

-- >>> statements (Return VUnit :: Term Int)
-- []
-- >>> statements (Do (StNew "t" 2 [1, 0]) (Do (StDrop 0 (VVar "t")) (Return VUnit)) :: Term Int)
-- [StNew "t" 2 [1,0],StDrop 0 (VVar "t")]
-- >>> statements (If (BParam "p") (Do (StDrop 0 (VVar "t")) (Return VUnit)) (Return VUnit) :: Term Int)
-- [StDrop 0 (VVar "t")]

-- | The qubits of a name, most significant first; none for a name never laid out.
wireQubits :: LayoutInfo -> Name -> [Int]
wireQubits layout n = Map.findWithDefault [] n (liWireQ layout)

-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (fmap (\l -> map (wireQubits l) ["x", "y", "a", "nothing"]) (layoutProgram prog))) (parseTyped src)
-- Right [[0],[1],[2],[]]

-- | The @k@ bits of the index @x@, most significant first.
bitsOfIndex :: Int -> Int -> [Int]
bitsOfIndex k x = [ if testBit x (k - 1 - i) then 1 else 0 | i <- [0 .. k - 1] ]

-- >>> bitsOfIndex 3 5
-- [1,0,1]
-- >>> map (bitsOfIndex 2) [0, 1, 2, 3]
-- [[0,0],[0,1],[1,0],[1,1]]
-- >>> bitsOfIndex 0 0
-- []

-- | The index of the one entry that equals 1, when the vector is exactly a
-- computational basis state; 'Nothing' for any other vector.
basisIndexOfExact :: StateV Cyclo -> Maybe Int
basisIndexOfExact psi = case [ i | (i, c) <- zip [0 ..] psi, c /= 0 ] of
  -- impossible: i comes from zip over psi, so it is a valid index
  [i] | psi !! i == 1 -> Just i
  _                   -> Nothing

-- >>> basisIndexOfExact [0, 0, 1, 0]
-- Just 2
-- >>> basisIndexOfExact [1, 1]
-- Nothing
-- >>> basisIndexOfExact [0, 2]
-- Nothing
-- >>> basisIndexOfExact []
-- Nothing
