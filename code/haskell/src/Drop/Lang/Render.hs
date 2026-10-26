-- Drop.Lang.Render: what a program file holds, and how a program is written back as text.
--
-- Question: What is a .s file, and how does a program print?
-- Answer:   A file is its gate declarations, a header (the program's name, its parameters and its
--           result type), a body that is a command list, and the value the body returns: SFile,
--           one field each. A parameter marked loan is a register the program is handed in a state
--           it does not know and must hand back. The printer follows the command list one clause
--           per command: a gate prints by its name when the gate table or the file's own
--           declarations name its matrix, and otherwise as a diag, a perm or a whole mat; a basis
--           state prints as a ket; a loan prints in the header, never in the body. Every scalar
--           of the tower up to Q(zeta_16) prints exactly, a scalar beyond it is refused by name,
--           and there is no float syntax. The parser reads back what renderFile
--           prints, to the same SFile (Drop.Lang.Parser shows it).
-- Paper:    sec:lang:syntax (the syntax of programs), fig:syntax (the grammar the printer follows).
-- Shapes:   SFile    one program file: its name, parameters, result type, own gate declarations,
--                    body (a command list over exact scalars) and returned value.
--           Param    one header parameter: its name, its dimension, and whether it is a loan.
--           GateEnv  the named gates a file may use: (name, matrix) pairs, the table first.

module Drop.Lang.Render
  ( SFile (..)
  , Param (..)
  , sfVis
  , GateEnv
  , gateTable
  , showTy
  , renderValue
  , renderCmd
  , renderFile
  , renderProgram
  ) where

import Data.List (intercalate, nub)
import Drop.Lang.Scalar
import Drop.Lang.Gates
import Drop.Lang.State (Matrix, StateV)
import Drop.Lang.Flat
import Drop.Lang.Syntax (Ty (..), Value (..))

-- A file ---------------------------------------------------------------------

-- | One input of the program: its name, its dimension, and whether it is a
-- loan (handed in a state the program does not know, to be handed back).
data Param = Param { prmName :: String, prmDim :: Int, prmLoan :: Bool }
  deriving (Eq, Show)

-- A parameter is a name, a dimension and a loan flag.
-- >>> Param "x" 2 False
-- Param {prmName = "x", prmDim = 2, prmLoan = False}
-- >>> Param "a" 2 True
-- Param {prmName = "a", prmDim = 2, prmLoan = True}
-- >>> prmLoan (Param "a" 2 True)
-- True

-- | A parsed file: the declarations, the program header, its body and the
-- value it returns.
data SFile = SFile
  { sfName   :: String
  , sfParams :: [Param]
  , sfResult :: Ty
  , sfDecls  :: [(String, Matrix Cyclo)]
  , sfBody   :: Prog Cyclo
  , sfReturn :: Value
  } deriving (Eq, Show)

-- The paper's temporary AND, read from its file: the header and the value it returns.
-- >>> :m + Drop.Lang.Parser
-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap (\f -> (sfName f, sfParams f)) (parseFile src))
-- Right ("temp_and",[Param {prmName = "x", prmDim = 2, prmLoan = False},Param {prmName = "y", prmDim = 2, prmLoan = False}])
-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap (\f -> (sfResult f, sfReturn f)) (parseFile src))
-- Right (TTensor (TReg 2) (TReg 2),VPair (VVar "x") (VVar "y"))
-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap (\f -> (length (sfDecls f), length (sfBody f))) (parseFile src))
-- Right (0,6)

-- | The ordinary (non-loan) input registers, the machine's 'VisSpec'.
sfVis :: SFile -> VisSpec
sfVis f = [ (prmName p, prmDim p) | p <- sfParams f, not (prmLoan p) ]

-- A loan is not a visible input: the loan program keeps only its four ordinary registers.
-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap sfVis (parseFile src))
-- Right [("x",2),("y",2)]
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap sfVis (parseFile src))
-- Right [("q1",2),("q2",2),("q3",2),("q",2)]
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (map prmName . filter prmLoan . sfParams) (parseFile src))
-- Right ["a"]

-- | The named gates a file may use: pairs of a name and its matrix.
type GateEnv = [(String, Matrix Cyclo)]

-- >>> map fst (gateTable :: GateEnv)
-- ["H","HC","X","Z","CX","CCX","Swap","T","S","tilt","READ3","Diff"]

-- | The named gates a .s file may write. H and HC name the same Hadamard
-- matrix over the tower; tilt and READ3 are the qutrit gates the
-- repeat-until-success program needs.
gateTable :: [(String, Matrix Cyclo)]
gateTable =
  [ ("H", gHC), ("HC", gHC)
  , ("X", gX), ("Z", gZ)
  , ("CX", gCX), ("CCX", gCCX), ("Swap", gSwap)
  , ("T", gT), ("S", gS)
  , ("tilt", gTilt), ("READ3", gREAD3), ("Diff", gDiff)
  ]

-- The smallest entry is a Pauli gate; H and HC are one matrix under two names.
-- >>> lookup "X" gateTable == Just gX
-- True
-- >>> lookup "H" gateTable == lookup "HC" gateTable
-- True
-- >>> fmap length (lookup "CCX" gateTable)
-- Just 8
-- >>> lookup "nope" gateTable == Nothing
-- True

-- Types and values -----------------------------------------------------------

-- | A right-nested tuple type over the given dimensions; @1@ when empty.
tyOfDims :: [Int] -> Ty
tyOfDims []       = TUnit
tyOfDims [d]      = TReg d
tyOfDims (d : ds) = TTensor (TReg d) (tyOfDims ds)

-- >>> tyOfDims []
-- TUnit
-- >>> tyOfDims [2]
-- TReg 2
-- >>> tyOfDims [2, 3, 2]
-- TTensor (TReg 2) (TTensor (TReg 3) (TReg 2))

-- | A right-nested tuple value over the given names; @()@ when empty.
valueOfNames :: [String] -> Value
valueOfNames []       = VUnit
valueOfNames [x]      = VVar x
valueOfNames (x : xs) = VPair (VVar x) (valueOfNames xs)

-- >>> valueOfNames []
-- VUnit
-- >>> valueOfNames ["x"]
-- VVar "x"
-- >>> valueOfNames ["x", "y", "z"]
-- VPair (VVar "x") (VPair (VVar "y") (VVar "z"))

-- | A type in the file's spelling: @1@, @[d]@, @A * B@.
showTy :: Ty -> String
showTy TUnit          = "1"
showTy (TReg d)       = "[" ++ show d ++ "]"
showTy (TTensor a b)  = showTyL a ++ " * " ++ showTy b
  where showTyL t@(TTensor _ _) = "(" ++ showTy t ++ ")"
        showTyL t               = showTy t

-- >>> showTy TUnit
-- "1"
-- >>> showTy (TReg 2)
-- "[2]"
-- >>> showTy (TTensor (TReg 2) (TReg 2))
-- "[2] * [2]"
-- >>> showTy (TTensor (TTensor (TReg 2) (TReg 2)) (TReg 2))
-- "([2] * [2]) * [2]"
-- >>> showTy (tyOfDims [2, 2, 2])
-- "[2] * [2] * [2]"

-- Scalars, gates and kets ----------------------------------------------------

-- | An exact scalar back to .s text, at tower levels 1 to 4.
renderScalar :: Cyclo -> String
renderScalar (Cyclo k cs)
  | k == 1    = case cs of { (c : _) -> showRat c ; [] -> "0" }
  -- refusal: a scalar beyond Q(zeta_16) has no spelling in a .s file
  | k > 4     = error "renderScalar: scalar beyond Q(zeta_16)"
  | otherwise =
      joinTerms [ (c < 0, term (abs c) j) | (j, c) <- zip [0 :: Int ..] cs, c /= 0 ]
  where
    base = case k of 2 -> "i"; 3 -> "z8"; _ -> "z16"
    pow j | j == 1    = base
          | otherwise = base ++ "^" ++ show j
    term c 0 = showRat c
    term c j | c == 1    = pow j
             | otherwise = showRat c ++ "*" ++ pow j
    joinTerms [] = "0"
    joinTerms ((n0, t0) : rest) =
      (if n0 then "-" else "") ++ t0
      ++ concat [ (if n then "-" else "+") ++ t | (n, t) <- rest ]

-- >>> renderScalar 0
-- "0"
-- >>> renderScalar 1
-- "1"
-- >>> renderScalar (-1 / 2)
-- "-1/2"
-- >>> renderScalar iC
-- "i"
-- >>> renderScalar (zetaC 3)
-- "z8"
-- >>> renderScalar (zetaP 3 3)
-- "z8^3"
-- >>> renderScalar invSqrt2C
-- "1/2*z8-1/2*z8^3"
-- >>> renderScalar (1 + iC)
-- "1+i"
-- >>> renderScalar (zetaC 4 * 3)
-- "3*z16"

-- | The first named gate whose matrix equals the given one.
gateNameOf :: GateEnv -> Matrix Cyclo -> Maybe String
gateNameOf env g = case [ nm | (nm, m) <- env, m == g ] of
  (nm : _) -> Just nm
  []       -> Nothing

-- >>> gateNameOf gateTable gX
-- Just "X"
-- >>> gateNameOf gateTable gHC
-- Just "H"
-- >>> gateNameOf gateTable [[1, 1], [1, 0]]
-- Nothing
-- >>> gateNameOf [("V", [[1, 1], [1, 0]])] [[1, 1], [1, 0]]
-- Just "V"

-- | The diagonal entries, when the matrix is square and zero off-diagonal.
-- (Drop.Lang.Parser's diagMat is the inverse.)
diagOf :: Matrix Cyclo -> Maybe [Cyclo]
diagOf g
  | not (null g), all ((== n) . length) g
  -- impossible: g is n by n here, so every index below is in range
  , and [ g !! i !! j == 0 | i <- [0 .. n - 1], j <- [0 .. n - 1], i /= j ]
  -- impossible: g is n by n here, so every index below is in range
  = Just [ g !! i !! i | i <- [0 .. n - 1] ]
  | otherwise = Nothing
  where n = length g

-- >>> diagOf [[1, 0], [0, 2]]
-- Just [Cyclo 1 [1 % 1],Cyclo 1 [2 % 1]]
-- >>> diagOf [[0, 1], [1, 0]]
-- Nothing
-- >>> diagOf [[1, 0, 0], [0, 1]]
-- Nothing
-- >>> diagOf []
-- Nothing

-- | The image list, when the matrix is a permutation matrix.
-- (Drop.Lang.Parser's permMat is the inverse.)
permOf :: Matrix Cyclo -> Maybe [Int]
permOf g
  | not (null g), all ((== n) . length) g
  , Just imgs <- mapM colImg [0 .. n - 1]
  , length (nub imgs) == n
  = Just imgs
  | otherwise = Nothing
  where
    n = length g
    -- impossible: g is n by n here, and i, j range over its rows and columns
    colImg j = case [ i | i <- [0 .. n - 1], g !! i !! j /= 0 ] of
      -- impossible: i came from the same range
      [i] | g !! i !! j == 1 -> Just i
      _                      -> Nothing

-- >>> permOf [[0, 1], [1, 0]]
-- Just [1,0]
-- >>> permOf [[0, 0, 1], [1, 0, 0], [0, 1, 0]]
-- Just [1,2,0]
-- >>> permOf [[1, 0], [0, 2]]
-- Nothing
-- >>> permOf [[1, 1], [1, 0]]
-- Nothing

-- | The basis index of a state vector that is exactly one ket.
basisKet :: StateV Cyclo -> Maybe Int
basisKet psi = case [ i | (i, c) <- zip [0 ..] psi, c /= 0 ] of
  -- impossible: i is an index of psi, from the zip
  [i] | psi !! i == 1 -> Just i
  _                   -> Nothing

-- >>> basisKet [1, 0]
-- Just 0
-- >>> basisKet [0, 0, 1]
-- Just 2
-- >>> basisKet [0, 2]
-- Nothing
-- >>> basisKet [1, 1]
-- Nothing

-- Commands -------------------------------------------------------------------

-- | A value in the file's spelling: @()@, a name, or a tuple.
renderValue :: Value -> String
renderValue VUnit      = "()"
renderValue (VVar x)   = x
renderValue v          = "(" ++ intercalate ", " (map renderValue (flatten v)) ++ ")"
  where
    flatten (VPair a b) = a : flatten b
    flatten w           = [w]

-- >>> renderValue VUnit
-- "()"
-- >>> renderValue (VVar "x")
-- "x"
-- >>> renderValue (valueOfNames ["x", "y", "z"])
-- "(x, y, z)"
-- >>> renderValue (VPair (VPair (VVar "x") (VVar "y")) (VVar "z"))
-- "((x, y), z)"

-- | One command in the file's spelling, naming gates from the given table.
renderCmdWith :: GateEnv -> Cmd Cyclo -> String
renderCmdWith env c = case c of
  New x d        -> "new " ++ x ++ " : [" ++ show d ++ "] @ |0>;"
  NewState x d s -> "new " ++ x ++ " : [" ++ show d ++ "] @ " ++ st ++ ";"
    -- A ket |i> is read back with d amplitudes, so a vector of any other
    -- length is printed in full rather than as the ket it would become.
    where st = case basisKet s of
                 Just i | length s == d -> "|" ++ show i ++ ">"
                 _                      -> "(" ++ intercalate ", " (map renderScalar s) ++ ")"
  -- A loan is a header parameter; 'renderFile' prints it there. A bare
  -- render (used only for diagnostics) shows it as the header would.
  Loan x d       -> "-- loan " ++ x ++ " : [" ++ show d ++ "]"
  Gate g xs -> case gateNameOf env g of
    Just nm -> nm ++ " " ++ unwords xs ++ ";"
    Nothing
      | Just ds <- diagOf g ->
          "diag " ++ unwords xs ++ " ("
          ++ intercalate ", " (map renderScalar ds) ++ ");"
      | Just ps <- permOf g ->
          "perm " ++ unwords xs ++ " (" ++ unwords (map show ps) ++ ");"
      | otherwise ->
          "mat " ++ unwords xs ++ " { "
          ++ intercalate " ; " [ intercalate ", " (map renderScalar row)
                               | row <- g ]
          ++ " }"
  Lift p x b -> p ++ " = lift[{" ++ intercalate "," (map show b) ++ "}] " ++ x ++ ";"
  IfBit g t e -> "if " ++ showGuard g ++ " { " ++ inline t ++ "} else { "
                 ++ inline e ++ "}"
  Drop xs -> "drop " ++ renderValue (valueOfNames xs) ++ ";"
  where
    inline = concatMap (\s -> renderCmdWith env s ++ " ")

-- A gate the file declares itself prints by its name; the same matrix against the table alone prints as a diag.
-- >>> renderCmdWith [("V", [[1, 0], [0, 2]])] (Gate [[1, 0], [0, 2]] ["x"])
-- "V x;"
-- >>> renderCmdWith gateTable (Gate [[1, 0], [0, 2]] ["x"])
-- "diag x (1, 2);"

-- | One command in the file's spelling, naming gates from 'gateTable'.
renderCmd :: Cmd Cyclo -> String
renderCmd = renderCmdWith gateTable

-- One command of each constructor, smallest first.
-- >>> renderCmd (New "t" 2)
-- "new t : [2] @ |0>;"
-- >>> renderCmd (NewState "t" 2 [0, 1])
-- "new t : [2] @ |1>;"
-- >>> renderCmd (NewState "p" 2 [invSqrt2C, invSqrt2C])
-- "new p : [2] @ (1/2*z8-1/2*z8^3, 1/2*z8-1/2*z8^3);"
--
-- A vector shaped like a ket but of the wrong length is printed in full, not as the ket.
-- >>> renderCmd (NewState "q" 3 [0, 1])
-- "new q : [3] @ (0, 1);"
-- >>> renderCmd (Loan "a" 2)
-- "-- loan a : [2]"
-- >>> renderCmd (Gate gX ["x"])
-- "X x;"
-- >>> renderCmd (Gate gCCX ["x", "y", "a"])
-- "CCX x y a;"
-- >>> renderCmd (Gate [[1, 0], [0, 2]] ["x"])
-- "diag x (1, 2);"
-- >>> renderCmd (Gate [[0, 0, 1], [1, 0, 0], [0, 1, 0]] ["q"])
-- "perm q (1 2 0);"
-- >>> renderCmd (Gate [[1, 1], [1, 0]] ["x"])
-- "mat x { 1, 1 ; 1, 0 }"
-- >>> renderCmd (Lift "m" "a" [1])
-- "m = lift[{1}] a;"
-- >>> renderCmd (IfBit (GParam "m") [Gate gX ["x"]] [])
-- "if m { X x; } else { }"
-- >>> renderCmd (Drop ["a"])
-- "drop a;"
-- >>> renderCmd (Drop ["a", "b"])
-- "drop (a, b);"
-- >>> renderCmd (Drop [])
-- "drop ();"

-- | A gate matrix in the file's spelling, as a declaration writes it.
renderGateLit :: Matrix Cyclo -> String
renderGateLit m
  | Just ds <- diagOf m = "diag (" ++ intercalate ", " (map renderScalar ds) ++ ")"
  | Just ps <- permOf m = "perm (" ++ unwords (map show ps) ++ ")"
  | otherwise = "mat { "
      ++ intercalate " ; " [ intercalate ", " (map renderScalar row) | row <- m ]
      ++ " }"

-- >>> renderGateLit [[1, 0], [0, 2]]
-- "diag (1, 2)"
-- >>> renderGateLit [[0, 0, 1], [1, 0, 0], [0, 1, 0]]
-- "perm (1 2 0)"
-- >>> renderGateLit [[1, 1], [1, 0]]
-- "mat { 1, 1 ; 1, 0 }"

-- Files and programs ---------------------------------------------------------

-- | Emit valid .s text; @parseFile . renderFile@ is the identity on 'SFile'.
renderFile :: SFile -> String
renderFile f = unlines $
  [ "gate " ++ nm ++ " : " ++ showTy (tyOfDims [length m]) ++ " = "
    ++ renderGateLit m ++ ";"
  | (nm, m) <- sfDecls f ]
  ++ [ "prog " ++ sfName f ++ " (" ++ intercalate ", " (map param (sfParams f))
       ++ ") : " ++ showTy (sfResult f) ++ " {" ]
  ++ [ "  " ++ renderCmdWith env c | c <- sfBody f, notLoan c ]
  ++ [ "  return " ++ renderValue (sfReturn f), "}" ]
  where
    env = gateTable ++ sfDecls f
    param p = (if prmLoan p then "loan " else "")
              ++ prmName p ++ " : [" ++ show (prmDim p) ++ "]"
    notLoan (Loan _ _) = False
    notLoan _          = True

-- The paper's temporary AND, as the printer lays it out (each line is shown with its quotes, so its indentation stays).
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (mapM_ print . lines . renderFile) (parseFile src)
-- "prog temp_and (x : [2], y : [2]) : [2] * [2] {"
-- "  new a : [2] @ |0>;"
-- "  CCX x y a;"
-- "  H a;"
-- "  m = lift[{1}] a;"
-- "  if m { diag x y (1, 1, 1, -1); } else { }"
-- "  drop a;"
-- "  return (x, y)"
-- "}"

-- A loan is printed in the header, and the body does not repeat it.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (mapM_ print . lines . renderFile) (parseFile src)
-- "prog mcx3_x (q1 : [2], q2 : [2], q3 : [2], q : [2], loan a : [2]) : [2] * [2] * [2] * [2] {"
-- "  X a;"
-- "  CCX q3 a q;"
-- "  CCX q1 q2 a;"
-- "  CCX q3 a q;"
-- "  CCX q1 q2 a;"
-- "  drop a;"
-- "  return (q1, q2, q3, q)"
-- "}"

-- | The registers still live after a flat program, in allocation order:
-- the inputs and loans it was handed plus the temporaries it allocated,
-- less the ones it dropped.
liveAfter :: VisSpec -> Prog a -> [(String, Int)]
liveAfter vis = foldl step vis
  where
    step live c = case c of
      New x d        -> live ++ [(x, d)]
      NewState x d _ -> live ++ [(x, d)]
      Loan x d       -> live ++ [(x, d)]
      Drop xs        -> filter ((`notElem` xs) . fst) live
      _              -> live

-- >>> liveAfter [("x", 2)] ([] :: Prog Cyclo)
-- [("x",2)]
-- >>> :m + Drop.Lang.Programs.TempAnd
-- >>> liveAfter visXY (take 2 andComputed)
-- [("x",2),("y",2),("a",2)]
-- >>> liveAfter visXY andComputed
-- [("x",2),("y",2)]
-- >>> liveAfter visXY andUncomputedByMeasurement
-- [("x",2),("y",2)]

-- | The flat program as a file named @p@, returning
-- whatever is still live. @parseProgram . renderProgram@ is the identity on
-- the abstract syntax.
renderProgram :: VisSpec -> Prog Cyclo -> String
renderProgram vis prog = renderFile SFile
  { sfName = "p"
  , sfParams = [ Param x d (x `elem` loanNames) | (x, d) <- vis ++ loanSpec ]
  , sfResult = tyOfDims (map snd live)
  , sfDecls = []
  , sfBody = prog
  , sfReturn = valueOfNames (map fst live)
  }
  where
    loanSpec = [ (x, d) | Loan x d <- prog ]
    loanNames = map fst loanSpec
    live = liveAfter (vis ++ loanSpec) [ c | c <- prog, notLoan c ]
    notLoan (Loan _ _) = False
    notLoan _          = True

-- >>> mapM_ print (lines (renderProgram [("x", 2)] []))
-- "prog p (x : [2]) : [2] {"
-- "  return x"
-- "}"
-- >>> mapM_ print (lines (renderProgram visXY andUncomputedByMeasurement))
-- "prog p (x : [2], y : [2]) : [2] * [2] {"
-- "  new a : [2] @ |0>;"
-- "  CCX x y a;"
-- "  H a;"
-- "  m = lift[{1}] a;"
-- "  if m { diag x y (1, 1, 1, -1); } else { }"
-- "  drop a;"
-- "  return (x, y)"
-- "}"
