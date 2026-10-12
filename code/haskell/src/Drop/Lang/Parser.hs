-- Parser.hs: the .s concrete syntax of the syntax figure, hand-rolled on base
-- alone, total, with a line number on every error, plus the pretty-printer
-- renderFile/renderProgram. The one-page reference is programs/SYNTAX.md;
-- Drop.Lang.Checks.Parser checks that parse . render is the identity on the abstract
-- syntax. Scalars are exact cyclotomic elements only, no float syntax.
-- Static checks below report a line and never fall back on a silent default.
--
-- A file is optional top-level gate declarations followed by ONE program:
--
--   gate V : [2] * [2] = mat { ... };
--   prog f (x : [2], loan a : [2]) : [2] {  M  }
--
-- The header supplies the input context (the paper's Omega), the result
-- type and, through the body's closing `return v`, the value the program
-- hands back. A header parameter marked `loan` is a register the program is
-- handed in a state it does not know and must hand back; the parser hoists
-- it to a 'Loan' command at the head of the body, before any `new`, so the
-- machine's allocation order puts it among the inputs.
--
-- Three statements are written as abbreviations, exactly as the paper's
-- syntax subsection does: `U v;` acts on v in place, with no separate output
-- name; `drop v;` binds nothing; and `new t : [d] @ psi;` names the
-- register once, at its declaration. An explicit-binding spelling of any
-- of the three -- `t = new [d] @ psi;`, `p = U v;`, `() = drop v;` -- is a
-- parse error naming the printed form: the accepted language is exactly
-- the printed grammar. A block `y = { ...; return v };` is the paper's sequencing
-- operator: its statements are spliced into the enclosing body and `y` is
-- bound to the wire `v` names (terms are identified up to renaming of
-- bound names), and the parameters the block binds leave scope at its
-- closing brace.

module Drop.Lang.Parser
  ( SFile (..)
  , SrcPos (..)
  , Param (..)
  , parseFile
  , parseFileAt
  , renderFile
  , parseProgram
  , renderProgram
  , renderCmd
  , gateTable
  , mapProg
  , tyOfDims
  , liveAfter
  , sfVis
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)
import Data.List (intercalate, nub)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Ratio ((%))
import Drop.Lang.Ring (showRat, showAmp)
import Drop.Lang.Cyclo
import Drop.Lang.Gates
import Drop.Lang.QState (Matrix, StateV, norm2S)
import Drop.Lang.Syntax
import Drop.Lang.Typed (Ty (..), Value (..), valueNames)

-- Tokens

data Tok = TWord String | TInt Integer | TSym Char | TEnd deriving (Eq, Show)
type LTok = (Int, Tok)

symChars :: String
symChars = ":;,@(){}[]=^*/+-|<>!&"

isIdentStart :: Char -> Bool
isIdentStart c = isAlpha c || c == '_'

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_'

tokenize :: String -> Either String [LTok]
tokenize src = fmap concat (mapM tokLine (zip [1 ..] (lines src)))
  where
    tokLine (n, ln) = go (stripComment ln)
      where
        stripComment ('-' : '-' : _) = []
        stripComment (c : cs)        = c : stripComment cs
        stripComment []              = []
        go [] = Right []
        go (c : cs)
          | isSpace c = go cs
          | isDigit c = let (ds, rest) = span isDigit (c : cs)
                        in ((n, TInt (read ds)) :) <$> go rest
          | isIdentStart c = let (ws, rest) = span isIdentChar (c : cs)
                             in ((n, TWord ws) :) <$> go rest
          | c `elem` symChars = ((n, TSym c) :) <$> go cs
          | otherwise =
              Left ("line " ++ show n ++ ": unexpected character " ++ show c)

showTok :: Tok -> String
showTok (TWord w) = "'" ++ w ++ "'"
showTok (TInt n)  = show n
showTok (TSym c)  = "'" ++ [c] ++ "'"
showTok TEnd      = "end of input"

errAt :: [LTok] -> String -> Either String a
errAt ((n, TEnd) : _) msg =
  Left ("line " ++ show n ++ ": " ++ msg ++ " (found end of input)")
errAt ((n, t) : _) msg =
  Left ("line " ++ show n ++ ": " ++ msg ++ " (found " ++ showTok t ++ ")")
errAt [] msg = Left ("line 1: " ++ msg)

errLn :: Int -> String -> Either String a
errLn n msg = Left ("line " ++ show n ++ ": " ++ msg)

lineAt :: [LTok] -> Int
lineAt ((n, _) : _) = n
lineAt []           = 1

-- | The name of the construct an @if@ branch binds, at any depth.
--
-- The calculus types both branches of a conditional in the same register
-- context, so a branch binds nothing: no allocation, no lift, no drop, and
-- so no block either. The surface language says the same, and says it here,
-- because every analysis downstream reads the binders off the top-level
-- statement list. A branch-local binder would be checked by nothing while
-- its name stayed live outside the branch.
branchBinder :: Cmd a -> Maybe String
branchBinder (New _ _)        = Just "new"
branchBinder (NewState _ _ _) = Just "new"
branchBinder (Loan _ _)       = Just "loan"
branchBinder (Lift _ _ _)     = Just "lift"
branchBinder (Drop _)         = Just "drop"
branchBinder (Gate _ _)       = Nothing
branchBinder (IfBit _ t e)    = listToMaybe (mapMaybe branchBinder (t ++ e))

-- | The line to report an error about a list of names at.
lineOf :: [(Int, String)] -> Int
lineOf ((n, _) : _) = n
lineOf []           = 1

-- Primitive parsers

expectSym :: Char -> [LTok] -> Either String ((), [LTok])
expectSym c ts = case ts of
  ((_, TSym c') : r) | c' == c -> Right ((), r)
  _ -> errAt ts ("expected '" ++ [c] ++ "'")

expectWord :: String -> [LTok] -> Either String ((), [LTok])
expectWord w ts = case ts of
  ((_, TWord w') : r) | w' == w -> Right ((), r)
  _ -> errAt ts ("expected '" ++ w ++ "'")

identL :: [LTok] -> Either String ((Int, String), [LTok])
identL ts = case ts of
  ((n, TWord w) : r) -> Right ((n, w), r)
  _ -> errAt ts "expected a name"

natL :: [LTok] -> Either String ((Int, Int), [LTok])
natL ts = case ts of
  ((n, TInt v) : r) -> Right ((n, fromInteger v), r)
  _ -> errAt ts "expected an integer"

-- | One or more register names, stopping at the first non-word token.
regList :: [LTok] -> Either String ([(Int, String)], [LTok])
regList ts0 = case ts0 of
  ((n, TWord w) : r) -> do
    (more, ts1) <- opt r
    Right ((n, w) : more, ts1)
  _ -> errAt ts0 "expected a register name"
  where
    opt ts = case ts of
      ((n, TWord w) : r) -> do
        (more, ts1) <- opt r
        Right ((n, w) : more, ts1)
      _ -> Right ([], ts)

-- Types, values and patterns

-- | @A ::= 1 | [d] | A * B@, with @*@ to the right.
pTy :: [LTok] -> Either String (Ty, [LTok])
pTy ts0 = do
  (a, ts1) <- pTyAtom ts0
  case ts1 of
    ((_, TSym '*') : r) -> do (b, ts2) <- pTy r; Right (TTensor a b, ts2)
    _                   -> Right (a, ts1)

pTyAtom :: [LTok] -> Either String (Ty, [LTok])
pTyAtom ts = case ts of
  ((_, TInt 1) : r)   -> Right (TUnit, r)
  ((_, TSym '[') : r) -> do
    (nd@(_, d), r1) <- natL r
    checkDim nd
    (_, r2) <- expectSym ']' r1
    Right (TReg d, r2)
  ((_, TSym '(') : r) -> do
    (a, r1) <- pTy r
    (_, r2) <- expectSym ')' r1
    Right (a, r2)
  _ -> errAt ts "expected a type ('1', '[d]' or 'A * B')"

-- | A right-nested tuple type over the given dimensions; @1@ when empty.
tyOfDims :: [Int] -> Ty
tyOfDims []       = TUnit
tyOfDims [d]      = TReg d
tyOfDims (d : ds) = TTensor (TReg d) (tyOfDims ds)

-- | A right-nested tuple value over the given names; @()@ when empty.
valueOfNames :: [String] -> Value
valueOfNames []       = VUnit
valueOfNames [x]      = VVar x
valueOfNames (x : xs) = VPair (VVar x) (valueOfNames xs)

pValue :: [LTok] -> Either String (Value, [LTok])
pValue ts = case ts of
  ((_, TWord w) : r) -> Right (VVar w, r)
  ((_, TSym '(') : r) -> case r of
    ((_, TSym ')') : r1) -> Right (VUnit, r1)
    _ -> do
      (vs, r1) <- commaSep pValue r
      (_, r2)  <- expectSym ')' r1
      case vs of
        [v] -> Right (v, r2)
        _   -> Right (foldr1 VPair vs, r2)
  _ -> errAt ts "expected a value (a register name, '()' or a tuple)"

commaSep :: ([LTok] -> Either String (b, [LTok])) -> [LTok]
         -> Either String ([b], [LTok])
commaSep p ts0 = do
  (x, ts1) <- p ts0
  go [x] ts1
  where
    go acc ((_, TSym ',') : r) = do (x, r') <- p r; go (acc ++ [x]) r'
    go acc ts                  = Right (acc, ts)

-- Scalars

pScalar :: [LTok] -> Either String (Cyclo, [LTok])
pScalar ts0 = do
  (t1, ts1) <- pProduct ts0
  goSum t1 ts1
  where
    goSum acc ts = case ts of
      ((_, TSym '+') : r) -> do (t, r') <- pProduct r; goSum (acc + t) r'
      ((_, TSym '-') : r) -> do (t, r') <- pProduct r; goSum (acc - t) r'
      _ -> Right (acc, ts)

pProduct :: [LTok] -> Either String (Cyclo, [LTok])
pProduct ts0 = do
  (f1, ts1) <- pFactor ts0
  go f1 ts1
  where
    go acc ((_, TSym '*') : r) = do (f, r') <- pFactor r; go (acc * f) r'
    go acc ts = Right (acc, ts)

pFactor :: [LTok] -> Either String (Cyclo, [LTok])
pFactor ts = case ts of
  ((_, TSym '-') : r)      -> do (f, r') <- pFactor r; Right (negate f, r')
  ((_, TWord "i") : r)     -> Right (iC, r)
  ((_, TWord "z8") : r)    -> pPow 3 r
  ((_, TWord "z16") : r)   -> pPow 4 r
  ((_, TInt n) : r) -> case r of
    ((_, TSym '/') : r2) -> case r2 of
      ((ln, TInt m) : r3)
        | m == 0    -> errLn ln "division by zero in scalar"
        | otherwise -> Right (fromRational (n % m), r3)
      ((_, TWord "rt2") : r3) -> Right (fromInteger n * invSqrt2C, r3)
      _ -> errAt r2 "malformed scalar: expected an integer or rt2 after '/'"
    _ -> Right (fromInteger n, r)
  _ -> errAt ts "malformed scalar"
  where
    pPow k r = case r of
      ((_, TSym '^') : r2) -> case r2 of
        ((_, TInt j) : r3) -> Right (zetaP k j, r3)
        _ -> errAt r2 "malformed scalar: expected an integer exponent"
      _ -> Right (zetaC k, r)

pScalarList :: [LTok] -> Either String ([Cyclo], [LTok])
pScalarList = commaSep pScalar

-- | Rows of a mat literal, with an optional trailing ';' before '}'.
pRows :: [LTok] -> Either String ([[Cyclo]], [LTok])
pRows ts0 = do
  (r1, ts1) <- pScalarList ts0
  go [r1] ts1
  where
    go acc ((_, TSym ';') : r) = case r of
      ((_, TSym '}') : _) -> Right (acc, r)
      _ -> do (row, r') <- pScalarList r; go (acc ++ [row]) r'
    go acc ts = Right (acc, ts)

-- | One or more space-separated naturals: a perm image list.
pNatsSpace :: [LTok] -> Either String ([(Int, Int)], [LTok])
pNatsSpace ts0 = do
  (v, ts1) <- natL ts0
  go [v] ts1
  where
    go acc ts@((_, TInt _) : _) = do (v, r) <- natL ts; go (acc ++ [v]) r
    go acc ts = Right (acc, ts)

pNatList :: [LTok] -> Either String ([(Int, Int)], [LTok])
pNatList = commaSep natL

-- The gate set

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

diagMat :: [Cyclo] -> Matrix Cyclo
diagMat ss = [ [ if i == j then ss !! i else 0 | j <- [0 .. d - 1] ]
             | i <- [0 .. d - 1] ]
  where d = length ss

-- | |j> -> |imgs_j>: column j has its 1 in row imgs_j.
permMat :: [Int] -> Matrix Cyclo
permMat imgs = [ [ if imgs !! j == i then 1 else 0 | j <- [0 .. d - 1] ]
               | i <- [0 .. d - 1] ]
  where d = length imgs

-- Scope

-- | What the parser knows as it walks the statements: the live registers
-- with their dimensions, the names it has already bound (a name is bound
-- once), the names already dropped, the parameters in scope, every
-- parameter ever bound, and the aliases a block left behind (a surface name
-- standing for the wire a block returned).
data Scope = Scope
  { scLive    :: [(String, Int)]
  , scDropped :: [String]
  , scBits    :: [String]
  , scAllBits :: [String]
  , scAllNames :: [String]
  , scAlias   :: [(String, String)]
  }

newScope :: [Param] -> Scope
newScope ps = Scope [ (prmName p, prmDim p) | p <- ps ] [] [] []
                    (map prmName ps) []

-- | A surface name resolved to the wire it stands for.
resolve :: Scope -> String -> String
resolve sc x = maybe x id (lookup x (scAlias sc))

bindReg :: String -> Int -> Scope -> Scope
bindReg x d sc = sc { scLive = scLive sc ++ [(x, d)]
                    , scAllNames = scAllNames sc ++ [x] }

-- | A dropped name leaves the live set and is remembered, so that naming it
-- again is an error with a reason rather than "unknown register".
dropRegs :: [String] -> Scope -> Scope
dropRegs xs sc = sc { scLive    = filter ((`notElem` xs) . fst) (scLive sc)
                    , scDropped = scDropped sc ++ xs }

bindBit :: String -> Scope -> Scope
bindBit q sc = sc { scBits = scBits sc ++ [q], scAllBits = scAllBits sc ++ [q] }

lookupReg :: Scope -> (Int, String) -> Either String (String, Int)
lookupReg sc (n, x0) =
  let x = resolve sc x0
  in case lookup x (scLive sc) of
       Just d -> Right (x, d)
       Nothing
         | x `elem` scDropped sc -> errLn n ("register '" ++ x0 ++ "' has been dropped")
         | otherwise             -> errLn n ("unknown register '" ++ x0 ++ "'")

-- | A name is bound once. Re-binding a dropped name would leave the machine
-- two wires with one name, since a drop is the identity and the first wire
-- is still there. Reuse of the underlying wire is the allocator's business,
-- not the program text's.
checkFresh :: Scope -> (Int, String) -> Either String ()
checkFresh sc (n, x)
  | x `elem` map fst (scLive sc) =
      errLn n ("register '" ++ x ++ "' already exists")
  | x `elem` scDropped sc =
      errLn n ("register '" ++ x ++ "' has been dropped, and a dropped name \
               \cannot be bound again")
  | x `elem` scAllNames sc =
      errLn n ("the name '" ++ x ++ "' is already bound")
  | otherwise = Right ()

checkDim :: (Int, Int) -> Either String ()
checkDim (n, d)
  | d < 2     = errLn n "register dimension must be at least 2"
  | otherwise = Right ()

-- | Register checks shared by every gate statement: distinct known
-- registers. Returns the wire names, a line to report errors at, and the
-- product dimension.
gateRegs :: Scope -> String -> [(Int, String)] -> Either String ([String], Int, Int)
gateRegs sc what regs = do
  found <- mapM (lookupReg sc) regs
  let names = map fst found
      dims  = map snd found
      ln    = lineOf regs
  if length (nub names) /= length names
    then errLn ln ("repeated register in " ++ what)
    else Right (names, ln, product dims)

-- The declarations and the program header

data Param = Param { prmName :: String, prmDim :: Int, prmLoan :: Bool }
  deriving (Eq, Show)

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

-- | Where a rule about the program text is to be reported: the line the
-- body's @return@ stands on, and the header line of each loan input. These
-- are metadata about the text the file was read from, NOT part of its
-- abstract syntax -- the renderer lays a program out its own way, so a
-- rendered file's lines are its own -- so they are kept out of 'SFile', and
-- @parseFile . renderFile@ stays an identity on 'SFile' itself.
-- Drop.Lang.Check's loan discipline works on the typed program and has no
-- lines of its own; Drop.Lang.Report.Run reads them from here to place its errors.
data SrcPos = SrcPos
  { spReturnLine :: Int
  , spLoanLines  :: [(String, Int)]
  } deriving (Eq, Show)

-- | The ordinary (non-loan) input registers, the machine's 'VisSpec'.
sfVis :: SFile -> VisSpec
sfVis f = [ (prmName p, prmDim p) | p <- sfParams f, not (prmLoan p) ]

type GateEnv = [(String, Matrix Cyclo)]

pDecls :: GateEnv -> [LTok] -> Either String (GateEnv, [LTok])
pDecls env ts = case ts of
  ((_, TWord "gate") : r) -> do
    ((ln, nm), r1) <- identL r
    (_, r2)  <- expectSym ':' r1
    (ty, r3) <- pTy r2
    (_, r4)  <- expectSym '=' r3
    (m, r5)  <- pGateLit r4
    (_, r6)  <- expectSym ';' r5
    let d = tyDim ty
    if nm `elem` map fst env
      then errLn ln ("gate '" ++ nm ++ "' is already declared")
      else if length m /= d
        then errLn ln ("gate '" ++ nm ++ "' is declared at dimension " ++ show d
                       ++ " but its matrix is " ++ show (length m) ++ "x"
                       ++ show (length m))
        else pDecls (env ++ [(nm, m)]) r6
  _ -> Right (env, ts)

tyDim :: Ty -> Int
tyDim TUnit         = 1
tyDim (TReg d)      = d
tyDim (TTensor a b) = tyDim a * tyDim b

-- | The right-hand side of a gate declaration: a matrix, a diagonal or a
-- permutation, written exactly as the corresponding statement writes it.
pGateLit :: [LTok] -> Either String (Matrix Cyclo, [LTok])
pGateLit ts = case ts of
  ((_, TWord "mat") : r) -> do
    (_, r1)    <- expectSym '{' r
    (rows, r2) <- pRows r1
    (_, r3)    <- expectSym '}' r2
    let d = length rows
    if any ((/= d) . length) rows
      then errLn (lineAt ts) "mat literal is not square"
      else Right (rows, r3)
  ((_, TWord "diag") : r) -> do
    (_, r1)  <- expectSym '(' r
    (ss, r2) <- pScalarList r1
    (_, r3)  <- expectSym ')' r2
    Right (diagMat ss, r3)
  ((_, TWord "perm") : r) -> do
    (_, r1)  <- expectSym '(' r
    (ps, r2) <- pNatsSpace r1
    (_, r3)  <- expectSym ')' r2
    let imgs = map snd ps
    if length (nub imgs) /= length imgs || any (>= length imgs) imgs
      then errLn (lineAt ts) "perm image list is not a permutation"
      else Right (permMat imgs, r3)
  _ -> errAt ts "expected 'mat', 'diag' or 'perm' after '=' in a gate declaration"

-- | The header, and the line each parameter is declared on (positionally
-- matching the parameter list).
pHeader :: [LTok] -> Either String ((String, [Param], Ty, [Int]), [LTok])
pHeader ts0 = do
  (_, ts1) <- expectWord "prog" ts0
  ((_, nm), ts2) <- identL ts1
  (_, ts3) <- expectSym '(' ts2
  (ps, ts4) <- case ts3 of
    ((_, TSym ')') : r) -> Right ([], r)
    _ -> do
      (ps, r1) <- commaSep pParam ts3
      (_, r2)  <- expectSym ')' r1
      Right (ps, r2)
  (_, ts5)  <- expectSym ':' ts4
  (ty, ts6) <- pTy ts5
  let names = map (prmName . fst) ps
  if length (nub names) /= length names
    then errLn (lineAt ts2) ("repeated parameter in the header of '" ++ nm ++ "'")
    else Right ((nm, map fst ps, ty, map snd ps), ts6)
  where
    pParam ts = do
      let (isLoan, r0) = case ts of
            ((_, TWord "loan") : r) -> (True, r)
            _                        -> (False, ts)
      ((_, x), r1) <- identL r0
      (_, r2)      <- expectSym ':' r1
      (ty, r3)     <- pTy r2
      case ty of
        TReg d -> Right ((Param x d isLoan, lineAt ts), r3)
        _      -> errLn (lineAt r0)
                    ("parameter '" ++ x ++ "' must have a register type [d]")

-- Statements

-- | True when the statement beginning here is a binding @p = N;@ rather
-- than one of the abbreviations. Decided by scanning to the first '=', ';'
-- or '{' at bracket depth zero.
isBinding :: [LTok] -> Bool
isBinding = go (0 :: Int)
  where
    go _ [] = False
    go d ((_, t) : r) = case t of
      TSym '(' -> go (d + 1) r
      TSym '[' -> go (d + 1) r
      TSym ')' -> go (d - 1) r
      TSym ']' -> go (d - 1) r
      TSym '=' | d == 0 -> True
      TSym ';' | d == 0 -> False
      TSym '{' | d == 0 -> False
      TEnd     -> False
      _        -> go d r

-- | Statements up to the body's closing @return v@.
-- | The 'Int' is the line the closing @return@ stands on.
pBody :: GateEnv -> Scope -> [LTok]
      -> Either String ([Cmd Cyclo], Value, Int, Scope, [LTok])
pBody env sc ts = case ts of
  ((_, TWord "return") : r) -> do
    (v, r1) <- pValue r
    let r2 = case r1 of ((_, TSym ';') : r') -> r'; _ -> r1
    v' <- resolveValue sc (lineAt r) v
    Right ([], v', lineAt ts, sc, r2)
  _ -> do
    (cs, sc1, ts1) <- pStmt env sc ts
    (cs2, v, rln, sc2, ts2) <- pBody env sc1 ts1
    Right (cs ++ cs2, v, rln, sc2, ts2)

resolveValue :: Scope -> Int -> Value -> Either String Value
resolveValue sc ln v = do
  mapM_ (\x -> lookupReg sc (ln, x)) (valueNames v)
  Right (go v)
  where
    go (VVar x)    = VVar (resolve sc x)
    go VUnit       = VUnit
    go (VPair a b) = VPair (go a) (go b)

pStmt :: GateEnv -> Scope -> [LTok]
      -> Either String ([Cmd Cyclo], Scope, [LTok])
pStmt env sc ts0
  | isBinding ts0 = do
      (p, ts1) <- pValue ts0
      (_, ts2) <- expectSym '=' ts1
      pBound env sc (lineAt ts0) p ts2
pStmt env sc ts0@((_, TWord w) : rest) = case w of

  "new"     -> do (c, sc', r) <- pNew sc rest;  Right ([c], sc', r)
  "drop"    -> do (c, sc', r) <- pDrop sc rest; Right ([c], sc', r)
  "if"      -> do (c, sc', r) <- pIf env sc rest; Right ([c], sc', r)

  "loan"    -> errAt ts0 "a loan is declared in the program header, as \
                         \`prog f (..., loan a : [d]) : A { ... }`, not as a \
                         \statement"
  "newdirty" -> errAt ts0 "'newdirty' is gone: a loan is declared in the \
                          \program header, as `loan a : [d]`"
  "vis"     -> errAt ts0 "'vis' is gone: the program header supplies the \
                         \input registers"
  "lift"    -> errAt ts0 "a lift binds its parameter: write `p = lift[S] x;`"
  "gate"    -> errAt ts0 "a gate statement names the gate: write `H t;`, and \
                         \`gate V : A = mat { ... };` before `prog` to declare one"
  "return"  -> errAt ts0 "'return' ends the body; it cannot appear here"

  _ -> do (c, sc', r) <- pGateStmt env sc ts0; Right ([c], sc', r)

pStmt _ _ ts = errAt ts "expected a statement"

-- | The right-hand side of a binding @p = N;@ (or @p = { ... };@).
pBound :: GateEnv -> Scope -> Int -> Value -> [LTok]
       -> Either String ([Cmd Cyclo], Scope, [LTok])
pBound env sc ln p ts = case ts of

  -- a block: the paper's sequencing operator, spliced
  ((_, TSym '{') : r) -> do
    let bitsBefore = scBits sc
    (cs, v, _, sc1, r1) <- pBody env sc r
    (_, r2) <- expectSym '}' r1
    (_, r3) <- expectSym ';' r2
    let names = valueNames p
        vs    = valueNames v
    if length names /= length vs
      then errLn ln ("the block returns " ++ show (length vs)
                     ++ " register(s), but the pattern binds " ++ show (length names))
      else do
        mapM_ (checkFresh sc1) [ (ln, x) | x <- names ]
        let sc2 = sc1 { scBits = bitsBefore
                      , scAlias = scAlias sc1 ++ zip names vs
                      , scAllNames = scAllNames sc1 ++ names }
        Right (cs, sc2, r3)

  -- p = lift[S] x;
  ((_, TWord "lift") : r) -> do
    pn <- singleName ln p "lift"
    (_, r1)   <- expectSym '[' r
    (_, r2)   <- expectSym '{' r1
    (lvls, r3) <- pNatList r2
    (_, r4)   <- expectSym '}' r3
    (_, r5)   <- expectSym ']' r4
    (nx, r6)  <- identL r5
    (_, r7)   <- expectSym ';' r6
    (x, d)    <- lookupReg sc nx
    let block = map snd lvls
    mapM_ (\(n, l) -> if l < 0 || l >= d
                        then errLn n ("level " ++ show l ++ " out of range for '"
                                      ++ x ++ "' (dimension " ++ show d ++ ")")
                        else Right ()) lvls
    if length (nub block) /= length block
      then errLn ln "repeated level in lift block"
      else if length block >= d
        then errLn ln ("the block of a lift must be a proper subset of the "
                       ++ show d ++ " levels of '" ++ x ++ "'")
      -- One parameter per lift, as the calculus writes them. A second
      -- binding of the same name would be read one way by the machine,
      -- which takes the latest, and another by the static pass, which takes
      -- the first, and the two would disagree in silence.
      else if pn `elem` scAllBits sc
        then errLn ln ("parameter '" ++ pn ++ "' is already bound by an \
                       \earlier lift")
        else Right ([Lift pn x block], bindBit pn sc, r7)

  -- The paper prints no name before 'new', so the explicit-binding
  -- spelling `t = new [d] @ psi;` is a parse error naming the printed form.
  ((_, TWord "new") : r) -> do
    x <- singleName ln p "new"
    (_, r1)  <- expectSym '[' r
    (nd@(_, d), r2) <- natL r1
    checkDim nd
    (_, r3)  <- expectSym ']' r2
    (cmd, _) <- pAlloc ln x d r3
    errLn ln ("an allocation binds its own name: write `"
              ++ renderCmd cmd ++ "`")

  -- () = drop v;  -- removed: the printed form binds nothing.
  ((_, TWord "drop") : r) -> do
    (c, _, _) <- pDrop sc r
    errLn ln ("a drop binds nothing: write `" ++ renderCmd c ++ "`")

  -- p = U v;  -- removed: a gate acts in place, on its own registers.
  _ -> do
    (c, _, _) <- pGateStmt env sc ts
    case c of
      Gate _ _ -> errLn ln ("a gate acts in place: write `" ++ renderCmd c ++ "`")
      _        -> errLn ln "expected a gate after '='"

singleName :: Int -> Value -> String -> Either String String
singleName ln p what = case valueNames p of
  [x] | p == VVar x -> Right x
  _ -> errLn ln (what ++ " binds exactly one name")

-- | @new x : [d] @ psi;@
pNew :: Scope -> [LTok] -> Either String (Cmd Cyclo, Scope, [LTok])
pNew sc ts = do
  (nx@(ln, x), ts1) <- identL ts
  (_, ts2)  <- expectSym ':' ts1
  (_, ts3)  <- expectSym '[' ts2
  (nd@(_, d), ts4) <- natL ts3
  checkDim nd
  (_, ts5)  <- expectSym ']' ts4
  checkFresh sc nx
  (cmd, ts6) <- pAlloc ln x d ts5
  (_, ts7)   <- expectSym ';' ts6
  Right (cmd, bindReg x d sc, ts7)

-- | The @\@ psi@ of an allocation: a ket @|i>@ or an exact amplitude vector.
pAlloc :: Int -> String -> Int -> [LTok] -> Either String (Cmd Cyclo, [LTok])
pAlloc ln x d ts = do
  (_, ts1) <- expectSym '@' ts
  case ts1 of
    ((_, TSym '|') : r) -> do
      ((_, i), r1) <- natL r
      (_, r2) <- expectSym '>' r1
      if i >= d
        then errLn ln ("|" ++ show i ++ "> is not a level of [" ++ show d ++ "]")
        else Right (if i == 0 then New x d else NewState x d (ketOf d i), r2)
    ((_, TSym '(') : r) -> do
      (amps, r1) <- pScalarList r
      (_, r2)    <- expectSym ')' r1
      if length amps /= d
        then errLn ln ("new " ++ x ++ " : [" ++ show d ++ "] needs " ++ show d
                       ++ " amplitudes, got " ++ show (length amps))
        -- The state named by hand must be a unit vector: every construct of
        -- the language is an isometry, and an unnormalised state would make
        -- a run's selection weights sum to something other than 1.
        else if norm2S amps /= 1
          then errLn ln ("new " ++ x ++ " : [" ++ show d ++ "] must name a unit"
                         ++ " state, but the vector given has squared norm "
                         ++ showAmp (norm2S amps) ++ ", not 1")
          else Right (NewState x d amps, r2)
    _ -> errAt ts1 "expected a state after '@': a ket |i> or an amplitude vector"

ketOf :: Int -> Int -> StateV Cyclo
ketOf d i = [ if k == i then 1 else 0 | k <- [0 .. d - 1] ]

-- | @drop v;@, v a register, a tuple of registers, or @()@. A tuple drop
-- is ONE site (the composite-temporary proposition). @drop ()@ is the site with no register,
-- a block of dimension one under the site definition's clause (1): the language admits it, it is safe
-- with the unit scalar as certificate, and its reclaiming gate is the
-- identity, so it parses to @Drop []@ and every consumer of a site handles
-- the empty list.
pDrop :: Scope -> [LTok] -> Either String (Cmd Cyclo, Scope, [LTok])
pDrop sc ts = do
  let ln = lineAt ts
  (v, ts1) <- pValue ts
  (_, ts2) <- expectSym ';' ts1
  v' <- resolveValue sc ln v
  let xs = valueNames v'
  if length (nub xs) /= length xs
    then errLn ln "repeated register in drop"
    else Right (Drop xs, dropRegs xs sc, ts2)

-- | @if e { M1 } else { M2 }@
pIf :: GateEnv -> Scope -> [LTok] -> Either String (Cmd Cyclo, Scope, [LTok])
pIf env sc ts = do
  let ln = lineAt ts
  (g, ts1) <- pGuard ts
  (_, ts2) <- expectSym '{' ts1
  (thn, _, ts3) <- pBranch env sc ts2
  (_, ts4) <- expectSym '}' ts3
  (_, ts5) <- expectWord "else" ts4
  (_, ts6) <- expectSym '{' ts5
  -- Each arm is read in the scope before the if: the then arm's exit scope
  -- would make a drop in both arms read as a drop of a dropped register.
  (els, _, ts7) <- pBranch env sc ts6
  (_, ts8) <- expectSym '}' ts7
  let ts9 = case ts8 of ((_, TSym ';') : r) -> r; _ -> ts8
  case [ p | p <- guardParams g, p `notElem` scBits sc ] of
    (p : _) -> errLn ln ("parameter '" ++ p ++ "' is not in scope here")
    [] -> case listToMaybe (mapMaybe branchBinder (thn ++ els)) of
      Just k  -> errLn ln ("'" ++ k ++ "' inside an if branch: a branch \
                           \binds nothing, so put it before or after the if")
      Nothing -> Right (IfBit g thn els, sc, ts9)

pBranch :: GateEnv -> Scope -> [LTok]
        -> Either String ([Cmd Cyclo], Scope, [LTok])
pBranch env sc ts = case ts of
  ((_, TSym '}') : _) -> Right ([], sc, ts)
  _ -> do
    (cs, sc1, ts1) <- pStmt env sc ts
    (cs2, sc2, ts2) <- pBranch env sc1 ts1
    Right (cs ++ cs2, sc2, ts2)

pGuard :: [LTok] -> Either String (Guard, [LTok])
pGuard = pOr
  where
    pOr ts = do
      (a, ts1) <- pAnd ts
      case ts1 of
        ((_, TSym '|') : (_, TSym '|') : r) -> do (b, r') <- pOr r; Right (GOr a b, r')
        _ -> Right (a, ts1)
    pAnd ts = do
      (a, ts1) <- pAtom ts
      case ts1 of
        ((_, TSym '&') : (_, TSym '&') : r) -> do (b, r') <- pAnd r; Right (GAnd a b, r')
        _ -> Right (a, ts1)
    pAtom ts = case ts of
      ((_, TSym '!') : r)      -> do (a, r') <- pAtom r; Right (GNot a, r')
      ((_, TWord "not") : r)   -> do (a, r') <- pAtom r; Right (GNot a, r')
      ((_, TSym '(') : r)      -> do
        (a, r1) <- pOr r
        (_, r2) <- expectSym ')' r1
        Right (a, r2)
      ((_, TInt 0) : r)        -> Right (GBit False, r)
      ((_, TInt 1) : r)        -> Right (GBit True, r)
      ((_, TWord p) : r)       -> Right (GParam p, r)
      _ -> errAt ts "expected a guard (0, 1, a parameter, '!e', 'e1 && e2' or 'e1 || e2')"

-- | A gate statement: a named gate, or one of the three literals.
pGateStmt :: GateEnv -> Scope -> [LTok]
          -> Either String (Cmd Cyclo, Scope, [LTok])
pGateStmt env sc ts0 = case ts0 of

  ((_, TWord "mat") : rest) -> do
    (regs, ts1) <- regList rest
    (_, ts2) <- expectSym '{' ts1
    (rows, ts3) <- pRows ts2
    (_, ts4) <- expectSym '}' ts3
    let ts5 = case ts4 of ((_, TSym ';') : r) -> r; _ -> ts4
    (names, ln, d) <- gateRegs sc "mat" regs
    if length rows /= d || any ((/= d) . length) rows
      then errLn ln ("mat over " ++ unwords names ++ " must be " ++ show d
                     ++ "x" ++ show d ++ ", got " ++ show (length rows)
                     ++ " row(s) of width(s) " ++ show (map length rows))
      else Right (Gate rows names, sc, ts5)

  ((_, TWord "diag") : rest) -> do
    (regs, ts1) <- regList rest
    (_, ts2) <- expectSym '(' ts1
    (ss, ts3) <- pScalarList ts2
    (_, ts4) <- expectSym ')' ts3
    (_, ts5) <- expectSym ';' ts4
    (names, ln, d) <- gateRegs sc "diag" regs
    if length ss /= d
      then errLn ln ("diag over " ++ unwords names ++ " needs " ++ show d
                     ++ " entries, got " ++ show (length ss))
      else Right (Gate (diagMat ss) names, sc, ts5)

  ((_, TWord "perm") : rest) -> do
    (regs, ts1) <- regList rest
    (_, ts2) <- expectSym '(' ts1
    (ps, ts3) <- pNatsSpace ts2
    (_, ts4) <- expectSym ')' ts3
    (_, ts5) <- expectSym ';' ts4
    (names, ln, d) <- gateRegs sc "perm" regs
    let imgs = map snd ps
    if length imgs /= d
      then errLn ln ("perm over " ++ unwords names ++ " needs " ++ show d
                     ++ " images, got " ++ show (length imgs))
      else case [ (n, p) | (n, p) <- ps, p >= d ] of
        ((n, p) : _) -> errLn n ("perm image " ++ show p
                                 ++ " out of range 0.." ++ show (d - 1))
        [] | length (nub imgs) /= d ->
               errLn ln "perm image list is not a permutation (repeated image)"
           | otherwise -> Right (Gate (permMat imgs) names, sc, ts5)

  ((ln, TWord nm) : rest) -> case lookup nm env of
    Nothing -> errLn ln ("unknown gate or statement '" ++ nm ++ "'")
    Just m -> do
      (regs, ts1) <- regList rest
      (_, ts2)  <- expectSym ';' ts1
      (names, _, d) <- gateRegs sc ("gate '" ++ nm ++ "'") regs
      if d /= length m
        then errLn ln ("gate '" ++ nm ++ "' has dimension " ++ show (length m)
                       ++ " but registers " ++ unwords names
                       ++ " have total dimension " ++ show d)
        else Right (Gate m names, sc, ts2)

  _ -> errAt ts0 "expected a statement"

-- Entry points

-- | 'parseFileAt', forgetting where the program's text put things.
parseFile :: String -> Either String SFile
parseFile = fmap fst . parseFileAt

-- | A parsed file, and the source positions 'SrcPos' records.
parseFileAt :: String -> Either String (SFile, SrcPos)
parseFileAt src = do
  ts0 <- tokenize src
  let endLn = max 1 (length (lines src))
      ts    = ts0 ++ [(endLn, TEnd)]
  (env, ts1) <- pDecls gateTable ts
  let decls = drop (length gateTable) env
  ((nm, ps, ty, paramLns), ts2) <- pHeader ts1
  (_, ts3) <- expectSym '{' ts2
  let loans = [ Loan (prmName p) (prmDim p) | p <- ps, prmLoan p ]
  (body, ret, retLn, sc, ts4) <- pBody env (newScope ps) ts3
  (_, ts5) <- expectSym '}' ts4
  case ts5 of
    [(_, TEnd)] -> Right ()
    _           -> errAt ts5 "unexpected token after the program"
  -- Every register is dropped or returned: the statics' own rule, reported
  -- here with a line rather than as a context mismatch later.
  let retNames = valueNames ret
      leftover = [ x | (x, _) <- scLive sc, x `notElem` retNames ]
  case leftover of
    (x : _) -> errLn endLn ("register '" ++ x
                            ++ "' is neither dropped nor returned")
    [] -> Right ()
  actual <- tyOfValue sc (lineAt ts4) ret
  if actual /= ty
    then errLn (lineAt ts2)
           ("the program returns " ++ showTy actual
            ++ " but its header declares " ++ showTy ty)
    else Right ( SFile { sfName = nm, sfParams = ps, sfResult = ty
                       , sfDecls = decls, sfBody = loans ++ body
                       , sfReturn = ret }
               , SrcPos { spReturnLine = retLn
                        , spLoanLines = [ (prmName p, ln)
                                        | (p, ln) <- zip ps paramLns, prmLoan p ] } )

tyOfValue :: Scope -> Int -> Value -> Either String Ty
tyOfValue sc ln v = case v of
  VUnit      -> Right TUnit
  VVar x     -> do (_, d) <- lookupReg sc (ln, x); Right (TReg d)
  VPair a b  -> do
    ta <- tyOfValue sc ln a
    tb <- tyOfValue sc ln b
    Right (TTensor ta tb)

showTy :: Ty -> String
showTy TUnit          = "1"
showTy (TReg d)       = "[" ++ show d ++ "]"
showTy (TTensor a b)  = showTyL a ++ " * " ++ showTy b
  where showTyL t@(TTensor _ _) = "(" ++ showTy t ++ ")"
        showTyL t               = showTy t

-- | The machine's view of a file: the ordinary input registers and the flat
-- command list (loans hoisted to its head).
parseProgram :: String -> Either String (VisSpec, Prog Cyclo)
parseProgram src = do
  f <- parseFile src
  Right (sfVis f, sfBody f)

-- Rendering

-- | An exact scalar back to .s text, at tower levels 1 to 4.
renderScalar :: Cyclo -> String
renderScalar (Cyclo k cs)
  | k == 1    = case cs of { (c : _) -> showRat c ; [] -> "0" }
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

-- | The first named gate whose matrix equals the given one.
gateNameOf :: GateEnv -> Matrix Cyclo -> Maybe String
gateNameOf env g = case [ nm | (nm, m) <- env, m == g ] of
  (nm : _) -> Just nm
  []       -> Nothing

-- | The diagonal entries, when the matrix is square and zero off-diagonal.
diagOf :: Matrix Cyclo -> Maybe [Cyclo]
diagOf g
  | not (null g), all ((== n) . length) g
  , and [ g !! i !! j == 0 | i <- [0 .. n - 1], j <- [0 .. n - 1], i /= j ]
  = Just [ g !! i !! i | i <- [0 .. n - 1] ]
  | otherwise = Nothing
  where n = length g

-- | The image list, when the matrix is a permutation matrix.
permOf :: Matrix Cyclo -> Maybe [Int]
permOf g
  | not (null g), all ((== n) . length) g
  , Just imgs <- mapM colImg [0 .. n - 1]
  , length (nub imgs) == n
  = Just imgs
  | otherwise = Nothing
  where
    n = length g
    colImg j = case [ i | i <- [0 .. n - 1], g !! i !! j /= 0 ] of
      [i] | g !! i !! j == 1 -> Just i
      _                      -> Nothing

-- | The basis index of a state vector that is exactly one ket.
basisKet :: StateV Cyclo -> Maybe Int
basisKet psi = case [ i | (i, c) <- zip [0 ..] psi, c /= 0 ] of
  [i] | psi !! i == 1 -> Just i
  _                   -> Nothing

renderCmd :: Cmd Cyclo -> String
renderCmd = renderCmdWith gateTable

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

renderValue :: Value -> String
renderValue VUnit      = "()"
renderValue (VVar x)   = x
renderValue v          = "(" ++ intercalate ", " (map renderValue (flatten v)) ++ ")"
  where
    flatten (VPair a b) = a : flatten b
    flatten w           = [w]

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

renderGateLit :: Matrix Cyclo -> String
renderGateLit m
  | Just ds <- diagOf m = "diag (" ++ intercalate ", " (map renderScalar ds) ++ ")"
  | Just ps <- permOf m = "perm (" ++ unwords (map show ps) ++ ")"
  | otherwise = "mat { "
      ++ intercalate " ; " [ intercalate ", " (map renderScalar row) | row <- m ]
      ++ " }"

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

-- | Legacy renderer: the flat program as a file named @p@, returning
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

-- | Map a program's scalars into another type.
mapProg :: (a -> b) -> Prog a -> Prog b
mapProg f = map go
  where
    go c = case c of
      New x d        -> New x d
      NewState x d s -> NewState x d (map f s)
      Loan x d       -> Loan x d
      Gate g xs      -> Gate (map (map f) g) xs
      Lift p x b     -> Lift p x b
      IfBit p t e    -> IfBit p (mapProg f t) (mapProg f e)
      Drop xs        -> Drop xs
