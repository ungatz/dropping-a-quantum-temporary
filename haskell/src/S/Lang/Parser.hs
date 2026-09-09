-- Parser.hs: the .s concrete syntax, hand-rolled on base alone, total, with
-- a line number on every error, plus the pretty-printer renderProgram. The
-- one-page reference is programs/SYNTAX.md; S.Test.Parser checks parse .
-- render is the identity on the abstract syntax. Scalars are exact
-- cyclotomic elements only, no float syntax. Static checks below report a
-- line and never fall back on a silent default.

module S.Lang.Parser (parseProgram, renderProgram, renderCmd, gateTable, mapProg) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)
import Data.List (intercalate, nub)
import Data.Ratio ((%))
import S.Lang.Ring (showRat, showAmp)
import S.Lang.Cyclo
import S.Lang.Gates
import S.Lang.QState (Matrix, norm2S)
import S.Lang.Syntax

-- Tokens

data Tok = TWord String | TInt Integer | TSym Char | TEnd deriving (Eq, Show)
type LTok = (Int, Tok)

symChars :: String
symChars = ":;,@(){}=^*/+-"

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
          | isAlpha c = let (ws, rest) = span isAlphaNum (c : cs)
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

-- The gate set

-- | The named gates a .s file may write; H and HC name the same Hadamard
-- matrix over the tower.
gateTable :: [(String, Matrix Cyclo)]
gateTable =
  [ ("H", gHC), ("HC", gHC)
  , ("X", gX), ("Z", gZ)
  , ("CX", gCX), ("CCX", gCCX), ("Swap", gSwap)
  , ("T", gT), ("S", gS)
  , ("tilt", gTilt), ("READ3", gREAD3), ("Diff", gDiff)
  ]

-- Statements

type Env = [(String, Int)]

lookupReg :: Env -> (Int, String) -> Either String Int
lookupReg env (n, x) = case lookup x env of
  Just d  -> Right d
  Nothing -> errLn n ("unknown register '" ++ x ++ "'")

checkFresh :: Env -> (Int, String) -> Either String ()
checkFresh env (n, x)
  | x `elem` map fst env = errLn n ("register '" ++ x ++ "' already exists")
  | otherwise            = Right ()

checkDim :: (Int, Int) -> Either String ()
checkDim (n, d)
  | d < 2     = errLn n "register dimension must be at least 2"
  | otherwise = Right ()

pStmts :: Env -> [String] -> [LTok]
       -> Either String ([Cmd Cyclo], [LTok])
pStmts env bits ts = case ts of
  ((_, TEnd) : _)     -> Right ([], ts)
  ((_, TSym '}') : _) -> Right ([], ts)
  _ -> do
    (c, env1, bits1, ts1) <- pStmt env bits ts
    (cs, ts2) <- pStmts env1 bits1 ts1
    Right (c : cs, ts2)

pStmt :: Env -> [String] -> [LTok]
      -> Either String (Cmd Cyclo, Env, [String], [LTok])
pStmt env bits ts0@((_, TWord w) : rest) = case w of

  "new" -> do
    (nx@(_, x), ts1) <- identL rest
    (_, ts2)  <- expectSym ':' ts1
    (nd@(_, d), ts3) <- natL ts2
    (_, ts4)  <- expectSym ';' ts3
    checkFresh env nx
    checkDim nd
    Right (New x d, env ++ [(x, d)], bits, ts4)

  "newdirty" -> do
    (nx@(ln, x), ts1) <- identL rest
    (_, ts2)  <- expectSym ':' ts1
    (nd@(_, d), ts3) <- natL ts2
    (_, ts4)  <- expectSym '@' ts3
    (_, ts5)  <- expectSym '(' ts4
    (amps, ts6) <- pScalarList ts5
    (_, ts7)  <- expectSym ')' ts6
    (_, ts8)  <- expectSym ';' ts7
    checkFresh env nx
    checkDim nd
    if length amps /= d
      then errLn ln ("newdirty " ++ x ++ ":" ++ show d ++ " needs " ++ show d
                     ++ " amplitudes, got " ++ show (length amps))
      -- The state named by hand must be a unit vector: every construct of
      -- the language is an isometry, and an unnormalised state would make a
      -- run's selection weights sum to something other than 1.
      else if norm2S amps /= 1
        then errLn ln ("newdirty " ++ x ++ ":" ++ show d ++ " must name a unit"
                       ++ " state, but the vector given has squared norm "
                       ++ showAmp (norm2S amps) ++ ", not 1")
      else Right (NewDirty x d amps, env ++ [(x, d)], bits, ts8)

  "gate" -> do
    ((ln, nm), ts1) <- identL rest
    (regs, ts2) <- regList ts1
    (_, ts3)  <- expectSym ';' ts2
    mat  <- case lookup nm gateTable of
      Just m  -> Right m
      Nothing -> errLn ln ("unknown gate '" ++ nm ++ "'")
    dims <- mapM (lookupReg env) regs
    let names = map snd regs
    if length (nub names) /= length names
      then errLn ln "repeated register in gate"
      else if product dims /= length mat
        then errLn ln ("gate '" ++ nm ++ "' has dimension " ++ show (length mat)
                       ++ " but registers " ++ unwords names
                       ++ " have total dimension " ++ show (product dims))
        else Right (Gate mat names, env, bits, ts3)

  "phase" -> do
    (_, ts1) <- expectSym '(' rest
    (z, ts2) <- pScalar ts1
    (_, ts3) <- expectSym ')' ts2
    (regs, ts4) <- regList ts3
    (_, ts5) <- expectSym ';' ts4
    dims <- mapM (lookupReg env) regs
    let names = map snd regs
        ln    = lineOf regs
    if length (nub names) /= length names
      then errLn ln "repeated register in phase"
      else case dims of
        [2]    -> Right (Gate (gPhase z) names, env, bits, ts5)
        [2, 2] -> Right (Gate (gCPhase z) names, env, bits, ts5)
        _      -> errLn ln "phase takes one or two 2-level registers"

  "mat" -> do
    (regs, ts1) <- regList rest
    (_, ts2) <- expectSym '{' ts1
    (rows, ts3) <- pRows ts2
    (_, ts4) <- expectSym '}' ts3
    let ts5 = case ts4 of ((_, TSym ';') : r) -> r; _ -> ts4
    (names, ln, d) <- gateRegs env "mat" regs
    if length rows /= d || any ((/= d) . length) rows
      then errLn ln ("mat over " ++ unwords names ++ " must be " ++ show d
                     ++ "x" ++ show d ++ ", got " ++ show (length rows)
                     ++ " row(s) of width(s) " ++ show (map length rows))
      else Right (Gate rows names, env, bits, ts5)

  "diag" -> do
    (regs, ts1) <- regList rest
    (_, ts2) <- expectSym '(' ts1
    (ss, ts3) <- pScalarList ts2
    (_, ts4) <- expectSym ')' ts3
    (_, ts5) <- expectSym ';' ts4
    (names, ln, d) <- gateRegs env "diag" regs
    if length ss /= d
      then errLn ln ("diag over " ++ unwords names ++ " needs " ++ show d
                     ++ " entries, got " ++ show (length ss))
      else Right (Gate (diagMat ss) names, env, bits, ts5)

  "perm" -> do
    (regs, ts1) <- regList rest
    (_, ts2) <- expectSym '(' ts1
    (ps, ts3) <- pNatsSpace ts2
    (_, ts4) <- expectSym ')' ts3
    (_, ts5) <- expectSym ';' ts4
    (names, ln, d) <- gateRegs env "perm" regs
    let imgs = map snd ps
    if length imgs /= d
      then errLn ln ("perm over " ++ unwords names ++ " needs " ++ show d
                     ++ " images, got " ++ show (length imgs))
      else case [ (n, p) | (n, p) <- ps, p >= d ] of
        ((n, p) : _) -> errLn n ("perm image " ++ show p
                                 ++ " out of range 0.." ++ show (d - 1))
        [] | length (nub imgs) /= d ->
               errLn ln "perm image list is not a permutation (repeated image)"
           | otherwise -> Right (Gate (permMat imgs) names, env, bits, ts5)

  "lift" -> do
    ((_, p), ts1) <- identL rest
    (_, ts2) <- expectSym '=' ts1
    (_, ts3) <- expectWord "meas" ts2
    (nx@(ln, x), ts4) <- identL ts3
    (_, ts5) <- expectWord "in" ts4
    (_, ts6) <- expectSym '{' ts5
    (lvls, ts7) <- pNatList ts6
    (_, ts8) <- expectSym '}' ts7
    (_, ts9) <- expectSym ';' ts8
    d <- lookupReg env nx
    let block = map snd lvls
    mapM_ (\(n, l) -> if l < 0 || l >= d
                        then errLn n ("level " ++ show l ++ " out of range for '"
                                      ++ x ++ "' (dimension " ++ show d ++ ")")
                        else Right ()) lvls
    if length (nub block) /= length block
      then errLn ln "repeated level in lift block"
      else Right (Lift p x block, env, p : bits, ts9)

  "if" -> do
    ((lp, p), ts1) <- identL rest
    (_, ts2) <- expectSym '{' ts1
    (thn, ts3) <- pStmts env bits ts2
    (_, ts4) <- expectSym '}' ts3
    (_, ts5) <- expectWord "else" ts4
    (_, ts6) <- expectSym '{' ts5
    (els, ts7) <- pStmts env bits ts6
    (_, ts8) <- expectSym '}' ts7
    let ts9 = case ts8 of ((_, TSym ';') : r) -> r; _ -> ts8
    if p `notElem` bits
      then errLn lp ("bit '" ++ p ++ "' has not been bound by a lift")
      else Right (IfBit p thn els, env, bits, ts9)

  "drop" -> do
    (nx@(_, x), ts1) <- identL rest
    (_, ts2) <- expectSym ';' ts1
    _ <- lookupReg env nx
    -- The dropped name leaves the environment, so a later statement naming
    -- it fails with "unknown register": the affine discipline of the core,
    -- enforced at the surface.  Re-allocating the name afterwards is legal,
    -- and is how temporary reuse is written.
    Right (Drop x, filter ((/= x) . fst) env, bits, ts2)

  "vis" -> errAt ts0 "'vis' is only allowed as the first statement"
  _     -> errAt ts0 ("unknown statement '" ++ w ++ "'")

pStmt _ _ ts = errAt ts "expected a statement"

pScalarList :: [LTok] -> Either String ([Cyclo], [LTok])
pScalarList ts0 = do
  (s, ts1) <- pScalar ts0
  go [s] ts1
  where
    go acc ((_, TSym ',') : r) = do (s, r') <- pScalar r; go (acc ++ [s]) r'
    go acc ts = Right (acc, ts)

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

-- | Register checks shared by mat, diag and perm: distinct known registers.
-- Returns the names, a line to report errors at, and the product dimension.
gateRegs :: Env -> String -> [(Int, String)] -> Either String ([String], Int, Int)
gateRegs env what regs = do
  dims <- mapM (lookupReg env) regs
  let names = map snd regs
      ln    = lineOf regs
  if length (nub names) /= length names
    then errLn ln ("repeated register in " ++ what)
    else Right (names, ln, product dims)

diagMat :: [Cyclo] -> Matrix Cyclo
diagMat ss = [ [ if i == j then ss !! i else 0 | j <- [0 .. d - 1] ]
             | i <- [0 .. d - 1] ]
  where d = length ss

-- | |j> -> |imgs_j>: column j has its 1 in row imgs_j.
permMat :: [Int] -> Matrix Cyclo
permMat imgs = [ [ if imgs !! j == i then 1 else 0 | j <- [0 .. d - 1] ]
               | i <- [0 .. d - 1] ]
  where d = length imgs

pNatList :: [LTok] -> Either String ([(Int, Int)], [LTok])
pNatList ts0 = do
  (v, ts1) <- natL ts0
  go [v] ts1
  where
    go acc ((_, TSym ',') : r) = do (v, r') <- natL r; go (acc ++ [v]) r'
    go acc ts = Right (acc, ts)

-- The vis line

pVis :: [LTok] -> Either String (VisSpec, [LTok])
pVis ts0 = case ts0 of
  ((_, TWord "vis") : rest) -> do
    (decls, ts1) <- go rest
    (_, ts2) <- expectSym ';' ts1
    let names = [ x | ((_, x), _) <- decls ]
    if length (nub names) /= length names
      then errLn (lineOf (map fst decls)) "repeated register in vis"
      else Right ([ (x, d) | ((_, x), (_, d)) <- decls ], ts2)
  _ -> errAt ts0 "program must begin with 'vis name:dim, ...;'"
  where
    go ts = do
      (nx, ts1) <- identL ts
      (_, ts2) <- expectSym ':' ts1
      (nd, ts3) <- natL ts2
      checkDim nd
      case ts3 of
        ((_, TSym ',') : r) -> do (more, ts4) <- go r; Right ((nx, nd) : more, ts4)
        _ -> Right ([(nx, nd)], ts3)

-- Entry points

parseProgram :: String -> Either String (VisSpec, Prog Cyclo)
parseProgram src = do
  ts0 <- tokenize src
  let endLn = max 1 (length (lines src))
      ts    = ts0 ++ [(endLn, TEnd)]
  (vis, ts1) <- pVis ts
  (prog, ts2) <- pStmts vis [] ts1
  case ts2 of
    [(_, TEnd)] -> Right (vis, prog)
    _           -> errAt ts2 "unexpected token after program"

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
gateNameOf :: Matrix Cyclo -> Maybe String
gateNameOf g = case [ nm | (nm, m) <- gateTable, m == g ] of
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

renderCmd :: Cmd Cyclo -> String
renderCmd c = case c of
  New x d        -> "new " ++ x ++ ":" ++ show d ++ ";"
  NewDirty x d s -> "newdirty " ++ x ++ ":" ++ show d ++ " @ ("
                    ++ intercalate ", " (map renderScalar s) ++ ");"
  Gate g xs -> case gateNameOf g of
    Just nm -> "gate " ++ nm ++ " " ++ unwords xs ++ ";"
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
  Lift p x b -> "lift " ++ p ++ " = meas " ++ x ++ " in {"
                ++ intercalate "," (map show b) ++ "};"
  IfBit p t e -> "if " ++ p ++ " { " ++ inline t ++ "} else { " ++ inline e ++ "}"
  Drop x -> "drop " ++ x ++ ";"
  where
    inline = concatMap (\s -> renderCmd s ++ " ")

-- | Emit valid .s text; @parseProgram . renderProgram@ is the identity on
-- the abstract syntax.
renderProgram :: VisSpec -> Prog Cyclo -> String
renderProgram vis prog =
  unlines (("vis " ++ intercalate ", " [ x ++ ":" ++ show d | (x, d) <- vis ] ++ ";")
           : map renderCmd prog)

-- | Map a program's scalars into another type.
mapProg :: (a -> b) -> Prog a -> Prog b
mapProg f = map go
  where
    go c = case c of
      New x d        -> New x d
      NewDirty x d s -> NewDirty x d (map f s)
      Gate g xs      -> Gate (map (map f) g) xs
      Lift p x b     -> Lift p x b
      IfBit p t e    -> IfBit p (mapProg f t) (mapProg f e)
      Drop x         -> Drop x
