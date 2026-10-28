-- Drop.Lang.Parser: reading a .s file, with a line number on every refusal.
--
-- Question: Which texts are programs, and what does each one say?
-- Answer:   Exactly the texts the printed grammar of programs/SYNTAX.md describes. tokenize cuts
--           the text into words, integers and symbols, each with its line; one parser per
--           construct of the grammar reads them, and each refusal names the line. A header
--           parameter marked loan is hoisted to a Loan command at the head of the body, before
--           any new, so the machine's allocation order puts it among the inputs. Three statements
--           are written as the paper abbreviates them: a gate acts in place (U v;), a drop binds
--           nothing (drop v;), an allocation names its register once (new t : [d] @ psi;); the
--           explicit-binding spelling of any of the three is refused with the printed form to
--           write instead. A block y = { ...; return v }; is the sequencing operator: its
--           statements are spliced into the enclosing body, y names the wire v names, and the
--           parameters its lifts bind leave scope at its closing brace. Before a file is accepted,
--           every register is dropped or returned and the returned value has the header's type.
--           parseFile after renderFile is the identity on SFile: shown below on every program in
--           programs/.
-- Paper:    fig:syntax (the grammar), sec:lang:syntax (the syntax), app:surface (the surface forms
--           the parser accepts: blocks, abbreviations, renaming).
-- Shapes:   SrcPos  where the text put two things the checks report: the line of the body's return
--                   and the header line of each loan. Kept apart from SFile, which has no lines.

module Drop.Lang.Parser
  ( SrcPos (..)
  , parseFile
  , parseFileAt
  , parseProgram
  , parseTyped
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)
import Data.List (nub)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Ratio ((%))
import Drop.Lang.Scalar
import Drop.Lang.State (Matrix, StateV, dimensionProduct, norm2S)
import Drop.Lang.Flat
import Drop.Lang.Render
import Drop.Lang.Elab (flatToProgramR)
import Drop.Lang.Syntax (Program (..), Ty (..), Value (..), valueNames)

-- Tokens --------------------------------------------------------------------

-- | A token: a word, a whole number, a one-character symbol, or the end of the input.
data Tok = TWord String | TInt Integer | TSym Char | TEnd deriving (Eq, Show)
-- | A token with the line it stands on.
type LTok = (Int, Tok)

-- A token carries its line.
-- >>> (3, TWord "x") :: LTok
-- (3,TWord "x")

-- >>> [TWord "drop", TInt 2, TSym ';', TEnd]
-- [TWord "drop",TInt 2,TSym ';',TEnd]

-- | The characters that are symbols, one token each.
symChars :: String
symChars = ":;,@(){}[]=^*/+-|<>!&"

-- >>> [ c | c <- "new t : [2];", c `elem` symChars ]
-- ":[];"

-- | Whether a character can begin a name.
isIdentStart :: Char -> Bool
isIdentStart c = isAlpha c || c == '_'

-- >>> map isIdentStart "a_1"
-- [True,True,False]

-- | Whether a character can continue a name.
isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_'

-- >>> map isIdentChar "a_1 "
-- [True,True,True,False]

-- | Cut a text into tokens, each with its line. A comment (from two hyphens to the
-- end of the line) is dropped; a character no token starts with is refused.
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

-- The smallest text, then a comment and a second line, then a character no token starts with.
-- >>> tokenize "drop x;"
-- Right [(1,TWord "drop"),(1,TWord "x"),(1,TSym ';')]

-- >>> tokenize "H x; -- a comment\nreturn x"
-- Right [(1,TWord "H"),(1,TWord "x"),(1,TSym ';'),(2,TWord "return"),(2,TWord "x")]

-- >>> fmap (map snd) (tokenize "new t : [2] @ |0>;")
-- Right [TWord "new",TWord "t",TSym ':',TSym '[',TInt 2,TSym ']',TSym '@',TSym '|',TInt 0,TSym '>',TSym ';']

-- >>> tokenize "H x;\n  y ? z"
-- Left "line 2: unexpected character '?'"

-- | A token as an error message quotes it.
showTok :: Tok -> String
showTok (TWord w) = "'" ++ w ++ "'"
showTok (TInt n)  = show n
showTok (TSym c)  = "'" ++ [c] ++ "'"
showTok TEnd      = "end of input"

-- >>> map showTok [TWord "x", TInt 2, TSym ';', TEnd]
-- ["'x'","2","';'","end of input"]

-- | Refuse at the first token of the list, naming it; the line is that token's.
errAt :: [LTok] -> String -> Either String a
errAt ((n, TEnd) : _) msg =
  Left ("line " ++ show n ++ ": " ++ msg ++ " (found end of input)")
errAt ((n, t) : _) msg =
  Left ("line " ++ show n ++ ": " ++ msg ++ " (found " ++ showTok t ++ ")")
errAt [] msg = Left ("line 1: " ++ msg)

-- >>> errAt [(3, TWord "x")] "expected a name" :: Either String ()
-- Left "line 3: expected a name (found 'x')"

-- >>> errAt [(5, TEnd)] "expected a name" :: Either String ()
-- Left "line 5: expected a name (found end of input)"

-- >>> errAt [] "expected a name" :: Either String ()
-- Left "line 1: expected a name"

-- | Refuse at a given line.
errLn :: Int -> String -> Either String a
errLn n msg = Left ("line " ++ show n ++ ": " ++ msg)

-- >>> errLn 7 "register dimension must be at least 2" :: Either String ()
-- Left "line 7: register dimension must be at least 2"

-- | The line of the first token, or line 1 when there is none.
lineAt :: [LTok] -> Int
lineAt ((n, _) : _) = n
lineAt []           = 1

-- >>> lineAt [(4, TWord "x")]
-- 4
-- >>> lineAt []
-- 1

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

-- >>> branchBinder (Gate [[0, 1], [1, 0]] ["x"] :: Cmd Cyclo)
-- Nothing

-- >>> branchBinder (Drop ["x"] :: Cmd Cyclo)
-- Just "drop"

-- A binder inside the arm of an if is found at any depth.
-- >>> branchBinder (IfBit (GBit True) [Gate [[0, 1], [1, 0]] ["x"]] [Lift "m" "x" [0]] :: Cmd Cyclo)
-- Just "lift"

-- Primitive parsers ---------------------------------------------------------

-- | The next token must be this symbol; it is consumed.
expectSym :: Char -> [LTok] -> Either String ((), [LTok])
expectSym c ts = case ts of
  ((_, TSym c') : r) | c' == c -> Right ((), r)
  _ -> errAt ts ("expected '" ++ [c] ++ "'")

-- >>> tokenize "; x" >>= expectSym ';'
-- Right ((),[(1,TWord "x")])

-- >>> tokenize "x" >>= expectSym ';'
-- Left "line 1: expected ';' (found 'x')"

-- >>> expectSym ';' []
-- Left "line 1: expected ';'"

-- | The next token must be this word; it is consumed.
expectWord :: String -> [LTok] -> Either String ((), [LTok])
expectWord w ts = case ts of
  ((_, TWord w') : r) | w' == w -> Right ((), r)
  _ -> errAt ts ("expected '" ++ w ++ "'")

-- >>> tokenize "prog f" >>= expectWord "prog"
-- Right ((),[(1,TWord "f")])

-- >>> tokenize "f" >>= expectWord "prog"
-- Left "line 1: expected 'prog' (found 'f')"

-- | A name, with the line it stands on.
identL :: [LTok] -> Either String ((Int, String), [LTok])
identL ts = case ts of
  ((n, TWord w) : r) -> Right ((n, w), r)
  _ -> errAt ts "expected a name"

-- >>> tokenize "x y" >>= identL
-- Right ((1,"x"),[(1,TWord "y")])

-- >>> tokenize "7" >>= identL
-- Left "line 1: expected a name (found 7)"

-- | A whole number, with the line it stands on.
natL :: [LTok] -> Either String ((Int, Int), [LTok])
natL ts = case ts of
  ((n, TInt v) : r)
    | v < 0 || v > toInteger (maxBound :: Int) ->
        errLn n ("integer " ++ show v ++ " is outside the supported range 0.."
                 ++ show (maxBound :: Int))
    | otherwise -> Right ((n, fromInteger v), r)
  _ -> errAt ts "expected an integer"

-- >>> tokenize "7 y" >>= natL
-- Right ((1,7),[(1,TWord "y")])

-- >>> tokenize "y" >>= natL
-- Left "line 1: expected an integer (found 'y')"

-- | A gate's registers: a value (unit, a name or nested pairs), or the
-- whitespace-separated names used by the program files.
regList :: [LTok] -> Either String ([(Int, String)], [LTok])
regList ts0 = case ts0 of
  ((n, TSym '(') : _) -> do
    (v, rest) <- pValue ts0
    Right ([(n, x) | x <- valueNames v], rest)
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

-- The registers stop at the first token that is not a name.
-- >>> tokenize "x y z ;" >>= regList
-- Right ([(1,"x"),(1,"y"),(1,"z")],[(1,TSym ';')])

-- >>> tokenize "x" >>= regList
-- Right ([(1,"x")],[])

-- >>> tokenize "; x" >>= regList
-- Left "line 1: expected a register name (found ';')"

-- Types, values and patterns ------------------------------------------------

-- | @A ::= 1 | [d] | A * B@, with @*@ to the right.
pTy :: [LTok] -> Either String (Ty, [LTok])
pTy ts0 = do
  (a, ts1) <- pTyAtom ts0
  case ts1 of
    ((_, TSym '*') : r) -> do (b, ts2) <- pTy r; Right (TTensor a b, ts2)
    _                   -> Right (a, ts1)

-- >>> tokenize "[2] * [2]" >>= pTy
-- Right (TTensor (TReg 2) (TReg 2),[])

-- >>> tokenize "1" >>= pTy
-- Right (TUnit,[])

-- The product is to the right, and parentheses regroup it.
-- >>> tokenize "[2] * [3] * [2]" >>= pTy
-- Right (TTensor (TReg 2) (TTensor (TReg 3) (TReg 2)),[])

-- >>> tokenize "([2] * [3]) * [2]" >>= pTy
-- Right (TTensor (TTensor (TReg 2) (TReg 3)) (TReg 2),[])

-- >>> tokenize "[2] *" >>= pTy
-- Left "line 1: expected a type ('1', '[d]' or 'A * B')"

-- | @1@, @[d]@ with @d@ at least 2, or a parenthesised type.
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

-- >>> tokenize "[3]" >>= pTyAtom
-- Right (TReg 3,[])

-- >>> tokenize "[1]" >>= pTyAtom
-- Left "line 1: register dimension must be at least 2"

-- >>> tokenize "*" >>= pTyAtom
-- Left "line 1: expected a type ('1', '[d]' or 'A * B') (found '*')"

-- | @v ::= x | () | (v1, ..., vn)@; a tuple of several is right-nested.
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
        -- impossible: commaSep returns at least one value
        _   -> Right (foldr1 VPair vs, r2)
  _ -> errAt ts "expected a value (a register name, '()' or a tuple)"

-- >>> tokenize "x" >>= pValue
-- Right (VVar "x",[])

-- >>> tokenize "()" >>= pValue
-- Right (VUnit,[])

-- >>> tokenize "(x, y, z)" >>= pValue
-- Right (VPair (VVar "x") (VPair (VVar "y") (VVar "z")),[])

-- >>> tokenize "(x)" >>= pValue
-- Right (VVar "x",[])

-- >>> tokenize ";" >>= pValue
-- Left "line 1: expected a value (a register name, '()' or a tuple) (found ';')"

-- | One or more of what @p@ reads, separated by commas.
commaSep :: ([LTok] -> Either String (b, [LTok])) -> [LTok]
         -> Either String ([b], [LTok])
commaSep p ts0 = do
  (x, ts1) <- p ts0
  go [x] ts1
  where
    go acc ((_, TSym ',') : r) = do (x, r') <- p r; go (acc ++ [x]) r'
    go acc ts                  = Right (acc, ts)

-- >>> fmap (\(xs, rest) -> (map snd xs, length rest)) (tokenize "1, 2, 3 ;" >>= commaSep natL)
-- Right ([1,2,3],1)

-- >>> fmap (\(xs, rest) -> (map snd xs, length rest)) (tokenize "1 ;" >>= commaSep natL)
-- Right ([1],1)

-- >>> tokenize ", 2" >>= commaSep natL
-- Left "line 1: expected an integer (found ',')"

-- Scalars -------------------------------------------------------------------

-- | A scalar: factors multiplied with @*@, and those products added and subtracted.
pScalar :: [LTok] -> Either String (Cyclo, [LTok])
pScalar ts0 = do
  (t1, ts1) <- pProduct ts0
  goSum t1 ts1
  where
    goSum acc ts = case ts of
      ((_, TSym '+') : r) -> do (t, r') <- pProduct r; goSum (acc + t) r'
      ((_, TSym '-') : r) -> do (t, r') <- pProduct r; goSum (acc - t) r'
      _ -> Right (acc, ts)

-- Rational, rational over the root of two, a power of the eighth root of unity, a product, a sum, and a refusal.
-- >>> fmap fst (tokenize "-1/2" >>= pScalar)
-- Right (Cyclo 1 [(-1) % 2])

-- >>> fmap fst (tokenize "1/rt2" >>= pScalar)
-- Right (Cyclo 3 [0 % 1,1 % 2,0 % 1,(-1) % 2])

-- >>> fmap fst (tokenize "z8^3" >>= pScalar)
-- Right (Cyclo 3 [0 % 1,0 % 1,0 % 1,1 % 1])

-- >>> fmap fst (tokenize "2*3" >>= pScalar) == Right 6
-- True

-- >>> fmap fst (tokenize "1+i" >>= pScalar) == Right (1 + iC)
-- True

-- >>> tokenize "1/0" >>= pScalar
-- Left "line 1: division by zero in scalar"

-- | Factors multiplied with @*@.
pProduct :: [LTok] -> Either String (Cyclo, [LTok])
pProduct ts0 = do
  (f1, ts1) <- pFactor ts0
  go f1 ts1
  where
    go acc ((_, TSym '*') : r) = do (f, r') <- pFactor r; go (acc * f) r'
    go acc ts = Right (acc, ts)

-- >>> fmap fst (tokenize "2*3*4" >>= pProduct)
-- Right (Cyclo 1 [24 % 1])

-- >>> fmap fst (tokenize "i*i" >>= pProduct) == Right (-1)
-- True

-- | One factor: an integer, @n/m@, @n/rt2@, @i@, @z8@ or @z16@ (the last two with an
-- optional @^j@), or a negated factor.
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

-- >>> fmap fst (tokenize "7" >>= pFactor)
-- Right (Cyclo 1 [7 % 1])

-- >>> fmap fst (tokenize "-i" >>= pFactor) == Right (negate iC)
-- True

-- >>> fmap fst (tokenize "z16" >>= pFactor) == Right (zetaC 4)
-- True

-- >>> fmap fst (tokenize "z8^8" >>= pFactor)
-- Right (Cyclo 1 [1 % 1])

-- >>> tokenize "z8^" >>= pFactor
-- Left "line 1: malformed scalar: expected an integer exponent"

-- >>> tokenize "+" >>= pFactor
-- Left "line 1: malformed scalar (found '+')"

-- | Scalars separated by commas.
pScalarList :: [LTok] -> Either String ([Cyclo], [LTok])
pScalarList = commaSep pScalar

-- >>> fmap (\(xs, rest) -> (xs == [1, 0, -1], length rest)) (tokenize "1, 0, -1 )" >>= pScalarList)
-- Right (True,1)

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

-- >>> fmap (\(rows, rest) -> (map (map (== 1)) rows, length rest)) (tokenize "1, 0 ; 0, 1 }" >>= pRows)
-- Right ([[True,False],[False,True]],1)

-- A trailing semicolon before the brace is allowed.
-- >>> fmap (\(rows, rest) -> (length rows, length rest)) (tokenize "1, 0 ; 0, 1 ; }" >>= pRows)
-- Right (2,1)

-- | One or more space-separated naturals: a perm image list.
pNatsSpace :: [LTok] -> Either String ([(Int, Int)], [LTok])
pNatsSpace ts0 = do
  (v, ts1) <- natL ts0
  go [v] ts1
  where
    go acc ts@((_, TInt _) : _) = do (v, r) <- natL ts; go (acc ++ [v]) r
    go acc ts = Right (acc, ts)

-- >>> fmap (\(xs, rest) -> (map snd xs, length rest)) (tokenize "1 2 0 )" >>= pNatsSpace)
-- Right ([1,2,0],1)

-- >>> tokenize ")" >>= pNatsSpace
-- Left "line 1: expected an integer (found ')')"

-- | Whole numbers separated by commas.
pNatList :: [LTok] -> Either String ([(Int, Int)], [LTok])
pNatList = commaSep natL

-- >>> fmap (\(xs, rest) -> (map snd xs, length rest)) (tokenize "1, 2 }" >>= pNatList)
-- Right ([1,2],1)

-- Gates written out --------------------------------------------------------
--
-- The matrices a diag and a perm statement stand for. Drop.Lang.Render has the
-- inverses: diagOf reads a diagonal back from a matrix, permOf a permutation.

-- | The diagonal matrix with the given entries.
diagMat :: [Cyclo] -> Matrix Cyclo

-- impossible: i ranges over 0 .. d - 1 and d is the length of ss
diagMat ss = [ [ if i == j then ss !! i else 0 | j <- [0 .. d - 1] ]
             | i <- [0 .. d - 1] ]
  where d = length ss

-- >>> diagMat [1, 2]
-- [[Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]],[Cyclo 1 [0 % 1],Cyclo 1 [2 % 1]]]
-- >>> diagMat [1, 2, 3] == [[1, 0, 0], [0, 2, 0], [0, 0, 3]]
-- True

-- | |j> -> |imgs_j>: column j has its 1 in row imgs_j.
permMat :: [Int] -> Matrix Cyclo

-- impossible: j ranges over 0 .. d - 1 and d is the length of imgs
permMat imgs = [ [ if imgs !! j == i then 1 else 0 | j <- [0 .. d - 1] ]
               | i <- [0 .. d - 1] ]
  where d = length imgs

-- >>> permMat [1, 0]
-- [[Cyclo 1 [0 % 1],Cyclo 1 [1 % 1]],[Cyclo 1 [1 % 1],Cyclo 1 [0 % 1]]]
-- >>> permMat [1, 2, 0] == [[0, 0, 1], [1, 0, 0], [0, 1, 0]]
-- True

-- Scope ---------------------------------------------------------------------

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

-- | The scope at the head of a body: the parameters are live and nothing else has happened.
newScope :: [Param] -> Scope
newScope ps = Scope [ (prmName p, prmDim p) | p <- ps ] [] [] []
                    (map prmName ps) []

-- A new scope has the inputs live, every name bound, and nothing dropped.
-- >>> scLive (newScope [Param "x" 2 False, Param "a" 3 True])
-- [("x",2),("a",3)]
-- >>> scAllNames (newScope [Param "x" 2 False, Param "y" 3 False])
-- ["x","y"]
-- >>> scDropped (newScope [Param "x" 2 False])
-- []

-- | A surface name resolved to the wire it stands for.
resolve :: Scope -> String -> String
resolve sc x = maybe x id (lookup x (scAlias sc))

-- >>> resolve (newScope []) "y"
-- "y"

-- >>> resolve ((newScope []) { scAlias = [("y", "x")] }) "y"
-- "x"

-- | A new live register.
bindReg :: String -> Int -> Scope -> Scope
bindReg x d sc = sc { scLive = scLive sc ++ [(x, d)]
                    , scAllNames = scAllNames sc ++ [x] }

-- >>> scLive (bindReg "t" 2 (newScope [Param "x" 2 False]))
-- [("x",2),("t",2)]

-- | A dropped name leaves the live set and is remembered, so that naming it
-- again is an error with a reason rather than "unknown register".
dropRegs :: [String] -> Scope -> Scope
dropRegs xs sc = sc { scLive    = filter ((`notElem` xs) . fst) (scLive sc)
                    , scDropped = scDropped sc ++ xs }

-- >>> let sc = dropRegs ["x"] (newScope [Param "x" 2 False]) in (scLive sc, scDropped sc)
-- ([],["x"])

-- | A new lifted parameter, in scope.
bindBit :: String -> Scope -> Scope
bindBit q sc = sc { scBits = scBits sc ++ [q], scAllBits = scAllBits sc ++ [q] }

-- >>> scBits (bindBit "m" (newScope []))
-- ["m"]

-- | A register by name, through the block aliases, or the refusal that says why it is not live.
lookupReg :: Scope -> (Int, String) -> Either String (String, Int)
lookupReg sc (n, x0) =
  let x = resolve sc x0
  in case lookup x (scLive sc) of
       Just d -> Right (x, d)
       Nothing
         | x `elem` scDropped sc -> errLn n ("register '" ++ x0 ++ "' has been dropped")
         | otherwise             -> errLn n ("unknown register '" ++ x0 ++ "'")

-- >>> lookupReg (newScope [Param "x" 3 False]) (1, "x")
-- Right ("x",3)

-- >>> lookupReg (newScope [Param "x" 3 False]) (2, "z")
-- Left "line 2: unknown register 'z'"

-- >>> lookupReg (dropRegs ["x"] (newScope [Param "x" 3 False])) (5, "x")
-- Left "line 5: register 'x' has been dropped"

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

-- >>> checkFresh (newScope [Param "x" 2 False]) (1, "t")
-- Right ()

-- >>> checkFresh (newScope [Param "x" 2 False]) (3, "x")
-- Left "line 3: register 'x' already exists"

-- >>> checkFresh (dropRegs ["x"] (newScope [Param "x" 2 False])) (4, "x")
-- Left "line 4: register 'x' has been dropped, and a dropped name cannot be bound again"

-- | A register has at least two levels.
checkDim :: (Int, Int) -> Either String ()
checkDim (n, d)
  | d < 2     = errLn n "register dimension must be at least 2"
  | otherwise = Right ()

-- >>> checkDim (4, 2)
-- Right ()
-- >>> checkDim (4, 1)
-- Left "line 4: register dimension must be at least 2"

-- | Register checks shared by every gate statement: distinct known
-- registers. Returns the wire names, a line to report errors at, and the
-- product dimension.
gateRegs :: Scope -> String -> Int -> [(Int, String)] -> Either String ([String], Int, Int)
gateRegs sc what ln regs = do
  found <- mapM (lookupReg sc) regs
  let names = map fst found
      dims  = map snd found
  if length (nub names) /= length names
    then errLn ln ("repeated register in " ++ what)
    else case dimensionProduct dims of
      Nothing -> errLn ln ("register dimensions in " ++ what
                           ++ " exceed the supported dimension range")
      Just d  -> Right (names, ln, d)

-- >>> gateRegs (newScope [Param "x" 2 False, Param "y" 3 False]) "mat" 1 [(1, "x"), (1, "y")]
-- Right (["x","y"],1,6)

-- >>> gateRegs (newScope [Param "x" 2 False]) "mat" 2 [(2, "x"), (2, "x")]
-- Left "line 2: repeated register in mat"

-- >>> gateRegs (newScope [Param "x" 2 False]) "mat" 2 [(2, "z")]
-- Left "line 2: unknown register 'z'"

-- The declarations and the program header -----------------------------------
--
-- A file is optional top-level gate declarations followed by one program:
--
--   gate V : [2] * [2] = mat { ... };
--   prog f (x : [2], loan a : [2]) : [2] {  M  }
--
-- The header supplies the input context (the paper's Omega), the result type
-- and, through the body's closing @return v@, the value the program hands back.

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

-- >>> spReturnLine (SrcPos 8 [("a", 2)])
-- 8

-- | Gate declarations, one after another, added to the table. A name declared twice, or
-- a matrix of the wrong size, is refused.
pDecls :: GateEnv -> [LTok] -> Either String (GateEnv, [LTok])
pDecls env ts = case ts of
  ((_, TWord "gate") : r) -> do
    ((ln, nm), r1) <- identL r
    (_, r2)  <- expectSym ':' r1
    (ty, r3) <- pTy r2
    (_, r4)  <- expectSym '=' r3
    (m, r5)  <- pGateLit r4
    (_, r6)  <- expectSym ';' r5
    d <- case tyDim ty of
      Nothing -> errLn ln ("gate '" ++ nm
                           ++ "' exceeds the supported dimension range")
      Just n  -> Right n
    if nm `elem` map fst env
      then errLn ln ("gate '" ++ nm ++ "' is already declared")
      else if length m /= d
        then errLn ln ("gate '" ++ nm ++ "' is declared at dimension " ++ show d
                       ++ " but its matrix is " ++ show (length m) ++ "x"
                       ++ show (length m))
        else pDecls (env ++ [(nm, m)]) r6
  _ -> Right (env, ts)

-- A declaration, then the program that follows it.
-- >>> fmap (\(env, rest) -> (map fst env, length rest)) (tokenize "gate V : [2] = diag (1, 2); prog f" >>= pDecls [])
-- Right (["V"],2)

-- >>> fmap (\(env, rest) -> (map fst env, length rest)) (tokenize "prog f" >>= pDecls [])
-- Right ([],2)

-- >>> tokenize "gate V : [2] = diag (1, 2);\ngate V : [2] = diag (1, 3); prog" >>= pDecls []
-- Left "line 2: gate 'V' is already declared"

-- >>> tokenize "gate V : [3] = diag (1, 2); prog" >>= pDecls []
-- Left "line 1: gate 'V' is declared at dimension 3 but its matrix is 2x2"

-- | The product of the dimensions a type names, when it fits an index.
tyDim :: Ty -> Maybe Int
tyDim TUnit         = Just 1
tyDim (TReg d)      = dimensionProduct [d]
tyDim (TTensor a b) = do
  da <- tyDim a
  db <- tyDim b
  dimensionProduct [da, db]

-- >>> tyDim TUnit
-- Just 1
-- >>> tyDim (TReg 3)
-- Just 3
-- >>> tyDim (TTensor (TReg 2) (TTensor (TReg 3) (TReg 2)))
-- Just 12

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

-- >>> fmap (\(m, rest) -> (m == [[1, 0], [0, 2]], length rest)) (tokenize "diag (1, 2)" >>= pGateLit)
-- Right (True,0)

-- >>> fmap (\(m, rest) -> (m == [[0, 1], [1, 0]], length rest)) (tokenize "perm (1 0)" >>= pGateLit)
-- Right (True,0)

-- >>> fmap (\(m, rest) -> (m == [[1, 2], [3, 4]], length rest)) (tokenize "mat { 1, 2 ; 3, 4 }" >>= pGateLit)
-- Right (True,0)

-- >>> tokenize "mat { 1, 2 ; 3 }" >>= pGateLit
-- Left "line 1: mat literal is not square"

-- >>> tokenize "perm (0 0)" >>= pGateLit
-- Left "line 1: perm image list is not a permutation"

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

-- >>> fmap (\((nm, ps, ty, lns), rest) -> (nm, [ (prmName q, prmLoan q) | q <- ps ], ty, lns, length rest)) (tokenize "prog f (x : [2], loan a : [3]) : [2] {" >>= pHeader)
-- Right ("f",[("x",False),("a",True)],TReg 2,[1,1],1)

-- >>> tokenize "prog f (x : [2], x : [3]) : [2] {" >>= pHeader
-- Left "line 1: repeated parameter in the header of 'f'"

-- >>> tokenize "prog f (x : [2] * [2]) : [2] {" >>= pHeader
-- Left "line 1: parameter 'x' must have a register type [d]"

-- Statements ----------------------------------------------------------------

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

-- >>> fmap isBinding (tokenize "p = lift[{1}] a;")
-- Right True
-- >>> fmap isBinding (tokenize "H x;")
-- Right False

-- A pattern with a tuple has its equals sign at depth zero; an equals sign inside brackets does not count.
-- >>> fmap isBinding (tokenize "(a, b) = { H a; return (a, b) };")
-- Right True

-- | Statements up to the body's closing @return v@. The 'Int' is the line the
-- closing @return@ stands on.
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

-- >>> tokenize "H x; return x }" >>= \ts -> fmap (\(cs, v, ln, _, rest) -> (map renderCmd cs, v, ln, length rest)) (pBody gateTable (newScope [Param "x" 2 False]) ts)
-- Right (["H x;"],VVar "x",1,1)

-- >>> tokenize "return x }" >>= \ts -> fmap (\(cs, v, ln, _, rest) -> (length cs, v, ln, length rest)) (pBody gateTable (newScope [Param "x" 2 False]) ts)
-- Right (0,VVar "x",1,1)

-- | A value with its block aliases replaced by wires; every name must be live.
resolveValue :: Scope -> Int -> Value -> Either String Value
resolveValue sc ln v = do
  mapM_ (\x -> lookupReg sc (ln, x)) (valueNames v)
  Right (go v)
  where
    go (VVar x)    = VVar (resolve sc x)
    go VUnit       = VUnit
    go (VPair a b) = VPair (go a) (go b)

-- >>> resolveValue (newScope [Param "x" 2 False]) 1 (VVar "x")
-- Right (VVar "x")

-- >>> resolveValue ((newScope [Param "x" 2 False]) { scAlias = [("y", "x")] }) 1 (VPair (VVar "y") VUnit)
-- Right (VPair (VVar "x") VUnit)

-- >>> resolveValue (newScope [Param "x" 2 False]) 3 (VVar "z")
-- Left "line 3: unknown register 'z'"

-- | One statement: its commands (a block gives several), the scope after it, and the
-- tokens left.
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

-- A new, a gate, and the statements the paper does not print.
-- >>> tokenize "new t : [2] @ |0>;" >>= \ts -> fmap (\(cs, _, rest) -> (map renderCmd cs, length rest)) (pStmt gateTable (newScope []) ts)
-- Right (["new t : [2] @ |0>;"],0)

-- >>> tokenize "H x;" >>= \ts -> fmap (\(cs, _, rest) -> (map renderCmd cs, length rest)) (pStmt gateTable (newScope [Param "x" 2 False]) ts)
-- Right (["H x;"],0)

-- >>> tokenize "lift x;" >>= pStmt gateTable (newScope [Param "x" 2 False]) >>= \(cs, _, _) -> return (length cs)
-- Left "line 1: a lift binds its parameter: write `p = lift[S] x;` (found 'lift')"

-- >>> either (Left . take 60) Right (tokenize "loan a : [2];" >>= pStmt gateTable (newScope []) >>= \(cs, _, _) -> return (length cs))
-- Left "line 1: a loan is declared in the program header, as `prog f"

-- >>> tokenize "return x;" >>= pStmt gateTable (newScope [Param "x" 2 False]) >>= \(cs, _, _) -> return (length cs)
-- Left "line 1: 'return' ends the body; it cannot appear here (found 'return')"

-- | The right-hand side of a binding @p = N;@ (or @p = { ... };@): the token
-- after the @=@ says which statement it is.
pBound :: GateEnv -> Scope -> Int -> Value -> [LTok]
       -> Either String ([Cmd Cyclo], Scope, [LTok])
pBound env sc ln p ts = case ts of
  ((_, TSym '{') : r)     -> pBlock env sc ln p r
  ((_, TWord "lift") : r) -> pLift sc ln p r
  _                       -> refuseBinding env sc ln p ts

-- pBound reads one of three things after the equals sign; each part is tried below through a tiny file.
-- >>> fmap (map renderCmd . sfBody) (parseFile "prog f (x : [2]) : [2] {\n  m = lift[{1}] x;\n  return x\n}")
-- Right ["m = lift[{1}] x;"]

-- >>> fmap (map renderCmd . sfBody) (parseFile "prog f (x : [2]) : [2] {\n  y = { H x; return x };\n  return x\n}")
-- Right ["H x;"]

-- | @y = { M; return v };@, the tokens after the opening brace: the paper's
-- sequencing operator, spliced. The block's statements join the enclosing
-- body, @y@ names the wire @v@ names, and the parameters its lifts bind leave
-- scope at the closing brace.
pBlock :: GateEnv -> Scope -> Int -> Value -> [LTok]
       -> Either String ([Cmd Cyclo], Scope, [LTok])
pBlock env sc ln p r = do
  let bitsBefore = scBits sc
  (cs, v, _, sc1, r1) <- pBody env sc r
  (_, r2) <- expectSym '}' r1
  (_, r3) <- expectSym ';' r2
  let names = valueNames p
      vs    = valueNames v
  if length (nub names) /= length names
    then errLn ln "repeated register in block pattern"
    else if length names /= length vs
      -- refusal: the pattern binds a different number of names than the block returns
      then errLn ln ("the block returns " ++ show (length vs)
                     ++ " register(s), but the pattern binds " ++ show (length names))
      else do
        mapM_ (checkFresh sc1) [ (ln, x) | x <- names ]
        let sc2 = sc1 { scBits = bitsBefore
                      , scAlias = scAlias sc1 ++ zip names vs
                      , scAllNames = scAllNames sc1 ++ names }
        Right (cs, sc2, r3)

-- A block splices its statements and names the wire it returns.
-- >>> fmap (map renderCmd . sfBody) (parseFile "prog f (x : [2]) : [2] {\n  y = { H x; return x };\n  return y\n}")
-- Right ["H x;"]

-- >>> fmap (map renderCmd . sfBody) (parseFile "prog f (x : [2]) : [2] {\n  y = { H x; X x; return x };\n  return y\n}")
-- Right ["H x;","X x;"]

-- A parameter the block binds is out of scope after it.
-- >>> parseFile "prog f (x : [2]) : [2] {\n  y = { m = lift[{1}] x; return x };\n  if m { X y; } else { }\n  return y\n}"
-- Left "line 3: parameter 'm' is not in scope here"

-- The pattern and the block must agree on how many names.
-- >>> parseFile "prog f (x : [2]) : [2] {\n  (y, z) = { H x; return x };\n  return y\n}"
-- Left "line 2: the block returns 1 register(s), but the pattern binds 2"

-- | @p = lift[S] x;@, the tokens after @lift@. One parameter per lift, as the
-- calculus writes them: a second binding of the same name would be read one
-- way by the machine, which takes the latest, and another by the static
-- pass, which takes the first, and the two would disagree in silence.
pLift :: Scope -> Int -> Value -> [LTok] -> Either String ([Cmd Cyclo], Scope, [LTok])
pLift sc ln p r = do
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
                      -- refusal: a level outside the register's dimension
                      then errLn n ("level " ++ show l ++ " out of range for '"
                                    ++ x ++ "' (dimension " ++ show d ++ ")")
                      else Right ()) lvls
  if length (nub block) /= length block
    -- refusal: a level named twice in the block
    then errLn ln "repeated level in lift block"
    else if length block >= d
      -- refusal: a block that is every level, not a proper subset
      then errLn ln ("the block of a lift must be a proper subset of the "
                     ++ show d ++ " levels of '" ++ x ++ "'")
    else if pn `elem` scAllBits sc
      -- refusal: a parameter name bound by an earlier lift
      then errLn ln ("parameter '" ++ pn ++ "' is already bound by an \
                     \earlier lift")
      else Right ([Lift pn x block], bindBit pn sc, r7)

-- >>> fmap (map renderCmd . sfBody) (parseFile "prog f (x : [2]) : [2] {\n  m = lift[{1}] x;\n  return x\n}")
-- Right ["m = lift[{1}] x;"]

-- >>> parseFile "prog f (x : [2]) : [2] {\n  m = lift[{0, 1}] x;\n  return x\n}"
-- Left "line 2: the block of a lift must be a proper subset of the 2 levels of 'x'"

-- >>> parseFile "prog f (x : [2]) : [2] {\n  m = lift[{2}] x;\n  return x\n}"
-- Left "line 2: level 2 out of range for 'x' (dimension 2)"

-- >>> parseFile "prog f (x : [2]) : [2] {\n  m = lift[{1, 1}] x;\n  return x\n}"
-- Left "line 2: repeated level in lift block"

-- One parameter per lift.
-- >>> parseFile "prog f (x : [2]) : [2] {\n  m = lift[{1}] x;\n  m = lift[{0}] x;\n  return x\n}"
-- Left "line 3: parameter 'm' is already bound by an earlier lift"

-- | The three explicit-binding spellings the paper does not print, each
-- refused with the form to write instead. Every refusal reads its statement
-- far enough to print that form, so a malformed statement is reported as
-- malformed first.
refuseBinding :: GateEnv -> Scope -> Int -> Value -> [LTok] -> Either String a
refuseBinding env sc ln p ts = case ts of

  -- The paper prints no name before 'new', so the explicit-binding
  -- spelling `t = new [d] @ psi;` is a parse error naming the printed form.
  ((_, TWord "new") : r) -> do
    x <- singleName ln p "new"
    (_, r1)  <- expectSym '[' r
    (nd@(_, d), r2) <- natL r1
    checkDim nd
    (_, r3)  <- expectSym ']' r2
    (cmd, _) <- pAlloc ln x d r3
    -- refusal: `t = new [d] @ psi;`, an allocation names its register once
    errLn ln ("an allocation binds its own name: write `"
              ++ renderCmd cmd ++ "`")

  -- () = drop v;  -- refused: the printed form binds nothing.
  ((_, TWord "drop") : r) -> do
    (c, _, _) <- pDrop sc r
    -- refusal: `() = drop v;`, a drop binds nothing
    errLn ln ("a drop binds nothing: write `" ++ renderCmd c ++ "`")

  -- p = U v;  -- refused: a gate acts in place, on its own registers.
  _ -> do
    (c, _, _) <- pGateStmt env sc ts
    case c of
      -- refusal: `p = U v;`, a gate acts in place
      Gate _ _ -> errLn ln ("a gate acts in place: write `" ++ renderCmd c ++ "`")
      -- refusal: something other than a gate after the equals sign
      _        -> errLn ln "expected a gate after '='"

-- The three explicit-binding spellings, each refused with the form the paper prints.
-- >>> parseFile "prog f (x : [2]) : [2] {\n  t = new [2] @ |0>;\n  return x\n}"
-- Left "line 2: an allocation binds its own name: write `new t : [2] @ |0>;`"

-- >>> parseFile "prog f (x : [2]) : [2] {\n  () = drop x;\n  return x\n}"
-- Left "line 2: a drop binds nothing: write `drop x;`"

-- >>> parseFile "prog f (x : [2]) : [2] {\n  p = H x;\n  return x\n}"
-- Left "line 2: a gate acts in place: write `H x;`"

-- >>> parseFile "prog f (x : [2]) : [2] {\n  p = 7;\n  return x\n}"
-- Left "line 2: expected a statement (found 7)"

-- | The one name a pattern binds, for a statement that binds exactly one.
singleName :: Int -> Value -> String -> Either String String
singleName ln p what = case valueNames p of
  [x] | p == VVar x -> Right x
  _ -> errLn ln (what ++ " binds exactly one name")

-- >>> singleName 1 (VVar "m") "lift"
-- Right "m"
-- >>> singleName 1 (VPair (VVar "m") (VVar "n")) "lift"
-- Left "line 1: lift binds exactly one name"

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

-- >>> tokenize "t : [2] @ |1>;" >>= \ts -> fmap (\(c, sc, rest) -> (renderCmd c, scLive sc, length rest)) (pNew (newScope []) ts)
-- Right ("new t : [2] @ |1>;",[("t",2)],0)

-- >>> tokenize "x : [2] @ |1>;" >>= pNew (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: register 'x' already exists"

-- >>> tokenize "t : [1] @ |0>;" >>= pNew (newScope []) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: register dimension must be at least 2"

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

-- A ket, the zero ket (a New), a vector, and three refusals.
-- >>> fmap (\(c, rest) -> (renderCmd c, length rest)) (tokenize "@ |1>;" >>= pAlloc 1 "t" 2)
-- Right ("new t : [2] @ |1>;",1)

-- >>> fmap (\(c, _) -> c == New "t" 2) (tokenize "@ |0>;" >>= pAlloc 1 "t" 2)
-- Right True

-- >>> fmap (\(c, _) -> renderCmd c) (tokenize "@ (1/rt2, 1/rt2);" >>= pAlloc 1 "p" 2)
-- Right "new p : [2] @ (1/2*z8-1/2*z8^3, 1/2*z8-1/2*z8^3);"

-- >>> tokenize "@ |2>;" >>= pAlloc 1 "t" 2
-- Left "line 1: |2> is not a level of [2]"

-- >>> tokenize "@ (1, 1);" >>= pAlloc 1 "t" 2
-- Left "line 1: new t : [2] must name a unit state, but the vector given has squared norm 2, not 1"

-- >>> tokenize "@ (1, 0, 0);" >>= pAlloc 1 "t" 2
-- Left "line 1: new t : [2] needs 2 amplitudes, got 3"

-- | The basis vector @|i>@ of dimension @d@.
ketOf :: Int -> Int -> StateV Cyclo
ketOf d i = [ if k == i then 1 else 0 | k <- [0 .. d - 1] ]

-- >>> ketOf 3 1 == [0, 1, 0]
-- True

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

-- >>> tokenize "x;" >>= \ts -> fmap (\(c, sc, rest) -> (renderCmd c, scLive sc, length rest)) (pDrop (newScope [Param "x" 2 False]) ts)
-- Right ("drop x;",[],0)

-- >>> tokenize "();" >>= \ts -> fmap (\(c, _, _) -> c == Drop []) (pDrop (newScope [Param "x" 2 False]) ts)
-- Right True

-- >>> tokenize "(x, x);" >>= pDrop (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: repeated register in drop"

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

-- >>> tokenize "m { X x; } else { }" >>= \ts -> fmap (\(c, _, rest) -> (renderCmd c, length rest)) (pIf gateTable (bindBit "m" (newScope [Param "x" 2 False])) ts)
-- Right ("if m { X x; } else { }",0)

-- >>> tokenize "q { X x; } else { }" >>= pIf gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: parameter 'q' is not in scope here"

-- >>> tokenize "m { drop x; } else { }" >>= pIf gateTable (bindBit "m" (newScope [Param "x" 2 False])) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: 'drop' inside an if branch: a branch binds nothing, so put it before or after the if"

-- | The statements of one arm of an @if@, up to its closing brace.
pBranch :: GateEnv -> Scope -> [LTok]
        -> Either String ([Cmd Cyclo], Scope, [LTok])
pBranch env sc ts = case ts of
  ((_, TSym '}') : _) -> Right ([], sc, ts)
  _ -> do
    (cs, sc1, ts1) <- pStmt env sc ts
    (cs2, sc2, ts2) <- pBranch env sc1 ts1
    Right (cs ++ cs2, sc2, ts2)

-- >>> tokenize "X x; Z x; }" >>= \ts -> fmap (\(cs, _, rest) -> (map renderCmd cs, length rest)) (pBranch gateTable (newScope [Param "x" 2 False]) ts)
-- Right (["X x;","Z x;"],1)

-- >>> tokenize "}" >>= \ts -> fmap (\(cs, _, rest) -> (length cs, length rest)) (pBranch gateTable (newScope [Param "x" 2 False]) ts)
-- Right (0,1)

-- | A guard: @||@ below @&&@ below @!@ or @not@, with parentheses; @0@, @1@ or a parameter
-- at the bottom.
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

-- >>> fmap fst (tokenize "m" >>= pGuard)
-- Right (GParam "m")

-- >>> fmap fst (tokenize "p && !q || r" >>= pGuard)
-- Right (GOr (GAnd (GParam "p") (GNot (GParam "q"))) (GParam "r"))

-- >>> fmap fst (tokenize "p && (q || r)" >>= pGuard)
-- Right (GAnd (GParam "p") (GOr (GParam "q") (GParam "r")))

-- >>> tokenize "&&" >>= pGuard
-- Left "line 1: expected a guard (0, 1, a parameter, '!e', 'e1 && e2' or 'e1 || e2') (found '&')"

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
    (names, ln, d) <- gateRegs sc "mat" (lineAt rest) regs
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
    (names, ln, d) <- gateRegs sc "diag" (lineAt rest) regs
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
    (names, ln, d) <- gateRegs sc "perm" (lineAt rest) regs
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
      (names, _, d) <- gateRegs sc ("gate '" ++ nm ++ "'") (lineAt rest) regs
      if d /= length m
        then errLn ln ("gate '" ++ nm ++ "' has dimension " ++ show (length m)
                       ++ " but registers " ++ unwords names
                       ++ " have total dimension " ++ show d)
        else Right (Gate m names, sc, ts2)

  _ -> errAt ts0 "expected a statement"

-- A named gate, then the three literals, each by its first word.
-- >>> tokenize "X x;" >>= \ts -> fmap (\(c, _, rest) -> (renderCmd c, length rest)) (pGateStmt gateTable (newScope [Param "x" 2 False]) ts)
-- Right ("X x;",0)

-- >>> tokenize "mat x { 0, 1 ; 1, 0 }" >>= \ts -> fmap (\(c, _, rest) -> (renderCmd c, length rest)) (pGateStmt gateTable (newScope [Param "x" 2 False]) ts)
-- Right ("X x;",0)

-- >>> tokenize "diag x (1, 2);" >>= \ts -> fmap (\(c, _, rest) -> (renderCmd c, length rest)) (pGateStmt gateTable (newScope [Param "x" 2 False]) ts)
-- Right ("diag x (1, 2);",0)

-- >>> tokenize "perm x (1 0);" >>= \ts -> fmap (\(c, _, rest) -> (renderCmd c, length rest)) (pGateStmt gateTable (newScope [Param "x" 2 False]) ts)
-- Right ("X x;",0)

-- The refusals, one per kind of mistake.
-- >>> tokenize "frobnicate x;" >>= pGateStmt gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: unknown gate or statement 'frobnicate'"

-- >>> tokenize ";" >>= pGateStmt gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: expected a statement (found ';')"

-- >>> tokenize "CX x;" >>= pGateStmt gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: gate 'CX' has dimension 4 but registers x have total dimension 2"

-- >>> tokenize "mat x { 1, 0 ; 0 }" >>= pGateStmt gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: mat over x must be 2x2, got 2 row(s) of width(s) [2,1]"

-- >>> tokenize "diag x (1, 2, 3);" >>= pGateStmt gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: diag over x needs 2 entries, got 3"

-- >>> tokenize "perm x (1);" >>= pGateStmt gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: perm over x needs 2 images, got 1"

-- >>> tokenize "perm x (1 2);" >>= pGateStmt gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: perm image 2 out of range 0..1"

-- >>> tokenize "perm x (1 1);" >>= pGateStmt gateTable (newScope [Param "x" 2 False]) >>= \(c, _, _) -> return (renderCmd c)
-- Left "line 1: perm image list is not a permutation (repeated image)"


-- Entry points --------------------------------------------------------------

-- | 'parseFileAt', forgetting where the program's text put things.
parseFile :: String -> Either String SFile
parseFile = fmap fst . parseFileAt

-- Static checks, the first of each kind: a register neither dropped nor returned, a result type that disagrees with the header.
-- >>> parseFile "prog f () : 1 {\n  new a : [2] @ |0>;\n  return ()\n}"
-- Left "line 4: register 'a' is neither dropped nor returned"

-- >>> parseFile "prog f (x : [2]) : [2] * [2] {\n  return x\n}"
-- Left "line 1: the program returns [2] but its header declares [2] * [2]"

-- >>> parseFile "prog f (x : [2]) : [2] {\n  return x\n} extra"
-- Left "line 3: unexpected token after the program (found 'extra')"

-- The smallest program, and the paper's temporary AND with its drop.
-- >>> fmap (\f -> (sfName f, length (sfBody f))) (parseFile "prog f (x : [2]) : [2] {\n  return x\n}")
-- Right ("f",0)

-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap (\f -> (sfName f, length (sfBody f))) (parseFile src))
-- Right ("temp_and",6)

-- The identity: render a parsed file and parse the text, and the
-- same SFile comes back. It holds on all 27 files of programs/: the paper's 19 corpus programs,
-- five reuse examples (a-then-u, two-phases, two-phases-uncompute, grover-two-rounds,
-- measured-and-twice) and
-- program (c)'s lowering, exposed map and witness (c-decomposed, c-exposed, c-witness). Each line
-- below is one file.
-- >>> mapM_ (\p -> readFile ("programs/" ++ p ++ ".s") >>= \src -> putStrLn (p ++ ": " ++ show (fmap (\f -> parseFile (renderFile f) == Right f) (parseFile src)))) ["a-then-u", "bell-block", "bell-pair-split", "bell-pair", "c-decomposed", "c-exposed", "c-witness", "c", "copy-input", "dj", "grover-two-rounds", "grover", "learns-nothing", "mcx-dirty-half", "mcx-dirty-x", "mcx-dirty", "measured-and-twice", "qpe", "rus", "shor", "simon", "superdense", "teleport", "temp-and", "temp-general", "two-phases-uncompute", "two-phases"]
-- a-then-u: Right True
-- bell-block: Right True
-- bell-pair-split: Right True
-- bell-pair: Right True
-- c-decomposed: Right True
-- c-exposed: Right True
-- c-witness: Right True
-- c: Right True
-- copy-input: Right True
-- dj: Right True
-- grover-two-rounds: Right True
-- grover: Right True
-- learns-nothing: Right True
-- mcx-dirty-half: Right True
-- mcx-dirty-x: Right True
-- mcx-dirty: Right True
-- measured-and-twice: Right True
-- qpe: Right True
-- rus: Right True
-- shor: Right True
-- simon: Right True
-- superdense: Right True
-- teleport: Right True
-- temp-and: Right True
-- temp-general: Right True
-- two-phases-uncompute: Right True
-- two-phases: Right True

-- The converse does not hold, which is why it is parseFile after renderFile and not the other
-- way: the printer lays a program out its own way (the file's comments, spacing and line numbers
-- are not part of SFile), so printing what was parsed does not give the text back.
-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap renderFile (parseFile src) == Right src)
-- False

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

-- The loan program of the corpus: where its return stands and where its loan is declared.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap snd (parseFileAt src))
-- Right (SrcPos {spReturnLine = 12, spLoanLines = [("a",8)]})

-- A loan is hoisted to the head of the body.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> print (fmap (take 2 . map renderCmd . sfBody . fst) (parseFileAt src))
-- Right ["-- loan a : [2]","X a;"]

-- | The type of a value, from the dimensions of its live registers.
tyOfValue :: Scope -> Int -> Value -> Either String Ty
tyOfValue sc ln v = case v of
  VUnit      -> Right TUnit
  VVar x     -> do (_, d) <- lookupReg sc (ln, x); Right (TReg d)
  VPair a b  -> do
    ta <- tyOfValue sc ln a
    tb <- tyOfValue sc ln b
    Right (TTensor ta tb)

-- >>> tyOfValue (newScope [Param "x" 2 False, Param "y" 3 False]) 1 (VPair (VVar "x") (VVar "y"))
-- Right (TTensor (TReg 2) (TReg 3))

-- >>> tyOfValue (newScope []) 1 VUnit
-- Right TUnit

-- >>> tyOfValue (newScope []) 4 (VVar "z")
-- Left "line 4: unknown register 'z'"

-- | The machine's view of a file: the ordinary input registers and the flat
-- command list (loans hoisted to its head).
parseProgram :: String -> Either String (VisSpec, Prog Cyclo)
parseProgram src = do
  f <- parseFile src
  Right (sfVis f, sfBody f)

-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap (\(vis, prog) -> (vis, length prog)) (parseProgram src))
-- Right ([("x",2),("y",2)],6)

-- >>> parseProgram "prog f (x : [2]) : [2] { return y }"
-- Left "line 1: unknown register 'y'"

-- | The typed program of a file, as the statics and the compiler read it: the
-- inputs and the body elaborated to a term that returns what the header names
-- (Drop.Lang.Elab.flatToProgramR).
parseTyped :: String -> Either String (Program Cyclo)
parseTyped src = do
  f <- parseFile src
  Right (flatToProgramR (sfVis f) (sfReturn f) (sfBody f))

-- >>> readFile "programs/temp-and.s" >>= \src -> print (fmap progCtx (parseTyped src))
-- Right [("x",2),("y",2)]
-- >>> fmap progCtx (parseTyped "prog f (x : [2]) : [2] { return y }")
-- Left "line 1: unknown register 'y'"
