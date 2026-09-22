-- |
-- Module      : Drop.Theory.Report
--
-- Rendering.  Nothing here computes anything; it formats what the other
-- modules decided, so every number the prose quotes is printed by the same
-- code that decides the verdicts.  Typography lives in "Drop.Theory.Pretty".
module Drop.Theory.Report
  ( -- * Whole-program reports
    reportProgram
  , reportGram
  , reportContext
  , reportWitness
    -- * Pieces, for the assembled document
  , programHeader
  , typedGramReport
  , verdictField
    -- * Tables
  , table
  , matrixTable
  ) where

import Drop.Theory.Criterion.Context
import Drop.Theory.Criterion
import Drop.Theory.Program.Elaborate
import Drop.Theory.Criterion.Gram
import Drop.Theory.Algebra.Linear
import Drop.Theory.Pretty
import Drop.Theory.Algebra.Scalar
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing
import Drop.Theory.Criterion.Witness

-- | A left-aligned text table with a header row and a rule under it.
table :: [String] -> [[String]] -> String
table hdr rows = unlines (line hdr : sep : map line rows)
  where
    widths  = [ maximum (map length col) | col <- transposeS (hdr : rows) ]
    -- `unwords` supplies the single space between columns, so a cell is padded
    -- to exactly its width.  `Pretty.padSep` guarantees a trailing space, which
    -- here would push every cell after a full-width one a column to the right.
    line xs = "  " ++ trimEnd (unwords [ padCell w x | (w,x) <- zip widths xs ])
    padCell w x = x ++ replicate (w - length x) ' '
    sep     = "  " ++ unwords [ replicate w '\9472' | w <- widths ]
    trimEnd = reverse . dropWhile (== ' ') . reverse
    transposeS xss
      | any null xss = []
      | otherwise    = map headOf xss : transposeS (map tailOf xss)
    headOf (x:_)  = x
    headOf []     = ""
    tailOf (_:xs) = xs
    tailOf []     = []

-- | A matrix rendered with row and column labels: the row label is the output
-- basis state, the column label the input.
matrixTable :: String -> [String] -> [String] -> Mat -> String
matrixTable title rowLbl colLbl m =
  unlines (numTable title rowLbl colLbl (map (map showK) m))

-- Program reports

-- | The verdict, as a field.  'Verdict'\'s own rendering puts the witness
-- minor on a second line, which is hung under the value here rather than left
-- to start a paragraph of its own.
verdictField :: Verdict -> [String]
verdictField v = case lines (show v) of
  []       -> kv "verdict" "-"
  (l : ls) -> kv "verdict" l
              ++ concat [ [ replicate (colonCol + 2) ' ' ++ w
                          | w <- wrapAt (measure - colonCol - 2)
                                        (dropWhile (== ' ') x) ]
                        | x <- ls ]

-- | The identifying block for one program: its source, then what the checker
-- knows about it before any matrix is shown.
programHeader :: Program -> [String]
programHeader p = case checkProgram p of
  Left e   -> gutter (prettySugared p) ++ blank ++ kv "TYPE ERROR" (show e)
  Right tp ->
    gutter (prettySugared p) ++ blank
    ++ kvs
       [ ("temporary",                       "tmp[" ++ show (tpTmpDim tp)
                                             ++ "], allocated in |"
                                             ++ show (tpAlloc tp) ++ ">")
       , ("visible register",                "vis[" ++ show (tpVisDim tp) ++ "]")
       , ("literally of the shape sep(R,W)", yesNo (inSepShape p))
       , ("denotation against the machine",  okBad "agree" "differ"
                                               (agreesWithMachine tp))
       , ("the two routes to the criterion", okBad "agree" "differ"
                                               (routesAgree tp)) ]
    ++ verdictField (verdict tp)

reportProgram :: Program -> String
reportProgram = unlines . programHeader

reportGram :: Program -> String
reportGram p = case checkProgram p of
  Left e   -> unlines (kv "TYPE ERROR" (show e))
  Right tp -> unlines (typedGramReport tp)

-- | The Gram report for an already-typed program: the denotation, its
-- Kraus operators, the pairwise table, and the one sentence the three ranks
-- are for.
typedGramReport :: TypedProgram -> [String]
typedGramReport tp =
  numTable ("core map  K : H_" ++ show m ++ "  \8594  H_" ++ show d
            ++ " (x) H_" ++ show m)
           [ "(" ++ show i ++ "," ++ show a ++ ")"
           | i <- [0 .. d-1], a <- [0 .. m-1] ]
           [ show j | j <- [0 .. m-1] ]
           (map (map showK) k)
  ++ para ("The slices: K_i is what the program does to the visible register "
           ++ "when the temporary sits at level i. Discard safety is exactly "
           ++ "that they all lie on one line.")
  ++ concat [ numTable ("slice K_" ++ show i)
                       [ show a | a <- [0 .. m-1] ]
                       [ show b | b <- [0 .. m-1] ]
                       (map (map showK) s)
            | (i, s) <- zip [0 :: Int ..] (slices d m k) ]
  ++ numTable "Gram matrix  G_ij = tr(K_i^dagger K_j)"
              [ show i | i <- [0 .. d-1] ] [ show j | j <- [0 .. d-1] ]
              (map (map showK) (gramMatrix d m k))
  ++ blank
  ++ kv "slice / Gram / Choi rank"
        (show (sliceRank d m k) ++ " / " ++ show (gramRank d m k) ++ " / "
         ++ show (choiRank d m k) ++ "   ("
         ++ okBad "the three agree" "they disagree" (ranksAgree d m k) ++ ")")
  ++ blank
  ++ para ("Rank at most one says the slices lie on one line, which says "
           ++ "K = g (x) W, which says the temporary carried nothing about "
           ++ "the visible input. Rank two or more is a leak, and the minor "
           ++ "above names where it is.")
  where
    d = tpTmpDim tp
    m = tpVisDim tp
    k = coreMap tp

reportContext :: Program -> String
reportContext p = case checkProgram p of
  Left e   -> unlines (kv "TYPE ERROR" (show e))
  Right tp -> unlines $
    para ("A client appends one gate to the visible register and reads outcome "
          ++ "statistics; the temporary is already gone. This is everything it "
          ++ "can see.")
    ++ blank
    ++ [ table ["continuation @ input", "outcome statistics"]
               [ [clientLabel c, show o]
               | (c, o) <- zip cls (observations tp cls) ] ]
    ++ kv "observable object"
          ("the Choi matrix of  Phi(X) = sum_i K_i X K_i^dagger")
    ++ kv "its rank" (show (rank (observableChannel tp)))
    ++ blank
    ++ para ("Rank one is exactly `no client can tell this from a separable "
             ++ "program'. That is the theorem the criterion is standing in "
             ++ "for, and it is why a rank is the right thing to compute.")
    where cls = standardClients (tpVisDim tp)

reportWitness :: Program -> String
reportWitness p = case checkProgram p of
  Left e   -> unlines (kv "TYPE ERROR" (show e))
  Right tp -> unlines (explainWitness tp (synthesize tp))
