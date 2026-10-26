-- Drop.Theory.Report: the reports the matrix checker prints.
--
-- Question: What does the matrix checker print for a program?
-- Answer:   It formats what the other modules decide, in the layout of Drop.Theory.Pretty. The
--           only arithmetic it does itself is the rank printed by reportContext.
--           programHeader shows a program's source and what the checker knows of it before any
--           matrix: its temporary and visible dimensions, whether it is literally of the shape
--           sep(R, W), whether the denotation and the machine agree, whether the two routes
--           to the criterion agree, and the verdict. reportGram adds the denotation, its Kraus
--           operators, the Gram matrix and the three ranks. reportContext shows what every
--           client of the standard family observes. reportWitness is the account of the
--           witness. A program that does not type prints its type error in place of the report.
-- Paper:    sec:criterion, sec:ctxequiv.
-- Shapes:   Every report is a String or a list of lines; table lays out columns.

module Drop.Theory.Report
  ( -- * Whole-program reports
    reportProgram
  , reportGram
  , reportContext
  , reportWitness
    -- * Pieces, for the assembled document
  , programHeader
  , typedGramReport
    -- * Tables
  , table
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

-- A header row, a rule under it, then the rows. Each line is quoted so its indentation shows.
-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> mapM_ print (lines (table ["name", "verdict"] [["park", "SAFE"], ["example-B", "UNSAFE"]]))
-- "  name      verdict"
-- "  \9472\9472\9472\9472\9472\9472\9472\9472\9472 \9472\9472\9472\9472\9472\9472\9472"
-- "  park      SAFE"
-- "  example-B UNSAFE"

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

-- The witness minor of an unsafe verdict is hung under the value, not left to start a line of its own.
-- >>> :m + Drop.Theory.Program.Typing
-- >>> mapM_ print (verdictField Unreachable)
-- "  verdict                         : UNREACHABLE (the zero map: no state, so no"
-- "                                    obligation)"
-- >>> mapM_ print (either (const []) (verdictField . verdict) (checkProgram spreadAndRead))
-- "  verdict                         : UNSAFE (slice rank 2, so the temporary"
-- "                                    carries 1 dimension(s) of information"
-- "                                    about the input)"
-- "                                    witness minor at rows (0,1) columns (0,1):"
-- "                                    1/2 /= 0"

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

-- The source of spread-and-park, then what the checker knows of it.
-- >>> mapM_ print (programHeader spreadAndPark)
-- "    \9474 -- program (a): spread and park"
-- "    \9474 let t = new |0> in"
-- "    \9474   t1 := H t;  v1 := v"
-- "    \9474   drop t1;"
-- "    \9474   return v1"
-- ""
-- "  temporary                       : tmp[2], allocated in |0>"
-- "  visible register                : vis[2]"
-- "  literally of the shape sep(R,W)  : no"
-- "  denotation against the machine  : agree"
-- "  the two routes to the criterion  : agree"
-- "  verdict                         : SAFE, parked on the line [1,1]"
-- >>> mapM_ print (programHeader (Program "p" "v" 2 (Ret "v")))
-- "    \9474 -- p"
-- "    \9474   return v"
-- ""
-- "  TYPE ERROR                      : a program must be `let t = new i0 in e`"

reportProgram :: Program -> String
reportProgram = unlines . programHeader

-- >>> mapM_ print (take 3 (lines (reportProgram spreadAndRead)))
-- "    \9474 -- example (B) = program (b): spread and read"
-- "    \9474 let t = new |0> in"
-- "    \9474   t1 := H t;  v1 := v"

reportGram :: Program -> String
reportGram p = case checkProgram p of
  Left e   -> unlines (kv "TYPE ERROR" (show e))
  Right tp -> unlines (typedGramReport tp)

-- >>> mapM_ print (take 6 (lines (reportGram spreadAndPark)))
-- ""
-- "    core map  K : H_2  \8594  H_2 (x) H_2"
-- ""
-- "                  0       1"
-- "      (0,0)  sqrt2/2       0"
-- "      (0,1)        0 sqrt2/2"
-- >>> mapM_ print (lines (reportGram (Program "p" "v" 2 (Ret "v"))))
-- "  TYPE ERROR                      : a program must be `let t = new i0 in e`"

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

-- The slice, Gram and Choi ranks line, for spread-and-read.
-- >>> mapM_ print (filter (\l -> take 7 (dropWhile (== ' ') l) == "slice /") (either (const []) typedGramReport (checkProgram spreadAndRead)))
-- "  slice / Gram / Choi rank        : 2 / 2 / 2 (the three agree)"

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

-- >>> mapM_ print (take 4 (lines (reportContext spreadAndPark)))
-- "  A client appends one gate to the visible register and reads outcome"
-- "  statistics; the temporary is already gone. This is everything it can see."
-- ""
-- "  continuation @ input outcome statistics"
-- >>> mapM_ print (filter (\l -> take 6 (dropWhile (== ' ') l) == "its ra") (lines (reportContext spreadAndPark)))
-- "  its rank                        : 1"

reportWitness :: Program -> String
reportWitness p = case checkProgram p of
  Left e   -> unlines (kv "TYPE ERROR" (show e))
  Right tp -> unlines (explainWitness tp (synthesize tp))

-- >>> mapM_ print (take 2 (lines (reportWitness spreadAndRead)))
-- "  no source witness for           : example (B) = program (b): spread and read"
-- "  reason                          : the drop is unsafe: the slices span 2"
-- >>> mapM_ print (take 3 (lines (reportWitness spreadAndPark)))
-- "  parked state  g                 : [sqrt2/2, sqrt2/2]"
-- "  its ray  [g]                    : [1, 1]"
-- ""
