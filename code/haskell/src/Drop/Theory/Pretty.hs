-- Drop.Theory.Pretty: typesetting for the printed reports.
--
-- Question: How are the reports laid out, so that they can be read without the paper beside them?
-- Answer:   Rules, headings and wrapped paragraphs are built from one width, measure; every
--           key : value line breaks at one column, colonCol, so scanning down a page follows a
--           single edge. Tables and small matrices pad their columns to the widest cell. Booleans
--           print as words (yesNo, okBad), where okBad upper-cases the failing word so a failure
--           in a page of passes can be found by eye. Everything here is pure: a list of lines
--           in, a list of lines out.
-- Paper:    none; the paper shows the printed reports, not this module.
-- Shapes:   measure and colonCol   the two widths. Every other value is a list of lines.

module Drop.Theory.Pretty
  ( -- * The measure
    measure, colonCol
    -- * Rules and headings
  , rule, thickRule, sectionHead, subHead
    -- * Paragraphs and fields
  , para, kv, kvs, gutter, blank
    -- * Tables and matrices
  , numTable, boxedMat
    -- * Words, not booleans
  , yesNo, okBad
    -- * Utilities
  , wrapAt, padSep
  ) where

import Data.Char (toUpper)

-- | Every rule, wrap and header is built from this, so the document cannot
-- drift out of alignment one line at a time.
measure :: Int
measure = 78

-- >>> measure
-- 78

-- | The single column at which every @key : value@ line in the document
-- breaks.  One column for the whole document, not one per block, so scanning
-- down a page follows a single edge.
colonCol :: Int
colonCol = 34

-- >>> colonCol
-- 34

rule, thickRule :: String
rule      = replicate measure '\9472'   -- U+2500 BOX DRAWINGS LIGHT HORIZONTAL
thickRule = replicate measure '\9552'   -- U+2550 BOX DRAWINGS DOUBLE HORIZONTAL

-- Each rule is one box-drawing character repeated measure times (shown as its code point).
-- >>> (length rule, length thickRule)
-- (78,78)
-- >>> (take 2 rule, take 2 thickRule)
-- ("\9472\9472","\9552\9552")
-- >>> thickRule == replicate measure '\9552'
-- True

-- | A numbered section heading, with the title on the left and a gloss set
-- flush right on the same rule.  The gloss says what the section is for.
sectionHead :: Int -> String -> String -> [String]
sectionHead n title gloss =
  [ "", left ++ replicate fill '\9472' ++ right, "" ]
  where
    left  = "\9472\9472 " ++ show n ++ "  " ++ map toUpper title ++ " "
    right = if null gloss then "\9472\9472" else " " ++ gloss ++ " \9472\9472"
    fill  = max 2 (measure - length left - length right)

-- A numbered heading: the title in capitals on the left, the gloss flush right, all on one rule.
-- >>> mapM_ print (sectionHead 2 "the matrix" "what K is")
-- ""
-- "\9472\9472 2  THE MATRIX \9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472 what K is \9472\9472"
-- ""
-- >>> map length (sectionHead 2 "the matrix" "what K is")
-- [0,78,0]
-- >>> mapM_ print (sectionHead 1 "verdicts" "")
-- ""
-- "\9472\9472 1  VERDICTS \9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472"
-- ""

-- | A minor heading inside a section: the name of the thing being reported.
subHead :: String -> [String]
subHead t = [ "", "  " ++ t, "  " ++ replicate (min (measure - 2) (length t)) '\9472' ]

-- >>> mapM_ print (subHead "slice K_0")
-- ""
-- "  slice K_0"
-- "  \9472\9472\9472\9472\9472\9472\9472\9472\9472"

-- | A paragraph, wrapped to the measure and indented two.
para :: String -> [String]
para = paraAt 2

-- A paragraph is wrapped to the measure and indented two.
-- >>> mapM_ print (para "Discard safety is exactly that the slices all lie on one line, which says the temporary carried nothing about the visible input.")
-- "  Discard safety is exactly that the slices all lie on one line, which says"
-- "  the temporary carried nothing about the visible input."
-- >>> para ""
-- []

paraAt :: Int -> String -> [String]
paraAt n s = [ replicate n ' ' ++ l | l <- wrapAt (measure - n) s ]

-- >>> mapM_ print (paraAt 6 "Indented six, wrapped to a narrower line so the right edge stays where it was.")
-- "      Indented six, wrapped to a narrower line so the right edge stays where"
-- "      it was."

blank :: [String]
blank = [""]

-- >>> blank
-- [""]

-- | One @key : value@ line, broken at 'colonCol', with the value wrapped and
-- hung under itself.
kv :: String -> String -> [String]
kv k v = case wrapAt (measure - colonCol - 2) v of
  []       -> [ lead ++ ":" ]
  (l : ls) -> (lead ++ ": " ++ l)
              : [ replicate (colonCol + 2) ' ' ++ x | x <- ls ]
  where lead = "  " ++ padSep (colonCol - 3) k ++ " "

-- The colon is at one column for the whole document; a long value hangs under itself.
-- >>> mapM_ print (kv "temporary" "tmp[2], allocated in |0>")
-- "  temporary                       : tmp[2], allocated in |0>"
-- >>> mapM_ print (kv "verdict" "UNSAFE (slice rank 2, so the temporary carries 1 dimension(s) of information about the input)")
-- "  verdict                         : UNSAFE (slice rank 2, so the temporary"
-- "                                    carries 1 dimension(s) of information"
-- "                                    about the input)"
-- >>> kv "empty" ""
-- ["  empty                           :"]

kvs :: [(String, String)] -> [String]
kvs = concatMap (uncurry kv)

-- >>> mapM_ print (kvs [("a", "1"), ("longer key", "2")])
-- "  a                               : 1"
-- "  longer key                      : 2"

-- | Source text, behind a left gutter so it cannot be mistaken for prose.
gutter :: String -> [String]
gutter src = [ "    \9474 " ++ l | l <- lines src ]

-- >>> mapM_ print (gutter "let t = new |0> in\n  drop t")
-- "    \9474 let t = new |0> in"
-- "    \9474   drop t"

-- | A table with row labels down the left and right-aligned numeric columns.
-- Used for the denotation, the Kraus operators and the Gram matrix, where the labels are
-- basis states and carry meaning.
numTable :: String -> [String] -> [String] -> [[String]] -> [String]
numTable title rowL colL rows =
  [ "", "    " ++ title, "" ]
  ++ [ pad0 "" ++ concat [ " " ++ padLeft w c | (w, c) <- zip widths colL ] ]
  ++ [ pad0 r  ++ concat [ " " ++ padLeft w x | (w, x) <- zip widths row ]
     | (r, row) <- zip rowL rows ]
  where
    lw     = maximum (0 : map length rowL)
    pad0 r = "      " ++ padSep lw r
    widths = [ maximum (length c : map length col)
             | (c, col) <- zip colL (columns rows) ]
    columns xss
      | any null xss || null xss = []
      | otherwise = map firstOf xss : columns (map restOf xss)
    firstOf (x : _)  = x
    firstOf []       = ""
    restOf  (_ : xs) = xs
    restOf  []       = []

-- Row labels down the left, right-aligned columns.
-- >>> mapM_ print (numTable "K" ["(0,0)", "(1,0)"] ["0", "1"] [["1", "0"], ["0", "12"]])
-- ""
-- "    K"
-- ""
-- "            0  1"
-- "      (0,0)  1  0"
-- "      (1,0)  0 12"

-- | A small matrix with no meaningful labels, framed by square delimiters.  @W@ and @R@
-- are the whole use: they are operators, not indexed tables.
boxedMat :: String -> [[String]] -> [String]
boxedMat name rows =
  [ lead r ++ "[" ++ concat [ " " ++ padLeft w x | (w, x) <- zip widths row ]
    ++ " ]"
  | (r, row) <- zip [0 :: Int ..] rows ]
  where
    lead 0 = "    " ++ name ++ " = "
    lead _ = "    " ++ replicate (length name + 3) ' '
    widths = [ maximum (map length col) | col <- columns rows ]
    columns xss
      | any null xss || null xss = []
      | otherwise = map firstOf xss : columns (map restOf xss)
    firstOf (x : _)  = x
    firstOf []       = ""
    restOf  (_ : xs) = xs
    restOf  []       = []

-- >>> mapM_ print (boxedMat "W" [["1", "0"], ["0", "-1"]])
-- "    W = [ 1  0 ]"
-- "        [ 0 -1 ]"
-- >>> boxedMat "W" []
-- []

-- | Answers in the vocabulary of the question asked, not a bare boolean.
yesNo :: Bool -> String
yesNo b = if b then "yes" else "no"

-- >>> map yesNo [True, False]
-- ["yes","no"]

-- | @okBad good bad b@: the failing word is upper-cased, so that a failure in
-- a page of passes is findable by eye.
okBad :: String -> String -> Bool -> String
okBad good bad b = if b then good else map toUpper bad

-- Only the failing word is shouted.
-- >>> okBad "agree" "differ" True
-- "agree"
-- >>> okBad "agree" "differ" False
-- "DIFFER"

wrapAt :: Int -> String -> [String]
wrapAt w = go . words
  where
    go [] = []
    go ws = let (l, r) = takeLine ws "" in l : go r
    takeLine [] acc = (acc, [])
    takeLine (x : xs) acc
      | null acc                         = takeLine xs x
      | length acc + 1 + length x <= w   = takeLine xs (acc ++ " " ++ x)
      | otherwise                        = (acc, x : xs)

-- >>> wrapAt 10 "one two three four five"
-- ["one two","three four","five"]
-- >>> wrapAt 3 "abcdef gh"
-- ["abcdef","gh"]
-- >>> wrapAt 10 ""
-- []

-- | Pad to a column width, but always leave at least one trailing space, so
-- that adjacent columns stay separated even when a cell fills its width.
-- It is therefore NOT a pad-to-exactly-w: a caller that supplies its own
-- separator wants plain padding instead (see 'Drop.Theory.Report.table').
padSep, padLeft :: Int -> String -> String
padSep   w x = x ++ replicate (max 1 (w - length x)) ' '
padLeft w x = replicate (max 0 (w - length x)) ' ' ++ x

-- padSep pads to the width but always leaves a space after; padLeft pads on the left.
-- >>> padSep 5 "ab"
-- "ab   "
-- >>> padSep 2 "abcd"
-- "abcd "
-- >>> padLeft 5 "ab"
-- "   ab"
-- >>> padLeft 2 "abcd"
-- "abcd"
