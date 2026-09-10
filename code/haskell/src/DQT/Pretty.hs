-- |
-- Module      : DQT.Pretty
--
-- Typesetting for the printed reports, so a run can be read on its own.
-- Everything is built from 'measure' and 'colonCol', so
-- the document cannot drift out of alignment one line at a time.
module DQT.Pretty
  ( -- * The measure
    measure, colonCol
    -- * Rules and headings
  , rule, thickRule, sectionHead, subHead
    -- * Paragraphs and fields
  , para, paraAt, kv, kvs, bullet, gutter, blank
    -- * Tables and matrices
  , numTable, boxedMat
    -- * Words, not booleans
  , yesNo, okBad
    -- * Utilities
  , wrapAt, padTo, padLeft
  ) where

import Data.Char (toUpper)

-- | Every rule, wrap and header is built from this, so the document cannot
-- drift out of alignment one line at a time.
measure :: Int
measure = 78

-- | The single column at which every @key : value@ line in the document
-- breaks.  One column for the whole document, not one per block, so scanning
-- down a page follows a single edge.
colonCol :: Int
colonCol = 34

rule, thickRule :: String
rule      = replicate measure '\9472'   -- U+2500 BOX DRAWINGS LIGHT HORIZONTAL
thickRule = replicate measure '\9552'   -- U+2550 BOX DRAWINGS DOUBLE HORIZONTAL

-- | A numbered section heading, with the title on the left and a gloss set
-- flush right on the same rule.  The gloss says what the section is for.
sectionHead :: Int -> String -> String -> [String]
sectionHead n title gloss =
  [ "", left ++ replicate fill '\9472' ++ right, "" ]
  where
    left  = "\9472\9472 " ++ show n ++ "  " ++ map toUpper title ++ " "
    right = if null gloss then "\9472\9472" else " " ++ gloss ++ " \9472\9472"
    fill  = max 2 (measure - length left - length right)

-- | A minor heading inside a section: the name of the thing being reported.
subHead :: String -> [String]
subHead t = [ "", "  " ++ t, "  " ++ replicate (min (measure - 2) (length t)) '\9472' ]

-- | A paragraph, wrapped to the measure and indented two.
para :: String -> [String]
para = paraAt 2

paraAt :: Int -> String -> [String]
paraAt n s = [ replicate n ' ' ++ l | l <- wrapAt (measure - n) s ]

blank :: [String]
blank = [""]

-- | One @key : value@ line, broken at 'colonCol', with the value wrapped and
-- hung under itself.
kv :: String -> String -> [String]
kv k v = case wrapAt (measure - colonCol - 2) v of
  []       -> [ lead ++ ":" ]
  (l : ls) -> (lead ++ ": " ++ l)
              : [ replicate (colonCol + 2) ' ' ++ x | x <- ls ]
  -- 'padExact', not 'padTo': the colon is the separator here, so a key that
  -- already fills the field must not be given a space of its own.  With
  -- 'padTo' every key of length @colonCol - 3@ or more put its colon one
  -- column right of every other, which is the single edge this whole module
  -- exists to keep.
  where lead = "  " ++ padExact (colonCol - 3) k ++ " "

kvs :: [(String, String)] -> [String]
kvs = concatMap (uncurry kv)

bullet :: String -> [String]
bullet s = case wrapAt (measure - 6) s of
  []       -> []
  (l : ls) -> ("    \9679 " ++ l) : [ "      " ++ x | x <- ls ]

-- | Source text, behind a left gutter so it cannot be mistaken for prose.
gutter :: String -> [String]
gutter src = [ "    \9474 " ++ l | l <- lines src ]

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
    -- Exact, for the reason 'kv' gives: each column supplies its own leading
    -- space below, so padding the label field must not add one.  With 'padTo'
    -- the header row -- whose label is empty -- sat one column left of every
    -- row of numbers under it.
    pad0 r = "      " ++ padExact lw r
    widths = [ maximum (length c : map length col)
             | (c, col) <- zip colL (columns rows) ]
    columns xss
      | any null xss || null xss = []
      | otherwise = map firstOf xss : columns (map restOf xss)
    firstOf (x : _)  = x
    firstOf []       = ""
    restOf  (_ : xs) = xs
    restOf  []       = []

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

-- | Answers in the vocabulary of the question asked, not a bare boolean.
yesNo :: Bool -> String
yesNo b = if b then "yes" else "no"

-- | @okBad good bad b@: the failing word is upper-cased, so that a failure in
-- a page of passes is findable by eye.
okBad :: String -> String -> Bool -> String
okBad good bad b = if b then good else map toUpper bad

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

-- | Pad on the right to at least @w@, /and always by at least one space/, so
-- that two fields laid side by side cannot run together.  Use it where the
-- padding is the only separator; where a separator is supplied independently
-- -- a colon, a space between columns -- use 'padExact'.
padTo, padLeft :: Int -> String -> String
padTo   w x = x ++ replicate (max 1 (w - length x)) ' '
padLeft w x = replicate (max 0 (w - length x)) ' ' ++ x

-- | Pad on the right to exactly @w@, adding nothing to a string that is
-- already that long.  Private: it is the right choice only next to a
-- separator, and the two callers here both have one.
padExact :: Int -> String -> String
padExact w x = x ++ replicate (max 0 (w - length x)) ' '
