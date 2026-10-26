-- Drop.Lang.Scalar: the numbers a program computes with.
--
-- Question: What is an amplitude here, and why is it never a floating-point number?
-- Answer:   An exact field element. Every gate the corpus uses has entries in Q, in Q[sqrt2]
--           (the Hadamard's 1/sqrt2) or in Q(zeta_{2^k}) (phases, the T gate's zeta_8, cos(pi/8)
--           at level 4). A verdict is an equation between such numbers, so it is decided
--           exactly: no tolerance, no rounding, no "close enough".
-- Paper:    sec:factor (the field the verdict is exact over), app:implementation (the scan
--           that keeps inexact numbers out of the decision code).
-- Shapes:   Rational      a/b, as Haskell has it.
--           QS2 a b       a + b*sqrt2, two rationals.
--           Cyclo k cs    an element of Q(zeta_{2^k}): 2^(k-1) rational coefficients of
--                         1, zeta, zeta^2, ..., reduced by zeta^(2^(k-1)) = -1 and to the least
--                         level that holds the element, so (==) is equality in the field.
--           Conj a        conjugation: the identity on the real fields, zeta -> 1/zeta on the tower.
--           Amp a         a field a program may run over: Eq, Fractional, Conj and a printed form.

module Drop.Lang.Scalar where

import Data.List (intercalate)
import Data.Ratio (numerator, denominator)

-- Rationals: only their printed form is ours.

-- | A rational as the paper prints it: an integer, or numerator/denominator.
showRat :: Rational -> String
showRat r
  | denominator r == 1 = show (numerator r)
  | otherwise          = show (numerator r) ++ "/" ++ show (denominator r)

-- >>> showRat 3
-- "3"
-- >>> showRat (-3/6)
-- "-1/2"
-- >>> showRat 0
-- "0"

-- Q[sqrt2]: the field of the Hadamard gate.

-- | a + b*sqrt2 with a, b in Q.
data QS2 = QS2 !Rational !Rational deriving (Eq, Ord)

-- >>> QS2 1 2
-- 1+2*r2
-- >>> QS2 1 2 == QS2 1 2
-- True
-- >>> QS2 0 1
-- 1*r2

instance Num QS2 where
  QS2 a b + QS2 c d = QS2 (a + c) (b + d)
  QS2 a b - QS2 c d = QS2 (a - c) (b - d)
  QS2 a b * QS2 c d = QS2 (a*c + 2*b*d) (a*d + b*c)
  negate (QS2 a b)  = QS2 (negate a) (negate b)
  fromInteger n     = QS2 (fromInteger n) 0
  -- exact sign of a + b*sqrt2: when a and b disagree in sign, compare a^2
  -- against 2b^2 in Q
  signum (QS2 a b)
    | a == 0 && b == 0       = 0
    | a >= 0 && b >= 0       = 1
    | a <= 0 && b <= 0       = -1
    | a > 0                  = if a*a > 2*b*b then 1 else -1   -- b < 0
    | otherwise              = if 2*b*b > a*a then 1 else -1   -- a < 0, b > 0
  abs x = x * signum x

-- >>> QS2 1 1 + QS2 2 (-3)
-- 3-2*r2
-- >>> QS2 1 1 * QS2 1 (-1)
-- -1
-- >>> signum (QS2 1 (-1))
-- -1
-- >>> signum (QS2 (-3) 2)
-- -1
-- >>> abs (QS2 1 (-1))
-- -1+1*r2

instance Fractional QS2 where
  recip (QS2 a b) =
    let n = a*a - 2*b*b   -- nonzero for nonzero (a, b): sqrt2 is irrational
    in if a == 0 && b == 0
         then error "QS2: division by zero"   -- refusal: division by zero
         else QS2 (a / n) (negate b / n)
  fromRational r = QS2 r 0

-- >>> recip (QS2 1 1)
-- -1+1*r2
-- >>> recip (QS2 1 1) * QS2 1 1
-- 1
-- >>> 3 / QS2 2 0
-- 3/2

sqrt2 :: QS2
sqrt2 = QS2 0 1

-- >>> sqrt2
-- 1*r2
-- >>> sqrt2 * sqrt2
-- 2

invSqrt2 :: QS2   -- 1/sqrt2 = sqrt2/2
invSqrt2 = QS2 0 (1/2)

-- >>> invSqrt2
-- 1/2*r2
-- >>> recip sqrt2 == invSqrt2
-- True
-- >>> invSqrt2 * invSqrt2
-- 1/2

-- | Numeric sign in Q[sqrt2].  The derived Ord on QS2 is lexicographic on
-- the coefficient pair rather than the numeric order; only signum is numeric.
qs2Sign :: QS2 -> Int
qs2Sign v = case signum v of
  QS2 s _ | s > 0     -> 1
          | s < 0     -> -1
          | otherwise -> 0

-- >>> qs2Sign (QS2 1 (-1))
-- -1
-- >>> qs2Sign (QS2 0 0)
-- 0
-- >>> qs2Sign (QS2 (-1) 1)
-- 1
-- >>> QS2 1 (-1) < QS2 2 (-100)
-- True

cmpQS2 :: QS2 -> QS2 -> Ordering
cmpQS2 a b = compare (qs2Sign (a - b)) 0

-- >>> cmpQS2 sqrt2 (QS2 1 0)
-- GT
-- >>> cmpQS2 sqrt2 (QS2 3 (-1))
-- LT
-- >>> cmpQS2 sqrt2 sqrt2
-- EQ

-- Conjugation and the printed form: what a program's scalars must provide.

-- | Complex conjugation: the identity on the real fields here, and
-- zeta -> zeta^{-1} on the cyclotomic tower below.
class Conj a where
  conj :: a -> a

-- >>> conj (3 :: Rational)
-- 3 % 1
-- >>> conj (QS2 1 2)
-- 1+2*r2

-- | The probability form |z|^2 = z * conj z, called at every norm site in
-- the package instead of plain squaring, which would give a complex
-- "probability" for a complex amplitude.
normSq :: (Num a, Conj a) => a -> a
normSq x = x * conj x

-- >>> normSq (3 :: Rational)
-- 9 % 1
-- >>> normSq (QS2 1 1)
-- 3+2*r2
-- >>> normSq invSqrt2
-- 1/2

instance Conj Rational where
  conj = id

instance Conj QS2 where
  conj = id

-- | The scalars a program may run over: an exact field with a printed form.
class (Eq a, Fractional a, Conj a) => Amp a where
  showAmp :: a -> String

instance Amp Rational where
  showAmp = showRat

instance Amp QS2 where
  showAmp (QS2 a b)
    | b == 0    = showRat a
    | a == 0    = showRat b ++ "*r2"
    | otherwise = showRat a ++ (if b > 0 then "+" else "") ++ showRat b ++ "*r2"

instance Show QS2 where
  show = showAmp

-- >>> showAmp (3/4 :: Rational)
-- "3/4"
-- >>> showAmp (QS2 2 0)
-- "2"
-- >>> showAmp (QS2 0 (1/2))
-- "1/2*r2"
-- >>> showAmp (QS2 1 (-3))
-- "1-3*r2"

-- Q(zeta_{2^k}): the tower of the phase gates.
--
-- Level k >= 1 is Q[x]/(x^N + 1) with N = 2^{k-1} and x = zeta_{2^k}; the
-- modulus is the 2^k-th cyclotomic polynomial, irreducible over Q, so the
-- quotient is a field.  Level 2 is Q(i), level 3 contains sqrt2 and so the
-- Hadamard gate, level 4 contains cos(pi/8).

-- | Invariant: @length coeffs == 2^(level-1)@ and the element is reduced to
-- its least containing level, so (==) is field equality.
data Cyclo = Cyclo !Int ![Rational] deriving (Eq, Show)

-- >>> Cyclo 2 [0, 1]
-- Cyclo 2 [0 % 1,1 % 1]
-- >>> Cyclo 1 [3] == Cyclo 1 [3]
-- True

levelC :: Cyclo -> Int
levelC (Cyclo k _) = k

-- >>> levelC (Cyclo 3 [0, 1, 0, 0])
-- 3
-- >>> levelC (zetaC 4 * zetaC 4)
-- 3

degC :: Int -> Int
degC k = 2 ^ (k - 1)

-- >>> degC 1
-- 1
-- >>> degC 3
-- 4
-- >>> degC 4
-- 8

-- | Smart constructor: reduce to the least containing level.  An element of
-- level k lies in level k-1 exactly when its odd-position coefficients all
-- vanish.
mkC :: Int -> [Rational] -> Cyclo
mkC k cs
  | length cs /= degC k = error "mkC: wrong coefficient count"   -- refusal: the list must have degC k entries
  | k > 1 && all (== 0) odds = mkC (k - 1) evens
  | otherwise = Cyclo k cs
  where
    evens = [ c | (i, c) <- zip [0 :: Int ..] cs, even i ]
    odds  = [ c | (i, c) <- zip [0 :: Int ..] cs, odd i ]

-- >>> mkC 1 [5]
-- Cyclo 1 [5 % 1]
-- >>> mkC 2 [1, 0]
-- Cyclo 1 [1 % 1]
-- >>> mkC 3 [0, 1, 0, 0]
-- Cyclo 3 [0 % 1,1 % 1,0 % 1,0 % 1]
-- >>> mkC 4 [0, 0, 1, 0, 0, 0, 0, 0] == zetaC 3
-- True

-- | Coefficients of an element re-expressed at level @k@, via
-- @zeta_{2^j} = zeta_{2^k}^{2^{k-j}}@.
liftTo :: Int -> Cyclo -> [Rational]
liftTo k (Cyclo j cs)
  | j > k     = error "liftTo: cannot lower"   -- refusal: an element is lifted up the tower, never down
  | otherwise = [ get i | i <- [0 .. degC k - 1] ]
  where
    stride = 2 ^ (k - j)
    -- impossible: i is a multiple of stride below degC k, so i / stride is below degC j = length cs
    get i = if i `mod` stride == 0 then cs !! (i `div` stride) else 0

-- >>> liftTo 3 (Cyclo 1 [2])
-- [2 % 1,0 % 1,0 % 1,0 % 1]
-- >>> liftTo 3 (Cyclo 2 [0, 1])
-- [0 % 1,0 % 1,1 % 1,0 % 1]
-- >>> liftTo 2 (zetaC 2)
-- [0 % 1,1 % 1]

withCommon :: Cyclo -> Cyclo -> ([Rational] -> [Rational] -> [Rational]) -> Cyclo
withCommon a b f = mkC k (f (liftTo k a) (liftTo k b))
  where k = max (levelC a) (levelC b)

-- >>> showAmp (withCommon 1 (zetaC 2) (zipWith (+)))
-- "1+1*z4"
-- >>> showAmp (withCommon (zetaC 3) (zetaC 3) (zipWith (-)))
-- "0"

-- | Multiply two coefficient vectors modulo x^N + 1.
mulMod :: [Rational] -> [Rational] -> [Rational]
mulMod as bs = foldl place (replicate n 0) terms
  where
    n = length as
    terms = [ (i + j, a * b) | (i, a) <- zip [0 ..] as, a /= 0
                             , (j, b) <- zip [0 ..] bs, b /= 0 ]
    place acc (m, v)
      | m < n     = bump m v acc
      | otherwise = bump (m - n) (negate v) acc   -- x^N = -1
    -- impossible: p is below n, the length of the accumulator
    bump p v l = take p l ++ [l !! p + v] ++ drop (p + 1) l

-- >>> mulMod [1] [3]
-- [3 % 1]
-- >>> mulMod [0, 1] [0, 1]
-- [(-1) % 1,0 % 1]
-- >>> mulMod [0, 0, 1, 0] [0, 0, 1, 0]
-- [(-1) % 1,0 % 1,0 % 1,0 % 1]

instance Num Cyclo where
  a + b = withCommon a b (zipWith (+))
  a - b = withCommon a b (zipWith (-))
  a * b = withCommon a b mulMod
  negate (Cyclo k cs) = Cyclo k (map negate cs)
  fromInteger n = Cyclo 1 [fromInteger n]
  abs    = error "Cyclo: abs undefined (complex field)"   -- refusal: the complex field has no absolute value
  signum = error "Cyclo: signum undefined (complex field)"   -- refusal: the complex field has no sign

-- >>> showAmp (1 + zetaC 2)
-- "1+1*z4"
-- >>> showAmp (zetaC 2 * zetaC 2)
-- "-1"
-- >>> showAmp (zetaC 3 - zetaC 3)
-- "0"
-- >>> showAmp (negate (zetaC 2))
-- "-1*z4"

-- | Exact Gauss-Jordan solve over Q.  'Nothing' when the columns are
-- dependent or the system is inconsistent.  Used for recip and for the
-- real-subfield decomposition.
solveLin :: [[Rational]] -> [Rational] -> Maybe [Rational]
solveLin [] _ = Nothing
solveLin m@(row0 : _) rhs = go (zip m rhs) [] 0
  where
    n = length row0
    go rows pivs col
      | col == n =
          -- every column pivoted and was eliminated from all other rows, so
          -- the leftover rows have zero coefficients and the right-hand side
          -- must agree
          if all (\(_, v) -> v == 0) rows
            then mapM (\c -> case lookup c pivs of
                               -- impossible: a pivot row has n entries and c is below n
                               Just (r, v) -> Just (v / (r !! c))
                               Nothing     -> Nothing)
                      [0 .. n - 1]
            else Nothing
      | otherwise =
          -- impossible: every row has n entries and col is below n
          case break (\(r, _) -> r !! col /= 0) rows of
            (_, []) -> Nothing                        -- no pivot
            (before, p : after) ->
              let elim = flip sub p
              in go (map elim (before ++ after))
                    ([ (c, elim rv) | (c, rv) <- pivs ] ++ [(col, p)])
                    (col + 1)
      where
        sub (r, v) (pr, pv) =
          -- impossible: both rows have n entries and col is below n
          let f = r !! col / pr !! col
          in (zipWith (\x y -> y - f * x) pr r, v - f * pv)

-- >>> solveLin [[1, 0], [0, 1]] [3, 4]
-- Just [3 % 1,4 % 1]
-- >>> solveLin [[2, 1], [1, 3]] [5, 10]
-- Just [1 % 1,3 % 1]
-- >>> solveLin [[1, 2], [2, 4]] [1, 2]
-- Nothing
-- >>> solveLin [[1, 1], [1, 1]] [1, 2]
-- Nothing

instance Fractional Cyclo where
  fromRational r = Cyclo 1 [r]
  -- the inverse is the solution of the multiplication-by-z linear system
  recip (Cyclo k cs)
    | all (== 0) cs = error "Cyclo: division by zero"   -- refusal: division by zero
    | otherwise =
        let n = degC k
            col j = mulMod cs [ if i == j then 1 else 0 | i <- [0 .. n - 1] ]
            -- impossible: col j has n entries and i is below n
            m = [ [ col j !! i | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
            e0 = 1 : replicate (n - 1) 0
        in case solveLin m e0 of
             Just v  -> mkC k v
             -- impossible: multiplication by a nonzero element of a field is invertible
             Nothing -> error "Cyclo: recip failed"

-- >>> showAmp (recip (2 :: Cyclo))
-- "1/2"
-- >>> showAmp (recip (zetaC 2))
-- "-1*z4"
-- >>> recip (1 + zetaC 3) * (1 + zetaC 3) == 1
-- True
-- >>> showAmp (1 / sqrt2C)
-- "1/2*z8+-1/2*z8^3"

instance Conj Cyclo where
  -- conj zeta = zeta^{-1}; with zeta^N = -1 this sends the coefficient at
  -- position j >= 1 to minus the coefficient at position N - j
  conj (Cyclo k cs) = mkC k [ get i | i <- [0 .. n - 1] ]
    where
      n = degC k
      -- impossible: cs has n entries, so position 0 exists
      get 0 = cs !! 0
      -- impossible: for i in 1 .. n - 1, n - i is in 1 .. n - 1, below the n entries of cs
      get i = negate (cs !! (n - i))

-- >>> showAmp (conj (zetaC 2))
-- "-1*z4"
-- >>> showAmp (conj (zetaC 3))
-- "-1*z8^3"
-- >>> conj (zetaC 3) == recip (zetaC 3)
-- True
-- >>> showAmp (conj (5 :: Cyclo))
-- "5"

-- Generators

-- | @zetaC k@ is the primitive 2^k-th root of unity.
zetaC :: Int -> Cyclo
zetaC 0 = 1
zetaC 1 = Cyclo 1 [-1]
zetaC k = Cyclo k (0 : 1 : replicate (degC k - 2) 0)

-- >>> showAmp (zetaC 0)
-- "1"
-- >>> showAmp (zetaC 1)
-- "-1"
-- >>> showAmp (zetaC 3 * zetaC 3)
-- "1*z4"
-- >>> zetaC 3 ^ (8 :: Int) == 1
-- True
-- >>> levelC (zetaC 4 * zetaC 4)
-- 3

-- | @zetaP k j@ is @zetaC k@ raised to any integer power @j@.
zetaP :: Int -> Integer -> Cyclo
zetaP 0 _ = 1
zetaP k j = mkC k [ v i | i <- [0 .. n - 1] ]
  where
    j' = fromInteger (j `mod` (2 ^ k)) :: Int
    n  = degC k
    v i | j' < n    = if i == j' then 1 else 0
        | otherwise = if i == j' - n then -1 else 0   -- zeta^{N+r} = -zeta^r

-- >>> showAmp (zetaP 3 2)
-- "1*z4"
-- >>> showAmp (zetaP 3 4)
-- "-1"
-- >>> zetaP 3 (-1) == conj (zetaC 3)
-- True
-- >>> sum [ zetaP 3 k | k <- [0 .. 7] ] == 0
-- True

iC :: Cyclo          -- zeta_4
iC = zetaC 2

-- >>> showAmp iC
-- "1*z4"
-- >>> iC * iC == -1
-- True

sqrt2C :: Cyclo      -- zeta_8 + zeta_8^{-1}
sqrt2C = zetaC 3 + conj (zetaC 3)

-- >>> showAmp sqrt2C
-- "1*z8+-1*z8^3"
-- >>> sqrt2C * sqrt2C == 2
-- True

invSqrt2C :: Cyclo
invSqrt2C = sqrt2C / 2

-- >>> showAmp invSqrt2C
-- "1/2*z8+-1/2*z8^3"
-- >>> invSqrt2C * sqrt2C == 1
-- True

cosPi8, sinPi8 :: Cyclo
cosPi8 = (zetaC 4 + conj (zetaC 4)) / 2
sinPi8 = (sqrt2C - 1) * cosPi8        -- tan(pi/8) = sqrt2 - 1

-- >>> levelC cosPi8
-- 4
-- >>> cosPi8 * cosPi8 + sinPi8 * sinPi8 == 1
-- True
-- >>> 2 * cosPi8 * cosPi8 - 1 == invSqrt2C
-- True

embedQS2 :: QS2 -> Cyclo
embedQS2 (QS2 a b) = fromRational a + fromRational b * sqrt2C

-- >>> showAmp (embedQS2 (QS2 3 0))
-- "3"
-- >>> embedQS2 sqrt2 == sqrt2C
-- True
-- >>> embedQS2 (QS2 2 (-5)) == 2 - 5 * sqrt2C
-- True

-- Exact sign in the real subfield of Q(zeta_16)
--
-- Every real element of Q(zeta_16) is p + q*cos(pi/8) with p, q in Q[sqrt2],
-- because tan(pi/8) = sqrt2 - 1 makes {1, sqrt2, c, sqrt2*c} a spanning set.
-- Deciding the sign of p + q*c then happens in Q[sqrt2]'s exact order, using
-- c^2 = (2 + sqrt2)/4.

-- | Decompose a real element of level at most 4 as p + q*cos(pi/8).
realPartsQ :: Cyclo -> Maybe (QS2, QS2)
realPartsQ x
  | conj x /= x || levelC x > 4 = Nothing
  | otherwise =
      let basis = [1, sqrt2C, cosPi8, sqrt2C * cosPi8]
          k = 4
          cols = [ liftTo k b | b <- basis ]
          -- impossible: cols has 4 columns of degC 4 = 8 entries, and j is below 4, i below 8
          m = [ [ cols !! j !! i | j <- [0 .. 3] ] | i <- [0 .. degC k - 1] ]
          rhs = liftTo k x
      in case solveLin m rhs of
           Just [p0, p1, q0, q1] -> Just (QS2 p0 p1, QS2 q0 q1)
           _ -> Nothing

-- >>> realPartsQ 5
-- Just (5,0)
-- >>> realPartsQ cosPi8
-- Just (0,1)
-- >>> realPartsQ iC
-- Nothing

-- | Sign of p + q*c with c = cos(pi/8) > 0, decided in Q[sqrt2].
signPQc :: QS2 -> QS2 -> Int
signPQc p q
  | q == 0 = qs2Sign p
  | p == 0 = qs2Sign q
  | qs2Sign p > 0 && qs2Sign q > 0 = 1
  | qs2Sign p < 0 && qs2Sign q < 0 = -1
  | otherwise =
      -- opposite signs: sign(p + q c) is sign(p) exactly when p^2 > q^2 c^2
      let c2 = QS2 (1 / 2) (1 / 4)   -- (2 + sqrt2)/4
      in case cmpQS2 (p * p) (q * q * c2) of
           GT -> qs2Sign p
           LT -> qs2Sign q
           EQ -> 0

-- >>> signPQc 1 1
-- 1
-- >>> signPQc 0 (-1)
-- -1
-- >>> signPQc 1 (-1)
-- 1
-- >>> signPQc (-1) 1
-- -1

-- | Exact sign of a real element of level at most 4: -1, 0 or 1.
realSign :: Cyclo -> Int
realSign x = case realPartsQ x of
  Just (p, q) -> signPQc p q
  Nothing     -> error "realSign: not a real element of Q(zeta_16)"   -- refusal: only real elements of level 4 or less have a sign

-- >>> realSign 0
-- 0
-- >>> realSign cosPi8
-- 1
-- >>> realSign (sinPi8 - cosPi8)
-- -1
-- >>> realSign (5 / 4 - 7 * sqrt2C / 8)
-- 1

-- | A real element that happens to lie in Q[sqrt2].
toQS2 :: Cyclo -> Maybe QS2
toQS2 x = case realPartsQ x of
  Just (p, q) | q == 0 -> Just p
  _                    -> Nothing

-- >>> toQS2 sqrt2C
-- Just 1*r2
-- >>> toQS2 cosPi8
-- Nothing
-- >>> toQS2 iC
-- Nothing
-- >>> toQS2 (embedQS2 (QS2 2 (-5)))
-- Just 2-5*r2

instance Amp Cyclo where
  showAmp (Cyclo 1 [c]) = showRat c
  showAmp (Cyclo k cs) =
    intercalate "+" [ term i c | (i, c) <- zip [0 :: Int ..] cs, c /= 0 ]
    where
      z = "z" ++ show ((2 :: Integer) ^ k)
      term 0 c = showRat c
      term 1 c = showRat c ++ "*" ++ z
      term i c = showRat c ++ "*" ++ z ++ "^" ++ show i

-- >>> showAmp (3 :: Cyclo)
-- "3"
-- >>> showAmp (zetaC 2)
-- "1*z4"
-- >>> showAmp (1 + zetaC 3)
-- "1+1*z8"
-- >>> showAmp (normSq (1 + iC))
-- "2"

-- The list dqt-test asserts: the field's identities, each with the claim it checks.
cycloChecks :: [(String, Bool)]
cycloChecks =
  [ ("i^2 = -1", iC * iC == -1)
  , ("z8^2 = i, z16^2 = z8 (tower embeddings)",
     zetaC 3 * zetaC 3 == iC && zetaC 4 * zetaC 4 == zetaC 3)
  , ("sqrt2^2 = 2", sqrt2C * sqrt2C == 2)
  , ("recip: z8, sqrt2, 1+z8, 3+2*z16^3 all invert exactly",
     recip (zetaC 3) == conj (zetaC 3)
       && recip sqrt2C * sqrt2C == 1
       && recip (1 + zetaC 3) * (1 + zetaC 3) == 1
       && recip (3 + 2 * zetaP 4 3) * (3 + 2 * zetaP 4 3) == 1)
  , ("normSq z8 = 1, normSq (1+i) = 2 (squaring would give 2i)",
     normSq (zetaC 3) == 1 && normSq (1 + iC) == 2)
  , ("conj is an involutive field homomorphism",
     conj (conj (1 + 2 * zetaC 4 + 3 * iC)) == 1 + 2 * zetaC 4 + 3 * iC
       && conj ((1 + zetaC 3) * (2 - iC)) == conj (1 + zetaC 3) * conj (2 - iC))
  , ("normalization: z16^2 reduces to level 3, z8^4 to level 1",
     levelC (zetaC 4 * zetaC 4) == 3 && levelC (zetaC 3 ^ (4 :: Int)) == 1)
  , ("cos^2(pi/8) + sin^2(pi/8) = 1 and 2cos^2 - 1 = cos(pi/4)",
     cosPi8 * cosPi8 + sinPi8 * sinPi8 == 1
       && 2 * cosPi8 * cosPi8 - 1 == sqrt2C / 2)
  , ("toQS2 extracts what embedQS2 embeds, and rejects cos(pi/8)",
     toQS2 (embedQS2 (QS2 2 (-5))) == Just (QS2 2 (-5))
       && toQS2 cosPi8 == Nothing)
  , ("realSign: cos > sin at pi/8; 5/4 - 7*sqrt2/8 > 0 (a 100 vs 98 margin)",
     realSign cosPi8 == 1 && realSign (sinPi8 - cosPi8) == -1
       && realSign (5 / 4 - 7 * sqrt2C / 8) == 1
       && realSign (cosPi8 - cosPi8) == 0)
  , ("geometric sum: the eight 8th roots of unity sum to 0",
     sum [ zetaP 3 k | k <- [0 .. 7] ] == 0)
  ]

-- >>> length cycloChecks
-- 11
-- >>> all snd cycloChecks
-- True
