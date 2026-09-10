-- Cyclo.hs: the 2-power cyclotomic tower Q(zeta_{2^k}), exactly.
--
-- Level k >= 1 is Q[x]/(x^N + 1) with N = 2^{k-1} and x = zeta_{2^k}; the
-- modulus is the 2^k-th cyclotomic polynomial, irreducible over Q, so the
-- quotient is a field.  Level 2 is Q(i), level 3 contains sqrt2 and so the
-- Hadamard gate, level 4 contains cos(pi/8).

module S.Lang.Cyclo where

import Data.List (intercalate)
import S.Lang.Ring

-- | Invariant: @length coeffs == 2^(level-1)@ and the element is reduced to
-- its least containing level, so (==) is field equality.
data Cyclo = Cyclo !Int ![Rational] deriving (Eq, Show)

levelC :: Cyclo -> Int
levelC (Cyclo k _) = k

degC :: Int -> Int
degC k = 2 ^ (k - 1)

-- | Smart constructor: reduce to the least containing level.  An element of
-- level k lies in level k-1 exactly when its odd-position coefficients all
-- vanish.
mkC :: Int -> [Rational] -> Cyclo
mkC k cs
  | length cs /= degC k = error "mkC: wrong coefficient count"
  | k > 1 && all (== 0) odds = mkC (k - 1) evens
  | otherwise = Cyclo k cs
  where
    evens = [ c | (i, c) <- zip [0 :: Int ..] cs, even i ]
    odds  = [ c | (i, c) <- zip [0 :: Int ..] cs, odd i ]

-- | Coefficients of an element re-expressed at level @k@, via
-- @zeta_{2^j} = zeta_{2^k}^{2^{k-j}}@.
liftTo :: Int -> Cyclo -> [Rational]
liftTo k (Cyclo j cs)
  | j > k     = error "liftTo: cannot lower"
  | otherwise = [ get i | i <- [0 .. degC k - 1] ]
  where
    stride = 2 ^ (k - j)
    get i = if i `mod` stride == 0 then cs !! (i `div` stride) else 0

withCommon :: Cyclo -> Cyclo -> ([Rational] -> [Rational] -> [Rational]) -> Cyclo
withCommon a b f = mkC k (f (liftTo k a) (liftTo k b))
  where k = max (levelC a) (levelC b)

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
    bump p v l = take p l ++ [l !! p + v] ++ drop (p + 1) l

instance Num Cyclo where
  a + b = withCommon a b (zipWith (+))
  a - b = withCommon a b (zipWith (-))
  a * b = withCommon a b mulMod
  negate (Cyclo k cs) = Cyclo k (map negate cs)
  fromInteger n = Cyclo 1 [fromInteger n]
  abs    = error "Cyclo: abs undefined (complex field)"
  signum = error "Cyclo: signum undefined (complex field)"

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
                               Just (r, v) -> Just (v / (r !! c))
                               Nothing     -> Nothing)
                      [0 .. n - 1]
            else Nothing
      | otherwise =
          case break (\(r, _) -> r !! col /= 0) rows of
            (_, []) -> Nothing                        -- no pivot
            (before, p : after) ->
              let elim = flip sub p
              in go (map elim (before ++ after))
                    ([ (c, elim rv) | (c, rv) <- pivs ] ++ [(col, p)])
                    (col + 1)
      where
        sub (r, v) (pr, pv) =
          let f = r !! col / pr !! col
          in (zipWith (\x y -> y - f * x) pr r, v - f * pv)

instance Fractional Cyclo where
  fromRational r = Cyclo 1 [r]
  -- the inverse is the solution of the multiplication-by-z linear system
  recip (Cyclo k cs)
    | all (== 0) cs = error "Cyclo: division by zero"
    | otherwise =
        let n = degC k
            col j = mulMod cs [ if i == j then 1 else 0 | i <- [0 .. n - 1] ]
            m = [ [ col j !! i | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]
            e0 = 1 : replicate (n - 1) 0
        in case solveLin m e0 of
             Just v  -> mkC k v
             Nothing -> error "Cyclo: recip failed"

instance Conj Cyclo where
  -- conj zeta = zeta^{-1}; with zeta^N = -1 this sends the coefficient at
  -- position j >= 1 to minus the coefficient at position N - j
  conj (Cyclo k cs) = mkC k [ get i | i <- [0 .. n - 1] ]
    where
      n = degC k
      get 0 = cs !! 0
      get i = negate (cs !! (n - i))

-- Generators

-- | @zetaC k@ is the primitive 2^k-th root of unity.
zetaC :: Int -> Cyclo
zetaC 0 = 1
zetaC 1 = Cyclo 1 [-1]
zetaC k = Cyclo k (0 : 1 : replicate (degC k - 2) 0)

-- | @zetaP k j@ is @zetaC k@ raised to any integer power @j@.
zetaP :: Int -> Integer -> Cyclo
zetaP 0 _ = 1
zetaP k j = mkC k [ v i | i <- [0 .. n - 1] ]
  where
    j' = fromInteger (j `mod` (2 ^ k)) :: Int
    n  = degC k
    v i | j' < n    = if i == j' then 1 else 0
        | otherwise = if i == j' - n then -1 else 0   -- zeta^{N+r} = -zeta^r

iC :: Cyclo          -- zeta_4
iC = zetaC 2

sqrt2C :: Cyclo      -- zeta_8 + zeta_8^{-1}
sqrt2C = zetaC 3 + conj (zetaC 3)

invSqrt2C :: Cyclo
invSqrt2C = sqrt2C / 2

cosPi8, sinPi8 :: Cyclo
cosPi8 = (zetaC 4 + conj (zetaC 4)) / 2
sinPi8 = (sqrt2C - 1) * cosPi8        -- tan(pi/8) = sqrt2 - 1

embedQS2 :: QS2 -> Cyclo
embedQS2 (QS2 a b) = fromRational a + fromRational b * sqrt2C

-- Exact Sign In The Real Subfield Of Q(zeta_16)
--
-- Every real element of Q(zeta_16) is p + q*cos(pi/8) with p, q in Q[sqrt2].
-- The real subfield is Q(c) with c = cos(pi/8), of degree 4, and c^2 =
-- (2 + sqrt2)/4 puts sqrt2 = 4c^2 - 2 and sqrt2*c = 4c^3 - 2c inside it, so
-- {1, sqrt2, c, sqrt2*c} spans the same space as {1, c, c^2, c^3} and is a
-- basis.  Deciding the sign of p + q*c then happens in Q[sqrt2]'s exact order,
-- using that same c^2.

-- | Decompose a real element of level at most 4 as p + q*cos(pi/8).
realPartsQ :: Cyclo -> Maybe (QS2, QS2)
realPartsQ x
  | conj x /= x || levelC x > 4 = Nothing
  | otherwise =
      let basis = [1, sqrt2C, cosPi8, sqrt2C * cosPi8]
          k = 4
          cols = [ liftTo k b | b <- basis ]
          m = [ [ cols !! j !! i | j <- [0 .. 3] ] | i <- [0 .. degC k - 1] ]
          rhs = liftTo k x
      in case solveLin m rhs of
           Just [p0, p1, q0, q1] -> Just (QS2 p0 p1, QS2 q0 q1)
           _ -> Nothing

-- | Numeric sign in Q[sqrt2], as an @Int@, which is what 'signPQc' compares.
-- 'S.Lang.Ring.signum' decides it; @Ord QS2@ is that same decision.
qs2Sign :: QS2 -> Int
qs2Sign v = case signum v of
  QS2 s _ | s > 0     -> 1
          | s < 0     -> -1
          | otherwise -> 0

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
      in case compare (p * p) (q * q * c2) of
           GT -> qs2Sign p
           LT -> qs2Sign q
           EQ -> 0

-- | Exact sign of a real element of level at most 4: -1, 0 or 1.
realSign :: Cyclo -> Int
realSign x = case realPartsQ x of
  Just (p, q) -> signPQc p q
  Nothing     -> error "realSign: not a real element of Q(zeta_16)"

-- | A real element that happens to lie in Q[sqrt2].
toQS2 :: Cyclo -> Maybe QS2
toQS2 x = case realPartsQ x of
  Just (p, q) | q == 0 -> Just p
  _                    -> Nothing

-- Field Checks

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

-- Display

instance Amp Cyclo where
  showAmp (Cyclo 1 [c]) = showRat c
  showAmp (Cyclo k cs) =
    intercalate "+" [ term i c | (i, c) <- zip [0 :: Int ..] cs, c /= 0 ]
    where
      z = "z" ++ show ((2 :: Integer) ^ k)
      term 0 c = showRat c
      term 1 c = showRat c ++ "*" ++ z
      term i c = showRat c ++ "*" ++ z ++ "^" ++ show i
