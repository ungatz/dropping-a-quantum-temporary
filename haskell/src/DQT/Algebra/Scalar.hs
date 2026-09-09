-- |
-- Module      : DQT.Algebra.Scalar
--
-- The scalar field used everywhere: @K = Q(w)@, @w = exp(i*pi/4)@, with
-- exact 'Rational' coordinates.  A field, not a ring, since the criterion
-- divides by a pivot; no floating point, since safety is exact.
module DQT.Algebra.Scalar
  ( -- * The field
    K(..)
  , fromRat
  , fromInt
    -- * Constants
  , kzero, kone, ktwo, khalf
  , komega, kimag, ksqrt2, kinvsqrt2
    -- * Field operations
  , kadd, ksub, kmul, kneg, kinv, kdiv, ksum, kprod
  , kconj, kgal
  , kIsZero, kIsOne
    -- * Norms and reality
  , knorm2
  , kIsRational, kToRational
  , kIsReal
    -- * Comparison of magnitudes (exact, on the real subfield)
  , krealCompare
    -- * Exact square roots
  , ratSqrt, isqrt, ksqrtReal
    -- * Printing
  , showK
  ) where

import Data.List (intercalate)
import Data.Ratio (numerator, denominator)

-- | @K a b c d@ is the field element @a + b*w + c*w^2 + d*w^3@ where
-- @w = exp(i*pi\/4)@ and @w^4 = -1@.
--
-- Equality is coordinate equality, which is correct because
-- @{1, w, w^2, w^3}@ is a @Q@-basis of @Q(w)@ (the eighth cyclotomic
-- polynomial is @x^4 + 1@, of degree four).
data K = K !Rational !Rational !Rational !Rational
  deriving (Eq, Ord)

instance Show K where show = showK

-- | The rationals sit inside @K@ as the constant coordinate.
fromRat :: Rational -> K
fromRat q = K q 0 0 0

fromInt :: Integer -> K
fromInt n = fromRat (fromInteger n)

kzero, kone, ktwo, khalf :: K
kzero = K 0 0 0 0
kone  = K 1 0 0 0
ktwo  = K 2 0 0 0
khalf = K (1/2) 0 0 0

-- | @w@ itself.
komega :: K
komega = K 0 1 0 0

-- | @i = w^2@.
kimag :: K
kimag = K 0 0 1 0

-- | @sqrt 2 = w - w^3@.  (Check: @(w - w^3)^2 = w^2 - 2w^4 + w^6
-- = i + 2 - i = 2@, using @w^4 = -1@ and @w^6 = w^2 * w^4 = -i@.)
ksqrt2 :: K
ksqrt2 = K 0 1 0 (-1)

-- | @1\/sqrt 2 = sqrt 2 \/ 2@.
kinvsqrt2 :: K
kinvsqrt2 = K 0 (1/2) 0 (-1/2)

kadd :: K -> K -> K
kadd (K a b c d) (K a' b' c' d') = K (a+a') (b+b') (c+c') (d+d')

kneg :: K -> K
kneg (K a b c d) = K (negate a) (negate b) (negate c) (negate d)

ksub :: K -> K -> K
ksub x y = kadd x (kneg y)

-- | Multiplication is convolution of coefficient sequences, reduced by
-- @w^4 = -1@: a product term of degree @k >= 4@ contributes with a minus sign
-- at degree @k - 4@.
kmul :: K -> K -> K
kmul (K a b c d) (K a' b' c' d') = K r0 r1 r2 r3
  where
    xs = [a,b,c,d]
    ys = [a',b',c',d']
    coeff k = sum [ x*y
                  | (i,x) <- zip [0 :: Int ..] xs
                  , (j,y) <- zip [0 :: Int ..] ys
                  , i + j == k ]
    r0 = coeff 0 - coeff 4
    r1 = coeff 1 - coeff 5
    r2 = coeff 2 - coeff 6
    r3 = coeff 3

ksum :: [K] -> K
ksum = foldl kadd kzero

kprod :: [K] -> K
kprod = foldl kmul kone

-- | Complex conjugation.  It sends @w@ to @w^{-1} = w^7 = -w^3@, hence
-- @(a,b,c,d) |-> (a, -d, -c, -b)@.
kconj :: K -> K
kconj (K a b c d) = K a (negate d) (negate c) (negate b)

-- | The Galois automorphism @sqrt 2 |-> -sqrt 2@, i.e. @w |-> w^5 = -w@,
-- hence @(a,b,c,d) |-> (a,-b,c,-d)@.  Used only to invert.
kgal :: K -> K
kgal (K a b c d) = K a (negate b) c (negate d)

kIsZero :: K -> Bool
kIsZero = (== kzero)

kIsOne :: K -> Bool
kIsOne = (== kone)

-- | @|x|^2 = x * conj x@.  It lands in the real subfield @Q(sqrt 2)@, i.e. in
-- elements of shape @(p, q, 0, -q) = p + q*sqrt 2@.
knorm2 :: K -> K
knorm2 x = kmul x (kconj x)

-- | Exact inverse.  Write @n1 = x * conj x@ (real, of shape @p + q sqrt2@) and
-- @n2 = gal n1 = p - q sqrt2@.  Then @N = n1 * n2 = p^2 - 2q^2@ is /rational/,
-- and @x * (conj x * n2) = N@, so @x^{-1} = conj x * n2 \/ N@.
kinv :: K -> K
kinv x
  | kIsZero x = error "DQT.Algebra.Scalar.kinv: division by zero"
  | otherwise =
      let n1 = knorm2 x
          n2 = kgal n1
          K n _ _ _ = kmul n1 n2
      in scaleRat (recip n) (kmul (kconj x) n2)
  where scaleRat q (K a b c d) = K (q*a) (q*b) (q*c) (q*d)

kdiv :: K -> K -> K
kdiv x y = kmul x (kinv y)

-- | Is this element a rational number?
kIsRational :: K -> Bool
kIsRational (K _ b c d) = b == 0 && c == 0 && d == 0

kToRational :: K -> Maybe Rational
kToRational x@(K a _ _ _) | kIsRational x = Just a
                          | otherwise     = Nothing

-- | Is this element fixed by complex conjugation, i.e. real?
kIsReal :: K -> Bool
kIsReal x = kconj x == x

-- | Compare two /real/ elements of @K@ exactly.
--
-- Real elements have shape @p + q*sqrt 2@, @p,q@ rational. Compared to
-- @0@ by sign of @p@, sign of @q@, or (when they disagree) @p^2@ vs.
-- @2q^2@. The only order comparison in the package, used to report how
-- far an unsafe program is from safety; no verdict depends on it.
krealCompare :: K -> K -> Ordering
krealCompare x y = signOf (ksub x y)
  where
    signOf z@(K p q _ _)
      | not (kIsReal z) = error "DQT.Algebra.Scalar.krealCompare: not a real element"
      | p == 0 && q == 0 = EQ
      | q == 0           = compare p 0
      | p == 0           = compare q 0
      | p > 0 && q > 0   = GT
      | p < 0 && q < 0   = LT
      -- p and q have opposite signs: compare p^2 with 2q^2, then re-sign.
      | p > 0            = if p*p > 2*q*q then GT else if p*p == 2*q*q then EQ else LT
      | otherwise        = if p*p > 2*q*q then LT else if p*p == 2*q*q then EQ else GT

-- Exact square roots

-- | Exact integer square root: @Just r@ when @n = r^2@, else 'Nothing'.
-- Newton's iteration on 'Integer', so no float is involved.
isqrt :: Integer -> Maybe Integer
isqrt n
  | n < 0     = Nothing
  | n == 0    = Just 0
  | otherwise = let r = loop n in if r*r == n then Just r else Nothing
  where
    loop k = let k' = (k + n `div` k) `div` 2
             in if k' < k then loop k' else k

-- | Exact rational square root.
ratSqrt :: Rational -> Maybe Rational
ratSqrt q
  | q < 0     = Nothing
  | otherwise = do
      a <- isqrt (numerator q)
      b <- isqrt (denominator q)
      pure (fromInteger a / fromInteger b)

-- | Exact square root of a real element of the field, when it has one.
--
-- Real elements have shape @p + q*sqrt 2@: if @q = 0@, take @sqrt p@ or,
-- when @p = 2s^2@, @s * sqrt 2@; otherwise solve @(a + b sqrt2)^2 = p +
-- q sqrt2@, i.e. @a^2 + 2b^2 = p@, @2ab = q@, giving @a^2 = (p +- sqrt(p^2
-- - 2q^2)) \/ 2@; missing when no candidate is a rational square.
ksqrtReal :: K -> Maybe K
ksqrtReal z@(K p q _ _)
  | not (kIsReal z) = Nothing
  | q == 0 =
      case ratSqrt p of
        Just r  -> Just (fromRat r)
        Nothing -> case ratSqrt (p / 2) of
                     Just s  -> Just (kmul (fromRat s) ksqrt2)
                     Nothing -> Nothing
  | otherwise = do
      dRoot <- ratSqrt (p*p - 2*q*q)
      let candidates = [ (p + dRoot) / 2, (p - dRoot) / 2 ]
      firstJust [ do a <- ratSqrt aSq
                     if a == 0 then Nothing else Just (K a (q / (2*a)) 0 (negate (q / (2*a))))
                | aSq <- candidates, aSq > 0 ]
  where
    firstJust xs = case [ x | Just x <- xs ] of
                     (x:_) -> Just x
                     []    -> Nothing

-- | Print a scalar the way a person would write it: recognise the rationals,
-- the pure @sqrt 2@ multiples, the pure imaginaries, and otherwise fall back to
-- coordinates in the basis @{1, w, w^2, w^3}@.
showK :: K -> String
showK z@(K a b c d)
  | z == kzero                = "0"
  | b == 0 && c == 0 && d == 0 = rat a
  | a == 0 && c == 0 && d == 0 && b == 1 = "w"
  | a == 0 && b == 0 && d == 0 = if c == 1 then "i" else rat c ++ "i"
  -- p + q*sqrt2 (real subfield): coordinates (p, q, 0, -q)
  | c == 0 && d == negate b && b /= 0 =
      combine (if a == 0 then Nothing else Just (rat a)) (sqrtTerm b)
  | otherwise =
      "(" ++ intercalate " + "
               [ rat r ++ u
               | (r,u) <- [(a,""),(b,"w"),(c,"w^2"),(d,"w^3")], r /= 0 ]
        ++ ")"
  where
    rat r | denominator r == 1 = show (numerator r)
          | otherwise          = show (numerator r) ++ "/" ++ show (denominator r)
    sqrtTerm q
      | q == 1        = "sqrt2"
      | q == -1       = "-sqrt2"
      | q == 1/2      = "sqrt2/2"
      | q == -(1/2)   = "-sqrt2/2"
      | otherwise     = rat q ++ "*sqrt2"
    combine Nothing s          = s
    combine (Just p) ('-':s)   = "(" ++ p ++ " - " ++ s ++ ")"
    combine (Just p) s         = "(" ++ p ++ " + " ++ s ++ ")"
