-- Ring.hs: the real exact scalar fields.
--
-- Rational carries every permutation gate and the rational rotations of
-- the tilt family. QS2 = Q[sqrt2], pairs (a, b) meaning a + b*sqrt2, is the
-- smallest field containing the 1/sqrt2 of the Hadamard gate. The complex
-- tower Q(zeta_{2^k}) is in Cyclo.hs.

module Drop.Lang.Ring where

import Data.Ratio (numerator, denominator)

-- | a + b*sqrt2 with a, b in Q.
data QS2 = QS2 !Rational !Rational deriving (Eq, Ord)

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

instance Fractional QS2 where
  recip (QS2 a b) =
    let n = a*a - 2*b*b   -- nonzero for nonzero (a, b): sqrt2 is irrational
    in if a == 0 && b == 0
         then error "QS2: division by zero"
         else QS2 (a / n) (negate b / n)
  fromRational r = QS2 r 0

sqrt2 :: QS2
sqrt2 = QS2 0 1

invSqrt2 :: QS2   -- 1/sqrt2 = sqrt2/2
invSqrt2 = QS2 0 (1/2)

-- Conjugation

-- | Complex conjugation: the identity on the real fields here, and
-- zeta -> zeta^{-1} on the cyclotomic tower of Cyclo.hs.
class Conj a where
  conj :: a -> a

-- | The probability form |z|^2 = z * conj z, called at every norm site in
-- the package instead of plain squaring, which would give a complex
-- "probability" for a complex amplitude.
normSq :: (Num a, Conj a) => a -> a
normSq x = x * conj x

instance Conj Rational where
  conj = id

instance Conj QS2 where
  conj = id

-- Display

showRat :: Rational -> String
showRat r
  | denominator r == 1 = show (numerator r)
  | otherwise          = show (numerator r) ++ "/" ++ show (denominator r)

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
