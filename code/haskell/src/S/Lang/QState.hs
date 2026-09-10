-- QState.hs: exact state vectors, gate application, and the minor test.
--
-- A state over registers [d1,...,dn] is a flat list of d1*...*dn scalars,
-- mixed radix, first register most significant, kept unnormalized so a
-- selected branch's weight is an exact scalar. factorSplit makes the
-- criterion executable: st factors as vA (x) vB iff nonzero minors vanish.

module S.Lang.QState where

import S.Lang.Ring (Conj (..), normSq)

type StateV a = [a]
type Matrix a = [[a]]

-- Index arithmetic

idxToLevels :: [Int] -> Int -> [Int]
idxToLevels dims k = go (reverse dims) k []
  where go [] _ acc = acc
        go (d:ds) i acc = go ds (i `div` d) (i `mod` d : acc)

levelsToIdx :: [Int] -> [Int] -> Int
levelsToIdx dims ls = foldl (\i (d, l) -> i * d + l) 0 (zip dims ls)

listSet :: Int -> b -> [b] -> [b]
listSet p v l = take p l ++ [v] ++ drop (p + 1) l

-- States

ket :: Num a => [Int] -> [Int] -> StateV a
ket dims ls =
  [ if k == levelsToIdx dims ls then 1 else 0 | k <- [0 .. product dims - 1] ]

tensorS :: Num a => StateV a -> StateV a -> StateV a
tensorS s1 s2 = [ a * b | a <- s1, b <- s2 ]

addS :: Num a => StateV a -> StateV a -> StateV a
addS = zipWith (+)

scaleS :: Num a => a -> StateV a -> StateV a
scaleS x = map (x *)

isZeroS :: (Eq a, Num a) => StateV a -> Bool
isZeroS = all (== 0)

-- | Squared norm, summing z * conj z rather than z^2 so that the value is
-- real also for complex scalars.
norm2S :: (Num a, Conj a) => StateV a -> a
norm2S s = sum [ normSq a | a <- s ]

-- | Both vectors nonzero and all 2x2 minors of the pair vanish, that is,
-- the two lie on one line.
stateProportional :: (Eq a, Num a) => StateV a -> StateV a -> Bool
stateProportional s1 s2 =
  not (isZeroS s1) && not (isZeroS s2) &&
  and [ s1 !! i * s2 !! j == s1 !! j * s2 !! i
      | i <- [0 .. length s1 - 1], j <- [0 .. length s1 - 1] ]

-- Gates

-- | Apply gate @g@ to the registers at positions @targets@, in that order.
-- Gather formulation: out[k] sums g[t(k)][j] over the states that agree with
-- k away from the targets.
applyGate :: (Eq a, Num a) => [Int] -> Matrix a -> [Int] -> StateV a -> StateV a
applyGate dims g targets st =
  [ sum [ (g !! ti) !! tj * (st !! src ls tj) | tj <- [0 .. tsize - 1] ]
  | k <- [0 .. n - 1]
  , let ls = idxToLevels dims k
  , let ti = levelsToIdx tdims [ ls !! t | t <- targets ] ]
  where
    n     = product dims
    tdims = [ dims !! t | t <- targets ]
    tsize = product tdims
    src ls tj =
      levelsToIdx dims
        (foldl (\l (p, v) -> listSet p v l) ls (zip targets (idxToLevels tdims tj)))

-- | Selected block measurement, unnormalized: zero every amplitude whose
-- basis state of register @reg@ is not in @keep@.
projectLevels :: (Eq a, Num a) => [Int] -> Int -> [Int] -> StateV a -> StateV a
projectLevels dims reg keep st =
  [ if (idxToLevels dims k !! reg) `elem` keep then a else 0
  | (k, a) <- zip [0 ..] st ]

-- Minor test
--
-- Conjugation-free and correctly so: "st = vA (x) vB" is the algebraic
-- condition that all 2x2 minors vanish, valid over any field; conjugation
-- enters the semantics only through norms.

-- | Split the registers into A = @regsA@ and B = the rest.  'Nothing' when
-- the state does not factor; otherwise @Just (vA, vB)@ with
-- @vA (x) vB == st@ exactly.
factorSplit :: (Eq a, Fractional a) => [Int] -> [Int] -> StateV a -> Maybe (StateV a, StateV a)
factorSplit dims regsA st =
  case pivot of
    Nothing -> Nothing                       -- zero state
    Just (a0, b0) ->
      let p = m a0 b0 in
      if and [ m a b * p == m a b0 * m a0 b | a <- [0 .. nA - 1], b <- [0 .. nB - 1] ]
        then Just ( [ m a b0 | a <- [0 .. nA - 1] ]
                  , [ m a0 b / p | b <- [0 .. nB - 1] ] )
        else Nothing
  where
    n     = length dims
    aIdx  = [ i | i <- [0 .. n - 1], i `elem` regsA ]        -- sorted
    bIdx  = [ i | i <- [0 .. n - 1], i `notElem` regsA ]
    dimsA = [ dims !! i | i <- aIdx ]
    dimsB = [ dims !! i | i <- bIdx ]
    nA    = product dimsA
    nB    = product dimsB
    m a b =
      let lsA = idxToLevels dimsA a
          lsB = idxToLevels dimsB b
          ls  = foldl (\l (p', v) -> listSet p' v l)
                      (replicate n 0)
                      (zip aIdx lsA ++ zip bIdx lsB)
      in st !! levelsToIdx dims ls
    pivot = case [ (a, b) | a <- [0 .. nA - 1], b <- [0 .. nB - 1], m a b /= 0 ] of
              []      -> Nothing
              (x : _) -> Just x

-- | Canonical representative of the line through a nonzero vector: scale so
-- that the first nonzero coordinate is 1.  Lines then compare with (==).
canonicalLine :: (Eq a, Fractional a) => StateV a -> StateV a
canonicalLine v = case [ a | a <- v, a /= 0 ] of
  []      -> error "canonicalLine: zero vector"
  (p : _) -> map (/ p) v

-- Matrices

matMul :: Num a => Matrix a -> Matrix a -> Matrix a
matMul m1 m2 =
  [ [ sum (zipWith (*) row col) | col <- cols ] | row <- m1 ]
  where cols = transposeM m2

transposeM :: Matrix a -> Matrix a
transposeM []          = []
transposeM m@(row0 : _) = [ map (!! j) m | j <- [0 .. length row0 - 1] ]

-- | Exact determinant by Gaussian elimination in the scalar field.
detM :: (Eq a, Fractional a) => Matrix a -> a
detM m0 = go m0 1
  where
    go [] acc = acc
    go m acc =
      case [ (i, p, rt) | (i, p : rt) <- zip [0 :: Int ..] m, p /= 0 ] of
        [] -> 0
        ((i, p, rt) : _) ->
          let others = [ r' | (i', r') <- zip [0 ..] m, i' /= i ]
              sign   = if even i then 1 else -1
              elim (h : t) = zipWith (\x y -> y - (h / p) * x) rt t
              elim []      = []
          in go (map elim others) (acc * sign * p)
