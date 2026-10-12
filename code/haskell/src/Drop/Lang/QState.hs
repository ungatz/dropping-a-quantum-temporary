-- QState.hs: exact state vectors, gate application, and the minor test.
--
-- A state over registers [d1,...,dn] is a flat list of d1*...*dn scalars,
-- mixed radix, first register most significant, kept unnormalized so a
-- selected branch's weight is an exact scalar. factorSplit makes the
-- criterion (the criterion section) executable: st factors as vA (x) vB iff nonzero minors vanish.

module Drop.Lang.QState where

import Drop.Lang.Ring (Conj (..), normSq)

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

-- | @U U^H = I@, exactly: the premise of the Gate rule (U is in the gate
-- set, a set of unitaries). There is no tolerance, because the whole
-- package is exact arithmetic.
isUnitary :: (Eq a, Num a, Conj a) => Matrix a -> Bool
isUnitary u =
  not (null u) && all ((== n) . length) u
  && and [ row i j == (if i == j then 1 else 0) | i <- [0 .. n - 1], j <- [0 .. n - 1] ]
  where
    n = length u
    row i j = sum [ (u !! i !! k) * conj (u !! j !! k) | k <- [0 .. n - 1] ]

-- | Apply gate @g@ to the registers at positions @targets@, in that order.
-- Gather formulation: out[k] sums g[t(k)][j] over the states that agree with
-- k away from the targets.
--
-- A gate whose matrix does not fit its registers is refused by name rather
-- than read: a larger matrix would be cut to its top-left block, a smaller
-- one would index past its end, and a repeated target would compute a map
-- that is no gate at all. Every caller in the package builds a well-shaped
-- call; a program built by hand need not.
applyGate :: Num a => [Int] -> Matrix a -> [Int] -> StateV a -> StateV a
applyGate dims g targets st
  | any (\t -> t < 0 || t >= length dims) targets =
      error ("applyGate: target position out of range " ++ show targets
             ++ " for " ++ show (length dims) ++ " registers")
  | length (nubInts targets) /= length targets =
      error ("applyGate: a register is named twice in one gate (positions "
             ++ show targets ++ ")")
  | length g /= tsize || any ((/= tsize) . length) g =
      error ("applyGate: a matrix of " ++ show (length g) ++ " rows does not act on registers of total \
             \dimension " ++ show tsize ++ "; the matrix of a gate is square, of side the product of \
             \its registers' dimensions")
  | otherwise =
  [ sum [ (g !! ti) !! tj * (st !! src ls tj) | tj <- [0 .. tsize - 1] ]
  | k <- [0 .. n - 1]
  , let ls = idxToLevels dims k
  , let ti = levelsToIdx tdims [ ls !! t | t <- targets ] ]
  where
    nubInts []       = []
    nubInts (x : xs) = x : nubInts (filter (/= x) xs)
    n     = product dims
    tdims = [ dims !! t | t <- targets ]
    tsize = product tdims
    src ls tj =
      levelsToIdx dims
        (foldl (\l (p, v) -> listSet p v l) ls (zip targets (idxToLevels tdims tj)))

-- | Selected block measurement, unnormalized: zero every amplitude whose
-- basis state of register @reg@ is not in @keep@.
projectLevels :: Num a => [Int] -> Int -> [Int] -> StateV a -> StateV a
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
-- @vA (x) vB == st@ exactly. The A factor is indexed with A's registers in
-- ascending machine order, whatever order @regsA@ lists them in; a caller
-- whose A side has an order of its own -- a drop site's block, which
-- the site definition reads as the tensor product of the registers in the order the
-- @drop@ names them -- uses 'factorSplitOrd'.
factorSplit :: (Eq a, Fractional a) => [Int] -> [Int] -> StateV a -> Maybe (StateV a, StateV a)
factorSplit dims regsA st =
  factorSplitOrd dims [ i | i <- [0 .. length dims - 1], i `elem` regsA ] st

-- | 'factorSplit' with the A factor indexed in the caller's /own/ order: the
-- a-th coordinate of @vA@ is the level tuple @idxToLevels [dims !! i | i <-
-- aIdx] a@ read against the registers @aIdx@ names, in that order (the B
-- side stays in ascending register order). The site's certificate is
-- computed with this (Drop.Lang.Interp.probeResultL, Drop.Lang.Compile.probeOutcome)
-- so that it is indexed as the drop's tuple is, the same convention as the
-- allocation state @psi@ and the emitted qubit list: with the sorted
-- 'factorSplit' a site @drop (b, a)@ whose registers were allocated a first
-- read its certificate on (a, b) and its allocation state on (b, a), and
-- the reflection between the two was wrong whenever neither was symmetric
-- (no corpus program drops a tuple out of allocation order, so the sorted
-- split is right on the corpus and wrong in general).
factorSplitOrd :: (Eq a, Fractional a) => [Int] -> [Int] -> StateV a -> Maybe (StateV a, StateV a)
factorSplitOrd dims aIdx st =
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
    bIdx  = [ i | i <- [0 .. n - 1], i `notElem` aIdx ]
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

-- | Reindex a state vector as a matrix over an A/B partition of the
-- registers (A = @regsA@, B its complement): entry (a,b) is the amplitude of
-- the basis state combining A's a-th level tuple with B's b-th. The same
-- indexing convention 'factorSplit' uses internally, exposed as data instead
-- of consumed by a factorization test -- used by the loan criterion
-- (Drop.Lang.Interp), which needs the raw block/rest matrix at several probe
-- inputs before it can even ask a factorization question.
reindexAB :: [Int] -> [Int] -> StateV a -> Matrix a
reindexAB dims regsA =
  reindexABOrd dims [ i | i <- [0 .. length dims - 1], i `elem` regsA ]

-- | 'reindexAB' with the A side indexed in the caller's /own/ order: the
-- a-th row combines the level tuple @idxToLevels [dims !! i | i <- regsA] a@
-- with the registers @regsA@ names, in that order (the B side stays in
-- ascending register order, as 'reindexAB' has it). The site definition's clause (3)
-- needs this: H_block is the tensor product of the block's registers as the
-- @drop@ writes them, which need not be their order in the machine.
reindexABOrd :: [Int] -> [Int] -> StateV a -> Matrix a
reindexABOrd dims aIdx st =
  [ [ m a b | b <- [0 .. nB - 1] ] | a <- [0 .. nA - 1] ]
  where
    n     = length dims
    bIdx  = [ i | i <- [0 .. n - 1], i `notElem` aIdx ]
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
