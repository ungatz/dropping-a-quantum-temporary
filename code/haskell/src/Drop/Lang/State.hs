-- Drop.Lang.State: a state is a list of amplitudes.
--
-- Question: How does the checker hold a quantum state, and how does it ask whether a block of
--           registers is a tensor factor of it?
-- Answer:   As one flat list, indexed in mixed radix with the first register most significant,
--           and never normalized, so the squared norm of a measured branch is its exact weight.
--           A state factors as (block) (x) (rest) exactly when, laid out as a block-by-rest
--           matrix, every 2x2 minor vanishes. That test is factorSplit, the one computation the
--           criterion needs; conjugation enters only through norms.
-- Paper:    def:site (the site map, block first), sec:factor (the rank test), fig:criterion.
-- Shapes:   StateV a   [a], of length the product of the register dimensions.
--           Matrix a   [[a]], a list of rows.
--           dims       [Int], the dimension of each register in machine order.
--           levels     [Int], one level per register; idxToLevels and levelsToIdx convert.

module Drop.Lang.State where

import Drop.Lang.Scalar (Conj (..), normSq)

type StateV a = [a]
type Matrix a = [[a]]

-- Index arithmetic

-- | The level of each register at flat position @k@, first register most significant.
idxToLevels :: [Int] -> Int -> [Int]
idxToLevels dims k = go (reverse dims) k []
  where go [] _ acc = acc
        go (d:ds) i acc = go ds (i `div` d) (i `mod` d : acc)

-- >>> idxToLevels [2,3] 5
-- [1,2]
-- >>> idxToLevels [2,3] 0
-- [0,0]
-- >>> idxToLevels [] 0
-- []

-- | The flat position of a level tuple, the inverse of 'idxToLevels'.
levelsToIdx :: [Int] -> [Int] -> Int
levelsToIdx dims ls = foldl (\i (d, l) -> i * d + l) 0 (zip dims ls)

-- >>> levelsToIdx [2,3] [1,2]
-- 5
-- >>> levelsToIdx [2,3] [0,0]
-- 0
-- >>> map (levelsToIdx [2,3] . idxToLevels [2,3]) [0 .. 5]
-- [0,1,2,3,4,5]

-- | The list with position @p@ replaced by @v@.
listSet :: Int -> b -> [b] -> [b]
listSet p v l = take p l ++ [v] ++ drop (p + 1) l

-- >>> listSet 1 'x' "abc"
-- "axc"
-- >>> listSet 5 'x' "abc"
-- "abcx"

-- | The dimensions of the named registers, in the order named.
registerDims :: [Int] -> [Int] -> [Int]
registerDims dims idx = [ dims !! i | i <- idx ]   -- impossible: idx names registers of dims

-- >>> registerDims [2,3,4] [2,0]
-- [4,2]
-- >>> registerDims [2,3,4] []
-- []

-- | The registers of an @n@-register machine that the list does not name, ascending.
restIdx :: Int -> [Int] -> [Int]
restIdx n idx = [ i | i <- [0 .. n - 1], i `notElem` idx ]

-- >>> restIdx 4 [2,0]
-- [1,3]
-- >>> restIdx 2 [0,1]
-- []

-- States

-- | The basis state with the given level in each register.
ket :: Num a => [Int] -> [Int] -> StateV a
ket dims ls =
  [ if k == levelsToIdx dims ls then 1 else 0 | k <- [0 .. product dims - 1] ]

-- >>> ket [2] [1]
-- [0,1]
-- >>> ket [2,2] [1,0]
-- [0,0,1,0]
-- >>> ket [] []
-- [1]

-- | The state of two register groups side by side, the first group most significant.
tensorS :: Num a => StateV a -> StateV a -> StateV a
tensorS s1 s2 = [ a * b | a <- s1, b <- s2 ]

-- >>> tensorS [1,0] [0,1]
-- [0,1,0,0]
-- >>> tensorS [1,1] [1,-1]
-- [1,-1,1,-1]
-- >>> tensorS [] [1,0]
-- []

addS :: Num a => StateV a -> StateV a -> StateV a
addS = zipWith (+)

-- >>> addS [1,2] [10,20]
-- [11,22]

scaleS :: Num a => a -> StateV a -> StateV a
scaleS x = map (x *)

-- >>> scaleS 3 [1,2]
-- [3,6]

isZeroS :: (Eq a, Num a) => StateV a -> Bool
isZeroS = all (== 0)

-- >>> isZeroS [0,0]
-- True
-- >>> isZeroS [0,1]
-- False

-- | Squared norm, summing z * conj z rather than z^2 so that the value is
-- real also for complex scalars.
norm2S :: (Num a, Conj a) => StateV a -> a
norm2S s = sum [ normSq a | a <- s ]

-- >>> :m + Drop.Lang.Scalar
-- >>> norm2S [QS2 0 1, 1]
-- 3
-- >>> norm2S [3, 4 :: Rational]
-- 25 % 1

-- | Both vectors nonzero and all 2x2 minors of the pair vanish, that is,
-- the two lie on one line.
stateProportional :: (Eq a, Num a) => StateV a -> StateV a -> Bool
stateProportional s1 s2 =
  not (isZeroS s1) && not (isZeroS s2) &&
  -- impossible: both are states of one register list, so of one length, and i, j are below it
  and [ s1 !! i * s2 !! j == s1 !! j * s2 !! i
      | i <- [0 .. length s1 - 1], j <- [0 .. length s1 - 1] ]

-- >>> stateProportional [1,2] [2,4]
-- True
-- >>> stateProportional [1,2] [2,5]
-- False
-- >>> stateProportional [0,0] [0,0]
-- False

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
    -- impossible: the test above has already checked that u is square of side n
    row i j = sum [ (u !! i !! k) * conj (u !! j !! k) | k <- [0 .. n - 1] ]

-- >>> isUnitary ([[1,0],[0,1]] :: [[Rational]])
-- True
-- >>> isUnitary ([[1,1],[0,1]] :: [[Rational]])
-- False
-- >>> isUnitary ([[1,0,0],[0,1,0]] :: [[Rational]])
-- False

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
      -- refusal: a target position outside the registers
      error ("applyGate: target position out of range " ++ show targets
             ++ " for " ++ show (length dims) ++ " registers")
  | length (nubInts targets) /= length targets =
      -- refusal: a register named twice in one gate
      error ("applyGate: a register is named twice in one gate (positions "
             ++ show targets ++ ")")
  | length g /= tsize || any ((/= tsize) . length) g =
      -- refusal: a matrix that is not square of side the product of the target dimensions
      error ("applyGate: a matrix of " ++ show (length g) ++ " rows does not act on registers of total \
             \dimension " ++ show tsize ++ "; the matrix of a gate is square, of side the product of \
             \its registers' dimensions")
  | otherwise =
  -- impossible: the guards checked g square of side tsize, ti and tj are below tsize; src is below n = length st
  [ sum [ (g !! ti) !! tj * (st !! src ls tj) | tj <- [0 .. tsize - 1] ]
  | k <- [0 .. n - 1]
  , let ls = idxToLevels dims k
  -- impossible: the guards checked every target is a register position, so ls has an entry there
  , let ti = levelsToIdx tdims [ ls !! t | t <- targets ] ]
  where
    nubInts []       = []
    nubInts (x : xs) = x : nubInts (filter (/= x) xs)
    n     = product dims
    tdims = registerDims dims targets
    tsize = product tdims
    src ls tj =
      levelsToIdx dims
        (foldl (\l (p, v) -> listSet p v l) ls (zip targets (idxToLevels tdims tj)))

-- >>> applyGate [2] [[0,1],[1,0]] [0] [1,0]
-- [0,1]
-- >>> applyGate [2,2] [[0,1],[1,0]] [1] [1,0,0,0]
-- [0,1,0,0]
-- >>> applyGate [2,2] [[0,1],[1,0]] [0] [1,0,0,0]
-- [0,0,1,0]

-- | Selected block measurement, unnormalized: zero every amplitude whose
-- basis state of register @reg@ is not in @keep@.
projectLevels :: Num a => [Int] -> Int -> [Int] -> StateV a -> StateV a
projectLevels dims reg keep st =
  -- impossible: reg is a register position of dims, so the level list has an entry there
  [ if (idxToLevels dims k !! reg) `elem` keep then a else 0
  | (k, a) <- zip [0 ..] st ]

-- >>> projectLevels [2,2] 0 [1] [1,2,3,4]
-- [0,0,3,4]
-- >>> projectLevels [2,2] 1 [0] [1,2,3,4]
-- [1,0,3,0]
-- >>> projectLevels [2,2] 0 [0,1] [1,2,3,4]
-- [1,2,3,4]

-- Minor test
--
-- Conjugation-free and correctly so: "st = vA (x) vB" is the algebraic
-- condition that all 2x2 minors vanish, valid over any field; conjugation
-- enters the semantics only through norms.

-- | The amplitude at block level @a@ and rest level @b@, the block's
-- registers in the order @aIdx@ lists them (the rest stays in ascending
-- register order): the entry (a, b) of the block-by-rest matrix.
entryAB :: [Int] -> [Int] -> StateV a -> Int -> Int -> a
entryAB dims aIdx st a b =
  -- impossible: the levels of A and B together fill every register once, so the flat position is below the length of st
  st !! levelsToIdx dims ls
  where
    n   = length dims
    bIdx = restIdx n aIdx
    lsA = idxToLevels (registerDims dims aIdx) a
    lsB = idxToLevels (registerDims dims bIdx) b
    ls  = foldl (\l (p, v) -> listSet p v l)
                (replicate n 0)
                (zip aIdx lsA ++ zip bIdx lsB)

-- >>> entryAB [2,2] [0] [1,2,3,4] 1 0
-- 3
-- >>> entryAB [2,2] [1] [1,2,3,4] 1 0
-- 2
-- >>> entryAB [2,3] [1,0] [0 .. 5] 2 1
-- 1

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

-- >>> factorSplit [2,2] [0] ([1,0,2,0] :: StateV QS2)
-- Just ([1,2],[1,0])
-- >>> factorSplit [2,2] [0] ([1,0,0,1] :: StateV QS2)
-- Nothing
-- >>> factorSplit [2,2] [0] ([0,0,0,0] :: StateV QS2)
-- Nothing

-- | 'factorSplit' with the A factor indexed in the caller's /own/ order: the
-- a-th coordinate of @vA@ is the level tuple @idxToLevels (registerDims dims aIdx) a@
-- read against the registers @aIdx@ names, in that order; the B side stays in
-- ascending register order. A drop site's certificate is computed with this,
-- so that it is indexed as the drop writes its tuple, the same convention as
-- the allocation state and the emitted qubit list: a site @drop (b, a)@ whose
-- registers were allocated a first must read its certificate on (b, a) too,
-- or the reflection between the two is wrong whenever neither is symmetric.
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
    nA    = product (registerDims dims aIdx)
    nB    = product (registerDims dims (restIdx (length dims) aIdx))
    m     = entryAB dims aIdx st
    pivot = case [ (a, b) | a <- [0 .. nA - 1], b <- [0 .. nB - 1], m a b /= 0 ] of
              []      -> Nothing
              (x : _) -> Just x

-- >>> factorSplitOrd [2,2] [0] ([1,0,2,0] :: StateV QS2)
-- Just ([1,2],[1,0])
-- >>> factorSplitOrd [2,3] [1] ([1,2,3,2,4,6] :: StateV QS2)
-- Just ([1,2,3],[1,2])
-- >>> factorSplitOrd [2,2] [1,0] ([1,2,3,6] :: StateV QS2)
-- Just ([1,3,2,6],[1])

-- | Reindex a state vector as a matrix over an A/B partition of the
-- registers (A = @regsA@, B its complement): entry (a,b) is the amplitude of
-- the basis state combining A's a-th level tuple with B's b-th. The same
-- indexing convention 'factorSplit' uses internally, exposed as data instead
-- of consumed by a factorization test -- used by the loan criterion
-- (Drop.Lang.Criterion), which needs the raw block/rest matrix at several probe
-- inputs before it can even ask a factorization question.
reindexAB :: [Int] -> [Int] -> StateV a -> Matrix a
reindexAB dims regsA =
  reindexABOrd dims [ i | i <- [0 .. length dims - 1], i `elem` regsA ]

-- >>> reindexAB [2,2] [0] [1,2,3,4]
-- [[1,2],[3,4]]
-- >>> reindexAB [2,2] [1] [1,2,3,4]
-- [[1,3],[2,4]]

-- | 'reindexAB' with the A side indexed in the caller's /own/ order: the
-- a-th row combines the level tuple @idxToLevels [dims !! i | i <- regsA] a@
-- with the registers @regsA@ names, in that order (the B side stays in
-- ascending register order, as 'reindexAB' has it). The site definition's clause (3)
-- needs this: H_block is the tensor product of the block's registers as the
-- @drop@ writes them, which need not be their order in the machine.
reindexABOrd :: [Int] -> [Int] -> StateV a -> Matrix a
reindexABOrd dims aIdx st =
  [ [ entryAB dims aIdx st a b | b <- [0 .. nB - 1] ] | a <- [0 .. nA - 1] ]
  where
    nA = product (registerDims dims aIdx)
    nB = product (registerDims dims (restIdx (length dims) aIdx))

-- >>> reindexABOrd [2,2] [0] [1,2,3,4]
-- [[1,2],[3,4]]
-- >>> reindexABOrd [2,2] [1,0] [1,2,3,4]
-- [[1],[3],[2],[4]]
-- >>> reindexABOrd [2,3] [1] [0 .. 5]
-- [[0,3],[1,4],[2,5]]

-- | Canonical representative of the line through a nonzero vector: scale so
-- that the first nonzero coordinate is 1.  Lines then compare with (==).
canonicalLine :: (Eq a, Fractional a) => StateV a -> StateV a
canonicalLine v = case [ a | a <- v, a /= 0 ] of
  []      -> error "canonicalLine: zero vector"   -- refusal: the zero vector spans no line
  (p : _) -> map (/ p) v

-- >>> canonicalLine [2,4] :: StateV Rational
-- [1 % 1,2 % 1]
-- >>> canonicalLine [0,3,6] :: StateV Rational
-- [0 % 1,1 % 1,2 % 1]

-- Matrices

-- | The matrix product.
matMul :: Num a => Matrix a -> Matrix a -> Matrix a
matMul m1 m2 =
  [ [ sum (zipWith (*) row col) | col <- cols ] | row <- m1 ]
  where cols = transposeM m2

-- >>> matMul [[1,2],[3,4]] [[0,1],[1,0]]
-- [[2,1],[4,3]]
-- >>> matMul [[0,1],[1,0]] [[0,1],[1,0]]
-- [[1,0],[0,1]]

-- | Rows become columns.
transposeM :: Matrix a -> Matrix a
transposeM []          = []
transposeM m@(row0 : _) =
  -- impossible: a matrix is rectangular, so every row has as many entries as the first
  [ map (!! j) m | j <- [0 .. length row0 - 1] ]

-- >>> transposeM [[1,2,3],[4,5,6]]
-- [[1,4],[2,5],[3,6]]
-- >>> transposeM ([] :: Matrix Int)
-- []

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

-- >>> detM ([[1,2],[3,4]] :: Matrix Rational)
-- (-2) % 1
-- >>> detM ([[2,0],[0,3]] :: Matrix Rational)
-- 6 % 1
-- >>> detM ([[1,2],[2,4]] :: Matrix Rational)
-- 0 % 1
-- >>> detM ([] :: Matrix Rational)
-- 1 % 1
