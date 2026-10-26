-- Drop.Theory.Algebra.Linear: exact vectors and matrices over K, and the index of a register in a tensor.
--
-- Question: How does the matrix checker compute with vectors and matrices exactly, and where does
--           each register of a tensor sit in a flat index?
-- Answer:   A vector is a list of K and a matrix a list of rows. In a flat index the first
--           register is the most significant digit, and matrix rows and columns are read the same
--           way (indexToLevels and levelsToIndex convert). The module adds, scales and multiplies,
--           takes the conjugate transpose, tests unitarity and tensors vectors and matrices
--           (kron). Rank and determinant are exact Gaussian elimination over the field, with no
--           pivoting heuristic since a nonzero entry is exactly nonzero. The criterion's
--           test of every 2 x 2 minor is here too. The last four functions place a gate on named
--           registers (applyGateAt), reorder the registers (reorder, permuteToFront) and keep
--           the amplitudes whose level in one register is selected (projectLevels).
-- Paper:    sec:criterion (the criterion is the vanishing of the cut minors), sec:residual (the
--           per-record table tests whether the visible action is right-invertible with det).
-- Shapes:   Vec   a list of K, one amplitude per basis state.
--           Mat   a list of rows of K, row-major: m !! i !! j is the entry of row i, column j.

module Drop.Theory.Algebra.Linear
  ( -- * Types
    Vec, Mat
    -- * Vectors
  , vbasis, vadd, vsub, vscale, vdot, vnorm2, vIsZero
  , vAllOnes
    -- * Tensor
  , tensorV, kron
    -- * Matrices
  , matId, matZero, matMul, matVec, matScale
  , matTranspose, matConjTranspose, matRows, matCols
  , matFromCols, matColumn
  , matIsUnitary, matIsIdentity, matIsRectangular, matRowWidths
    -- * Exact rank, determinant, and minors
  , rank, det, allTwoByTwoMinorsVanish
    -- * Mixed radix
  , indexToLevels, levelsToIndex, dimProduct
    -- * Register plumbing
  , applyGateAt, reorder, permuteToFront, projectLevels
  ) where

import Data.List (transpose)

import Drop.Theory.Algebra.Scalar

type Vec = [K]

-- A vector is a list of scalars; a matrix is a list of rows.
-- >>> [fromInt 1, khalf, kimag] :: Vec
-- [1,1/2,i]
-- >>> map (map fromInt) [[1, 2], [3, 4]] :: Mat
-- [[1,2],[3,4]]
type Mat = [[K]]      -- ^ row-major: @m !! i !! j@ is the entry in row @i@, column @j@

-- Vectors

vzero :: Int -> Vec
vzero n = replicate n kzero

-- >>> vzero 3
-- [0,0,0]
-- >>> vzero 0
-- []

-- | @vbasis n j@ is the basis vector @e_j@ in dimension @n@.
vbasis :: Int -> Int -> Vec
vbasis n j = [ if i == j then kone else kzero | i <- [0 .. n-1] ]

-- >>> vbasis 3 1
-- [0,1,0]
-- >>> vbasis 2 0
-- [1,0]

-- | The all-ones superposition, unnormalised.  It is the @+1@ in the
-- @dim + 1@ test states of the certification count.
vAllOnes :: Int -> Vec
vAllOnes n = replicate n kone

-- >>> vAllOnes 3
-- [1,1,1]

vadd :: Vec -> Vec -> Vec
vadd = zipWith kadd

-- >>> vadd (vbasis 2 0) (vbasis 2 1)
-- [1,1]
-- >>> vadd [komega, kone] [komega, kone]
-- [(2w),2]

vsub :: Vec -> Vec -> Vec
vsub = zipWith ksub

-- >>> vsub [ktwo, kone] [kone, kone]
-- [1,0]

vscale :: K -> Vec -> Vec
vscale c = map (kmul c)

-- >>> vscale kimag [kone, kimag]
-- [i,-1]
-- >>> vscale kzero (vAllOnes 3)
-- [0,0,0]

-- | The Hermitian inner product, conjugate-linear in the /first/ argument.
vdot :: Vec -> Vec -> K
vdot u v = ksum (zipWith (\a b -> kmul (kconj a) b) u v)

-- The inner product conjugates its first argument.
-- >>> vdot [kimag] [kimag]
-- 1
-- >>> vdot [kimag] [kone]
-- -1i
-- >>> vdot (vbasis 2 0) (vbasis 2 1)
-- 0

vnorm2 :: Vec -> K
vnorm2 v = vdot v v

-- >>> vnorm2 [kone, kimag]
-- 2
-- >>> vnorm2 (vbasis 3 2)
-- 1

vIsZero :: Vec -> Bool
vIsZero = all kIsZero

-- >>> vIsZero (vzero 3)
-- True
-- >>> vIsZero (vbasis 3 0)
-- False

-- Tensor

-- | Kronecker product of vectors, first argument most significant.
tensorV :: Vec -> Vec -> Vec
tensorV u v = [ kmul a b | a <- u, b <- v ]

-- The first argument is the most significant register.
-- >>> tensorV [kone, ktwo] [kone, kzero]
-- [1,0,2,0]
-- >>> tensorV (vbasis 2 1) (vbasis 2 0)
-- [0,0,1,0]

-- | Kronecker product of matrices, first argument most significant.
kron :: Mat -> Mat -> Mat
kron a b =
  [ [ kmul x y | x <- rowA, y <- rowB ] | rowA <- a, rowB <- b ]

-- >>> kron (matId 2) [[kone, ktwo]]
-- [[1,2,0,0],[0,0,1,2]]
-- >>> kron [[kone, ktwo]] (matId 2)
-- [[1,0,2,0],[0,1,0,2]]

-- Matrices

matId :: Int -> Mat
matId n = [ vbasis n i | i <- [0 .. n-1] ]

-- >>> matId 2
-- [[1,0],[0,1]]
-- >>> matId 0
-- []

matZero :: Int -> Int -> Mat
matZero r c = replicate r (vzero c)

-- >>> matZero 2 3
-- [[0,0,0],[0,0,0]]

matRows :: Mat -> Int
matRows = length

-- >>> matRows (matZero 2 3)
-- 2

matCols :: Mat -> Int
matCols []      = 0
matCols (r : _) = length r

-- >>> matCols (matZero 2 3)
-- 3
-- >>> matCols []
-- 0

matMul :: Mat -> Mat -> Mat
matMul a b =
  [ [ ksum (zipWith kmul row col) | col <- bT ] | row <- a ]
  where bT = matTranspose b

-- >>> matMul (map (map fromInt) [[1, 2], [3, 4]]) (map (map fromInt) [[0, 1], [1, 0]])
-- [[2,1],[4,3]]
-- >>> matMul (map (map fromInt) [[1, 2], [3, 4]]) (matId 2)
-- [[1,2],[3,4]]

matVec :: Mat -> Vec -> Vec
matVec a v = [ ksum (zipWith kmul row v) | row <- a ]

-- >>> matVec (map (map fromInt) [[1, 2], [3, 4]]) (map fromInt [1, 1])
-- [3,7]

matScale :: K -> Mat -> Mat
matScale c = map (map (kmul c))

-- >>> matScale khalf (matId 2)
-- [[1/2,0],[0,1/2]]

matTranspose :: Mat -> Mat
matTranspose = transpose

-- >>> matTranspose (map (map fromInt) [[1, 2, 3], [4, 5, 6]])
-- [[1,4],[2,5],[3,6]]

-- | Conjugate transpose.  This is the adjoint that 'matIsUnitary' and the Gram
-- matrix use; over the real subfield it coincides with 'matTranspose'.
matConjTranspose :: Mat -> Mat
matConjTranspose = map (map kconj) . matTranspose

-- The adjoint of [[1, i], [0, 1]]: conjugate, then transpose.
-- >>> matConjTranspose [[kone, kimag], [kzero, kone]]
-- [[1,0],[-1i,1]]

-- | Build a matrix from its columns.
matFromCols :: [Vec] -> Mat
matFromCols = matTranspose

-- >>> matFromCols [vbasis 2 0, vAllOnes 2]
-- [[1,1],[0,1]]

matColumn :: Mat -> Int -> Vec
matColumn m j = map (!! j) m

-- >>> matColumn (map (map fromInt) [[1, 2], [3, 4]]) 1
-- [2,4]

matIsIdentity :: Mat -> Bool
matIsIdentity m = m == matId (matRows m)

-- >>> matIsIdentity (matId 3)
-- True
-- >>> matIsIdentity (matZero 2 2)
-- False

-- | The row widths of a matrix, in order.  Exported because an error message
-- that says /which/ rows are ragged is worth more than one that says the
-- matrix is.
matRowWidths :: Mat -> [Int]
matRowWidths = map length

-- >>> matRowWidths [[kone, kone], [kone]]
-- [2,1]
-- >>> matRowWidths (matId 3)
-- [3,3,3]

-- | Is this an @n@-by-@n@ matrix, checking every row?
--
-- 'Mat' is a bare @[[K]]@ with no rectangularity invariant, and 'matCols'
-- reports only the first row's width, so @matRows u == matCols u@ passes
-- rows 4, 3, 2, 1 wide, which then passes 'matIsUnitary' too ('zipWith'
-- stops at the shorter list) and fails only later, as an index error.
matIsRectangular :: Int -> Mat -> Bool
matIsRectangular n u = matRows u == n && all (== n) (matRowWidths u)

-- A ragged matrix of the right height is refused.
-- >>> matIsRectangular 2 (matId 2)
-- True
-- >>> matIsRectangular 2 [[kone, kzero], [kzero]]
-- False
-- >>> matIsRectangular 3 (matId 2)
-- False

-- | @U^dagger U = I@ and @U U^dagger = I@: the premise of the @Gate@ rule,
-- checked exactly, and only after the shape test above.
matIsUnitary :: Mat -> Bool
matIsUnitary u =
  matIsRectangular n u
  && matMul (matConjTranspose u) u == matId n
  && matMul u (matConjTranspose u) == matId n
  where n = matRows u

-- The Hadamard matrix is unitary; a matrix of ones is not; a ragged matrix is refused at once.
-- >>> matIsUnitary (matScale kinvsqrt2 [[kone, kone], [kone, kneg kone]])
-- True
-- >>> matIsUnitary [[kone, kone], [kone, kone]]
-- False
-- >>> matIsUnitary [[kone, kzero], [kzero]]
-- False
-- >>> matIsUnitary [[kimag, kzero], [kzero, kone]]
-- True

-- Rank, determinant, minors

-- | Exact rank by Gaussian elimination over the field.  No pivoting heuristic
-- is needed: a nonzero entry is exactly nonzero.
rank :: Mat -> Int
rank m0 = go m0 0
  where
    go [] _ = 0
    go m c
      | c >= matCols m = 0
      | otherwise =
          -- impossible: c < matCols m and the rows of a matrix share a width
          case break (\r -> not (kIsZero (r !! c))) m of
            (_, [])          -> go m (c+1)             -- column is all zero
            (above, p : below) ->
              -- impossible: as above, the row p has an entry in column c
              let piv   = p !! c
                  -- impossible: every row has an entry in column c
                  clear r = let f = kdiv (r !! c) piv
                            in zipWith (\x y -> ksub x (kmul f y)) r p
                  rest  = map clear (above ++ below)
              in 1 + go rest (c+1)

-- A singular matrix has rank below its size.
-- >>> rank (matId 3)
-- 3
-- >>> rank (map (map fromInt) [[1, 2], [2, 4]])
-- 1
-- >>> rank (matZero 2 2)
-- 0
-- >>> rank (map (map fromInt) [[1, 2, 3], [4, 5, 6]])
-- 2

-- | Exact determinant by Gaussian elimination.  The scalars form a field, so
-- ordinary elimination is exact; the pivot is the first row whose leading
-- entry is nonzero, and a swap costs one sign.
--
-- "Drop.Theory.Residual" uses it to test whether the visible action of the
-- per-record table is right-invertible (paper: sec:residual).
det :: Mat -> K
det m0 = go m0 kone
  where
    go [] acc = acc
    go m acc =
      case break (\r -> not (leadIsZero r)) m of
        (_, [])            -> kzero
        (above, p : below) ->
          let sgn  = if null above then kone else kneg kone
              piv  = leadOf p
              clear r = dropFirst (zipWith (\x y -> ksub x (kmul (kdiv (leadOf r) piv) y)) r p)
          in go (map clear (above ++ below)) (kmul acc (kmul sgn piv))
    leadOf (x:_) = x
    -- refusal: a determinant is of a square matrix
    leadOf []    = error "Drop.Theory.Algebra.Linear.det: not square"
    leadIsZero r = kIsZero (leadOf r)
    dropFirst (_:xs) = xs
    dropFirst []     = []

-- >>> det (matId 3)
-- 1
-- >>> det (map (map fromInt) [[1, 2], [3, 4]])
-- -2
-- >>> det (map (map fromInt) [[1, 2], [2, 4]])
-- 0
-- >>> det (map (map fromInt) [[0, 1], [1, 0]])
-- -1

-- | Do all two-by-two minors of a matrix vanish?  Equivalent to
-- @'rank' m <= 1@, and kept separate because the criterion (the criterion section) is
-- stated in exactly this form, as the vanishing of the cut minors.  Checking
-- that the two agree on every example is one of the two independent routes to
-- the criterion (see "Drop.Theory.Criterion").
allTwoByTwoMinorsVanish :: Mat -> Bool
allTwoByTwoMinorsVanish m =
  and [ kmul (e a b) (e a' b') == kmul (e a b') (e a' b)
      | a <- [0 .. r-1], a' <- [a+1 .. r-1]
      , b <- [0 .. c-1], b' <- [b+1 .. c-1] ]
  where
    r = matRows m
    c = matCols m
    -- impossible: i and j range over the rows and columns of m
    e i j = m !! i !! j

-- Agrees with rank <= 1.
-- >>> allTwoByTwoMinorsVanish (map (map fromInt) [[1, 2], [2, 4]])
-- True
-- >>> allTwoByTwoMinorsVanish (matId 2)
-- False
-- >>> allTwoByTwoMinorsVanish [[kone, kzero, kone]]
-- True

-- Mixed radix

dimProduct :: [Int] -> Int
dimProduct = product

-- >>> dimProduct [2, 3]
-- 6
-- >>> dimProduct []
-- 1

-- | Decode a flat index into per-register basis states, first register most
-- significant.
indexToLevels :: [Int] -> Int -> [Int]
indexToLevels dims k = reverse (go (reverse dims) k)
  where
    go []       _ = []
    go (d : ds) n = (n `mod` d) : go ds (n `div` d)

-- Dimensions 2 and 3: index 5 is level 1 of the first register, level 2 of the second.
-- >>> indexToLevels [2, 3] 5
-- [1,2]
-- >>> indexToLevels [2, 3] 0
-- [0,0]
-- >>> map (indexToLevels [2, 2]) [0 .. 3]
-- [[0,0],[0,1],[1,0],[1,1]]

-- | Encode per-register basis states into a flat index.
levelsToIndex :: [Int] -> [Int] -> Int
levelsToIndex dims ls = foldl (\acc (d,l) -> acc * d + l) 0 (zip dims ls)

-- >>> levelsToIndex [2, 3] [1, 2]
-- 5
-- >>> levelsToIndex [2, 3] (indexToLevels [2, 3] 4)
-- 4

-- Register plumbing

-- | @applyGateAt dims g targets@ applies the matrix @g@ to the registers
-- at @targets@ (in order) of a state over @dims@: the operator the @Gate@
-- rule denotes, lifted to the whole named tensor.
--
-- Built as a /matrix/ rather than a function since later analysis (rank,
-- minors, Gram) wants coefficients.
applyGateAt :: [Int] -> Mat -> [Int] -> Mat
applyGateAt dims g targets =
  matFromCols [ column k | k <- [0 .. n - 1] ]
  where
    n        = dimProduct dims
    -- impossible: each target names a register of dims
    tgtDims  = [ dims !! t | t <- targets ]
    tgtSize  = dimProduct tgtDims
    column k =
      let ls   = indexToLevels dims k
          -- impossible: ls has one level for each register, and each target names one
          jls  = [ ls !! t | t <- targets ]
          j    = levelsToIndex tgtDims jls
          -- column j of g scatters into every row i of the target block
          contrib i =
            -- impossible: g has one row and one column for each joint level of the targets, and i, j are such levels
            let gij = g !! i !! j
            in if kIsZero gij then Nothing
               else let ils = indexToLevels tgtDims i
                        ls' = foldl (\acc (t,l) -> setAt t l acc) ls (zip targets ils)
                    in Just (levelsToIndex dims ls', gij)
      in accumulate n [ c | i <- [0 .. tgtSize - 1], Just c <- [contrib i] ]
    setAt i x xs = take i xs ++ [x] ++ drop (i+1) xs
    accumulate n' assocs =
      [ ksum [ v | (i,v) <- assocs, i == r ] | r <- [0 .. n' - 1] ]

-- X on the second of two qubits swaps basis states 0 and 1, and 2 and 3.
-- >>> applyGateAt [2, 2] [[kzero, kone], [kone, kzero]] [1]
-- [[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]
-- >>> applyGateAt [2, 2] [[kzero, kone], [kone, kzero]] [0] == kron [[kzero, kone], [kone, kzero]] (matId 2)
-- True

-- | @reorder dims order@ is the permutation matrix that rearranges the tensor
-- factors: @order@ lists the /old/ positions in their /new/ order.
--
-- This is the only place the symmetry of the tensor is used.  In the typing
-- rules that symmetry is invisible (contexts are finite maps, so exchange is
-- not a rule); in the elaboration it has to be a matrix, and this is it.
reorder :: [Int] -> [Int] -> Mat
reorder dims order =
  matFromCols [ vbasis n (target k) | k <- [0 .. n-1] ]
  where
    n        = dimProduct dims
    -- impossible: order lists positions of dims
    dims'    = [ dims !! i | i <- order ]
    target k = let ls = indexToLevels dims k
               -- impossible: order lists positions of dims, and ls has a level for each
               in levelsToIndex dims' [ ls !! i | i <- order ]

-- Swapping two qubits exchanges the basis states 01 and 10.
-- >>> reorder [2, 2] [1, 0]
-- [[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]]
-- >>> reorder [2, 3] [0, 1] == matId 6
-- True

-- | The permutation matrix that moves the register at position @p@ to the
-- front, leaving the others in order.  Used to make the @Drop@ rule
-- compositional: see "Drop.Theory.Program.Elaborate".
permuteToFront :: [Int] -> Int -> Mat
permuteToFront dims p = reorder dims (p : [ i | i <- [0 .. length dims - 1], i /= p ])

-- >>> permuteToFront [2, 2] 1 == reorder [2, 2] [1, 0]
-- True
-- >>> permuteToFront [2, 2, 2] 0 == matId 8
-- True

-- | Zero every amplitude whose basis state in register @p@ is outside @keep@.  This
-- is a /selected/ block measurement, left unnormalised so that branch weights
-- stay exact: the squared norm of the result is the branch's probability.
projectLevels :: [Int] -> Int -> [Int] -> Vec -> Vec
projectLevels dims p keep st =
  -- impossible: p names a register of dims
  [ if (indexToLevels dims k !! p) `elem` keep then a else kzero
  | (k, a) <- zip [0 ..] st ]

-- Keep the amplitudes whose second qubit is 0.
-- >>> projectLevels [2, 2] 1 [0] [kone, ktwo, kimag, khalf]
-- [1,0,i,0]
-- >>> projectLevels [2, 2] 0 [0, 1] [kone, ktwo, kimag, khalf]
-- [1,2,i,1/2]
