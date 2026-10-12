-- |
-- Module      : Drop.Theory.Algebra.Linear
--
-- Exact linear algebra over "Drop.Theory.Algebra.Scalar".  Vectors are lists, matrices lists
-- of rows.  Flat index @k = ((l1 * d2 + l2) * d3 + l3) ...@: the first
-- register is most significant, and matrix rows read the same way.
module Drop.Theory.Algebra.Linear
  ( -- * Types
    Vec, Mat
    -- * Vectors
  , vzero, vbasis, vadd, vsub, vscale, vdot, vnorm2, vIsZero, vEqual
  , vAllOnes
    -- * Tensor
  , tensorV, kron
    -- * Matrices
  , matId, matZero, matMul, matVec, matAdd, matScale
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
type Mat = [[K]]      -- ^ row-major: @m !! i !! j@ is the entry in row @i@, column @j@

-- Vectors

vzero :: Int -> Vec
vzero n = replicate n kzero

-- | @vbasis n j@ is the basis vector @e_j@ in dimension @n@.
vbasis :: Int -> Int -> Vec
vbasis n j = [ if i == j then kone else kzero | i <- [0 .. n-1] ]

-- | The all-ones superposition, unnormalised.  It is the @+1@ in the
-- @dim + 1@ test states of the certification count.
vAllOnes :: Int -> Vec
vAllOnes n = replicate n kone

vadd :: Vec -> Vec -> Vec
vadd = zipWith kadd

vsub :: Vec -> Vec -> Vec
vsub = zipWith ksub

vscale :: K -> Vec -> Vec
vscale c = map (kmul c)

-- | The Hermitian inner product, conjugate-linear in the /first/ argument.
vdot :: Vec -> Vec -> K
vdot u v = ksum (zipWith (\a b -> kmul (kconj a) b) u v)

vnorm2 :: Vec -> K
vnorm2 v = vdot v v

vIsZero :: Vec -> Bool
vIsZero = all kIsZero

vEqual :: Vec -> Vec -> Bool
vEqual u v = length u == length v && and (zipWith (==) u v)

-- Tensor

-- | Kronecker product of vectors, first argument most significant.
tensorV :: Vec -> Vec -> Vec
tensorV u v = [ kmul a b | a <- u, b <- v ]

-- | Kronecker product of matrices, first argument most significant.
kron :: Mat -> Mat -> Mat
kron a b =
  [ [ kmul x y | x <- rowA, y <- rowB ] | rowA <- a, rowB <- b ]

-- Matrices

matId :: Int -> Mat
matId n = [ vbasis n i | i <- [0 .. n-1] ]

matZero :: Int -> Int -> Mat
matZero r c = replicate r (vzero c)

matRows :: Mat -> Int
matRows = length

matCols :: Mat -> Int
matCols []      = 0
matCols (r : _) = length r

matMul :: Mat -> Mat -> Mat
matMul a b =
  [ [ ksum (zipWith kmul row col) | col <- bT ] | row <- a ]
  where bT = matTranspose b

matVec :: Mat -> Vec -> Vec
matVec a v = [ ksum (zipWith kmul row v) | row <- a ]

matAdd :: Mat -> Mat -> Mat
matAdd = zipWith (zipWith kadd)

matScale :: K -> Mat -> Mat
matScale c = map (map (kmul c))

matTranspose :: Mat -> Mat
matTranspose = transpose

-- | Conjugate transpose.  This is the adjoint that 'matIsUnitary' and the Gram
-- matrix use; over the real subfield it coincides with 'matTranspose'.
matConjTranspose :: Mat -> Mat
matConjTranspose = map (map kconj) . matTranspose

-- | Build a matrix from its columns.
matFromCols :: [Vec] -> Mat
matFromCols = matTranspose

matColumn :: Mat -> Int -> Vec
matColumn m j = map (!! j) m

matIsIdentity :: Mat -> Bool
matIsIdentity m = m == matId (matRows m)

-- | The row widths of a matrix, in order.  Exported because an error message
-- that says /which/ rows are ragged is worth more than one that says the
-- matrix is.
matRowWidths :: Mat -> [Int]
matRowWidths = map length

-- | Is this an @n@-by-@n@ matrix, checking every row?
--
-- 'Mat' is a bare @[[K]]@ with no rectangularity invariant, and 'matCols'
-- reports only the first row's width, so @matRows u == matCols u@ passes
-- rows 4, 3, 2, 1 wide, which then passes 'matIsUnitary' too ('zipWith'
-- stops at the shorter list) and fails only later, as an index error.
matIsRectangular :: Int -> Mat -> Bool
matIsRectangular n u = matRows u == n && all (== n) (matRowWidths u)

-- | @U^dagger U = I@ and @U U^dagger = I@: the premise of the @Gate@ rule,
-- checked exactly, and only after the shape test above.
matIsUnitary :: Mat -> Bool
matIsUnitary u =
  matIsRectangular n u
  && matMul (matConjTranspose u) u == matId n
  && matMul u (matConjTranspose u) == matId n
  where n = matRows u

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
          case break (\r -> not (kIsZero (r !! c))) m of
            (_, [])          -> go m (c+1)             -- column is all zero
            (above, p : below) ->
              let piv   = p !! c
                  clear r = let f = kdiv (r !! c) piv
                            in zipWith (\x y -> ksub x (kmul f y)) r p
                  rest  = map clear (above ++ below)
              in 1 + go rest (c+1)

-- | Exact determinant by Gaussian elimination.  The scalars form a field, so
-- ordinary elimination is exact; the pivot is the first row whose leading
-- entry is nonzero, and a swap costs one sign.
--
-- Used only for the right-invertibility hypothesis of the per-record table
-- (the record-dependent reclaim section), never for a drop verdict.
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
    leadOf []    = error "Drop.Theory.Algebra.Linear.det: not square"
    leadIsZero r = kIsZero (leadOf r)
    dropFirst (_:xs) = xs
    dropFirst []     = []

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
    e i j = m !! i !! j

-- Mixed radix

dimProduct :: [Int] -> Int
dimProduct = product

-- | Decode a flat index into per-register basis states, first register most
-- significant.
indexToLevels :: [Int] -> Int -> [Int]
indexToLevels dims k = reverse (go (reverse dims) k)
  where
    go []       _ = []
    go (d : ds) n = (n `mod` d) : go ds (n `div` d)

-- | Encode per-register basis states into a flat index.
levelsToIndex :: [Int] -> [Int] -> Int
levelsToIndex dims ls = foldl (\acc (d,l) -> acc * d + l) 0 (zip dims ls)

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
    tgtDims  = [ dims !! t | t <- targets ]
    tgtSize  = dimProduct tgtDims
    column k =
      let ls   = indexToLevels dims k
          jls  = [ ls !! t | t <- targets ]
          j    = levelsToIndex tgtDims jls
          -- column j of g scatters into every row i of the target block
          contrib i =
            let gij = g !! i !! j
            in if kIsZero gij then Nothing
               else let ils = indexToLevels tgtDims i
                        ls' = foldl (\acc (t,l) -> setAt t l acc) ls (zip targets ils)
                    in Just (levelsToIndex dims ls', gij)
      in accumulate n [ c | i <- [0 .. tgtSize - 1], Just c <- [contrib i] ]
    setAt i x xs = take i xs ++ [x] ++ drop (i+1) xs
    accumulate n' assocs =
      [ ksum [ v | (i,v) <- assocs, i == r ] | r <- [0 .. n' - 1] ]

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
    dims'    = [ dims !! i | i <- order ]
    target k = let ls = indexToLevels dims k
               in levelsToIndex dims' [ ls !! i | i <- order ]

-- | The permutation matrix that moves the register at position @p@ to the
-- front, leaving the others in order.  Used to make the @Drop@ rule
-- compositional: see "Drop.Theory.Program.Elaborate".
permuteToFront :: [Int] -> Int -> Mat
permuteToFront dims p = reorder dims (p : [ i | i <- [0 .. length dims - 1], i /= p ])

-- | Zero every amplitude whose basis state in register @p@ is outside @keep@.  This
-- is a /selected/ block measurement, left unnormalised so that branch weights
-- stay exact: the squared norm of the result is the branch's probability.
projectLevels :: [Int] -> Int -> [Int] -> Vec -> Vec
projectLevels dims p keep st =
  [ if (indexToLevels dims k !! p) `elem` keep then a else kzero
  | (k, a) <- zip [0 ..] st ]
