-- Drop.Theory.Corpus.Classical: the obstruction is not quantum.
--
-- Question: Can one reversible classical program, run on a fair three-way coin, drop safely on one run
--           and unsafely on another?
-- Answer:   Yes. A ClassicalProgram is a permutation of pairs (visible value, temporary value) and
--           a block of temporary values that a read distinguishes. The drop is safe on a block when
--           the temporary the run leaves behind does not depend on the visible input
--           (safeOnBlock); classicalSplit asks whether the two blocks, S and its complement, get
--           opposite verdicts. classicalWitness is one text with three equiprobable runs, the
--           temporary 0, 1 or 2: it leaks the visible bit on the first two and is safe on the third.
--           For two temporary levels no program splits, checked over every permutation for a given
--           number of visible values (twoLevelsNeverSplit); threeLevelsCanSplit is the witness.
-- Paper:    sec:boundary (why the record matters).
-- Shapes:   ClassicalProgram   a label, the two sizes, the permutation pi(v, t) and the block S.

module Drop.Theory.Corpus.Classical
  ( -- * The model
    ClassicalProgram(..)
  , blocks
  , classicalProfile
  , classicalSplit
    -- * The witness
  , classicalWitness
    -- * The converse: a temporary bit is never underdetermined
  , twoLevelsNeverSplit
  , threeLevelsCanSplit
  ) where

import Data.List (permutations)

-- | A classical reversible program over @V x T@: a permutation of the pair set,
-- and the block of temporary values the read distinguishes.
data ClassicalProgram = ClassicalProgram
  { cpLabel :: String
  , cpVis   :: Int                    -- ^ @|V|@
  , cpTmp   :: Int                    -- ^ @|T|@
  , cpPerm  :: (Int, Int) -> (Int, Int)  -- ^ @pi(v, t)@
  , cpBlock :: [Int]                  -- ^ @S@, the block the read distinguishes
  }

-- The witness: two visible values, three temporary values, the permutation, and the block {0, 1}.
-- >>> cpLabel classicalWitness
-- "one fair trit, one permutation, one partial read"
-- >>> (cpVis classicalWitness, cpTmp classicalWitness, cpBlock classicalWitness)
-- (2,3,[0,1])
-- >>> map (cpPerm classicalWitness) [(1, 0), (1, 1), (1, 2)]
-- [(1,1),(1,0),(1,2)]

-- | The temporary value the run leaves behind.
outgoingTemporary :: ClassicalProgram -> Int -> Int -> Int
outgoingTemporary p v t = snd (cpPerm p (v, t))

-- On t = 0 or 1 the temporary comes out as t + v mod 2; on t = 2 it stays 2.
-- >>> [ outgoingTemporary classicalWitness v 0 | v <- [0, 1] ]
-- [0,1]
-- >>> [ outgoingTemporary classicalWitness v 2 | v <- [0, 1] ]
-- [2,2]

-- | The drop is safe on a surviving block when the outgoing temporary does not
-- depend on the visible input, for any coin value in that block.
safeOnBlock :: ClassicalProgram -> [Int] -> Bool
safeOnBlock p b =
  and [ outgoingTemporary p v t == outgoingTemporary p v' t
      | t <- b, v <- [0 .. cpVis p - 1], v' <- [0 .. cpVis p - 1] ]

-- >>> safeOnBlock classicalWitness [0, 1]
-- False
-- >>> safeOnBlock classicalWitness [2]
-- True
-- >>> safeOnBlock classicalWitness []
-- True

-- | The two blocks a read distinguishes: @S@ and its complement.
blocks :: ClassicalProgram -> [[Int]]
blocks p = [ cpBlock p, [ t | t <- [0 .. cpTmp p - 1], t `notElem` cpBlock p ] ]

-- >>> blocks classicalWitness
-- [[0,1],[2]]

classicalProfile :: ClassicalProgram -> [([Int], Bool)]
classicalProfile p = [ (b, safeOnBlock p b) | b <- blocks p, not (null b) ]

-- >>> classicalProfile classicalWitness
-- [([0,1],False),([2],True)]
-- >>> classicalProfile (ClassicalProgram "identity" 2 2 id [0])
-- [([0],True),([1],True)]

-- | Does one text give opposite verdicts on its two outcomes?
classicalSplit :: ClassicalProgram -> Bool
classicalSplit p =
  case map snd (classicalProfile p) of
    vs -> or vs && not (and vs)

-- >>> classicalSplit classicalWitness
-- True
-- >>> classicalSplit (ClassicalProgram "identity" 2 2 id [0])
-- False

-- | The witness.
--
-- > pi(v, t) = (v, t (+) v)  for t in {0,1};   (v, 2)  for t = 2.
--
-- A bijection (involution on the first block, identity on the second).
-- @t in {0,1}@: outgoing temporary is @t (+) v@, both values as @v@ varies,
-- leaks @v@. @t = 2@: outgoing temporary is constantly @2@, safe.
--
-- Three equiprobable runs, opposite verdicts, one text: an analysis that sees
-- the text and not the run must reject it, and so rejects the safe run @t = 2@.
classicalWitness :: ClassicalProgram
classicalWitness = ClassicalProgram
  { cpLabel = "one fair trit, one permutation, one partial read"
  , cpVis   = 2
  , cpTmp   = 3
  , cpPerm  = \(v, t) -> if t <= 1 then (v, (t + v) `mod` 2) else (v, 2)
  , cpBlock = [0, 1]
  }

-- One text, three equiprobable runs, opposite verdicts.
-- >>> map (\b -> (b, safeOnBlock classicalWitness [b])) [0, 1, 2]
-- [(0,False),(1,False),(2,True)]
-- >>> classicalSplit classicalWitness
-- True

-- The Converse, Checked Exhaustively

-- | A temporary bit is never underdetermined: over every permutation of
-- @V x {0,1}@ and every block, if the drop is safe on one block then it is safe
-- on the other.  Checked by exhaustive search for a given @|V|@, which is
-- @4! = 24@ permutations at @|V| = 2@ and @6! = 720@ at @|V| = 3@.
twoLevelsNeverSplit :: Int -> Bool
twoLevelsNeverSplit nv =
  and [ not (classicalSplit (fromPerm nv 2 pm b))
      | pm <- allPerms (nv * 2)
      , b  <- [[0], [1]] ]

-- Every permutation of V x {0, 1}: 4! = 24 of them for two visible values, 6! = 720 for three.
-- >>> twoLevelsNeverSplit 1
-- True
-- >>> twoLevelsNeverSplit 2
-- True
-- >>> twoLevelsNeverSplit 3
-- True

-- | At dimension three a split exists, 'classicalWitness' being one, so this
-- returns 'True'; the two results together are the two halves of the
-- statement.
threeLevelsCanSplit :: Bool
threeLevelsCanSplit = classicalSplit classicalWitness

-- >>> threeLevelsCanSplit
-- True

-- | Build a classical program from a permutation of the flat index set.
fromPerm :: Int -> Int -> [Int] -> [Int] -> ClassicalProgram
fromPerm nv nt pm b = ClassicalProgram
  { cpLabel = "search"
  , cpVis   = nv
  , cpTmp   = nt
  -- impossible: pm permutes the nv * nt flat indices, and v * nt + t is one of them
  , cpPerm  = \(v, t) -> let k = pm !! (v * nt + t) in (k `div` nt, k `mod` nt)
  , cpBlock = b
  }

-- The flat index v * nt + t is sent to pm !! (v * nt + t): here the swap of the two temporary values.
-- >>> let p = fromPerm 2 2 [1, 0, 3, 2] [0]
-- >>> map (cpPerm p) [(0, 0), (0, 1), (1, 0), (1, 1)]
-- [(0,1),(0,0),(1,1),(1,0)]
-- >>> classicalProfile p
-- [([0],True),([1],True)]

allPerms :: Int -> [[Int]]
allPerms n = permutations [0 .. n - 1]

-- >>> allPerms 3
-- [[0,1,2],[1,0,2],[2,1,0],[1,2,0],[2,0,1],[0,2,1]]
-- >>> length (allPerms 4)
-- 24
