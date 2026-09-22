-- |
-- Module      : Drop.Theory.Corpus.Classical
--
-- The obstruction is not quantum: one fair three-way classical coin and one
-- reversible permutation give a single text with three equiprobable runs
-- and opposite drop verdicts; two dimensions never split ('twoLevelsNeverSplit').
module Drop.Theory.Corpus.Classical
  ( -- * The model
    ClassicalProgram(..)
  , outgoingTemporary
  , safeOnBlock
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

-- | The temporary value the run leaves behind.
outgoingTemporary :: ClassicalProgram -> Int -> Int -> Int
outgoingTemporary p v t = snd (cpPerm p (v, t))

-- | The drop is safe on a surviving block when the outgoing temporary does not
-- depend on the visible input, for any coin value in that block.
safeOnBlock :: ClassicalProgram -> [Int] -> Bool
safeOnBlock p b =
  and [ outgoingTemporary p v t == outgoingTemporary p v' t
      | t <- b, v <- [0 .. cpVis p - 1], v' <- [0 .. cpVis p - 1] ]

-- | The two blocks a read distinguishes: @S@ and its complement.
blocks :: ClassicalProgram -> [[Int]]
blocks p = [ cpBlock p, [ t | t <- [0 .. cpTmp p - 1], t `notElem` cpBlock p ] ]

classicalProfile :: ClassicalProgram -> [([Int], Bool)]
classicalProfile p = [ (b, safeOnBlock p b) | b <- blocks p, not (null b) ]

-- | Does one text give opposite verdicts on its two outcomes?
classicalSplit :: ClassicalProgram -> Bool
classicalSplit p =
  case map snd (classicalProfile p) of
    vs -> or vs && not (and vs)

-- | The witness.
--
-- > pi(v, t) = (v, t (+) v)  for t in {0,1};   (v, 2)  for t = 2.
--
-- A bijection (involution on the first block, identity on the second).
-- @t in {0,1}@: outgoing temporary is @t (+) v@, both values as @v@ varies,
-- leaks @v@. @t = 2@: outgoing temporary is constantly @2@, safe.
--
-- Three equiprobable runs, opposite verdicts, one text: any sound analysis
-- must reject it, losing the genuinely safe run @t = 2@.
classicalWitness :: ClassicalProgram
classicalWitness = ClassicalProgram
  { cpLabel = "one fair trit, one permutation, one partial read"
  , cpVis   = 2
  , cpTmp   = 3
  , cpPerm  = \(v, t) -> if t <= 1 then (v, (t + v) `mod` 2) else (v, 2)
  , cpBlock = [0, 1]
  }

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

-- | At dimension three a split exists, 'classicalWitness' being one, so this
-- returns 'True'; the two results together are the two halves of the
-- statement.
threeLevelsCanSplit :: Bool
threeLevelsCanSplit = classicalSplit classicalWitness

-- | Build a classical program from a permutation of the flat index set.
fromPerm :: Int -> Int -> [Int] -> [Int] -> ClassicalProgram
fromPerm nv nt pm b = ClassicalProgram
  { cpLabel = "search"
  , cpVis   = nv
  , cpTmp   = nt
  , cpPerm  = \(v, t) -> let k = pm !! (v * nt + t) in (k `div` nt, k `mod` nt)
  , cpBlock = b
  }

allPerms :: Int -> [[Int]]
allPerms n = permutations [0 .. n - 1]
