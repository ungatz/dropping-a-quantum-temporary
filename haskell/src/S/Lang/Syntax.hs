-- Syntax.hs: abstract syntax of the surface language S.
--
-- One constructor per construct of the calculus. Gate covers
-- both a temporary gate and a visible-only gate, distinguished by the names
-- it carries, not by the constructor. Drop carries no obligation: it is
-- denotationally the identity, so unsafe programs stay expressible.

module S.Lang.Syntax where

data Cmd a
  = New String Int
    -- ^ @new x:d@: allocate a temporary of dimension d at the basis state |0>
  | NewDirty String Int [a]
    -- ^ @newdirty x:d \@ psi@: introduce x on the named unit state, a dirty
    -- ancilla whose provenance is outside the program.
  | Gate [[a]] [String]
    -- ^ a joint unitary, given as an exact matrix, on the named registers
  | Lift String String [Int]
    -- ^ @p = lift(meas x in S)@: block measurement of x against the set of
    -- basis states S. The run's selection chooses the surviving block and
    -- binds p to 1 (the block) or 0 (its complement); x survives, restricted.
  | IfBit String [Cmd a] [Cmd a]
    -- ^ classical control on a lifted bit
  | Drop String
    -- ^ @drop x@: the construct under study, denotationally the identity
  deriving (Show, Eq)   -- Eq lets the parse-render identity compare programs

type Prog a = [Cmd a]

-- | The visible registers a program starts with, as (name, dimension).
type VisSpec = [(String, Int)]

-- | One choice per lift: SIn selects the measured block, SOut its complement.
data Sel = SIn | SOut deriving (Eq, Ord, Show)

selBit :: Sel -> Int
selBit SIn  = 1
selBit SOut = 0
