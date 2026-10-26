-- Drop.Lang.Flat: a program as the interpreter and the compiler run it, one command after another.
--
-- Question: Why a second syntax, and how does it relate to the first?
-- Answer:   The typed term is what the type checker reads and the paper's machine steps; the
--           interpreter, the criterion and the compiler run a flat list of commands with no binder
--           to track: New, NewState, Loan, Gate, Lift, IfBit and Drop, one per construct of the
--           calculus. Drop.Lang.Elab is the bridge, and the desugaring lemma says the two agree.
--           A Drop names its registers in the order the value names them: a tuple drop is one site.
-- Paper:    fig:syntax (the constructs, one per command), sec:lang:denotation (what a command denotes).
-- Shapes:   Cmd a      one command; Prog a = [Cmd a].
--           Guard      the guards over lifted parameters: GBit, GParam, GNot, GAnd, GOr.
--           VisSpec    the header's ordinary inputs as (name, dimension); a loan is a Loan command.
--           Sel        SIn or SOut, one choice per lift; selBit prints it as 1 or 0.

module Drop.Lang.Flat where

-- The commands ---------------------------------------------------------------
--
-- One constructor per construct of the calculus (the language section, the syntax figure).
-- 'Gate' covers every gate statement, named or written out as a matrix,
-- distinguished by the registers it carries, not by the constructor. 'Drop'
-- carries no obligation: it is denotationally the identity, so unsafe
-- programs stay expressible, and it names a list of registers because a
-- tuple drop is ONE site (the composite-temporary proposition), not two.
--
-- Two allocation forms and one input form. A temporary the program owns is
-- allocated by 'New' (the basis state |0>) or 'NewState' (@new x : [d] @
-- psi@, any named unit state). A 'Loan' is not allocated at all: it is an
-- input register, declared in the program header as @loan a : [d]@, which
-- the program is handed in a state it does not know and must hand back. The
-- parser hoists each header loan to a 'Loan' command at the head of the
-- body, before any 'New', so the machine's allocation order puts every loan
-- among the inputs, which is what it is; the compiler prepares it with
-- nothing.

data Cmd a
  = New String Int
    -- ^ @new x : [d];@: a temporary allocated at the basis state |0>
  | NewState String Int [a]
    -- ^ @new x : [d] @ psi;@: a temporary allocated on the named unit state
  | Loan String Int
    -- ^ @loan x : [d]@ in the program header: an input register in a state
    -- the program does not know, to be handed back at its drop. Hoisted by
    -- the parser to the head of the body; never written as a statement.
  | Gate [[a]] [String]
    -- ^ a joint unitary, given as an exact matrix, on the named registers
  | Lift String String [Int]
    -- ^ @p = lift[S] x;@: block measurement of x against the set of levels
    -- S. The run's selection chooses the surviving block and binds p to 1
    -- (the block) or 0 (its complement); x survives under its own name.
  | IfBit Guard [Cmd a] [Cmd a]
    -- ^ classical control on a guard over lifted parameters
  | Drop [String]
    -- ^ @drop v;@: the construct under study, denotationally the identity.
    -- The list is the registers the value names, in the order it names
    -- them; a tuple drop is one site.
  deriving (Show, Eq)   -- Eq lets the parse-render identity compare programs

-- | A guard: the paper's @e ::= b | p | not e | e1 and e2 | e1 or e2@ over
-- the parameters the lifts bind. 'GBit' is the bit constant; it is what
-- Step-Lift leaves in place of the parameter it consumed, so a guard stays a
-- guard as the machine reduces it.
data Guard
  = GBit Bool
  | GParam String
  | GNot Guard
  | GAnd Guard Guard
  | GOr Guard Guard
  deriving (Show, Eq)

-- | Every parameter a guard reads.
guardParams :: Guard -> [String]
guardParams (GBit _)   = []
guardParams (GParam p) = [p]
guardParams (GNot e)   = guardParams e
guardParams (GAnd a b) = guardParams a ++ guardParams b
guardParams (GOr a b)  = guardParams a ++ guardParams b

-- >>> guardParams (GBit True)
-- []
-- >>> guardParams (GParam "p")
-- ["p"]
-- >>> guardParams (GAnd (GParam "p") (GNot (GParam "q")))
-- ["p","q"]
-- >>> guardParams (GOr (GParam "p") (GParam "p"))
-- ["p","p"]

-- | A guard's value, given the bits in scope.
evalGuard :: (String -> Bool) -> Guard -> Bool
evalGuard _   (GBit b)   = b
evalGuard env (GParam p) = env p
evalGuard env (GNot e)   = not (evalGuard env e)
evalGuard env (GAnd a b) = evalGuard env a && evalGuard env b
evalGuard env (GOr a b)  = evalGuard env a || evalGuard env b

-- >>> evalGuard (const False) (GBit True)
-- True
-- >>> evalGuard (== "p") (GParam "p")
-- True
-- >>> evalGuard (== "p") (GAnd (GParam "p") (GNot (GParam "q")))
-- True
-- >>> evalGuard (const False) (GOr (GParam "p") (GParam "q"))
-- False

-- | A guard back to the concrete syntax (@0@, @1@, @!@, @&&@, @||@).
showGuard :: Guard -> String
showGuard = go (0 :: Int)
  where
    go _ (GBit b)   = if b then "1" else "0"
    go _ (GParam p) = p
    go _ (GNot e)   = "!" ++ go 3 e
    go d (GAnd a b) = paren (d > 2) (go 2 a ++ " && " ++ go 2 b)
    go d (GOr a b)  = paren (d > 1) (go 1 a ++ " || " ++ go 1 b)
    paren True s  = "(" ++ s ++ ")"
    paren False s = s

-- A constant and a parameter need no parentheses.
-- >>> showGuard (GBit True)
-- "1"
-- >>> showGuard (GParam "m")
-- "m"

-- An and inside an or needs none, because and binds tighter.
-- >>> showGuard (GOr (GAnd (GParam "p") (GParam "q")) (GParam "r"))
-- "p && q || r"

-- An or inside an and needs them.
-- >>> showGuard (GAnd (GOr (GParam "p") (GParam "q")) (GParam "r"))
-- "(p || q) && r"
-- >>> showGuard (GNot (GAnd (GParam "p") (GParam "q")))
-- "!(p && q)"

-- | A program is a list of commands.
type Prog a = [Cmd a]

-- The abstract's temporary AND, uncomputed by measurement, is six commands: one drop, one lift, one if.
-- >>> :m + Drop.Lang.Programs.TempAnd
-- >>> length andUncomputedByMeasurement
-- 6
-- >>> [ x | Drop x <- andUncomputedByMeasurement ]
-- [["a"]]
-- >>> [ (p, x, s) | Lift p x s <- andUncomputedByMeasurement ]
-- [("m","a",[1])]
-- >>> [ g | IfBit g _ _ <- andUncomputedByMeasurement ]
-- [GParam "m"]

-- | Map a program's scalars into another type.
mapProg :: (a -> b) -> Prog a -> Prog b
mapProg f = map go
  where
    go c = case c of
      New x d        -> New x d
      NewState x d s -> NewState x d (map f s)
      Loan x d       -> Loan x d
      Gate g xs      -> Gate (map (map f) g) xs
      Lift p x b     -> Lift p x b
      IfBit p t e    -> IfBit p (mapProg f t) (mapProg f e)
      Drop xs        -> Drop xs

-- Two commands over the rationals, every scalar doubled; the register names and the gate's shape stay.
-- >>> mapProg (* 2) ([NewState "a" 2 [0, 1], Gate [[0, 1], [1, 0]] ["a"]] :: Prog Rational)
-- [NewState "a" 2 [0 % 1,2 % 1],Gate [[0 % 1,2 % 1],[2 % 1,0 % 1]] ["a"]]

-- The same two commands, each scalar turned into its text.
-- >>> mapProg show ([NewState "a" 2 [0, 1], Gate [[0, 1], [1, 0]] ["a"]] :: Prog Rational)
-- [NewState "a" 2 ["0 % 1","1 % 1"],Gate [["0 % 1","1 % 1"],["1 % 1","0 % 1"]] ["a"]]

-- The commands that carry no scalar come back as they were.
-- >>> mapProg (* 2) ([Lift "m" "a" [1], Drop ["a"], IfBit (GParam "m") [Drop ["b"]] []] :: Prog Rational)
-- [Lift "m" "a" [1],Drop ["a"],IfBit (GParam "m") [Drop ["b"]] []]

-- | The registers a program starts with, as (name, dimension): the header's
-- ordinary parameters. A loan is an input too, but it is carried by its own
-- 'Loan' command so that the criterion can tell the two apart.
type VisSpec = [(String, Int)]

-- >>> :m + Drop.Lang.Programs.TempAnd
-- >>> visXY
-- [("x",2),("y",2)]

-- | One choice per lift: SIn selects the measured block, SOut its complement.
data Sel = SIn | SOut deriving (Eq, Ord, Show)

-- | The bit a choice binds to the lifted parameter: 1 for the block, 0 for its complement.
selBit :: Sel -> Int
selBit SIn  = 1
selBit SOut = 0

-- >>> selBit SIn
-- 1
-- >>> selBit SOut
-- 0
-- >>> map selBit [SIn, SOut, SIn]
-- [1,0,1]

