-- |
-- Module      : DQT.Calculus.Syntax
--
-- The measurement-free affine calculus: @new@ brings a
-- temporary into existence, a joint gate lets it act on the visible
-- register, and @drop@ removes its name, with no side condition of its own.
module DQT.Calculus.Syntax
  ( -- * Types
    RegTy(..), Ty(..)
  , regDim, tyDim
    -- * Gates
  , Gate(..), GateKind(..)
  , onTmp, onVis, joint, gateDim, gateFactors
    -- * Terms
  , Name
  , Term(..)
  , Program(..)
    -- * The allocation-free predicate, by structural recursion
  , allocFree
    -- * Occurrences
  , freeNames, dropsIn, gatesIn
    -- * Printing
  , pretty, prettyProgram, prettySugared
  ) where

import Data.List (nub)

import DQT.Algebra.Linear

-- Types

-- | Register types.  @Tmp d@ is a @d@-dimensional temporary; @Vis m@ an
-- @m@-dimensional visible register.  Both are finite registers; the
-- distinction is a discipline: only a @Tmp@ can be the subject of a @drop@.
data RegTy = Tmp Int | Vis Int
  deriving (Eq)

instance Show RegTy where
  show (Tmp d) = "tmp[" ++ show d ++ "]"
  show (Vis m) = "vis[" ++ show m ++ "]"

-- | Value types: @A, B ::= Q | A (x) B@.
data Ty = TyReg RegTy | TyPair Ty Ty
  deriving (Eq)

instance Show Ty where
  show (TyReg q)    = show q
  show (TyPair a b) = "(" ++ show a ++ " (x) " ++ show b ++ ")"

regDim :: RegTy -> Int
regDim (Tmp d) = d
regDim (Vis m) = m

tyDim :: Ty -> Int
tyDim (TyReg q)    = regDim q
tyDim (TyPair a b) = tyDim a * tyDim b

-- Gates

-- | Which register a gate was /declared/ to touch: a syntactic label
-- rather than a semantic test. The identity is simultaneously @I (x) I@,
-- so asking the matrix "is this a product?" is ambiguous while asking
-- the program text "how was this gate written?" is not. @sep(R,W)@ is a
-- statement about how gates were written.
data GateKind = OnTmp | OnVis | Joint
  deriving (Eq, Show)

-- | A gate of the calculus: a named unitary on @H_d (x) H_m@, temporary factor
-- first.  The @Gate@ typing rule's premise @U^dagger U = U U^dagger = I@ is
-- checked in "DQT.Calculus.Typing", not here, so that an ill-typed program can still be
-- built and then rejected.
data Gate = Gate
  { gateLabel  :: String    -- ^ how it prints
  , gateKind   :: GateKind
  , gateTmpDim :: Int
  , gateVisDim :: Int
  , gateMat    :: Mat       -- ^ on @H_{tmpDim} (x) H_{visDim}@, temporary most significant
  }

instance Show Gate where show = gateLabel

gateDim :: Gate -> Int
gateDim g = gateTmpDim g * gateVisDim g

-- | @onTmp name r m@ is @R (x) I_m@: a gate that touches only the temporary.
onTmp :: String -> Mat -> Int -> Gate
onTmp nm r m = Gate nm OnTmp (matRows r) m (kron r (matId m))

-- | @onVis name d w@ is @I_d (x) W@: a gate that touches only the visible
-- register.  These two constructors are exactly the two holes of the shape
-- @sep(R, W)@ that "DQT.Criterion.Witness" fills.
onVis :: String -> Int -> Mat -> Gate
onVis nm d w = Gate nm OnVis d (matRows w) (kron (matId d) w)

-- | A genuinely joint gate: the general case, and the only one that can
-- correlate the two registers.
joint :: String -> Int -> Int -> Mat -> Gate
joint nm = Gate nm Joint

-- | The one-register factor of a declared product gate: @R@ for an 'OnTmp'
-- gate, @W@ for an 'OnVis' one, and nothing for a joint gate.
gateFactors :: Gate -> Maybe (GateKind, Mat)
gateFactors g = case gateKind g of
  Joint -> Nothing
  OnTmp -> Just (OnTmp, [ [ u (i*m) (j*m) | j <- [0 .. d-1] ] | i <- [0 .. d-1] ])
  OnVis -> Just (OnVis, [ [ u a b | b <- [0 .. m-1] ] | a <- [0 .. m-1] ])
  where
    d = gateTmpDim g
    m = gateVisDim g
    u a b = gateMat g !! a !! b

-- Terms

type Name = String

-- | The term grammar:
--
-- > e ::= v
-- >     | <v1, v2>
-- >     | let t = new i0 in e
-- >     | let (t', v') = U(t, v) in e
-- >     | drop t ; e
data Term
  = Ret  Name                              -- ^ @v@
  | Pair Name Name                         -- ^ @\<v1, v2\>@
  | New  Name Int Int Term                 -- ^ @let t = new_{i0} in e@: name, dimension, @i0@, body
  | Act  (Name, Name) Gate (Name, Name) Term
      -- ^ @let (t', v') = U(t, v) in e@: outputs, gate, inputs, body
  | Drop Name Term                         -- ^ @drop t ; e@: @vis[m]@ only
      -- promises the temporary was weakened away; "DQT.Calculus.Elaborate" checks the
      -- promise, exactly when the retained factor is constant.

-- | A closed program: one visible register in, one visible register out, and a
-- term that must be a single @New@ whose body allocates nothing further.
data Program = Program
  { progLabel  :: String
  , progVis    :: Name
  , progVisDim :: Int
  , progTerm   :: Term
  }

-- AllocFree

-- | @allocFree e@: the premise of the @New@ rule, by structural
-- recursion on the term and nothing more.
--
-- Reads "@e@ contains no @new@": a typed program has exactly one
-- temporary scope, the outermost @New@ forced by the program judgement.
-- "DQT.Many.Multi" lifts this restriction by composition.
allocFree :: Term -> Bool
allocFree (Ret _)        = True
allocFree (Pair _ _)     = True
allocFree (New _ _ _ _)  = False
allocFree (Act _ _ _ e)  = allocFree e
allocFree (Drop _ e)     = allocFree e

-- Occurrences

-- | Names occurring free in a term.
freeNames :: Term -> [Name]
freeNames = nub . go
  where
    go (Ret v)                 = [v]
    go (Pair a b)              = [a, b]
    go (New t _ _ e)           = filter (/= t) (go e)
    go (Act (t',v') _ (t,v) e) = [t, v] ++ filter (`notElem` [t', v']) (go e)
    go (Drop t e)              = t : go e

-- | Every name dropped in a term, in source order.
dropsIn :: Term -> [Name]
dropsIn (Ret _)       = []
dropsIn (Pair _ _)    = []
dropsIn (New _ _ _ e) = dropsIn e
dropsIn (Act _ _ _ e) = dropsIn e
dropsIn (Drop t e)    = t : dropsIn e

-- | Every gate applied in a term, in source order.
gatesIn :: Term -> [Gate]
gatesIn (Ret _)        = []
gatesIn (Pair _ _)     = []
gatesIn (New _ _ _ e)  = gatesIn e
gatesIn (Act _ g _ e)  = g : gatesIn e
gatesIn (Drop _ e)     = gatesIn e

-- Printing

-- | The term in concrete syntax, one binder per line.
pretty :: Term -> String
pretty = unlines . go 0
  where
    ind n s = replicate (2*n) ' ' ++ s
    go n (Ret v)    = [ind n v]
    go n (Pair a b) = [ind n ("<" ++ a ++ ", " ++ b ++ ">")]
    go n (New t d i0 e) =
      ind n ("let " ++ t ++ " = new |" ++ show i0 ++ ">"
             ++ "  -- tmp[" ++ show d ++ "]")
      : ind n "in" : go (n+1) e
    go n (Act (t',v') g (t,v) e) =
      ind n ("let (" ++ t' ++ ", " ++ v' ++ ") = "
             ++ gateLabel g ++ "(" ++ t ++ ", " ++ v ++ ") in")
      : go n e
    go n (Drop t e) = ind n ("drop " ++ t ++ ";") : go n e

prettyProgram :: Program -> String
prettyProgram p =
  "-- " ++ progLabel p ++ "\n"
  ++ progVis p ++ " : vis[" ++ show (progVisDim p) ++ "]  |-  \n"
  ++ pretty (progTerm p)

-- | The sugared printing used in the example tables, where the /shape/
-- of a program becomes visible.
--
-- @R (x) I@ prints as @t := R t@; @I (x) W@ as @v := W v@; anything else
-- as a joint gate, the only kind that can correlate the two registers:
-- @sep(R, W)@ reads as /prepare the temporary once, touch the rest/.
prettySugared :: Program -> String
prettySugared p = "-- " ++ progLabel p ++ "\n" ++ unlines (go (progTerm p))
  where
    go (Ret v)    = ["  return " ++ v]
    go (Pair a b) = ["  return <" ++ a ++ ", " ++ b ++ ">"]
    go (New t _ i0 e) = ("let " ++ t ++ " = new |" ++ show i0 ++ "> in") : go e
    go (Act (t',v') g (t,v) e) = ("  " ++ line) : go e
      where
        line = case gateKind g of
          OnTmp -> t' ++ " := " ++ gateLabel g ++ " " ++ t ++ carry v' v
          OnVis -> v' ++ " := " ++ gateLabel g ++ " " ++ v ++ carry t' t
          Joint -> "(" ++ t' ++ ", " ++ v' ++ ") := "
                   ++ gateLabel g ++ "(" ++ t ++ ", " ++ v ++ ")"
        carry new old' = if new == old' then "" else ";  " ++ new ++ " := " ++ old'
    go (Drop t e) = ("  drop " ++ t ++ ";") : go e
