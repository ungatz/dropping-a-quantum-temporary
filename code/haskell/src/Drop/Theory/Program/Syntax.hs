-- Drop.Theory.Program.Syntax: the terms of the measurement-free calculus, and how they print.
--
-- Question: What is a program of the matrix checker, and how is it written down?
-- Answer:   A term is built from five forms: Ret returns a register, Pair returns two, New
--           allocates a temporary in a basis state, Act applies a gate to a temporary and a visible
--           register, and Drop removes the temporary's name. A Gate is a matrix with a label and a
--           kind that records how it was declared (OnTmp for R (x) I, OnVis for I (x) W, Joint for
--           the rest), because the shape sep(R, W) of the criterion is a statement about how
--           gates were written, not about their matrices. Whether a term is well typed is
--           decided in Drop.Theory.Program.Typing, so an ill-typed term can be built and then
--           refused. This module also has the allocation-free test, the names a term uses, drops
--           and gates, and two printers (pretty, and prettySugared for the shape of a program).
-- Paper:    sec:lang:syntax (the grammar), fig:syntax.
-- Shapes:   RegTy     Tmp d, a temporary of dimension d; Vis m, a visible register of dimension m.
--           Ty        a register type, or a pair of types.
--           GateKind  OnTmp, OnVis or Joint.
--           Gate      a label, a kind, the two dimensions and the matrix, temporary most significant.
--           Term      Ret, Pair, New, Act or Drop, each ending in the rest of the term.
--           Program   a label, the visible register's name and dimension, and a term.

module Drop.Theory.Program.Syntax
  ( -- * Types
    RegTy(..), Ty(..)
  , regDim, tyDim
    -- * Gates
  , Gate(..), GateKind(..)
  , onTmp, onVis, joint, gateDim
    -- * Terms
  , Name
  , Term(..)
  , Program(..)
    -- * The allocation-free predicate, by structural recursion
  , allocFree
    -- * Occurrences
  , gatesIn
    -- * Printing
  , pretty, prettySugared
  ) where

import Drop.Theory.Algebra.Linear

-- Types

-- | Register types.  @Tmp d@ is a @d@-dimensional temporary; @Vis m@ an
-- @m@-dimensional visible register.  Both are finite registers; the
-- distinction is a discipline: only a @Tmp@ can be the subject of a @drop@.
data RegTy = Tmp Int | Vis Int
  deriving (Eq)

-- A temporary and a visible register print as tmp[d] and vis[m].
-- >>> [Tmp 2, Vis 3]
-- [tmp[2],vis[3]]
-- >>> Tmp 2 == Vis 2
-- False

instance Show RegTy where
  show (Tmp d) = "tmp[" ++ show d ++ "]"
  show (Vis m) = "vis[" ++ show m ++ "]"

-- >>> show (Tmp 2)
-- "tmp[2]"
-- >>> show (Vis 3)
-- "vis[3]"

-- | Value types: @A, B ::= Q | A (x) B@.
data Ty = TyReg RegTy | TyPair Ty Ty
  deriving (Eq)

-- A type is a register type or a pair of types.
-- >>> TyReg (Tmp 2)
-- tmp[2]
-- >>> TyPair (TyReg (Vis 2)) (TyPair (TyReg (Tmp 2)) (TyReg (Vis 3)))
-- (vis[2] (x) (tmp[2] (x) vis[3]))

instance Show Ty where
  show (TyReg q)    = show q
  show (TyPair a b) = "(" ++ show a ++ " (x) " ++ show b ++ ")"

-- >>> show (TyPair (TyReg (Tmp 2)) (TyReg (Vis 3)))
-- "(tmp[2] (x) vis[3])"

regDim :: RegTy -> Int
regDim (Tmp d) = d
regDim (Vis m) = m

-- >>> regDim (Tmp 2)
-- 2
-- >>> regDim (Vis 5)
-- 5

tyDim :: Ty -> Int
tyDim (TyReg q)    = regDim q
tyDim (TyPair a b) = tyDim a * tyDim b

-- >>> tyDim (TyReg (Vis 3))
-- 3
-- >>> tyDim (TyPair (TyReg (Tmp 2)) (TyReg (Vis 3)))
-- 6

-- Gates

-- | Which register a gate was /declared/ to touch: a syntactic label
-- rather than a semantic test. The identity is simultaneously @I (x) I@,
-- so asking the matrix "is this a product?" is ambiguous while asking
-- the program text "how was this gate written?" is not. @sep(R,W)@ is a
-- statement about how gates were written.
data GateKind = OnTmp | OnVis | Joint
  deriving (Eq, Show)

-- A gate carries its label, its kind, its two dimensions and its matrix.
-- >>> :m + Drop.Theory.Program.Gates
-- >>> gHt 2
-- H
-- >>> (gateKind (gHt 2), gateTmpDim (gHt 2), gateVisDim (gHt 2))
-- (OnTmp,2,2)
-- >>> gateMat (gHt 2)
-- [[sqrt2/2,0,sqrt2/2,0],[0,sqrt2/2,0,sqrt2/2],[sqrt2/2,0,-sqrt2/2,0],[0,sqrt2/2,0,-sqrt2/2]]

-- >>> [OnTmp, OnVis, Joint]
-- [OnTmp,OnVis,Joint]
-- >>> OnTmp == Joint
-- False

-- | A gate of the calculus: a named unitary on @H_d (x) H_m@, temporary factor
-- first.  The @Gate@ typing rule's premise @U^dagger U = U U^dagger = I@ is
-- checked in "Drop.Theory.Program.Typing", not here, so that an ill-typed program can still be
-- built and then rejected.
data Gate = Gate
  { gateLabel  :: String    -- ^ how it prints
  , gateKind   :: GateKind
  , gateTmpDim :: Int
  , gateVisDim :: Int
  , gateMat    :: Mat       -- ^ on @H_{tmpDim} (x) H_{visDim}@, temporary most significant
  }

instance Show Gate where show = gateLabel

-- A gate prints as its label.
-- >>> show (gHt 2)
-- "H"
-- >>> show (gRead 2)
-- "READ"

gateDim :: Gate -> Int
gateDim g = gateTmpDim g * gateVisDim g

-- >>> gateDim (gHt 2)
-- 4
-- >>> gateDim (gRead 3)
-- 9

-- | @onTmp name r m@ is @R (x) I_m@: a gate that touches only the temporary.
onTmp :: String -> Mat -> Int -> Gate
onTmp nm r m = Gate nm OnTmp (matRows r) m (kron r (matId m))

-- onTmp "X" r m is X on the temporary and the identity on a visible register of dimension m.
-- >>> gateKind (onTmp "X" mX 2)
-- OnTmp
-- >>> gateMat (onTmp "X" mX 1)
-- [[0,1],[1,0]]
-- >>> gateMat (onTmp "X" mX 2) == kron mX (matId 2)
-- True

-- | @onVis name d w@ is @I_d (x) W@: a gate that touches only the visible
-- register.  These two constructors are exactly the two holes of the shape
-- @sep(R, W)@ that "Drop.Theory.Criterion.Witness" fills.
onVis :: String -> Int -> Mat -> Gate
onVis nm d w = Gate nm OnVis d (matRows w) (kron (matId d) w)

-- >>> gateKind (onVis "X" 2 mX)
-- OnVis
-- >>> gateMat (onVis "X" 2 mX) == kron (matId 2) mX
-- True

-- | A genuinely joint gate: the general case, and the only one that can
-- correlate the two registers.
joint :: String -> Int -> Int -> Mat -> Gate
joint nm = Gate nm Joint

-- A joint gate is any matrix; the controlled not is one.
-- >>> gateKind (joint "cx" 2 2 mCX)
-- Joint
-- >>> gateMat (joint "cx" 2 2 mCX)
-- [[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]]

-- Terms

type Name = String

-- >>> "t1" :: Name
-- "t1"

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
  | Drop Name Term                         -- ^ @drop t ; e@: removes the temporary @t@ from the context;
      -- "Drop.Theory.Program.Elaborate" keeps its dimension in front of the result.

-- A term that spreads the temporary with H and drops it (a Term has no Show instance; pretty prints it).
-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> let spread = New "t" 2 0 (Act ("t1", "v1") (gHt 2) ("t", "v") (Drop "t1" (Ret "v1")))
-- >>> mapM_ print (lines (pretty spread))
-- "let t = new |0>  -- tmp[2]"
-- "in"
-- "  let (t1, v1) = H(t, v) in"
-- "  drop t1;"
-- "  v1"
-- >>> mapM_ print (lines (pretty (Pair "a" "b")))
-- "<a, b>"

-- | A closed program: one visible register in, one visible register out, and a
-- term that must be a single @New@ whose body allocates nothing further.
data Program = Program
  { progLabel  :: String
  , progVis    :: Name
  , progVisDim :: Int
  , progTerm   :: Term
  }

-- A program names its visible register and gives its dimension.
-- >>> let prog = Program "spread, then drop" "v" 2 spread
-- >>> (progLabel prog, progVis prog, progVisDim prog)
-- ("spread, then drop","v",2)
-- >>> mapM_ print (lines (pretty (progTerm spreadAndPark)))
-- "let t = new |0>  -- tmp[2]"
-- "in"
-- "  let (t1, v1) = H(t, v) in"
-- "  drop t1;"
-- "  v1"

-- AllocFree

-- | @allocFree e@: the premise of the @New@ rule, by structural
-- recursion on the term and nothing more.
--
-- Reads "@e@ contains no @new@": a typed program has exactly one
-- temporary scope, the outermost @New@ forced by the program judgement.
-- "Drop.Theory.Many.Multi" lifts this restriction by composition.
allocFree :: Term -> Bool
allocFree (Ret _)        = True
allocFree (Pair _ _)     = True
allocFree (New _ _ _ _)  = False
allocFree (Act _ _ _ e)  = allocFree e
allocFree (Drop _ e)     = allocFree e

-- A second new in the body is what the New rule refuses.
-- >>> allocFree (Ret "v")
-- True
-- >>> allocFree spread
-- False
-- >>> allocFree (progTerm spreadAndRead)
-- False
-- >>> allocFree (Act ("t2", "v2") (gHt 2) ("t", "v") spread)
-- False

-- Occurrences

-- | Every gate applied in a term, in source order.
gatesIn :: Term -> [Gate]
gatesIn (Ret _)        = []
gatesIn (Pair _ _)     = []
gatesIn (New _ _ _ e)  = gatesIn e
gatesIn (Act _ g _ e)  = g : gatesIn e
gatesIn (Drop _ e)     = gatesIn e

-- >>> gatesIn spread
-- [H]
-- >>> gatesIn (progTerm spreadAndRead)
-- [H,READ]
-- >>> gatesIn (Ret "v")
-- []

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

-- One binder to a line; each line is shown with quotes so its indentation stays.
-- >>> mapM_ print (lines (pretty (progTerm spreadAndRead)))
-- "let t = new |0>  -- tmp[2]"
-- "in"
-- "  let (t1, v1) = H(t, v) in"
-- "  let (t2, v2) = READ(t1, v1) in"
-- "  drop t2;"
-- "  v2"

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

-- R (x) I prints as t := R t, I (x) W as v := W v, and a joint gate in full.
-- >>> mapM_ print (lines (prettySugared (Program "x" "v" 2 (New "t" 2 0 (Act ("t1", "v1") (gHt 2) ("t", "v") (Act ("t2", "v2") (gRead 2) ("t1", "v1") (Drop "t2" (Ret "v2"))))))))
-- "-- x"
-- "let t = new |0> in"
-- "  t1 := H t;  v1 := v"
-- "  (t2, v2) := READ(t1, v1)"
-- "  drop t2;"
-- "  return v2"
-- >>> mapM_ print (lines (prettySugared sepHX))
-- "-- sep(H, X): literally of the separable shape"
-- "let t = new |0> in"
-- "  t1 := H t;  v1 := v"
-- "  v2 := X v1;  t2 := t1"
-- "  drop t2;"
-- "  return v2"
