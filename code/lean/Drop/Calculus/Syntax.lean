import Drop.Source.Reflection

set_option autoImplicit false

/-!
# the syntax of the affine weakening calculus, and its elaboration

This file writes down the smallest source language in which the sentence
"the temporary may be dropped" is a typing* sentence — values, `let`, one scoped temporary,
and an unrestricted affine `drop` — and elaborates it into the shipped `Body` core, so that
every later claim is a claim about a program of a language with binders, not about a matrix.*

## The grammar

```
A, B ::= tmp | vis | A ⊗ B                          types
t    ::= x                                          value: a variable
       | ⟨x, y⟩                                     value: a pair
       | let a = new i₀ in t                        the scoped temporary
       | let (a', v') = U (a, v) in t               one joint gate, consuming and rebinding
       | drop a ; t                                 affine weakening
```

Nothing else.  There is no gate that is not a `let`-bound joint unitary, no measurement, no
second wire, no recursion, and no arrow type — each omission is deliberate, keeping the
calculus to exactly the fragment developed here.  A visible-only gate is derived syntax
(`letVis` below), not a primitive.

Contexts are finite partial maps `Var → Option Ty`, so the exchange rule is invisible (contexts
are unordered by construction) and the *only* structural rule the calculus has is the one under
study: `drop`.  There is no implicit weakening — the rule for a variable demands that the
context be exactly that variable — and there is no contraction, since no rule ever uses a
variable twice.

## Elaboration

`elabBody` erases every binder and keeps the gates, in order.  This is the typed map from the
calculus to bodies, and it is total on raw syntax; `Calculus/Typing.lean` proves it takes typing derivations
to `Body.WellTyped`, and `Calculus/Machine.lean` proves it computes the same state as the
operational semantics.
-/

namespace Calculus

open SourceLanguage Circuit SimpleTensor Matrix

/-! ### Variables, types, contexts -/

/-- Source variables. -/
abbrev Var := ℕ

/-- The types: the temporary, the visible register, and their pair. -/
inductive Ty where
  | tmp : Ty
  | vis : Ty
  | tensor : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- A typing context: a partial map from variables to types.  Unordered by construction, so
exchange is not a rule. -/
abbrev Ctx := Var → Option Ty

namespace Ctx

/-- The empty context. -/
def empty : Ctx := fun _ => none

/-- The one-variable context. -/
def single (x : Var) (A : Ty) : Ctx := fun y => if y = x then some A else none

/-- Extend a context. -/
def insert (Γ : Ctx) (x : Var) (A : Ty) : Ctx := fun y => if y = x then some A else Γ y

/-- Remove a variable from a context. -/
def erase (Γ : Ctx) (x : Var) : Ctx := fun y => if y = x then none else Γ y

@[simp] lemma empty_apply (y : Var) : empty y = none := rfl

@[simp] lemma single_self (x : Var) (A : Ty) : single x A x = some A := by simp [single]

lemma single_apply_of_ne {x y : Var} (A : Ty) (h : y ≠ x) : single x A y = none := by
  simp [single, h]

@[simp] lemma insert_self (Γ : Ctx) (x : Var) (A : Ty) : (Γ.insert x A) x = some A := by
  simp [insert]

lemma insert_apply_of_ne (Γ : Ctx) {x y : Var} (A : Ty) (h : y ≠ x) :
    (Γ.insert x A) y = Γ y := by simp [insert, h]

@[simp] lemma erase_self (Γ : Ctx) (x : Var) : (Γ.erase x) x = none := by simp [erase]

lemma erase_apply_of_ne (Γ : Ctx) {x y : Var} (h : y ≠ x) : (Γ.erase x) y = Γ y := by
  simp [erase, h]

end Ctx

/-- *No temporary is live in `Γ`*: the side condition of the allocation rule, which is what
makes the temporary scoped and the wire unique. -/
def NoTmp (Γ : Ctx) : Prop := ∀ x, Γ x ≠ some Ty.tmp

lemma noTmp_single_vis (v : Var) : NoTmp (Ctx.single v Ty.vis) := by
  intro x hx
  by_cases h : x = v <;> simp [Ctx.single, h] at hx

/-! ### Terms -/

/-- The terms of the affine weakening calculus. -/
inductive Tm (ι μ : Type*) where
  /-- a variable, the only value of ground type -/
  | ret : Var → Tm ι μ
  /-- the pair value -/
  | pair : Var → Var → Tm ι μ
  /-- `let a = new i₀ in t`: the scoped temporary, allocated in the basis state `i₀` -/
  | letNew : ι → Var → Tm ι μ → Tm ι μ
  /-- `let (a', v') = U (a, v) in t`: one joint gate, consuming `a, v` and rebinding `a', v'` -/
  | letGate : Matrix (ι × μ) (ι × μ) ℝ → Var → Var → Var → Var → Tm ι μ → Tm ι μ
  /-- `drop a ; t`: affine weakening of the temporary -/
  | drop : Var → Tm ι μ → Tm ι μ

variable {ι μ : Type*}

/-- *`t` allocates no temporary*: the premise of the allocation rule, which forbids a second
scope and so keeps the elaboration faithful. -/
inductive AllocFree : Tm ι μ → Prop
  | ret (x : Var) : AllocFree (.ret x)
  | pair (x y : Var) : AllocFree (.pair x y)
  | letGate (U : Matrix (ι × μ) (ι × μ) ℝ) (a v a' v' : Var) {t : Tm ι μ} :
      AllocFree t → AllocFree (.letGate U a v a' v' t)
  | drop (a : Var) {t : Tm ι μ} : AllocFree t → AllocFree (.drop a t)

/-! ### Elaboration into the shipped core -/

/-- The elaboration.  Erase the binders, keep the gates in order.  The map respects typing:
`Calculus.elabBody_wellTyped` sends a typing derivation to `Body.WellTyped`. -/
def elabBody : Tm ι μ → Body ℝ ι μ
  | .ret _ => .halt
  | .pair _ _ => .halt
  | .letNew _ _ t => elabBody t
  | .letGate U _ _ _ _ t => .gate U (elabBody t)
  | .drop _ t => elabBody t

@[simp] lemma elabBody_ret (x : Var) : elabBody (.ret x : Tm ι μ) = .halt := rfl

@[simp] lemma elabBody_pair (x y : Var) : elabBody (.pair x y : Tm ι μ) = .halt := rfl

@[simp] lemma elabBody_letNew (i₀ : ι) (a : Var) (t : Tm ι μ) :
    elabBody (.letNew i₀ a t) = elabBody t := rfl

@[simp] lemma elabBody_letGate (U : Matrix (ι × μ) (ι × μ) ℝ) (a v a' v' : Var) (t : Tm ι μ) :
    elabBody (.letGate U a v a' v' t) = .gate U (elabBody t) := rfl

@[simp] lemma elabBody_drop (a : Var) (t : Tm ι μ) :
    elabBody (.drop a t) = elabBody t := rfl

/-! ### Programs -/

/-- A program: an allocation point, the temporary's name, the input's name, and a body.
Its term is `let a = new i₀ in body`, and it is read as a function of the visible input. -/
structure Prog (ι μ : Type*) where
  /-- the basis state the temporary is allocated in -/
  init : ι
  /-- the name of the temporary -/
  scope : Var
  /-- the name of the visible input -/
  input : Var
  /-- the body, run with the temporary in scope -/
  body : Tm ι μ

/-- The term of a program. -/
def Prog.tm (P : Prog ι μ) : Tm ι μ := .letNew P.init P.scope P.body

section Registers

variable [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-- Derived syntax: a visible-only gate.  `let v' = W v in t` is the joint gate `1 ⊗ W`,
which by construction never touches the temporary. -/
noncomputable def Tm.letVis (W : Matrix μ μ ℝ) (v v' : Var) (a : Var) (t : Tm ι μ) : Tm ι μ :=
  .letGate (localGate 1 W) a v a v' t

/-- Derived syntax: a temporary-only gate. -/
noncomputable def Tm.letTmp (R : Matrix ι ι ℝ) (a a' : Var) (v : Var) (t : Tm ι μ) : Tm ι μ :=
  .letGate (localGate R 1) a v a' v t

/-- The denotation of a program: the shipped denotation of its elaborated body at its
allocation point. -/
noncomputable def Prog.denote (P : Prog ι μ) (v : EuclideanSpace ℝ μ) :
    EuclideanSpace ℝ (ι × μ) :=
  SourceLanguage.denote P.init (elabBody P.body) v

lemma Prog.denote_def (P : Prog ι μ) (v : EuclideanSpace ℝ μ) :
    P.denote v = SourceLanguage.denote P.init (elabBody P.body) v := rfl

end Registers

end Calculus
