import Drop.Calculus.Syntax

set_option autoImplicit false

/-!
# the typing judgment, and type preservation under elaboration

The judgment `Γ ⊢ t : A` is affine — no implicit weakening, no contraction,
one live temporary — and it is a typed* elaboration: every derivation produces a
`Body.WellTyped` core program, so the isometry hypothesis of `Drop/Source/Language.lean` is
discharged by the type system rather than assumed.*

## The rules

```
─────────────────────────  var                  ────────────────────────────── pair (x ≠ y)
 x : A ⊢ x : A                                   x : A, y : B ⊢ ⟨x,y⟩ : A ⊗ B

 Γ(a) undefined    no tmp live in Γ    t allocates nothing    Γ, a : tmp ⊢ t : C
────────────────────────────────────────────────────────────────────────────────── new
 Γ ⊢ let a = new i₀ in t : C

 Uᴴ U = 1   a ≠ v   a' ≠ v'   Γ(a) = tmp   Γ(v) = vis   Γ∖{a,v}, a' : tmp, v' : vis ⊢ t : C
──────────────────────────────────────────────────────────────────────────────────────── gate
 Γ ⊢ let (a',v') = U (a,v) in t : C

 Γ(a) = tmp     Γ ∖ {a} ⊢ t : C
─────────────────────────────────  drop
 Γ ⊢ drop a ; t : C
```

The `drop` rule has no side condition.  That is deliberate and is the whole point: the
rule is unconditionally derivable, and `Calculus/Reflection.lean` decides exactly when
it is *semantically admissible*.

Two consequences are proved here.

* `elabBody_wellTyped` — type preservation under elaboration: a derivation elaborates to a
  well-typed body.  The only typing premise it consumes is the unitarity carried by `gate`.
* `Prog.Typed` — a program is typed when `input : vis ⊢ let a = new i₀ in body : vis`.  Its
  result type is `vis`, not `tmp ⊗ vis`: *the type records that the temporary was weakened away.*
-/

namespace Calculus

open SourceLanguage Circuit SimpleTensor Matrix

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-! ### The judgment -/

/-- The affine typing judgment. -/
inductive HasTy : Ctx → Tm ι μ → Ty → Prop
  | ret {Γ : Ctx} {x : Var} {A : Ty} (hΓ : Γ = Ctx.single x A) : HasTy Γ (.ret x) A
  | pair {Γ : Ctx} {x y : Var} {A B : Ty} (hxy : x ≠ y)
      (hΓ : Γ = (Ctx.single x A).insert y B) : HasTy Γ (.pair x y) (Ty.tensor A B)
  | new {Γ : Ctx} {i₀ : ι} {a : Var} {t : Tm ι μ} {C : Ty}
      (hfresh : Γ a = none) (hno : NoTmp Γ) (hfree : AllocFree t)
      (ht : HasTy (Γ.insert a Ty.tmp) t C) : HasTy Γ (.letNew i₀ a t) C
  | gate {Γ : Ctx} {U : Matrix (ι × μ) (ι × μ) ℝ} {a v a' v' : Var} {t : Tm ι μ} {C : Ty}
      (hU : Uᴴ * U = 1) (hav : a ≠ v) (hav' : a' ≠ v')
      (ha : Γ a = some Ty.tmp) (hv : Γ v = some Ty.vis)
      (ht : HasTy ((((Γ.erase a).erase v).insert a' Ty.tmp).insert v' Ty.vis) t C) :
      HasTy Γ (.letGate U a v a' v' t) C
  | drop {Γ : Ctx} {a : Var} {t : Tm ι μ} {C : Ty}
      (ha : Γ a = some Ty.tmp) (ht : HasTy (Γ.erase a) t C) :
      HasTy Γ (.drop a t) C

/-! ### Derived rules for the two derived gate forms -/

/-- The derived rule for a visible-only gate. -/
lemma HasTy.letVis {Γ : Ctx} {W : Matrix μ μ ℝ} {a v v' : Var} {t : Tm ι μ} {C : Ty}
    (hW : Wᴴ * W = 1) (hav : a ≠ v) (hav' : a ≠ v')
    (ha : Γ a = some Ty.tmp) (hv : Γ v = some Ty.vis)
    (ht : HasTy ((((Γ.erase a).erase v).insert a Ty.tmp).insert v' Ty.vis) t C) :
    HasTy Γ (Tm.letVis W v v' a t) C :=
  .gate (localGate_unitary (by simp) hW) hav hav' ha hv ht

/-- The derived rule for a temporary-only gate. -/
lemma HasTy.letTmp {Γ : Ctx} {R : Matrix ι ι ℝ} {a a' v : Var} {t : Tm ι μ} {C : Ty}
    (hR : Rᴴ * R = 1) (hav : a ≠ v) (hav' : a' ≠ v)
    (ha : Γ a = some Ty.tmp) (hv : Γ v = some Ty.vis)
    (ht : HasTy ((((Γ.erase a).erase v).insert a' Ty.tmp).insert v Ty.vis) t C) :
    HasTy Γ (Tm.letTmp R a a' v t) C :=
  .gate (localGate_unitary hR (by simp)) hav hav' ha hv ht

/-! ### Type preservation under elaboration -/

/-- Type preservation, elaboration form.  A typing derivation elaborates to a well-typed
body of the shipped core: every gate of the elaboration is unitary. -/
theorem elabBody_wellTyped {Γ : Ctx} {t : Tm ι μ} {C : Ty} (h : HasTy Γ t C) :
    (elabBody t).WellTyped := by
  induction h with
  | ret => exact .halt
  | pair => exact .halt
  | new _ _ _ _ ih => exact ih
  | gate hU _ _ _ _ _ ih => exact .gate hU ih
  | drop _ _ ih => exact ih

/-- A typed term allocates at most the temporaries its `new` rules mention: the body of a `new`
is allocation-free, so a typed program has exactly one temporary scope. -/
theorem allocFree_of_new {Γ : Ctx} {i₀ : ι} {a : Var} {t : Tm ι μ} {C : Ty}
    (h : HasTy Γ (.letNew i₀ a t) C) : AllocFree t := by
  cases h with
  | new _ _ hfree _ => exact hfree

/-! ### Typed programs -/

/-- A typed program: with the visible input in scope, `let a = new i₀ in body` has type
`vis`.  The result type is the point: the temporary has been weakened away. -/
def Prog.Typed (P : Prog ι μ) : Prop :=
  HasTy (Ctx.single P.input Ty.vis) P.tm Ty.vis

/-- In a typed program the temporary and the input are different variables. -/
theorem Prog.scope_ne_input {P : Prog ι μ} (hP : P.Typed) : P.scope ≠ P.input := by
  have h : HasTy (Ctx.single P.input Ty.vis) (Tm.letNew P.init P.scope P.body) Ty.vis := hP
  cases h with
  | new hfresh _ _ _ =>
    intro hcon
    rw [hcon] at hfresh
    simp [Ctx.single] at hfresh

/-- A typed program allocates exactly one temporary. -/
theorem Prog.allocFree_body {P : Prog ι μ} (hP : P.Typed) : AllocFree P.body :=
  allocFree_of_new hP

/-- The body of a typed program is typed with the temporary in scope. -/
theorem Prog.body_hasTy {P : Prog ι μ} (hP : P.Typed) :
    HasTy ((Ctx.single P.input Ty.vis).insert P.scope Ty.tmp) P.body Ty.vis := by
  have h : HasTy (Ctx.single P.input Ty.vis) (Tm.letNew P.init P.scope P.body) Ty.vis := hP
  cases h with
  | new _ _ _ ht => exact ht

/-- The elaboration of a typed program is a well-typed core program. -/
theorem Prog.elab_wellTyped {P : Prog ι μ} (hP : P.Typed) : (elabBody P.body).WellTyped :=
  elabBody_wellTyped (P.body_hasTy hP)

/-- A typed program denotes an isometry — the hypothesis of `Drop/Source/Language.lean`,
discharged by the type system. -/
theorem Prog.norm_denote {P : Prog ι μ} (hP : P.Typed) (v : EuclideanSpace ℝ μ) :
    ‖P.denote v‖ = ‖v‖ :=
  SourceLanguage.norm_denote (P.elab_wellTyped hP) v

end Calculus
