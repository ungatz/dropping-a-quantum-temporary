import Drop.Calculus.Typing

set_option autoImplicit false

/-!
# the operational semantics, type preservation, progress, adequacy

The calculus runs on a two-wire machine — a joint state vector and a term —
and the three theorems a source language owes are proved: a step preserves the judgment and the
machine shape, a well-formed non-value steps, and running a program to a value produces exactly
the state its elaboration denotes.

## The machine

A configuration is a joint state `x : TEMPORARY ⊗ VISIBLE` together with the term still to run.
There are exactly two rules.

```
⟨x, let (a',v') = U (a,v) in t⟩  ⟶  ⟨U x, t⟩
⟨x, drop a ; t⟩                  ⟶  ⟨x, t⟩
```

`drop` costs nothing at run time: the machine cannot tell whether the temporary was dropped.
That is exactly why its admissibility is not an operational property, and why the criterion of
`Calculus/Reflection.lean` is denotational.  Allocation is not a machine step: it is how the
initial configuration of a program is built (`Prog.initConfig`).

## The invariant

`MachineCtx Γ` says at most one temporary and at most one visible variable are live — the
machine has two wires and no aliasing.  Preservation carries it.
-/

namespace Calculus

open SourceLanguage Circuit SimpleTensor Matrix

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-! ### Configurations and steps -/

/-- A machine configuration: the joint state and the term still to run. -/
structure Config (ι μ : Type*) [Fintype ι] [Fintype μ] where
  /-- the joint TEMPORARY ⊗ VISIBLE state -/
  state : EuclideanSpace ℝ (ι × μ)
  /-- the term still to run -/
  term : Tm ι μ

/-- The values: a variable and a pair of variables. -/
inductive Value : Tm ι μ → Prop
  | ret (x : Var) : Value (.ret x)
  | pair (x y : Var) : Value (.pair x y)

/-- The small-step semantics.  A gate moves the joint state; a drop moves nothing. -/
inductive Step : Config ι μ → Config ι μ → Prop
  | gate (x : EuclideanSpace ℝ (ι × μ)) (U : Matrix (ι × μ) (ι × μ) ℝ) (a v a' v' : Var)
      (t : Tm ι μ) : Step ⟨x, .letGate U a v a' v' t⟩ ⟨actJoint U x, t⟩
  | drop (x : EuclideanSpace ℝ (ι × μ)) (a : Var) (t : Tm ι μ) :
      Step ⟨x, .drop a t⟩ ⟨x, t⟩

/-- Many steps. -/
def Steps (c c' : Config ι μ) : Prop := Relation.ReflTransGen Step c c'

omit [DecidableEq ι] [DecidableEq μ] in
lemma Steps.refl (c : Config ι μ) : Steps c c := Relation.ReflTransGen.refl

omit [DecidableEq ι] [DecidableEq μ] in
lemma Steps.head {c c' c'' : Config ι μ} (h : Step c c') (h' : Steps c' c'') : Steps c c'' :=
  Relation.ReflTransGen.head h h'

/-! ### The machine shape of a context -/

/-- *At most one temporary and at most one visible variable are live.*  The machine has two
wires, and this is the invariant saying the context describes them. -/
def MachineCtx (Γ : Ctx) : Prop :=
  (∀ x y, Γ x = some Ty.tmp → Γ y = some Ty.tmp → x = y) ∧
  (∀ x y, Γ x = some Ty.vis → Γ y = some Ty.vis → x = y)

lemma machineCtx_single_vis (v : Var) : MachineCtx (Ctx.single v Ty.vis) := by
  constructor
  · intro x y hx _
    by_cases h : x = v <;> simp [Ctx.single, h] at hx
  · intro x y hx hy
    by_cases hxv : x = v
    · by_cases hyv : y = v
      · rw [hxv, hyv]
      · simp [Ctx.single, hyv] at hy
    · simp [Ctx.single, hxv] at hx

lemma MachineCtx.insert_tmp {Γ : Ctx} (h : MachineCtx Γ) (hno : NoTmp Γ) (a : Var) :
    MachineCtx (Γ.insert a Ty.tmp) := by
  refine ⟨fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · have hx' : x = a := by
      by_cases hxa : x = a
      · exact hxa
      · rw [Ctx.insert_apply_of_ne _ _ hxa] at hx; exact absurd hx (hno x)
    have hy' : y = a := by
      by_cases hya : y = a
      · exact hya
      · rw [Ctx.insert_apply_of_ne _ _ hya] at hy; exact absurd hy (hno y)
    rw [hx', hy']
  · have hx' : x ≠ a := by rintro rfl; simp [Ctx.insert] at hx
    have hy' : y ≠ a := by rintro rfl; simp [Ctx.insert] at hy
    rw [Ctx.insert_apply_of_ne _ _ hx'] at hx
    rw [Ctx.insert_apply_of_ne _ _ hy'] at hy
    exact h.2 x y hx hy

lemma MachineCtx.erase {Γ : Ctx} (h : MachineCtx Γ) (a : Var) : MachineCtx (Γ.erase a) := by
  refine ⟨fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · have hx' : x ≠ a := by rintro rfl; simp at hx
    have hy' : y ≠ a := by rintro rfl; simp at hy
    rw [Ctx.erase_apply_of_ne _ hx'] at hx
    rw [Ctx.erase_apply_of_ne _ hy'] at hy
    exact h.1 x y hx hy
  · have hx' : x ≠ a := by rintro rfl; simp at hx
    have hy' : y ≠ a := by rintro rfl; simp at hy
    rw [Ctx.erase_apply_of_ne _ hx'] at hx
    rw [Ctx.erase_apply_of_ne _ hy'] at hy
    exact h.2 x y hx hy

/-- The context the `gate` rule hands to its continuation is again a machine context: the two
consumed names are erased, the two rebound names are the only live ones.  Write `E` for the
context with `a` and `v` erased.  Erasing leaves `E` with no live temporary or visible name at
all (the old ones are gone, and `MachineCtx Γ` rules out any other name sharing their type with
`a` or `v`), so after `E` is extended with the fresh names `a'` and `v'`, those two are the
*only* names of their type — which is exactly `MachineCtx` for the resulting context. -/
lemma MachineCtx.gate_step {Γ : Ctx} (h : MachineCtx Γ) {a v a' v' : Var}
    (ha : Γ a = some Ty.tmp) (hv : Γ v = some Ty.vis) :
    MachineCtx ((((Γ.erase a).erase v).insert a' Ty.tmp).insert v' Ty.vis) := by
  -- `a` and `v` are distinct: `Γ` cannot type one name as both temporary and visible.
  have hdistinct : a ≠ v := by rintro rfl; rw [ha] at hv; simp at hv
  set E : Ctx := (Γ.erase a).erase v with hE
  -- How lookup in `E` behaves: `a` and `v` are gone, every other name is unchanged.
  have herase_a : E a = none := by rw [hE, Ctx.erase_apply_of_ne _ hdistinct, Ctx.erase_self]
  have herase_v : E v = none := by rw [hE, Ctx.erase_self]
  have herase_agrees : ∀ x, x ≠ a → x ≠ v → E x = Γ x := by
    intro x hxa hxv
    rw [hE, Ctx.erase_apply_of_ne _ hxv, Ctx.erase_apply_of_ne _ hxa]
  -- Consequently `E` types no name as temporary or visible at all: any other candidate name
  -- would already have witnessed a second temporary (resp. visible) name in `Γ`, against `h`.
  have herased_not_tmp : ∀ x, E x = some Ty.tmp → False := by
    intro x hx
    by_cases hxv : x = v
    · rw [hxv, herase_v] at hx; simp at hx
    · by_cases hxa : x = a
      · rw [hxa, herase_a] at hx; simp at hx
      · rw [herase_agrees x hxa hxv] at hx
        exact hxa (h.1 x a hx ha)
  have herased_not_vis : ∀ x, E x = some Ty.vis → False := by
    intro x hx
    by_cases hxv : x = v
    · rw [hxv, herase_v] at hx; simp at hx
    · by_cases hxa : x = a
      · rw [hxa, herase_a] at hx; simp at hx
      · rw [herase_agrees x hxa hxv] at hx
        exact hxv (h.2 x v hx hv)
  -- With `E` clear of both types, inserting `a'` then `v'` makes each the unique name of its
  -- type: any name typed temporary (resp. visible) after both inserts must be `a'` (resp. `v'`).
  refine ⟨fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · have hnew_tmp_unique :
        ∀ z, ((E.insert a' Ty.tmp).insert v' Ty.vis) z = some Ty.tmp → z = a' := by
      intro z hz
      by_cases hzv' : z = v'
      · rw [hzv'] at hz; simp [Ctx.insert] at hz
      · rw [Ctx.insert_apply_of_ne _ _ hzv'] at hz
        by_cases hza' : z = a'
        · exact hza'
        · rw [Ctx.insert_apply_of_ne _ _ hza'] at hz
          exact absurd hz (fun hh => herased_not_tmp z hh)
    rw [hnew_tmp_unique x hx, hnew_tmp_unique y hy]
  · have hnew_vis_unique :
        ∀ z, ((E.insert a' Ty.tmp).insert v' Ty.vis) z = some Ty.vis → z = v' := by
      intro z hz
      by_cases hzv' : z = v'
      · exact hzv'
      · rw [Ctx.insert_apply_of_ne _ _ hzv'] at hz
        by_cases hza' : z = a'
        · rw [hza'] at hz; simp [Ctx.insert] at hz
        · rw [Ctx.insert_apply_of_ne _ _ hza'] at hz
          exact absurd hz (fun hh => herased_not_vis z hh)
    rw [hnew_vis_unique x hx, hnew_vis_unique y hy]

/-! ### Type preservation -/

/-- Type preservation, per rule: the gate step. -/
theorem preservation_gate {Γ : Ctx} {U : Matrix (ι × μ) (ι × μ) ℝ} {a v a' v' : Var}
    {t : Tm ι μ} {C : Ty} (ht : HasTy Γ (.letGate U a v a' v' t) C) :
    HasTy ((((Γ.erase a).erase v).insert a' Ty.tmp).insert v' Ty.vis) t C := by
  cases ht with
  | gate _ _ _ _ _ ht => exact ht

/-- Type preservation, per rule: the drop step. -/
theorem preservation_drop {Γ : Ctx} {a : Var} {t : Tm ι μ} {C : Ty}
    (ht : HasTy Γ (.drop a t) C) : HasTy (Γ.erase a) t C := by
  cases ht with
  | drop _ ht => exact ht

/-- Type preservation.  A step preserves the type and the machine shape of the context. -/
theorem preservation {Γ : Ctx} {C : Ty} {c c' : Config ι μ}
    (hM : MachineCtx Γ) (ht : HasTy Γ c.term C) (hs : Step c c') :
    ∃ Γ', MachineCtx Γ' ∧ HasTy Γ' c'.term C := by
  cases hs with
  | gate x U a v a' v' t =>
    refine ⟨(((Γ.erase a).erase v).insert a' Ty.tmp).insert v' Ty.vis, ?_, preservation_gate ht⟩
    cases ht with
    | gate _ _ _ ha hv _ => exact hM.gate_step ha hv
  | drop x a t => exact ⟨Γ.erase a, hM.erase a, preservation_drop ht⟩

/-! ### Progress

Progress needs no typing hypothesis in this calculus: allocation-free non-values are exactly the
two stepping forms.  That is a fact about the grammar, and it is recorded as such. -/

omit [DecidableEq ι] [DecidableEq μ] in
/-- Progress.  An allocation-free term that is not a value steps, from any state. -/
theorem progress {t : Tm ι μ} (hfree : AllocFree t) (hv : ¬ Value t)
    (x : EuclideanSpace ℝ (ι × μ)) : ∃ c' : Config ι μ, Step ⟨x, t⟩ c' := by
  cases hfree with
  | ret x' => exact absurd (Value.ret x') hv
  | pair x' y' => exact absurd (Value.pair x' y') hv
  | letGate U a v a' v' _ => exact ⟨_, Step.gate x U a v a' v' _⟩
  | drop a _ => exact ⟨_, Step.drop x a _⟩

/-! ### Adequacy: the machine computes the elaboration -/

/-- Adequacy of the elaboration.  An allocation-free term runs to a value, and the state it
reaches is exactly the state its elaborated body computes. -/
theorem run_to_value {t : Tm ι μ} (hfree : AllocFree t) (x : EuclideanSpace ℝ (ι × μ)) :
    ∃ w : Tm ι μ, Value w ∧ Steps ⟨x, t⟩ ⟨actJoint (elabBody t).run x, w⟩ := by
  induction hfree generalizing x with
  | ret x' =>
    refine ⟨.ret x', .ret x', ?_⟩
    simp only [elabBody_ret, Body.run, actJoint_one]
    exact Steps.refl _
  | pair x' y' =>
    refine ⟨.pair x' y', .pair x' y', ?_⟩
    simp only [elabBody_pair, Body.run, actJoint_one]
    exact Steps.refl _
  | letGate U a v a' v' _ ih =>
    obtain ⟨w, hw, hsteps⟩ := ih (actJoint U x)
    refine ⟨w, hw, Steps.head (Step.gate x U a v a' v' _) ?_⟩
    rwa [elabBody_letGate, Body.run, actJoint_mul]
  | drop a _ ih =>
    obtain ⟨w, hw, hsteps⟩ := ih x
    exact ⟨w, hw, Steps.head (Step.drop x a _) (by rwa [elabBody_drop])⟩

/-- The initial configuration of a program at a visible input: allocate, then run the body. -/
noncomputable def Prog.initConfig (P : Prog ι μ) (v : EuclideanSpace ℝ μ) : Config ι μ :=
  ⟨alloc P.init v, P.body⟩

/-- Adequacy, for a typed program.  Running a typed program on the machine terminates in a
value, and the final joint state is the program's denotation. -/
theorem Prog.run_denote {P : Prog ι μ} (hP : P.Typed) (v : EuclideanSpace ℝ μ) :
    ∃ w : Tm ι μ, Value w ∧ Steps (P.initConfig v) ⟨P.denote v, w⟩ := by
  obtain ⟨w, hw, hsteps⟩ := run_to_value (P.allocFree_body hP) (alloc P.init v)
  exact ⟨w, hw, hsteps⟩

end Calculus
