import Drop.Calculus.Machine

set_option autoImplicit false

/-!
# admissible source weakening, and its exact reflection into `DiscardSafe`

Say that the `drop` in a program is justified in the source* when the
program is denotationally equal to a typed program of the same weakened type in which the
temporary is manifestly independent of the input — prepare it once, run a visible-only gate,
drop — and then: source weakening is admissible exactly when the elaborated core program is
`DiscardSafe` and denotes an isometry; for a typed program the second clause is free, so on
the whole type system the two notions coincide.*

## Why this is not a rename of `DiscardSafe`

`DiscardSafe i₀ p` is an existential over an arbitrary unit vector `g` and an arbitrary matrix
`W`.  `SourceWeakenable P` is an existential over programs of the source language: the
witness must be a `Prog` whose typing derivation exists, so its two gates must be unitary and
its parked state must be *prepared* by a gate from the allocated basis state.  The two are
therefore a priori different, and the difference is located exactly:

* `Calculus.sourceWeakenable_iff_discardSafe_and_isometric` names the missing clause: norm
  preservation, and nothing else.  This is the *largest fragment* statement, and it is
  semantic rather than syntactic — it holds of raw, untypable programs too.  A program that
  is `DiscardSafe` and not source-weakenable is therefore one whose gate is not an isometry;
  no such program is exhibited here.
* `Calculus.typed_weakening_iff_discardSafe` is the headline: on typed programs the extra clause
  is discharged by the type system, so reflection succeeds.

The mathematical content of the `←` direction is that *every* unit parked state and *every*
isometric residual visible map are source-expressible: the parking gate is the Householder
reflection of `SourceLanguage.reflectionTo`, and the residual map is a legal visible gate.
-/

namespace Calculus

open SourceLanguage Circuit SimpleTensor Matrix

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-! ### The canonical justification: a program in which the temporary is manifestly independent -/

/-- The separable body `let a = R a in let v = W v in drop a ; v`: prepare the temporary
once, act on the visible register once, drop.  Nothing the input does reaches the temporary. -/
noncomputable def sepBody (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ) (a v : Var) : Tm ι μ :=
  .letGate (localGate R 1) a v a v (.letGate (localGate 1 W) a v a v (.drop a (.ret v)))

/-- The separable program at an allocation point. -/
noncomputable def sepProg (i₀ : ι) (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ) (a v : Var) :
    Prog ι μ := ⟨i₀, a, v, sepBody R W a v⟩

omit [Fintype ι] [Fintype μ] in
@[simp] lemma sepProg_init (i₀ : ι) (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ) (a v : Var) :
    (sepProg i₀ R W a v).init = i₀ := rfl

omit [Fintype ι] [Fintype μ] in
@[simp] lemma sepProg_body (i₀ : ι) (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ) (a v : Var) :
    (sepProg i₀ R W a v).body = sepBody R W a v := rfl

omit [Fintype ι] [Fintype μ] in
lemma allocFree_sepBody (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ) (a v : Var) :
    AllocFree (sepBody R W a v) :=
  .letGate _ _ _ _ _ (.letGate _ _ _ _ _ (.drop _ (.ret _)))

omit [Fintype ι] [Fintype μ] in
lemma elabBody_sepBody (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ) (a v : Var) :
    elabBody (sepBody R W a v) = .gate (localGate R 1) (.gate (localGate 1 W) .halt) := rfl

lemma run_elab_sepBody (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ) (a v : Var) :
    (elabBody (sepBody R W a v)).run = localGate R W := by
  rw [elabBody_sepBody, Body.run, Body.run, Body.run, Matrix.one_mul, localGate_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- The separable program does what its name says: the temporary ends in the prepared state
`R e_{i₀}`, and the visible register receives `W`, whatever the input. -/
lemma denote_sepProg (i₀ : ι) (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ) (a v : Var)
    (x : EuclideanSpace ℝ μ) :
    (sepProg i₀ R W a v).denote x
      = tens (act R (EuclideanSpace.single i₀ (1 : ℝ))) (act W x) := by
  rw [Prog.denote_def, sepProg_body, sepProg_init, denote, LinearMap.comp_apply,
    run_elab_sepBody, alloc_eq_tens]
  exact actJoint_localGate_tens R W _ x

/-! ### The separable program is typed -/

lemma ctx_gate_fix {a v : Var} (hav : a ≠ v) :
    (((((Ctx.single v Ty.vis).insert a Ty.tmp).erase a).erase v).insert a Ty.tmp).insert v
        Ty.vis = (Ctx.single v Ty.vis).insert a Ty.tmp := by
  funext z
  by_cases hzv : z = v <;> by_cases hza : z = a <;>
    simp [Ctx.insert, Ctx.erase, Ctx.single, hzv, hza, hav, hav.symm]

lemma ctx_erase_tmp {a v : Var} (hav : a ≠ v) :
    ((Ctx.single v Ty.vis).insert a Ty.tmp).erase a = Ctx.single v Ty.vis := by
  funext z
  by_cases hza : z = a <;> simp [Ctx.insert, Ctx.erase, Ctx.single, hza, hav]

/-- A two-gate scoped program is typed as soon as both gates are legal and the temporary is
not the input.  This is the shape of every weakening witness. -/
theorem twoGateProg_typed {i₀ : ι} {G₁ G₂ : Matrix (ι × μ) (ι × μ) ℝ} {a v : Var}
    (hav : a ≠ v) (h1 : G₁ᴴ * G₁ = 1) (h2 : G₂ᴴ * G₂ = 1) :
    (Prog.mk i₀ a v
      (.letGate G₁ a v a v (.letGate G₂ a v a v (.drop a (.ret v))))).Typed := by
  show HasTy (Ctx.single v Ty.vis)
    (Tm.letNew i₀ a (.letGate G₁ a v a v (.letGate G₂ a v a v (.drop a (.ret v))))) Ty.vis
  refine HasTy.new (Γ := Ctx.single v Ty.vis) (Ctx.single_apply_of_ne _ hav)
    (noTmp_single_vis v)
    (.letGate _ _ _ _ _ (.letGate _ _ _ _ _ (.drop _ (.ret _)))) ?_
  have hΓa : ((Ctx.single v Ty.vis).insert a Ty.tmp) a = some Ty.tmp := Ctx.insert_self _ _ _
  have hΓv : ((Ctx.single v Ty.vis).insert a Ty.tmp) v = some Ty.vis := by
    rw [Ctx.insert_apply_of_ne _ _ hav.symm, Ctx.single_self]
  refine HasTy.gate h1 hav hav hΓa hΓv ?_
  rw [ctx_gate_fix hav]
  refine HasTy.gate h2 hav hav hΓa hΓv ?_
  rw [ctx_gate_fix hav]
  refine HasTy.drop hΓa ?_
  rw [ctx_erase_tmp hav]
  exact HasTy.ret rfl

/-- The canonical justification is a well-typed program.  Two legal gates, one drop, one
returned visible value. -/
theorem sepProg_typed {i₀ : ι} {R : Matrix ι ι ℝ} {W : Matrix μ μ ℝ} {a v : Var}
    (hav : a ≠ v) (hR : Rᴴ * R = 1) (hW : Wᴴ * W = 1) : (sepProg i₀ R W a v).Typed :=
  twoGateProg_typed hav (localGate_unitary hR (by simp)) (localGate_unitary (by simp) hW)

/-! ### Admissible source weakening -/

/-- A program is separable when its body is the canonical justification. -/
def Prog.Separable (Q : Prog ι μ) : Prop :=
  ∃ (R : Matrix ι ι ℝ) (W : Matrix μ μ ℝ), Q.body = sepBody R W Q.scope Q.input

/-- Admissible source weakening.  The `drop` in `P` is justified in the source when `P` is
denotationally equal to a *typed* program, allocating at the same point, whose temporary is
manifestly independent of the input.

No product state, no subspace and no matrix condition occurs in this definition: it quantifies
over programs of the source language and their typing derivations. -/
def SourceWeakenable (P : Prog ι μ) : Prop :=
  ∃ Q : Prog ι μ, Q.init = P.init ∧ Q.Separable ∧ Q.Typed ∧ ∀ v, P.denote v = Q.denote v

/-- Non-vacuity.  The canonical justification justifies itself: a typed separable program is
source-weakenable. -/
theorem sepProg_sourceWeakenable {i₀ : ι} {R : Matrix ι ι ℝ} {W : Matrix μ μ ℝ} {a v : Var}
    (hav : a ≠ v) (hR : Rᴴ * R = 1) (hW : Wᴴ * W = 1) :
    SourceWeakenable (sepProg i₀ R W a v) :=
  ⟨sepProg i₀ R W a v, rfl, ⟨R, W, rfl⟩, sepProg_typed hav hR hW, fun _ => rfl⟩

/-! ### Two facts about the source witness -/

/-- A separable typed program prepares a unit temporary state: the preparation gate is
legal, so it cannot change the length of the allocated basis state. -/
lemma norm_act_of_localGate_left [Nonempty μ] {R : Matrix ι ι ℝ}
    (h : (localGate R (1 : Matrix μ μ ℝ))ᴴ * localGate R (1 : Matrix μ μ ℝ) = 1)
    (a : EuclideanSpace ℝ ι) : ‖act R a‖ = ‖a‖ := by
  obtain ⟨j⟩ := ‹Nonempty μ›
  set b : EuclideanSpace ℝ μ := EuclideanSpace.single j (1 : ℝ) with hb
  have hbnorm : ‖b‖ = 1 := by simp [hb]
  have hjoint : ‖actJoint (localGate R (1 : Matrix μ μ ℝ)) (tens a b)‖ = ‖tens a b‖ :=
    norm_act_of_unitary h (tens a b)
  rw [actJoint_localGate_tens, act_one, norm_tens, norm_tens, hbnorm, mul_one, mul_one] at hjoint
  exact hjoint

/-- The unit length of the allocated basis state. -/
lemma norm_single_one (i₀ : ι) : ‖(EuclideanSpace.single i₀ (1 : ℝ))‖ = 1 := by simp

/-! ### The reflection theorem -/

/-- Admissible source weakening forces an isometry.  The justifying program is typed, so it
is norm-preserving, and the two have the same denotation. -/
theorem norm_denote_of_sourceWeakenable {P : Prog ι μ} (h : SourceWeakenable P)
    (v : EuclideanSpace ℝ μ) : ‖P.denote v‖ = ‖v‖ := by
  obtain ⟨Q, _, _, hQ, heq⟩ := h
  rw [heq v]
  exact Q.norm_denote hQ v

/-- Admissible source weakening implies the core criterion.  The justifying program parks
the temporary in the prepared state and applies one visible map. -/
theorem discardSafe_of_sourceWeakenable [Nonempty μ] {P : Prog ι μ} (h : SourceWeakenable P) :
    DiscardSafe P.init (elabBody P.body) := by
  obtain ⟨Q, hinit, ⟨R, W, hbody⟩, hQ, heq⟩ := h
  have hwt : (elabBody (sepBody R W Q.scope Q.input)).WellTyped := by
    have := Q.elab_wellTyped hQ
    rwa [hbody] at this
  rw [elabBody_sepBody] at hwt
  have hU1 : (localGate R (1 : Matrix μ μ ℝ))ᴴ * localGate R 1 = 1 := by
    cases hwt with
    | gate hU _ => exact hU
  have hQden : ∀ x, Q.denote x
      = tens (act R (EuclideanSpace.single P.init (1 : ℝ))) (act W x) := by
    intro x
    have hQeq : Q = sepProg Q.init R W Q.scope Q.input := by
      cases Q with
      | mk init scope input body => simp [sepProg] at hbody ⊢; exact hbody
    rw [hQeq, denote_sepProg, hinit]
  refine ⟨act R (EuclideanSpace.single P.init (1 : ℝ)), W, ?_, fun x => ?_⟩
  · rw [norm_act_of_localGate_left hU1, norm_single_one]
  · rw [← Prog.denote_def, heq x, hQden x]

/-- The sharp reflection theorem.  Source weakening is admissible exactly when the
elaborated core program is `DiscardSafe` *and* denotes an isometry.  No typing hypothesis: this
is the largest fragment on which the source notion and the core notion agree, and the second
clause is exactly what a program outside the type system can fail. -/
theorem sourceWeakenable_iff_discardSafe_and_isometric [Nonempty μ] {P : Prog ι μ}
    (hne : P.scope ≠ P.input) :
    SourceWeakenable P ↔
      (DiscardSafe P.init (elabBody P.body) ∧ ∀ v, ‖P.denote v‖ = ‖v‖) := by
  constructor
  · exact fun h => ⟨discardSafe_of_sourceWeakenable h, norm_denote_of_sourceWeakenable h⟩
  · rintro ⟨⟨g, W, hg, hgW⟩, hiso⟩
    have hWiso : ∀ x, ‖act W x‖ = ‖x‖ := by
      intro x
      have h1 := hiso x
      rw [Prog.denote_def, hgW x, norm_tens, hg, one_mul] at h1
      exact h1
    have hW : Wᴴ * W = 1 := unitary_of_norm_act hWiso
    refine ⟨sepProg P.init (reflectionTo P.init g) W P.scope P.input, rfl,
      ⟨reflectionTo P.init g, W, rfl⟩,
      sepProg_typed hne (reflectionTo_unitary P.init g) hW, fun x => ?_⟩
    rw [denote_sepProg, act_reflectionTo_single hg, Prog.denote_def, hgW x]

/-- The headline.  For a *typed* program, admissible source weakening and `DiscardSafe`
agree — reflection succeeds on the whole type system. -/
theorem typed_weakening_iff_discardSafe [Nonempty μ] {P : Prog ι μ} (hP : P.Typed) :
    SourceWeakenable P ↔ DiscardSafe P.init (elabBody P.body) := by
  rw [sourceWeakenable_iff_discardSafe_and_isometric (Prog.scope_ne_input hP)]
  exact ⟨fun h => h.1, fun h => ⟨h, fun v => P.norm_denote hP v⟩⟩

end Calculus
