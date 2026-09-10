import Drop.Dilation.Bridge
import Drop.Calculus.Reflection

set_option autoImplicit false

/-!
# the hypothesis, discharged: source weakening is mediator-erasability

The source calculus's `DiscardSafe` is, literally, "the mediator quotient identifies
this program with one that never allocated" — so the source-level criterion of
`Calculus.typed_weakening_iff_discardSafe` is a statement about the unit of the completion, and
that hypothesis can be discharged, with one condition attached.

`progDil i₀ p` is the fragment `alloc i₀ ; p` read as a dilation: environment the temporary
register, visible register the visible register.  Then

* `discardSafe_iff_productForm` — the source calculus's predicate is the abstract one, verbatim;
* `discardSafe_iff_erasable` — and it is mediator-erasability over the isometry base;
* `typed_weakening_iff_erasable` — chaining `Calculus`, admissible source weakening of a typed
  program is mediator-erasability.

The hypothesis that must travel with it: the temporary register is nonempty.  For a *program*
the hypothesis is free — `P.init : ι` inhabits the register — so on the source calculus's own
carrier the bridge is unconditional, and the empty-environment exception is invisible from the
source language.  It is visible in the completion, which is the honest way
to say what the bridge costs.
-/

namespace Dilation

open Matrix SourceLanguage Circuit SimpleTensor

variable {ι μ : Type} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-! ## Matrices and linear maps on the visible register -/

/-- A visible-register matrix as a linear map. -/
noncomputable def actLM (M : Matrix μ μ ℝ) :
    EuclideanSpace ℝ μ →ₗ[ℝ] EuclideanSpace ℝ μ where
  toFun v := act M v
  map_add' u v := by ext j; simp [act, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext j; simp [act, Finset.mul_sum, mul_left_comm]

omit [DecidableEq μ] in
@[simp] lemma actLM_apply (M : Matrix μ μ ℝ) (v : EuclideanSpace ℝ μ) : actLM M v = act M v := rfl

/-- Every linear map of the visible register is the action of its matrix. -/
lemma exists_matrix_act (W : EuclideanSpace ℝ μ →ₗ[ℝ] EuclideanSpace ℝ μ) :
    ∃ M : Matrix μ μ ℝ, ∀ v, act M v = W v := by
  refine ⟨Matrix.of fun j k => W (EuclideanSpace.single k 1) j, fun v => ?_⟩
  have hv : v = ∑ k, v k • EuclideanSpace.single (𝕜 := ℝ) k (1 : ℝ) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  ext j
  rw [act_apply]
  conv_rhs => rw [hv]
  rw [map_sum]
  simp [mul_comm]

/-! ## A source fragment, as a dilation -/

/-- The fragment `alloc i₀ ; p`, read as a dilation: the temporary register is the
environment. -/
@[reducible] noncomputable def progDil (i₀ : ι) (p : Body ℝ ι μ) : Dil ℝ μ μ where
  env := ι
  map := denote i₀ p

/-- The source calculus's predicate is the abstract one. -/
theorem discardSafe_iff_productForm (i₀ : ι) (p : Body ℝ ι μ) :
    DiscardSafe i₀ p ↔ ProductForm (progDil i₀ p) := by
  constructor
  · rintro ⟨g, W, hg, hd⟩
    exact ⟨g, actLM W, hg, fun v => hd v⟩
  · rintro ⟨g, W, hg, hd⟩
    obtain ⟨M, hM⟩ := exists_matrix_act W
    exact ⟨g, M, hg, fun v => by rw [hd v, hM v]⟩

/-- The bridge, on the source calculus's carrier.  A fragment is discard-safe exactly when the
`L`-completion over the isometry base identifies it with a fragment that never allocated. -/
theorem discardSafe_iff_erasable (i₀ : ι) (p : Body ℝ ι μ) :
    DiscardSafe i₀ p ↔ Erasable (isometries ℝ) (progDil i₀ p) := by
  haveI : Nonempty (progDil i₀ p).env := ⟨i₀⟩
  rw [discardSafe_iff_productForm]
  exact productForm_iff_erasable_isometries

/-- The hypothesis, discharged.  For a typed program, admissible source weakening — a source-level
statement about typing derivations, with no matrix and no subspace in it — is exactly
mediator-erasability in the `L`-completion over the isometry base. -/
theorem typed_weakening_iff_erasable [Nonempty μ] {P : Calculus.Prog ι μ} (hP : P.Typed) :
    Calculus.SourceWeakenable P ↔
      Erasable (isometries ℝ) (progDil P.init (Calculus.elabBody P.body)) :=
  (Calculus.typed_weakening_iff_discardSafe hP).trans
    (discardSafe_iff_erasable P.init (Calculus.elabBody P.body))

end Dilation
