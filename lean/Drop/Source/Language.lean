import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Drop.Circuit.Output

/-!
# A source language, and the extraction of an isometry from a program

The clean-discard estimate carries the hypothesis

> *"a compiler wanting to quote this must separately justify that its admitted
> executions form the range of a single isometry"*.

This file discharges that obligation for the smallest language in which the
obligation can be stated, and shows the hypothesis is exactly the isometry condition:
the programs of the language denote isometries `A → G ⊗ B` and nothing else,
and every such isometry is denoted by a program (`Drop/Source/Complete.lean`).

## The language

allocate a temporary in a fixed basis state, apply a finite list
of unitary gates to the temporary and the visible register jointly, and stop.

```
Body ::= halt | gate U ; Body            (U a square matrix on TEMPORARY × VISIBLE)
Frag ::= alloc i₀ ; Body                 (i₀ the initial value of the TEMPORARY)
```

`discard` is not a syntactic form: it is the *reading* of the output as living
in `G ⊗ B`, and `Drop/Source/Safety.lean` says when that reading is safe.
Nothing else is in the language, deliberately.

## What is proved here

* `Body.run_isometric` — a well-typed body runs to a matrix with orthonormal
  columns.
* `denote_eq_outLM_computeSide` — the extraction.  The denotation of
  `alloc i₀ ; p` is the output map of the extracted compute side
  `computeSide i₀ p i j k = (run p) (i,j) (i₀,k)`: the column block of the
  circuit unitary at the allocated temporary value.  This is the sentence that
  puts a *program* into the hypotheses of `Drop/Circuit/Output.lean`.
* `computeSide_isometry_law` — the extracted compute side satisfies
  `∑ i, (P i)ᴴ * (P i) = 1`, which is the hypothesis `norm_outLM_of_isometry` consumes.
* `norm_denote` — hence the denotation is an isometry `A → G ⊗ B`.

Typing hypotheses actually consumed by the extraction: every gate satisfies
`Uᴴ * U = 1`; the scalars are real or complex (`RCLike`); the temporary and
visible indices are finite with decidable equality.  Nothing else — no
nonemptiness, no dimension comparison, no commutativity.
-/

namespace SourceLanguage

open Matrix Circuit

/-! ### Syntax -/

/-- The syntax of a straight-line body: a finite list of gates acting jointly on
the TEMPORARY register (index `ι`) and the VISIBLE register (index `μ`). -/
inductive Body (𝕜 ι μ : Type*) where
  | halt : Body 𝕜 ι μ
  | gate : Matrix (ι × μ) (ι × μ) 𝕜 → Body 𝕜 ι μ → Body 𝕜 ι μ

variable {𝕜 : Type*} [RCLike 𝕜] {ι μ : Type*}
  [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-! ### Semantics -/

/-- The matrix a body runs to: the gates are applied left to right. -/
def Body.run : Body 𝕜 ι μ → Matrix (ι × μ) (ι × μ) 𝕜
  | .halt => 1
  | .gate U r => r.run * U

/-- Well-typedness: every gate is unitary. -/
inductive Body.WellTyped : Body 𝕜 ι μ → Prop
  | halt : Body.WellTyped .halt
  | gate {U : Matrix (ι × μ) (ι × μ) 𝕜} {r : Body 𝕜 ι μ} :
      Uᴴ * U = 1 → r.WellTyped → (Body.gate U r).WellTyped

/-- A well-typed body runs to a matrix with orthonormal columns. -/
theorem Body.run_isometric : ∀ {p : Body 𝕜 ι μ}, p.WellTyped → p.runᴴ * p.run = 1
  | .halt, _ => by simp [Body.run]
  | .gate U r, h => by
    cases h with
    | gate hU hr =>
      have hrun := Body.run_isometric hr
      simp only [Body.run, conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc r.runᴴ, hrun, Matrix.one_mul, hU]

/-- Allocation: the visible input `v` with the TEMPORARY register initialised in
the basis state `i₀`. -/
noncomputable def alloc (i₀ : ι) : EuclideanSpace 𝕜 μ →ₗ[𝕜] EuclideanSpace 𝕜 (ι × μ) where
  toFun v := WithLp.toLp 2 fun p => if p.1 = i₀ then v p.2 else 0
  map_add' u v := by ext p; by_cases h : p.1 = i₀ <;> simp [h]
  map_smul' c v := by ext p; by_cases h : p.1 = i₀ <;> simp [h]

omit [DecidableEq μ] in
@[simp] lemma alloc_apply (i₀ : ι) (v : EuclideanSpace 𝕜 μ) (p : ι × μ) :
    alloc i₀ v p = if p.1 = i₀ then v p.2 else 0 := rfl

/-- The action of a joint matrix on the joint register. -/
noncomputable def actJoint (M : Matrix (ι × μ) (ι × μ) 𝕜) :
    EuclideanSpace 𝕜 (ι × μ) →ₗ[𝕜] EuclideanSpace 𝕜 (ι × μ) where
  toFun x := WithLp.toLp 2 fun p => ∑ q, M p q * x q
  map_add' x y := by ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext p; simp [Finset.mul_sum, mul_left_comm]

omit [DecidableEq ι] [DecidableEq μ] in
@[simp] lemma actJoint_apply (M : Matrix (ι × μ) (ι × μ) 𝕜)
    (x : EuclideanSpace 𝕜 (ι × μ)) (p : ι × μ) :
    actJoint M x p = ∑ q, M p q * x q := rfl

/-- The denotation of a fragment `alloc i₀ ; p`: a linear map from the
visible input to the joint TEMPORARY-VISIBLE output. -/
noncomputable def denote (i₀ : ι) (p : Body 𝕜 ι μ) :
    EuclideanSpace 𝕜 μ →ₗ[𝕜] EuclideanSpace 𝕜 (ι × μ) :=
  (actJoint p.run).comp (alloc i₀)

/-- The extracted compute side.  `computeSide i₀ p i` is the visible action
on the branch where the temporary ends in the basis state `i`: the `(·, i₀)`
column block of the circuit matrix. -/
def computeSide (i₀ : ι) (p : Body 𝕜 ι μ) : ι → Matrix μ μ 𝕜 :=
  fun i => Matrix.of fun j k => p.run (i, j) (i₀, k)

@[simp] lemma computeSide_apply (i₀ : ι) (p : Body 𝕜 ι μ) (i : ι) (j k : μ) :
    computeSide i₀ p i j k = p.run (i, j) (i₀, k) := rfl

/-! ### The extraction -/

/-- The extraction, as an identity.  running a fragment is
the same as applying its extracted compute side branch by branch. -/
theorem denote_eq_outLM_computeSide (i₀ : ι) (p : Body 𝕜 ι μ) (v : EuclideanSpace 𝕜 μ) :
    denote i₀ p v = outLM (computeSide i₀ p) v := by
  ext q
  simp only [denote, LinearMap.comp_apply, actJoint_apply, outLM_apply, alloc_apply,
    computeSide_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- The extracted compute side of a well-typed fragment is isometric.
This is exactly the hypothesis `Circuit.norm_outLM_of_isometry` consumes. -/
theorem computeSide_isometry_law {i₀ : ι} {p : Body 𝕜 ι μ} (hp : p.WellTyped) :
    ∑ i, (computeSide i₀ p i)ᴴ * (computeSide i₀ p i) = 1 := by
  have hrun := Body.run_isometric hp
  ext k' k
  have hentry : (p.runᴴ * p.run) (i₀, k') (i₀, k)
      = (1 : Matrix (ι × μ) (ι × μ) 𝕜) (i₀, k') (i₀, k) := by rw [hrun]
  rw [Matrix.mul_apply, Fintype.sum_prod_type] at hentry
  simp only [conjTranspose_apply] at hentry
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, computeSide_apply]
  rw [hentry]
  simp [Matrix.one_apply, Prod.ext_iff]

/-- The denotation of a well-typed fragment is an isometry `A → G ⊗ B`. -/
theorem norm_denote {i₀ : ι} {p : Body 𝕜 ι μ} (hp : p.WellTyped) (v : EuclideanSpace 𝕜 μ) :
    ‖denote i₀ p v‖ = ‖v‖ := by
  rw [denote_eq_outLM_computeSide]
  exact norm_outLM_of_isometry (computeSide_isometry_law hp) v

/-- The extraction, in the form the clean-discard estimate needs.  A well-typed
fragment with one allocated temporary denotes an isometry from the visible input
to `TEMPORARY ⊗ VISIBLE`, and that isometry is the output map of an explicitly
named compute side. -/
theorem extraction {i₀ : ι} {p : Body 𝕜 ι μ} (hp : p.WellTyped) :
    ∃ P : ι → Matrix μ μ 𝕜,
      (∑ i, (P i)ᴴ * P i = 1) ∧ (∀ v, denote i₀ p v = outLM P v) ∧
        (∀ v, ‖denote i₀ p v‖ = ‖v‖) :=
  ⟨computeSide i₀ p, computeSide_isometry_law hp,
    denote_eq_outLM_computeSide i₀ p, fun v => norm_denote hp v⟩

end SourceLanguage
