import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Drop.SimpleTensor

/-!
# The output map of a compute side

A compute side is a family `P : ι → Matrix μ μ 𝕜`, one visible matrix per
basis state of the temporary. It sends a visible input `v` to the joint output

  `outLM P v = ∑ i, eᵢ ⊗ P i v ∈ EuclideanSpace 𝕜 (ι × μ)`.

Two facts about this map carry the exact criterion:

* `tens_contractL_outLM` — contracting the output against a unit temporary
  state `g` and tensoring back gives the output of the *disposable* compute
  side `i ↦ gᵢ · postSel g P`, where `postSel g P = ∑ᵢ conj(gᵢ) • P i` is the
  visible map obtained by post-selecting the temporary on `g`;
* `norm_outLM_of_isometry` — a compute side satisfying the isometry law
  `∑ᵢ (P i)ᴴ P i = 1` preserves the norm.
-/

namespace Circuit

open SimpleTensor Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq μ]

/-! ### The output map -/

/-- A matrix acting on a Euclidean visible register. -/
noncomputable def act (M : Matrix μ μ 𝕜) (v : EuclideanSpace 𝕜 μ) : EuclideanSpace 𝕜 μ :=
  WithLp.toLp 2 fun j => ∑ k, M j k * v k

omit [DecidableEq μ] in
@[simp] lemma act_apply (M : Matrix μ μ 𝕜) (v : EuclideanSpace 𝕜 μ) (j : μ) :
    act M v j = ∑ k, M j k * v k := rfl

/-- The output map of a compute side: `v ↦ ∑ i, eᵢ ⊗ P i v`. -/
noncomputable def outLM (P : ι → Matrix μ μ 𝕜) :
    EuclideanSpace 𝕜 μ →ₗ[𝕜] EuclideanSpace 𝕜 (ι × μ) where
  toFun v := WithLp.toLp 2 fun p => ∑ k, P p.1 p.2 k * v k
  map_add' u v := by
    ext p
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext p
    simp [Finset.mul_sum, mul_left_comm]

omit [DecidableEq μ] in
@[simp] lemma outLM_apply (P : ι → Matrix μ μ 𝕜) (v : EuclideanSpace 𝕜 μ) (p : ι × μ) :
    outLM P v p = ∑ k, P p.1 p.2 k * v k := rfl

/-- Post-selection of the ancilla on the direction `g`: the residual visible
map. -/
noncomputable def postSel (g : EuclideanSpace 𝕜 ι) (P : ι → Matrix μ μ 𝕜) : Matrix μ μ 𝕜 :=
  ∑ i, (starRingEnd 𝕜) (g i) • P i

omit [DecidableEq μ] in
/-- Post-selection is the contraction.  Contracting the output against the
ancilla direction `g` applies the post-selected visible map. -/
lemma contractL_outLM (g : EuclideanSpace 𝕜 ι) (P : ι → Matrix μ μ 𝕜)
    (v : EuclideanSpace 𝕜 μ) :
    contractL g (outLM P v) = act (postSel g P) v := by
  ext j
  simp only [contractL_apply, outLM_apply, act_apply, postSel, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq μ] in
/-- The closest point of the disposal ruling `span g ⊗ V` to an output is the
output of the *disposable* interface `i ↦ gᵢ · postSel g P`. -/
lemma tens_contractL_outLM (g : EuclideanSpace 𝕜 ι) (P : ι → Matrix μ μ 𝕜)
    (v : EuclideanSpace 𝕜 μ) :
    tens g (contractL g (outLM P v)) = outLM (fun i => g i • postSel g P) v := by
  ext p
  simp [contractL_outLM, Finset.mul_sum, mul_assoc]

/-! ### The exact case: disposability is a ruling -/

/-- An isometric compute side does not change the norm.  The inner product `⟪outLM P v, outLM P
v⟫` expands, index by index, to `∑ k k', conj (v k') * ((∑ᵢ Pᵢᴴ Pᵢ) k' k) * v k`; the isometry
law collapses the inner sum `∑ᵢ Pᵢᴴ Pᵢ` to the identity matrix, leaving exactly `⟪v, v⟫`.  Equal
inner products of a vector with itself give equal squared norms, and norms are nonnegative, so
the norms themselves agree. -/
lemma norm_outLM_of_isometry {P : ι → Matrix μ μ 𝕜}
    (hiso : ∑ i, (P i)ᴴ * P i = 1) (v : EuclideanSpace 𝕜 μ) :
    ‖outLM P v‖ = ‖v‖ := by
  -- The two joint states have equal inner products with themselves.
  have hinner_eq : (inner 𝕜 (outLM P v) (outLM P v) : 𝕜) = inner 𝕜 v v := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [RCLike.inner_apply', outLM_apply]
    rw [Fintype.sum_prod_type]
    -- Expand each `i`-summand and regroup it as a bilinear expression in `(P i)ᴴ * P i`.
    have hexpand : ∀ i : ι, ∑ j : μ, (starRingEnd 𝕜) (∑ k, P i j k * v k) * (∑ k, P i j k * v k)
        = ∑ k, ∑ k', (starRingEnd 𝕜) (v k') * (((P i)ᴴ * P i) k' k * v k) := by
      intro i
      simp only [map_sum, map_mul, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j _ => by
        rw [RCLike.star_def]; ring
    rw [Finset.sum_congr rfl fun i _ => hexpand i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    -- Sum the isometry law over `i` first, collapsing `∑ᵢ (Pᵢ)ᴴ Pᵢ` to the identity matrix.
    have hisometry : ∀ k' : μ, ∑ i : ι, (starRingEnd 𝕜) (v k') * (((P i)ᴴ * P i) k' k * v k)
        = (starRingEnd 𝕜) (v k') * ((1 : Matrix μ μ 𝕜) k' k * v k) := by
      intro k'
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← Matrix.sum_apply, hiso]
    rw [Finset.sum_congr rfl fun k' _ => hisometry k']
    simp [Matrix.one_apply]
  -- Convert the equal inner products to equal squared norms, then take square roots.
  have hnorm_sq_outLM := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (outLM P v)
  have hnorm_sq_v := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) v
  rw [hnorm_sq_outLM, hnorm_sq_v] at hinner_eq
  have hreal : (‖outLM P v‖ : ℝ) ^ 2 = (‖v‖ : ℝ) ^ 2 := by
    have := congrArg (RCLike.re (K := 𝕜)) hinner_eq
    simpa using this
  nlinarith [norm_nonneg (outLM P v), norm_nonneg v]

end Circuit
