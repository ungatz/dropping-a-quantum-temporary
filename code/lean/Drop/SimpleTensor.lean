import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Basic

/-!
# Simple tensors and contractions

The joint register of a temporary and a visible register is
`EuclideanSpace 𝕜 (ι × κ)`, the Hilbert tensor product of the two Euclidean
spaces. This file defines the simple tensor `tens g b`, the two contractions
`contractL g x` and `contractR b x` (partial inner products against a fixed
vector on one side), and proves the inner-product and norm identities the
rest of the development uses: `⟪g ⊗ b, p ⊗ q⟫ = ⟪g, p⟫ ⟪b, q⟫`, `‖g ⊗ b‖ = ‖g‖ ‖b‖`,
and that a contraction against a unit vector does not increase the norm.
No cardinality of `ι` or `κ` enters any constant.
-/

namespace SimpleTensor

open RCLike ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### A one-dimensional projection bound, in any inner product space -/

section Proj

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Pythagoras for the projection onto a unit vector. -/
lemma norm_sub_proj_sq (b u : F) (hb : ‖b‖ = 1) :
    ‖u - (inner 𝕜 b u : 𝕜) • b‖ ^ 2 = ‖u‖ ^ 2 - ‖(inner 𝕜 b u : 𝕜)‖ ^ 2 := by
  set c : 𝕜 := inner 𝕜 b u with hc
  have h1 : (inner 𝕜 u b : 𝕜) = conj c := by rw [hc, inner_conj_symm]
  rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, h1, norm_smul, hb, RCLike.mul_conj]
  simp
  ring

/-- Removing the component along a unit vector does not increase the norm. -/
lemma norm_sub_proj_le (b u : F) (hb : ‖b‖ = 1) :
    ‖u - (inner 𝕜 b u : 𝕜) • b‖ ≤ ‖u‖ := by
  have h := norm_sub_proj_sq (𝕜 := 𝕜) b u hb
  nlinarith [norm_nonneg (u - (inner 𝕜 b u : 𝕜) • b), norm_nonneg u,
    sq_nonneg ‖(inner 𝕜 b u : 𝕜)‖]

end Proj

/-! ### Simple tensors -/

/-- The simple tensor `g ⊗ b`, as a vector indexed by pairs. -/
noncomputable def tens (g : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    EuclideanSpace 𝕜 (ι × κ) := WithLp.toLp 2 (fun p => g p.1 * b p.2)

omit [Fintype ι] [Fintype κ] in
@[simp] lemma tens_apply (g : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) (p : ι × κ) :
    tens g b p = g p.1 * b p.2 := rfl

@[simp] lemma tens_add_left (g g' : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    tens (g + g') b = tens g b + tens g' b := by
  ext p; simp [add_mul]

@[simp] lemma tens_add_right (g : EuclideanSpace 𝕜 ι) (b b' : EuclideanSpace 𝕜 κ) :
    tens g (b + b') = tens g b + tens g b' := by
  ext p; simp [mul_add]

@[simp] lemma tens_sub_left (g g' : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    tens (g - g') b = tens g b - tens g' b := by
  ext p; simp [sub_mul]

@[simp] lemma tens_sub_right (g : EuclideanSpace 𝕜 ι) (b b' : EuclideanSpace 𝕜 κ) :
    tens g (b - b') = tens g b - tens g b' := by
  ext p; simp [mul_sub]

omit [Fintype ι] [Fintype κ] in
@[simp] lemma tens_smul_left (c : 𝕜) (g : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    tens (c • g) b = c • tens g b := by
  ext p; simp [mul_assoc]

omit [Fintype ι] [Fintype κ] in
@[simp] lemma tens_smul_right (c : 𝕜) (g : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    tens g (c • b) = c • tens g b := by
  ext p; simp; ring

omit [Fintype ι] [Fintype κ] in
@[simp] lemma tens_zero_left (b : EuclideanSpace 𝕜 κ) : tens (0 : EuclideanSpace 𝕜 ι) b = 0 := by
  ext p; simp

omit [Fintype ι] [Fintype κ] in
@[simp] lemma tens_zero_right (g : EuclideanSpace 𝕜 ι) : tens g (0 : EuclideanSpace 𝕜 κ) = 0 := by
  ext p; simp

/-! ### Contractions -/

/-- Contract a vector of `G ⊗ B` against `g` in the first factor. -/
noncomputable def contractL (g : EuclideanSpace 𝕜 ι) (x : EuclideanSpace 𝕜 (ι × κ)) :
    EuclideanSpace 𝕜 κ := WithLp.toLp 2 (fun j => ∑ i, conj (g i) * x (i, j))

/-- Contract a vector of `G ⊗ B` against `b` in the second factor. -/
noncomputable def contractR (b : EuclideanSpace 𝕜 κ) (x : EuclideanSpace 𝕜 (ι × κ)) :
    EuclideanSpace 𝕜 ι := WithLp.toLp 2 (fun i => ∑ j, conj (b j) * x (i, j))

omit [Fintype κ] in
@[simp] lemma contractL_apply (g : EuclideanSpace 𝕜 ι) (x : EuclideanSpace 𝕜 (ι × κ)) (j : κ) :
    contractL g x j = ∑ i, conj (g i) * x (i, j) := rfl

omit [Fintype ι] in
@[simp] lemma contractR_apply (b : EuclideanSpace 𝕜 κ) (x : EuclideanSpace 𝕜 (ι × κ)) (i : ι) :
    contractR b x i = ∑ j, conj (b j) * x (i, j) := rfl

@[simp] lemma contractL_add (g : EuclideanSpace 𝕜 ι) (x y : EuclideanSpace 𝕜 (ι × κ)) :
    contractL g (x + y) = contractL g x + contractL g y := by
  ext j; simp [mul_add, Finset.sum_add_distrib]

@[simp] lemma contractL_sub (g : EuclideanSpace 𝕜 ι) (x y : EuclideanSpace 𝕜 (ι × κ)) :
    contractL g (x - y) = contractL g x - contractL g y := by
  ext j; simp [mul_sub, Finset.sum_sub_distrib]

omit [Fintype κ] in
@[simp] lemma contractL_smul (c : 𝕜) (g : EuclideanSpace 𝕜 ι) (x : EuclideanSpace 𝕜 (ι × κ)) :
    contractL g (c • x) = c • contractL g x := by
  ext j; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

@[simp] lemma contractR_add (b : EuclideanSpace 𝕜 κ) (x y : EuclideanSpace 𝕜 (ι × κ)) :
    contractR b (x + y) = contractR b x + contractR b y := by
  ext i; simp [mul_add, Finset.sum_add_distrib]

@[simp] lemma contractR_sub (b : EuclideanSpace 𝕜 κ) (x y : EuclideanSpace 𝕜 (ι × κ)) :
    contractR b (x - y) = contractR b x - contractR b y := by
  ext i; simp [mul_sub, Finset.sum_sub_distrib]

omit [Fintype ι] in
@[simp] lemma contractR_smul (c : 𝕜) (b : EuclideanSpace 𝕜 κ) (x : EuclideanSpace 𝕜 (ι × κ)) :
    contractR b (c • x) = c • contractR b x := by
  ext i; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

/-- Contraction is adjoint to tensoring.  This and its mirror image are the only
coordinate computations in the development. -/
lemma inner_tens_left (g : EuclideanSpace 𝕜 ι) (u : EuclideanSpace 𝕜 κ)
    (x : EuclideanSpace 𝕜 (ι × κ)) :
    inner 𝕜 (tens g u) x = inner 𝕜 u (contractL g x) := by
  simp only [PiLp.inner_apply, contractL_apply, RCLike.inner_apply, tens_apply,
    Fintype.sum_prod_type, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma inner_tens_right (b : EuclideanSpace 𝕜 κ) (v : EuclideanSpace 𝕜 ι)
    (x : EuclideanSpace 𝕜 (ι × κ)) :
    inner 𝕜 (tens v b) x = inner 𝕜 v (contractR b x) := by
  simp only [PiLp.inner_apply, contractR_apply, RCLike.inner_apply, tens_apply,
    Fintype.sum_prod_type, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype κ] in
@[simp] lemma contractL_tens (g p : EuclideanSpace 𝕜 ι) (q : EuclideanSpace 𝕜 κ) :
    contractL g (tens p q) = (inner 𝕜 g p : 𝕜) • q := by
  ext j
  simp only [contractL_apply, tens_apply, PiLp.smul_apply, PiLp.inner_apply, RCLike.inner_apply,
    smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype ι] in
@[simp] lemma contractR_tens (b q : EuclideanSpace 𝕜 κ) (p : EuclideanSpace 𝕜 ι) :
    contractR b (tens p q) = (inner 𝕜 b q : 𝕜) • p := by
  ext i
  simp only [contractR_apply, tens_apply, PiLp.smul_apply, PiLp.inner_apply, RCLike.inner_apply,
    smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma inner_tens_tens (g p : EuclideanSpace 𝕜 ι) (b q : EuclideanSpace 𝕜 κ) :
    inner 𝕜 (tens g b) (tens p q) = (inner 𝕜 g p : 𝕜) * inner 𝕜 b q := by
  rw [inner_tens_left, contractL_tens, inner_smul_right]

/-- The Hilbert tensor norm is multiplicative on simple tensors. -/
lemma norm_tens (g : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖tens g b‖ = ‖g‖ * ‖b‖ := by
  have h : ‖tens (𝕜 := 𝕜) g b‖ ^ 2 = (‖g‖ * ‖b‖) ^ 2 := by
    have h0 := congrArg (RCLike.re (K := 𝕜)) (inner_tens_tens (𝕜 := 𝕜) g g b b)
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h0
    rw [h0]
    simp [mul_pow]
  calc ‖tens (𝕜 := 𝕜) g b‖ = Real.sqrt (‖tens (𝕜 := 𝕜) g b‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((‖g‖ * ‖b‖) ^ 2) := by rw [h]
    _ = ‖g‖ * ‖b‖ := Real.sqrt_sq (by positivity)

/-- Contracting against a unit vector does not increase the norm. -/
lemma norm_contractL_le (g : EuclideanSpace 𝕜 ι) (x : EuclideanSpace 𝕜 (ι × κ)) :
    ‖contractL g x‖ ≤ ‖g‖ * ‖x‖ := by
  set u := contractL g x with hu
  have key : (‖u‖ : ℝ) ^ 2 = RCLike.re (inner 𝕜 (tens g u) x : 𝕜) := by
    rw [inner_tens_left, ← hu, inner_self_eq_norm_sq]
  have h2 : RCLike.re (inner 𝕜 (tens g u) x : 𝕜) ≤ ‖tens (𝕜 := 𝕜) g u‖ * ‖x‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  rw [norm_tens] at h2
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h]; positivity
  · have : ‖u‖ ^ 2 ≤ ‖g‖ * ‖u‖ * ‖x‖ := by rw [key]; linarith
    nlinarith

lemma norm_contractR_le (b : EuclideanSpace 𝕜 κ) (x : EuclideanSpace 𝕜 (ι × κ)) :
    ‖contractR b x‖ ≤ ‖b‖ * ‖x‖ := by
  set v := contractR b x with hv
  have key : (‖v‖ : ℝ) ^ 2 = RCLike.re (inner 𝕜 (tens v b) x : 𝕜) := by
    rw [inner_tens_right, ← hv, inner_self_eq_norm_sq]
  have h2 : RCLike.re (inner 𝕜 (tens v b) x : 𝕜) ≤ ‖tens (𝕜 := 𝕜) v b‖ * ‖x‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  rw [norm_tens] at h2
  rcases eq_or_lt_of_le (norm_nonneg v) with h | h
  · rw [← h]; positivity
  · have : ‖v‖ ^ 2 ≤ ‖b‖ * ‖v‖ * ‖x‖ := by rw [key]; linarith
    nlinarith

end SimpleTensor
