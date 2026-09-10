import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The scalar steps of the robustness theorem

The theorem *the criterion is robust* bounds the distance from the
denotation to the weakenable shape by the linear entropy of the temporary.
Its proof is linear algebra plus a handful of one-variable inequalities;
those are the steps a reader is most likely to want checked, and they are
proved here.

* `sum_sq_le_max_mul_sum`: a state's purity `∑ λᵢ²` is at most its largest
  eigenvalue (the eigenvalues are nonnegative and sum to one);
* `sq_le_sum_sq`: the purity is at least the square of any eigenvalue;
* `one_sub_sqrt_le`: `1 - √(1 - x) ≤ x` on `[0, 1]`, the polar step;
* `sqrt_add_le_two_sqrt`: `√(3ε) + 3ε ≤ 2√(3ε)` exactly when `ε ≤ 1/3`,
  which is where the hypothesis of part (1) comes from;
* `one_sub_pow_four`: `(1 - δ)⁴ ≥ 1 - 4δ` on `[0, 1]`, the converse;
* `sq_one_sub_le`: `(1 - s)² ≤ 1 - s²` on `[0, 1]`, the Frobenius step of
  part (2).
-/

namespace Drop

open Finset

theorem sum_sq_le_max_mul_sum {ι : Type*} [Fintype ι] (l : ι → ℝ) (M : ℝ)
    (h0 : ∀ i, 0 ≤ l i) (hM : ∀ i, l i ≤ M) :
    ∑ i, l i ^ 2 ≤ M * ∑ i, l i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have := mul_le_mul_of_nonneg_right (hM i) (h0 i)
  nlinarith

theorem sq_le_sum_sq {ι : Type*} [Fintype ι] (l : ι → ℝ) (i₀ : ι) :
    l i₀ ^ 2 ≤ ∑ i, l i ^ 2 :=
  Finset.single_le_sum (fun i _ => sq_nonneg (l i)) (Finset.mem_univ i₀)

theorem one_sub_sqrt_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    1 - Real.sqrt (1 - x) ≤ x := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x by linarith)
  have hn := Real.sqrt_nonneg (1 - x)
  have hle : Real.sqrt (1 - x) ≤ 1 :=
    (Real.sqrt_le_left zero_le_one).2 (by nlinarith)
  nlinarith

theorem sqrt_add_le_two_sqrt {ε : ℝ} (h0 : 0 ≤ ε) :
    Real.sqrt (3 * ε) + 3 * ε ≤ 2 * Real.sqrt (3 * ε) ↔ ε ≤ 1 / 3 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 * ε by linarith)
  have hn := Real.sqrt_nonneg (3 * ε)
  constructor
  · intro h
    nlinarith
  · intro h
    have hle : Real.sqrt (3 * ε) ≤ 1 :=
      (Real.sqrt_le_left zero_le_one).2 (by nlinarith)
    nlinarith

theorem one_sub_pow_four (δ : ℝ) :
    1 - 4 * δ ≤ (1 - δ) ^ 4 := by
  have := mul_nonneg (sq_nonneg δ) (add_nonneg (sq_nonneg (δ - 2)) (zero_le_two (α := ℝ)))
  nlinarith

theorem sq_one_sub_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (1 - s) ^ 2 ≤ 1 - s ^ 2 := by
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]

end Drop
