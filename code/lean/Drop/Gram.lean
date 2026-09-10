import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic

/-!
# The Gram matrix of a drop

A program with one temporary of dimension `d` and a visible register of
dimension `m` denotes an isometry `K : H_m → H_d ⊗ H_m`.  Its Kraus
operators are the `d` blocks `K i : H_m → H_m`, and its Gram matrix is
`Γ i j = tr ((K i)ᴴ * K j)`.

The drop is safe exactly when the blocks are collinear, `K i = g i • W`
for one vector `g` on the temporary and one matrix `W` on the visible
register (the weakenable shape).  This file proves the two identities the
checker relies on in that case:

* `gram_apply_of_collinear`: `Γ i j = star (g i) * g j * tr (Wᴴ * W)`, so
  `Γ` has rank at most one; and
* `gram_sq_of_collinear`: `Γ * Γ = tr Γ • Γ`, the single matrix identity
  equivalent to the rank the checker computes.

The converse (the identity forces collinearity) uses that `Γ` is positive
semidefinite and is checked, on every catalogue program, by the Haskell
suite rather than proved here.
-/

namespace Drop

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜]
variable {d m : Type*} [Fintype d] [Fintype m]

/-- The Gram matrix of a family of Kraus operators. -/
def gram (K : d → Matrix m m 𝕜) : Matrix d d 𝕜 :=
  Matrix.of fun i j => Matrix.trace ((K i)ᴴ * K j)

/-- The weakenable shape: every Kraus operator is a multiple of one matrix. -/
def Collinear (K : d → Matrix m m 𝕜) : Prop :=
  ∃ (g : d → 𝕜) (W : Matrix m m 𝕜), ∀ i, K i = g i • W

omit [Fintype d] in
theorem gram_apply (K : d → Matrix m m 𝕜) (i j : d) :
    gram K i j = Matrix.trace ((K i)ᴴ * K j) := rfl

omit [Fintype d] in
theorem gram_apply_of_collinear (g : d → 𝕜) (W : Matrix m m 𝕜) (i j : d) :
    gram (fun i => g i • W) i j = star (g i) * g j * Matrix.trace (Wᴴ * W) := by
  simp only [gram_apply, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  ring

/-- For a collinear family the Gram matrix satisfies `Γ * Γ = tr Γ • Γ`. -/
theorem gram_sq_of_collinear (g : d → 𝕜) (W : Matrix m m 𝕜) :
    gram (fun i => g i • W) * gram (fun i => g i • W)
      = Matrix.trace (gram (fun i => g i • W)) • gram (fun i => g i • W) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag,
    gram_apply_of_collinear, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The same identity, stated for any family of the weakenable shape. -/
theorem gram_sq (K : d → Matrix m m 𝕜) (h : Collinear K) :
    gram K * gram K = Matrix.trace (gram K) • gram K := by
  obtain ⟨g, W, hK⟩ := h
  have : K = fun i => g i • W := funext hK
  subst this
  exact gram_sq_of_collinear g W

end Drop
