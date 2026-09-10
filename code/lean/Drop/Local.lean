import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Local procedures

A procedure is local when its denotation is `A ⊗ B`, one matrix on the
temporary and one on the visible register.  Two facts about them:

* `local_comp`: the composite of two local procedures is local, with
  temporary summary `A₂ * A₁`; and
* `local_mulVec`: a local procedure carries the product input `s ⊗ v` to
  the product `(A s) ⊗ (B v)`, so after any sequence of local calls the
  temporary is in the state `A s`, whatever the visible input.
-/

namespace Drop

open Matrix Kronecker

variable {𝕜 : Type*} [CommRing 𝕜]
variable {d m : Type*} [Fintype d] [Fintype m]

theorem local_comp (A₁ A₂ : Matrix d d 𝕜) (B₁ B₂ : Matrix m m 𝕜) :
    (A₂ ⊗ₖ B₂) * (A₁ ⊗ₖ B₁) = (A₂ * A₁) ⊗ₖ (B₂ * B₁) :=
  (Matrix.mul_kronecker_mul A₂ A₁ B₂ B₁).symm

/-- The product vector `s ⊗ v`. -/
def tensor (s : d → 𝕜) (v : m → 𝕜) : d × m → 𝕜 := fun p => s p.1 * v p.2

theorem local_mulVec (A : Matrix d d 𝕜) (B : Matrix m m 𝕜) (s : d → 𝕜) (v : m → 𝕜) :
    (A ⊗ₖ B) *ᵥ tensor s v = tensor (A *ᵥ s) (B *ᵥ v) := by
  ext ⟨i, a⟩
  simp only [Matrix.mulVec, dotProduct, tensor, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Drop
