import Drop.Gram

/-!
# The temporary's state at the maximally mixed input

Write the denotation as one matrix `joint K : H_m → H_d ⊗ H_m`, indexed by
pairs `(i, a)` with `i` the temporary index and `a` the visible one.
Tracing out the visible register of `joint K * (joint K)ᴴ` gives the Gram
matrix transposed: `Tr_v [K Kᴴ] = Γᵀ`.  Dividing by `m` this is the state
of the temporary when the visible register is fed the maximally mixed
state, the identity behind the swap test.
-/

namespace Drop

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜]
variable {d m : Type*} [Fintype d] [Fintype m]

/-- The denotation as a single matrix from the visible register to the joint
register. -/
def joint (K : d → Matrix m m 𝕜) : Matrix (d × m) m 𝕜 :=
  Matrix.of fun p b => K p.1 p.2 b

/-- The partial trace over the visible register. -/
def traceVisible (X : Matrix (d × m) (d × m) 𝕜) : Matrix d d 𝕜 :=
  Matrix.of fun i j => ∑ a, X (i, a) (j, a)

omit [Fintype d] in
theorem traceVisible_joint (K : d → Matrix m m 𝕜) :
    traceVisible (joint K * (joint K)ᴴ) = (gram K)ᵀ := by
  ext i j
  simp only [traceVisible, joint, gram, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end Drop
