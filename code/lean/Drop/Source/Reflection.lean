import Drop.Source.Gates
import Drop.Source.Safety

/-!
# Two facts the reflection step needs

* `unitary_of_norm_act` — a matrix that acts by an isometry on a finite
  register is unitary (the converse of `norm_act_of_unitary`), so the visible
  map of a safe well-typed program is a legal gate (`unitary_of_discardSafe`).
* `reflectionTo i₀ g` — the Householder reflection through the hyperplane
  orthogonal to `e_{i₀} − g`. It is orthogonal (`reflectionTo_unitary`) and
  carries the allocated basis state `e_{i₀}` to the unit vector `g`
  (`act_reflectionTo_single`); when `g = e_{i₀}` the axis is zero and the
  formula degenerates, correctly, to the identity. This is the one gate that
  prepares an arbitrary final state of the temporary, step ⟨3⟩ of the
  criterion's proof.
-/

namespace SourceLanguage

open Matrix Circuit SimpleTensor

variable {𝕜 : Type*} [RCLike 𝕜] {ι μ : Type*}
  [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-- The action of a matrix on the visible register, as a linear map. -/
noncomputable def actLM (W : Matrix μ μ 𝕜) :
    EuclideanSpace 𝕜 μ →ₗ[𝕜] EuclideanSpace 𝕜 μ where
  toFun v := act W v
  map_add' u v := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext j; simp [Finset.mul_sum, mul_left_comm]

omit [DecidableEq μ] in
@[simp] lemma actLM_apply (W : Matrix μ μ 𝕜) (v : EuclideanSpace 𝕜 μ) : actLM W v = act W v := rfl

/-- A matrix that acts by an isometry is unitary.  The converse of
`SourceLanguage.norm_act_of_unitary`; over any `RCLike` field and any finite
register.  The proof is polarisation followed by reading off the matrix entry
`(Wᴴ W) k l = ⟪W eₖ, W eₗ⟫`. -/
theorem unitary_of_norm_act {W : Matrix μ μ 𝕜} (h : ∀ v, ‖act W v‖ = ‖v‖) : Wᴴ * W = 1 := by
  have hinner := (LinearMap.norm_map_iff_inner_map_map (𝕜 := 𝕜) (actLM W)).1 (by simpa using h)
  ext k l
  have hkl := hinner (EuclideanSpace.single k (1 : 𝕜)) (EuclideanSpace.single l (1 : 𝕜))
  rw [PiLp.inner_apply, PiLp.inner_apply] at hkl
  simp only [RCLike.inner_apply', actLM_apply, act_apply, EuclideanSpace.single_apply] at hkl
  have hL : ∀ j : μ, ∑ m, W j m * (if m = k then (1 : 𝕜) else 0) = W j k := by
    intro j; simp
  have hL' : ∀ j : μ, ∑ m, W j m * (if m = l then (1 : 𝕜) else 0) = W j l := by
    intro j; simp
  simp only [hL, hL'] at hkl
  have hRHS : ∑ j : μ, (starRingEnd 𝕜) (if j = k then (1 : 𝕜) else 0)
      * (if j = l then (1 : 𝕜) else 0) = if k = l then (1 : 𝕜) else 0 := by
    by_cases hkl' : k = l
    · subst hkl'; simp
    · rw [if_neg hkl']
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases eq_or_ne j k with rfl | h1
      · simp [hkl']
      · simp [h1]
  rw [hRHS] at hkl
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa only [conjTranspose_apply, RCLike.star_def] using hkl

/-- The visible map of an exactly-safe well-typed program is unitary. -/
theorem unitary_of_discardSafe {i₀ : ι} {p : Body 𝕜 ι μ} (hp : p.WellTyped)
    {g : EuclideanSpace 𝕜 ι} {W : Matrix μ μ 𝕜} (hg : ‖g‖ = 1)
    (hv : ∀ v, denote i₀ p v = tens g (act W v)) : Wᴴ * W = 1 := by
  refine unitary_of_norm_act fun v => ?_
  have h1 : ‖tens g (act W v)‖ = ‖v‖ := by rw [← hv v]; exact norm_denote hp v
  rw [norm_tens, hg, one_mul] at h1
  exact h1

section Householder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `e_{i₀} - g`, in coordinates. -/
def reflAxis (i₀ : ι) (g : EuclideanSpace ℝ ι) : ι → ℝ :=
  fun i => (if i = i₀ then 1 else 0) - g i

/-- The Householder reflection exchanging `e_{i₀}` and the unit vector `g`.
When `g = e_{i₀}` the axis is zero and the formula degenerates — correctly — to
the identity, because in Lean division by zero is zero. -/
noncomputable def reflectionTo (i₀ : ι) (g : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) -
    2 * reflAxis i₀ g i * reflAxis i₀ g j / ∑ k, reflAxis i₀ g k ^ 2

omit [DecidableEq ι] in
lemma sum_sq_of_norm_one' {g : EuclideanSpace ℝ ι} (hg : ‖g‖ = 1) : ∑ k, g k ^ 2 = 1 := by
  have h := congrArg (fun t : ℝ => t ^ 2) hg
  simp only [EuclideanSpace.norm_eq, one_pow] at h
  rw [Real.sq_sqrt (by positivity)] at h
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- The squared length of the axis, in terms of the `i₀`-th coordinate of `g`. -/
lemma sum_reflAxis_sq {i₀ : ι} {g : EuclideanSpace ℝ ι} (hg : ‖g‖ = 1) :
    ∑ k, reflAxis i₀ g k ^ 2 = 2 - 2 * g i₀ := by
  have hg2 := sum_sq_of_norm_one' hg
  have hexp : ∀ k, reflAxis i₀ g k ^ 2
      = (if k = i₀ then (1:ℝ) else 0) - 2 * (if k = i₀ then g k else 0) + g k ^ 2 := by
    intro k
    by_cases h : k = i₀
    · simp [reflAxis, h]
      ring
    · simp [reflAxis, h]
  rw [Finset.sum_congr rfl fun k _ => hexp k]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [hg2]
  ring

/-- The reflection is orthogonal.  Write `H = I - 2 a aᵀ / c` for the axis `a = reflAxis i₀ g`
and `c = ‖a‖²`; expanding `(HᴴH)_{ij}` as a sum over `k` splits it into four pieces — the
identity term, two cross terms linear in `a`, and one quadratic term — and the cross and
quadratic terms cancel exactly, whether or not `c = 0`. -/
lemma reflectionTo_unitary (i₀ : ι) (g : EuclideanSpace ℝ ι) :
    (reflectionTo i₀ g)ᴴ * reflectionTo i₀ g = 1 := by
  set a : ι → ℝ := reflAxis i₀ g with ha
  set c : ℝ := ∑ k, a k ^ 2 with hc
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  -- Expand the `k`-th summand of `(HᴴH)_{ij}` from the definition of `H`.
  have hexpand : ∀ k : ι,
      (reflectionTo i₀ g)ᴴ i k * reflectionTo i₀ g k j
        = (if k = i then (1:ℝ) else 0) * (if k = j then 1 else 0)
          - (if k = i then (1:ℝ) else 0) * (2 * a k * a j / c)
          - (2 * a k * a i / c) * (if k = j then (1:ℝ) else 0)
          + (2 * a k * a i / c) * (2 * a k * a j / c) := by
    intro k
    simp only [conjTranspose_apply, star_trivial, reflectionTo, Matrix.of_apply, ← ha, ← hc]
    ring
  rw [Finset.sum_congr rfl fun k _ => hexpand k]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- The identity term sums to the Kronecker delta.
  have hdiag : ∑ k : ι, (if k = i then (1:ℝ) else 0) * (if k = j then 1 else 0)
      = if i = j then (1:ℝ) else 0 := by
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases eq_or_ne k i with rfl | hk
      · simp [h]
      · simp [hk]
  -- The two cross terms, each concentrated at a single index `k = i` resp. `k = j`.
  have hcross_left : ∑ k : ι, (if k = i then (1:ℝ) else 0) * (2 * a k * a j / c)
      = 2 * a i * a j / c := by
    rw [Finset.sum_eq_single i] <;> simp +contextual
  have hcross_right : ∑ k : ι, (2 * a k * a i / c) * (if k = j then (1:ℝ) else 0)
      = 2 * a j * a i / c := by
    rw [Finset.sum_eq_single j] <;> simp +contextual
  -- The quadratic term collapses to `c` itself via `∑ k, a k ^ 2 = c`.
  have hquad : ∑ k : ι, (2 * a k * a i / c) * (2 * a k * a j / c)
      = 4 * a i * a j * c / c ^ 2 := by
    have : ∀ k : ι, (2 * a k * a i / c) * (2 * a k * a j / c)
        = (4 * a i * a j / c ^ 2) * a k ^ 2 := by intro k; field_simp; ring
    rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.mul_sum, ← hc]
    ring
  rw [hdiag, hcross_left, hcross_right, hquad]
  -- The remaining algebraic identity holds whether `c = 0` (axis is zero) or `c ≠ 0`.
  rcases eq_or_ne c 0 with hc0 | hc0
  · have haxis_zero : ∀ k, a k = 0 := by
      intro k
      have hsum : ∑ k, a k ^ 2 = 0 := hc0
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a k))).1 hsum k
        (Finset.mem_univ k)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simp [haxis_zero]
  · field_simp
    ring

/-- The reflection carries the allocated basis state to `g`.  Reading off row `i` of the
reflection acting on `e_{i₀}` leaves one column, with denominator `2 - 2 g_{i₀}`.  When
`g_{i₀} = 1` the axis is entirely zero (`‖g‖ = 1` forces every other coordinate to vanish too),
so the fraction is `0` regardless of the denominator and the formula reads off `g` itself; when
`g_{i₀} ≠ 1` the denominator is nonzero and the fraction cancels algebraically. -/
lemma act_reflectionTo_single {i₀ : ι} {g : EuclideanSpace ℝ ι} (hg : ‖g‖ = 1) :
    act (reflectionTo i₀ g) (EuclideanSpace.single i₀ (1 : ℝ)) = g := by
  have hcsum := sum_reflAxis_sq (i₀ := i₀) hg
  -- Only the `k = i₀` summand of the matrix-vector product survives.
  have hcolumn : ∀ i, act (reflectionTo i₀ g) (EuclideanSpace.single i₀ (1 : ℝ)) i
      = (if i = i₀ then (1:ℝ) else 0) - 2 * reflAxis i₀ g i * reflAxis i₀ g i₀ / (2 - 2 * g i₀) := by
    intro i
    rw [act_apply]
    rw [Finset.sum_eq_single i₀ (by intro b _ hb; simp [EuclideanSpace.single_apply, hb])
      (by simp)]
    simp [EuclideanSpace.single_apply, reflectionTo, Matrix.of_apply, hcsum]
  ext i
  rw [hcolumn]
  rcases eq_or_ne (g i₀) 1 with hextreme | hgeneric
  · -- Extremal case: `g i₀ = 1` forces the whole axis to vanish, hence `g` is `e_{i₀}` itself.
    have haxis_zero : ∀ k, reflAxis i₀ g k = 0 := by
      have hg2 := sum_sq_of_norm_one' hg
      have hrest : ∑ k, (if k = i₀ then (0:ℝ) else g k ^ 2) = 0 := by
        have hsplit : ∑ k, g k ^ 2 = g i₀ ^ 2 + ∑ k, (if k = i₀ then (0:ℝ) else g k ^ 2) := by
          rw [Finset.sum_congr rfl (fun k _ => by
            by_cases hk : k = i₀ <;> simp [hk] : ∀ k ∈ Finset.univ,
              g k ^ 2 = (if k = i₀ then g k ^ 2 else 0) + (if k = i₀ then (0:ℝ) else g k ^ 2))]
          rw [Finset.sum_add_distrib]
          simp
        rw [hg2, hextreme] at hsplit
        linarith [hsplit]
      intro k
      by_cases hk : k = i₀
      · simp [reflAxis, hk, hextreme]
      · have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
          by_cases h : k = i₀
          · simp [h]
          · simpa [h] using sq_nonneg (g k))).1 hrest k (Finset.mem_univ k)
        rw [if_neg hk] at this
        have hgk : g k = 0 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
          exact this
        simp [reflAxis, hk, hgk]
    have hg_eq_basis : g i = if i = i₀ then 1 else 0 := by
      have := haxis_zero i
      simp only [reflAxis, sub_eq_zero] at this
      exact this.symm
    by_cases h : i = i₀ <;> simp [h, hg_eq_basis, reflAxis, hextreme]
  · -- Generic case: the denominator `2 - 2 g_{i₀}` is nonzero, and the fraction cancels.
    have hdenom_ne : (2 : ℝ) - 2 * g i₀ ≠ 0 := fun h0 => hgeneric (by linarith)
    have haxis_i0 : reflAxis i₀ g i₀ = 1 - g i₀ := by simp [reflAxis]
    have hcancel : 2 * reflAxis i₀ g i * (1 - g i₀) / (2 - 2 * g i₀) = reflAxis i₀ g i := by
      rw [show (2 : ℝ) - 2 * g i₀ = 2 * (1 - g i₀) by ring]
      field_simp [sub_ne_zero.mpr (Ne.symm hgeneric)]
    rw [haxis_i0, hcancel]
    simp [reflAxis]

end Householder

end SourceLanguage
