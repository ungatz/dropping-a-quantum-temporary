import Drop.Source.Language

/-!
# Drop safety, stated about programs

`DiscardSafe i₀ p` is drop safety: the fragment
`alloc i₀ ; p` leaves the temporary in one fixed unit state `g`, whatever the
visible input, and acts on the visible register by one fixed map `W`.

`discardSafe_iff_temporary_fixed` is the reading used to decide it:
the drop is safe exactly when the temporary always ends in one and the same
state, and then the visible map left behind is post-selection of the output on
that state. The proof consumes no typing hypothesis: the exact test does not
need the gates to be unitary.
-/

namespace SourceLanguage

open Matrix Circuit SimpleTensor

variable {𝕜 : Type*} [RCLike 𝕜] {ι μ : Type*}
  [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-- The exact promise: the temporary ends in a fixed state and the visible
register receives a fixed map. -/
def DiscardSafe (i₀ : ι) (p : Body 𝕜 ι μ) : Prop :=
  ∃ (g : EuclideanSpace 𝕜 ι) (W : Matrix μ μ 𝕜), ‖g‖ = 1 ∧
    ∀ v, denote i₀ p v = tens g (act W v)

omit [DecidableEq ι] [DecidableEq μ] in
/-- A product of a fixed temporary state with a fixed visible map is the output
map of the disposable compute side it names. -/
lemma tens_act_eq_outLM (g : EuclideanSpace 𝕜 ι) (W : Matrix μ μ 𝕜) (v : EuclideanSpace 𝕜 μ) :
    tens g (act W v) = outLM (fun i => g i • W) v := by
  ext q
  simp [Finset.mul_sum, mul_assoc]

/-- The exact test, in program language.

the temporary of a well-typed fragment may be discarded exactly
when it always ends in one and the same state, whatever the input — and then
the visible map left behind is post-selection of the output on that state.

No subspace appears, and — worth recording — the proof consumes no typing
hypothesis at all: the exact test does not need the gates to be unitary. -/
theorem discardSafe_iff_temporary_fixed {i₀ : ι} {p : Body 𝕜 ι μ} :
    DiscardSafe i₀ p ↔
      ∃ g : EuclideanSpace 𝕜 ι, ‖g‖ = 1 ∧
        ∀ v, denote i₀ p v = tens g (contractL g (denote i₀ p v)) := by
  constructor
  · rintro ⟨g, W, hg, hv⟩
    refine ⟨g, hg, fun v => ?_⟩
    have hps : postSel g (fun i => g i • W) = W := by
      have hnorm : ∑ i, (starRingEnd 𝕜) (g i) * g i = 1 := by
        have h := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) g
        rw [PiLp.inner_apply] at h
        rw [show (∑ i, (starRingEnd 𝕜) (g i) * g i) = ∑ i, (inner 𝕜 (g i) (g i) : 𝕜) from
          Finset.sum_congr rfl fun i _ => by rw [RCLike.inner_apply'], h, hg]
        norm_num
      rw [postSel]
      rw [show (∑ i, (starRingEnd 𝕜) (g i) • (g i • W)) = (∑ i, (starRingEnd 𝕜) (g i) * g i) • W by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun i _ => by rw [smul_smul], hnorm,
        one_smul]
    rw [hv v, tens_act_eq_outLM, tens_contractL_outLM, hps]
  · rintro ⟨g, hg, hv⟩
    refine ⟨g, postSel g (computeSide i₀ p), hg, fun v => ?_⟩
    calc denote i₀ p v = tens g (contractL g (denote i₀ p v)) := hv v
      _ = tens g (act (postSel g (computeSide i₀ p)) v) := by
          rw [denote_eq_outLM_computeSide, contractL_outLM]

end SourceLanguage
