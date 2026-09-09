import Drop.Dilation.Dilation

set_option autoImplicit false

/-!
# the bridge: discard-safe = mediator-erasable, and exactly why

Mediators preserve "all environment slices are parallel", and injective*
mediators reflect it — so over any base whose mediators are injective, "the environment can be
discarded" is literally "the completion added nothing", and the isometry base is such a base.*

One might suspect a crack — that the mediator preorder is direction-sensitive, since an
isometry `E → E'` needs `dim E ≤ dim E'` — does not bite, and the reason is worth one line:
*the bridge only ever needs the mediator to point the easy way*, from the unit object into the
environment.  The state `g` is itself the mediator `I → E`, and it always exists.

Two hypotheses on the mediator class carry everything:

* `MedClass.HasStates` — every unit vector is a mediator `I → E` (this gives
  discard-safe ⟹ erasable);
* `MedClass.Injective` — every mediator is injective (this gives erasable ⟹ discard-safe).

`Drop/Dilation/Falsifiers.lean` shows both are necessary, and that dropping the second
does not merely weaken the bridge but destroys the quotient.
-/

namespace Dilation

open Matrix SimpleTensor Circuit

variable {𝕜 : Type} [RCLike 𝕜] {α μ : Type} [Fintype α] [Fintype μ]

/-! ## The two properties of a mediator class -/

/-- The mediator that puts the environment in the state `g`: the column matrix `I → E`. -/
def stateMat {ι : Type} (g : EuclideanSpace 𝕜 ι) : Matrix ι Unit 𝕜 := fun i _ => g i

/-- *Every unit state is a mediator out of the unit object.* -/
def MedClass.HasStates (C : MedClass 𝕜) : Prop :=
  ∀ {ι : Type} [Fintype ι] (g : EuclideanSpace 𝕜 ι), ‖g‖ = 1 → C.mem (stateMat g)

/-- *Every mediator is injective on environment vectors.* -/
def MedClass.Injective (C : MedClass 𝕜) : Prop :=
  ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] (m : Matrix ι' ι 𝕜),
    C.mem m → Function.Injective (colAct m)

lemma isometries_injective : (isometries 𝕜).Injective :=
  fun _ hm => IsIsom.injective hm

lemma isometries_hasStates : (isometries 𝕜).HasStates := by
  intro ι _ g hg x y
  have hgg : ∑ i, g i * (starRingEnd 𝕜) (g i) = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (x := g)
    rw [PiLp.inner_apply] at h
    simp only [RCLike.inner_apply] at h
    rw [h, hg]; norm_num
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, colAct_apply, stateMat, Finset.univ_unique,
    Finset.sum_singleton]
  have key : ∀ i : ι, g i * y default * (starRingEnd 𝕜) (g i * x default)
      = (g i * (starRingEnd 𝕜) (g i)) * (y default * (starRingEnd 𝕜) (x default)) := by
    intro i; rw [map_mul]; ring
  rw [Finset.sum_congr rfl fun i _ => key i, ← Finset.sum_mul, hgg, one_mul]

/-- Which mediators reach the unit object — a sub-question, computed.  An
isometric mediator `E → I` exists only when the environment is at most a line, because an
isometry is injective and the unit object is one-dimensional.  So erasability can never be
obtained by *pushing a large environment down*; the only mediator available at the unit object
is a state `I → E`, pointing the other way.  This is the direction-sensitivity of the mediator
preorder, and it is what makes the bridge a theorem rather than a triviality. -/
theorem subsingleton_of_isom_to_unit {ι : Type} [Fintype ι] {m : Matrix Unit ι 𝕜}
    (h : IsIsom m) : Subsingleton ι := by
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := colAct (𝕜 := 𝕜) (ι := ι) (ι' := Unit) m) h.injective
  rw [finrank_euclideanSpace, finrank_euclideanSpace] at hle
  simp only [Fintype.card_unit] at hle
  exact Fintype.card_le_one_iff_subsingleton.mp hle

/-! ## `SliceRankLe1` is a mediator invariant -/

/-- Mediators preserve parallel slices — no hypothesis on the mediator at all. -/
lemma sliceRankLe1_of_step {C : MedClass 𝕜} {d e : Dil 𝕜 α μ} (hs : Step C d e)
    (hd : SliceRankLe1 d) : SliceRankLe1 e := by
  obtain ⟨m, -, hm⟩ := hs
  obtain ⟨g, hg⟩ := hd
  refine ⟨colAct m g, fun v b => ?_⟩
  obtain ⟨c, hc⟩ := hg v b
  refine ⟨c, ?_⟩
  rw [hm v, slice_envAct, hc, map_smul]

/-- Injective mediators reflect parallel slices. -/
lemma sliceRankLe1_of_step_rev {C : MedClass 𝕜} (hinj : C.Injective) {d e : Dil 𝕜 α μ}
    (hs : Step C d e) (he : SliceRankLe1 e) : SliceRankLe1 d := by
  obtain ⟨m, hmem, hm⟩ := hs
  obtain ⟨g', hg'⟩ := he
  have hi : Function.Injective (colAct m) := hinj m hmem
  by_cases hz : ∀ (v : EuclideanSpace 𝕜 α) (b : μ), slice (d.map v) b = 0
  · exact ⟨0, fun v b => ⟨0, by rw [hz v b]; simp⟩⟩
  · push_neg at hz
    obtain ⟨v₀, b₀, hv₀⟩ := hz
    obtain ⟨c₀, hc₀⟩ := hg' v₀ b₀
    have hkey : colAct m (slice (d.map v₀) b₀) = c₀ • g' := by
      rw [← slice_envAct, ← hm v₀]; exact hc₀
    have hc₀ne : c₀ ≠ 0 := by
      rintro rfl
      exact hv₀ (hi (by simpa using hkey))
    refine ⟨c₀⁻¹ • slice (d.map v₀) b₀, fun v b => ?_⟩
    obtain ⟨c, hc⟩ := hg' v b
    refine ⟨c, hi ?_⟩
    rw [map_smul, map_smul, hkey, smul_smul, smul_smul, ← slice_envAct, ← hm v, hc]
    congr 1
    field_simp

/-- `SliceRankLe1` is invariant under the completion's identification, when the mediators are
injective. -/
lemma sliceRankLe1_congr {C : MedClass 𝕜} (hinj : C.Injective) {d e : Dil 𝕜 α μ}
    (h : MedEq C d e) : SliceRankLe1 d ↔ SliceRankLe1 e := by
  induction h with
  | rel _ _ hxy => exact ⟨fun hx => sliceRankLe1_of_step hxy hx,
      fun hy => sliceRankLe1_of_step_rev hinj hxy hy⟩
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The unit of the completion -/

lemma sliceRankLe1_unitDil (W : EuclideanSpace 𝕜 α →ₗ[𝕜] EuclideanSpace 𝕜 μ) :
    SliceRankLe1 (unitDil W) := by
  refine ⟨WithLp.toLp 2 fun _ : Unit => (1 : 𝕜), fun v b => ⟨W v b, ?_⟩⟩
  ext i
  simp

/-! ## The bridge -/

/-- Discard-safe implies erasable — and this is the direction one might expect to
fail.  It does not: the required mediator is the state `g` itself, pointing from the unit
object into the environment, which is the direction an isometry may always point. -/
theorem erasable_of_productForm {C : MedClass 𝕜} (hst : C.HasStates) {d : Dil 𝕜 α μ}
    (h : ProductForm d) : Erasable C d := by
  obtain ⟨g, W, hg, hd⟩ := h
  refine ⟨W, Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨stateMat g, hst g hg, fun v => ?_⟩)⟩
  refine eq_of_slice_eq fun b => ?_
  rw [hd v, slice_tens, slice_envAct]
  ext i
  simp only [colAct_apply, slice_apply, unitDil_map_apply, stateMat, PiLp.smul_apply,
    smul_eq_mul, mul_comm]
  rw [Finset.sum_const, Finset.card_univ, show Fintype.card (unitDil W).env = 1 from rfl]
  simp

/-- Erasable implies parallel slices, for an injective mediator class. -/
theorem sliceRankLe1_of_erasable {C : MedClass 𝕜} (hinj : C.Injective) {d : Dil 𝕜 α μ}
    (h : Erasable C d) : SliceRankLe1 d := by
  obtain ⟨W, hW⟩ := h
  exact (sliceRankLe1_congr hinj hW).mpr (sliceRankLe1_unitDil W)

/-- The bridge.  *Over a mediator class that contains the states and consists of injective
maps, a dilation with a nonempty environment is discard-safe exactly when the completion has
added nothing to it.*  The nonemptiness hypothesis is exactly sharp: see
`Dilation.erasable_not_productForm_of_empty_env`. -/
theorem productForm_iff_erasable {C : MedClass 𝕜} (hst : C.HasStates) (hinj : C.Injective)
    {d : Dil 𝕜 α μ} [Nonempty d.env] [DecidableEq d.env] :
    ProductForm d ↔ Erasable C d :=
  ⟨erasable_of_productForm hst, fun h => productForm_of_sliceRankLe1 (sliceRankLe1_of_erasable hinj h)⟩

/-- The bridge over the isometry base — the statement in its final form, with the base
`R[Unitary] ≃ Isometry` fixed. -/
theorem productForm_iff_erasable_isometries {d : Dil 𝕜 α μ} [Nonempty d.env]
    [DecidableEq d.env] : ProductForm d ↔ Erasable (isometries 𝕜) d :=
  productForm_iff_erasable isometries_hasStates isometries_injective

end Dilation
