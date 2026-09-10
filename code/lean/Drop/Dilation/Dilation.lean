import Drop.Source.Safety

set_option autoImplicit false

/-!
# dilations, mediators, and the erasability predicate

A dilation is a map into `environment ⊗ visible`; a mediator moves the
environment; and the question is whether "the environment can be discarded"
survives the quotient by mediators.

This file sets up, over an arbitrary finite-dimensional `RCLike` base, the hom-set data of the
`L`-completion of a base category of linear maps: a morphism `α → μ` is a pair `(E, f)` with
`f : α → E ⊗ μ`, and two pairs are identified when a mediator relates them.  The mediator
class is a parameter (`MedClass`), so that the same theorems can be read over the isometries —
the base `R[Unitary] ≃ Isometry` of the quantum-information-effects stack — and over the
contractions, which is what selected (subnormalised) branches force.

The four predicates:

* `ProductForm d` — the concrete "discard-safe" shape: `d.map v = g ⊗ W v` for a unit vector
  `g` and a fixed map `W`.  This is `SourceLanguage.DiscardSafe` with the register data
  abstracted away.
* `SliceRankLe1 d` — *all environment slices of `d` are parallel*: the same thing with the unit
  norm dropped.  This is the mediator-invariant one.
* `Erasable C d` — `d` is identified, in the mediator quotient, with a dilation whose
  environment is the unit object.  This is "lands in the image of the unit of the completion".
* `chan d` — the environment-traced form `⟪slice v b', slice u b⟫`.  Invariant under isometric
  mediators, and the tool that proves dilations inequivalent.

Nothing here is quantum-specific: `𝕜` is any `RCLike` field and the registers are finite types.
-/

namespace Dilation

open Matrix SimpleTensor Circuit

variable {𝕜 : Type} [RCLike 𝕜]

/-! ## Slices of a joint vector -/

section Slices

variable {ι ι' μ : Type} [Fintype ι] [Fintype ι'] [Fintype μ]

/-- The `b`-th environment slice of a joint vector: the environment vector obtained by
fixing the visible index. -/
noncomputable def slice (x : EuclideanSpace 𝕜 (ι × μ)) (b : μ) : EuclideanSpace 𝕜 ι :=
  WithLp.toLp 2 fun i => x (i, b)

omit [RCLike 𝕜] [Fintype ι] [Fintype μ] in
@[simp] lemma slice_apply (x : EuclideanSpace 𝕜 (ι × μ)) (b : μ) (i : ι) :
    slice x b i = x (i, b) := rfl

omit [RCLike 𝕜] [Fintype ι] [Fintype μ] in
/-- A joint vector is determined by its slices. -/
lemma eq_of_slice_eq {x y : EuclideanSpace 𝕜 (ι × μ)} (h : ∀ b, slice x b = slice y b) :
    x = y := by
  ext p
  exact congrArg (fun z : EuclideanSpace 𝕜 ι => z p.1) (h p.2)

omit [Fintype ι] [Fintype μ] in
@[simp] lemma slice_zero (b : μ) : slice (0 : EuclideanSpace 𝕜 (ι × μ)) b = 0 := by
  ext i; simp

@[simp] lemma slice_add (x y : EuclideanSpace 𝕜 (ι × μ)) (b : μ) :
    slice (x + y) b = slice x b + slice y b := by
  ext i; simp

omit [Fintype ι] [Fintype μ] in
@[simp] lemma slice_smul (c : 𝕜) (x : EuclideanSpace 𝕜 (ι × μ)) (b : μ) :
    slice (c • x) b = c • slice x b := by
  ext i; simp

omit [Fintype ι] [Fintype μ] in
/-- The slices of a simple tensor are all parallel to its environment factor. -/
@[simp] lemma slice_tens (g : EuclideanSpace 𝕜 ι) (w : EuclideanSpace 𝕜 μ) (b : μ) :
    slice (tens g w) b = w b • g := by
  ext i; simp [mul_comm]

end Slices

/-! ## Mediators -/

section Mediators

variable {ι ι' μ : Type} [Fintype ι] [Fintype ι'] [Fintype μ]

/-- A mediator matrix acting on environment vectors. -/
noncomputable def colAct (m : Matrix ι' ι 𝕜) :
    EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι' where
  toFun x := WithLp.toLp 2 fun i' => ∑ i, m i' i * x i
  map_add' x y := by ext i'; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext i'; simp [Finset.mul_sum, mul_left_comm]

@[simp] lemma colAct_apply (m : Matrix ι' ι 𝕜) (x : EuclideanSpace 𝕜 ι) (i' : ι') :
    colAct m x i' = ∑ i, m i' i * x i := rfl

/-- A mediator matrix acting on the environment factor of a joint vector. -/
noncomputable def envAct (m : Matrix ι' ι 𝕜) :
    EuclideanSpace 𝕜 (ι × μ) →ₗ[𝕜] EuclideanSpace 𝕜 (ι' × μ) where
  toFun x := WithLp.toLp 2 fun p => ∑ i, m p.1 i * x (i, p.2)
  map_add' x y := by ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext p; simp [Finset.mul_sum, mul_left_comm]

@[simp] lemma envAct_apply (m : Matrix ι' ι 𝕜) (x : EuclideanSpace 𝕜 (ι × μ)) (p : ι' × μ) :
    envAct (μ := μ) m x p = ∑ i, m p.1 i * x (i, p.2) := rfl

/-- Mediation is slicewise.  The whole file rests on this one line: moving the environment
of a joint vector is moving each of its slices. -/
@[simp] lemma slice_envAct (m : Matrix ι' ι 𝕜) (x : EuclideanSpace 𝕜 (ι × μ)) (b : μ) :
    slice (envAct (μ := μ) m x) b = colAct m (slice x b) := by
  ext i'; simp

@[simp] lemma colAct_zero : colAct (0 : Matrix ι' ι 𝕜) = 0 := by
  ext x i'; simp

@[simp] lemma envAct_zero : envAct (μ := μ) (0 : Matrix ι' ι 𝕜) = 0 := by
  ext x p; simp

/-- An isometric mediator: it preserves the inner product of environment vectors. -/
def IsIsom (m : Matrix ι' ι 𝕜) : Prop :=
  ∀ x y : EuclideanSpace 𝕜 ι, inner 𝕜 (colAct m x) (colAct m y) = (inner 𝕜 x y : 𝕜)

/-- A contractive mediator. -/
def IsContraction (m : Matrix ι' ι 𝕜) : Prop :=
  ∀ x : EuclideanSpace 𝕜 ι, ‖colAct m x‖ ≤ ‖x‖

lemma IsIsom.injective {m : Matrix ι' ι 𝕜} (h : IsIsom m) : Function.Injective (colAct m) := by
  intro x y hxy
  have h0 : (inner 𝕜 (x - y) (x - y) : 𝕜) = 0 := by
    rw [← h]
    simp [map_sub, hxy]
  exact sub_eq_zero.mp (inner_self_eq_zero (𝕜 := 𝕜) (x := x - y) |>.mp h0)

lemma IsIsom.norm_map {m : Matrix ι' ι 𝕜} (h : IsIsom m) (x : EuclideanSpace 𝕜 ι) :
    ‖colAct m x‖ = ‖x‖ := by
  have h1 : (inner 𝕜 (colAct m x) (colAct m x) : 𝕜) = inner 𝕜 x x := h x x
  have h2 : ‖colAct m x‖ ^ 2 = ‖x‖ ^ 2 := by
    have hx := @inner_self_eq_norm_sq 𝕜 _ _ _ _ (colAct m x)
    have hy := @inner_self_eq_norm_sq 𝕜 _ _ _ _ x
    have := congrArg (RCLike.re (K := 𝕜)) h1
    rw [hx, hy] at this
    linarith
  nlinarith [norm_nonneg (colAct m x), norm_nonneg x]

lemma IsIsom.isContraction {m : Matrix ι' ι 𝕜} (h : IsIsom m) : IsContraction m :=
  fun x => le_of_eq (h.norm_map x)

end Mediators

/-! ## Dilations, mediator classes, and the completion's identification -/

variable {α μ : Type} [Fintype α] [Fintype μ]

/-- A dilation of a map `α → μ`: a finite environment together with a linear map into
`environment ⊗ visible`.  This is a morphism of the `L`-completion before the quotient. -/
structure Dil (𝕜 : Type) [RCLike 𝕜] (α μ : Type) [Fintype α] [Fintype μ] where
  /-- the auxiliary (environment) register -/
  env : Type
  [envFintype : Fintype env]
  /-- the map into environment ⊗ visible -/
  map : EuclideanSpace 𝕜 α →ₗ[𝕜] EuclideanSpace 𝕜 (env × μ)

attribute [instance] Dil.envFintype

/-- A mediator class: which matrices are allowed to move an environment.  Over the base
`Isometry` this is `IsIsom`; over a base that admits subnormalised branches it is
`IsContraction`. -/
structure MedClass (𝕜 : Type) [RCLike 𝕜] where
  /-- the allowed mediator matrices -/
  mem : ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'], Matrix ι' ι 𝕜 → Prop

/-- The isometric mediator class — the one the `L`-completion over `Isometry` uses. -/
def isometries (𝕜 : Type) [RCLike 𝕜] : MedClass 𝕜 := ⟨fun {_ _} _ _ m => IsIsom m⟩

/-- The contractive mediator class. -/
def contractions (𝕜 : Type) [RCLike 𝕜] : MedClass 𝕜 := ⟨fun {_ _} _ _ m => IsContraction m⟩

/-- One mediation step: `e` is `d` with its environment pushed along a mediator of the class. -/
def Step (C : MedClass 𝕜) (d e : Dil 𝕜 α μ) : Prop :=
  ∃ m : Matrix e.env d.env 𝕜, C.mem m ∧ ∀ v, e.map v = envAct m (d.map v)

/-- The identification made by the completion: the equivalence generated by mediation. -/
def MedEq (C : MedClass 𝕜) (d e : Dil 𝕜 α μ) : Prop := Relation.EqvGen (Step C) d e

/-- The dilation with trivial environment attached to a map `W` — the unit `ε` of the
completion. -/
noncomputable def unitDil (W : EuclideanSpace 𝕜 α →ₗ[𝕜] EuclideanSpace 𝕜 μ) : Dil 𝕜 α μ where
  env := Unit
  map :=
    { toFun := fun v => WithLp.toLp 2 fun p => W v p.2
      map_add' := fun u v => by ext p; simp
      map_smul' := fun c v => by ext p; simp }

@[simp] lemma unitDil_map_apply (W : EuclideanSpace 𝕜 α →ₗ[𝕜] EuclideanSpace 𝕜 μ)
    (v : EuclideanSpace 𝕜 α) (p : Unit × μ) : (unitDil W).map v p = W v p.2 := rfl

/-- Mediator-erasable: identified by the completion with a dilation of trivial
environment, i.e. *lands in the image of the unit `ε`*. -/
def Erasable (C : MedClass 𝕜) (d : Dil 𝕜 α μ) : Prop :=
  ∃ W : EuclideanSpace 𝕜 α →ₗ[𝕜] EuclideanSpace 𝕜 μ, MedEq C d (unitDil W)

/-! ## The two shapes of "discard-safe" -/

/-- Discard-safe, concretely: the environment ends in one fixed *unit* state and the
visible register receives one fixed map.  This is `SourceLanguage.DiscardSafe`. -/
def ProductForm (d : Dil 𝕜 α μ) : Prop :=
  ∃ (g : EuclideanSpace 𝕜 d.env) (W : EuclideanSpace 𝕜 α →ₗ[𝕜] EuclideanSpace 𝕜 μ),
    ‖g‖ = 1 ∧ ∀ v, d.map v = tens g (W v)

/-- All slices parallel — discard-safety with the unit-norm clause dropped.  This is the
mediator-invariant form. -/
def SliceRankLe1 (d : Dil 𝕜 α μ) : Prop :=
  ∃ g : EuclideanSpace 𝕜 d.env, ∀ (v : EuclideanSpace 𝕜 α) (b : μ),
    ∃ c : 𝕜, slice (d.map v) b = c • g

lemma sliceRankLe1_of_productForm {d : Dil 𝕜 α μ} (h : ProductForm d) : SliceRankLe1 d := by
  obtain ⟨g, W, -, hd⟩ := h
  exact ⟨g, fun v b => ⟨W v b, by rw [hd v, slice_tens]⟩⟩

/-- The two shapes agree as soon as the environment is nonempty; the *only* gap between them
is the empty environment, where a unit vector does not exist.  If every slice is literally zero,
any unit vector serves as the environment factor and the visible map is `0`.  Otherwise the
common direction `g` witnessing `SliceRankLe1` is itself nonzero, so `gh = g / ‖g‖` is a unit
vector; taking the visible map to be `v ↦ ⟪gh, slice (d.map v)⟫` reconstructs each slice, because
the scalar `c` with `slice (d.map v) b = c • g` satisfies `⟪gh, c • g⟫ = c * ‖g‖`. -/
lemma productForm_of_sliceRankLe1 {d : Dil 𝕜 α μ} [Nonempty d.env] [DecidableEq d.env]
    (h : SliceRankLe1 d) : ProductForm d := by
  obtain ⟨g, hg⟩ := h
  by_cases hz : ∀ (v : EuclideanSpace 𝕜 α) (b : μ), slice (d.map v) b = 0
  · -- Degenerate case: no slice carries any information, so any unit vector will do.
    refine ⟨EuclideanSpace.single (Classical.arbitrary d.env) (1 : 𝕜), 0, by simp, fun v => ?_⟩
    refine eq_of_slice_eq fun b => ?_
    rw [hz v b, slice_tens]
    simp
  · push_neg at hz
    obtain ⟨v₀, b₀, hv₀⟩ := hz
    -- The common direction `g` is nonzero: some slice along it is nonzero.
    have hg_ne : g ≠ 0 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hg v₀ b₀
      exact hv₀ (by simpa using hc)
    have hnorm_ne : ‖g‖ ≠ 0 := fun h => hg_ne (norm_eq_zero.mp h)
    -- Normalise `g` to a unit vector `gh = r⁻¹ • g`, `r = ‖g‖` viewed in `𝕜`.
    set r : 𝕜 := ((‖g‖ : ℝ) : 𝕜) with hr
    have hr_ne : r ≠ 0 := by
      simpa [hr, RCLike.ofReal_eq_zero] using hnorm_ne
    set gh : EuclideanSpace 𝕜 d.env := r⁻¹ • g with hgh
    have hgh_unit : ‖gh‖ = 1 := by
      rw [hgh, norm_smul, hr]
      rw [norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg g)]
      field_simp
    -- Projecting `g` onto `gh` recovers the scale factor `r`.
    have hinner_gh_g : (inner 𝕜 gh g : 𝕜) = r := by
      rw [hgh, inner_smul_left, hr]
      rw [inner_self_eq_norm_sq_to_K (𝕜 := 𝕜)]
      rw [map_inv₀, RCLike.conj_ofReal]
      field_simp
    -- `gh` together with `v ↦ ⟪gh, slice (d.map v)⟫` is the required product decomposition.
    refine ⟨gh,
      { toFun := fun v => WithLp.toLp 2 fun b => (inner 𝕜 gh (slice (d.map v) b) : 𝕜)
        map_add' := fun u v => by ext b; simp [inner_add_right]
        map_smul' := fun c v => by ext b; simp [inner_smul_right] },
      hgh_unit, fun v => ?_⟩
    refine eq_of_slice_eq fun b => ?_
    obtain ⟨c, hc⟩ := hg v b
    rw [slice_tens, hc]
    show (c • g) = (inner 𝕜 gh (slice (d.map v) b) : 𝕜) • gh
    rw [hc, inner_smul_right, hinner_gh_g, hgh, smul_smul]
    congr 1
    field_simp

end Dilation
