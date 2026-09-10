import Drop.Source.Language

/-!
# Two families of gates, and the algebra of running them

Everything downstream is built out of two kinds of gate.

* `permGate σ` — a classical reversible gate: a permutation of the joint
  basis.
* `localGate V W` — a gate that acts on the temporary and on the visible
  register separately, `V ⊗ W`.  This is the shape of the two gates of a
  weakening witness: prepare the temporary, act on the visible register.

The lemmas are the ones any calculation with programs needs: composition of
gates is composition of matrices (`actJoint_mul`), local gates compose
(`localGate_mul`), a local gate maps a product to a product
(`actJoint_localGate_tens`), allocation is tensoring with a basis state
(`alloc_eq_tens`), and a well-typed body is norm-preserving hence contractive
(`norm_actJoint_run`).
-/

namespace SourceLanguage

open Matrix Circuit SimpleTensor

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The action of a square matrix is norm-preserving when it is unitary -/

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- A unitary matrix acts by an isometry. -/
lemma norm_act_of_unitary {V : Matrix ν ν 𝕜} (h : Vᴴ * V = 1) (a : EuclideanSpace 𝕜 ν) :
    ‖act V a‖ = ‖a‖ := by
  have key : (inner 𝕜 (act V a) (act V a) : 𝕜) = inner 𝕜 a a := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [RCLike.inner_apply', act_apply]
    have hexp : ∑ j, (starRingEnd 𝕜) (∑ k, V j k * a k) * (∑ k, V j k * a k)
        = ∑ k, ∑ k', (starRingEnd 𝕜) (a k') * ((Vᴴ * V) k' k * a k) := by
      simp only [map_sum, map_mul, Matrix.mul_apply, conjTranspose_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j _ => by
        rw [RCLike.star_def]; ring
    rw [hexp, h]
    simp [Matrix.one_apply]
  have h1 := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (act V a)
  have h2 := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) a
  rw [h1, h2] at key
  have hreal : (‖act V a‖ : ℝ) ^ 2 = (‖a‖ : ℝ) ^ 2 := by
    have := congrArg (RCLike.re (K := 𝕜)) key
    simpa using this
  nlinarith [norm_nonneg (act V a), norm_nonneg a]

@[simp] lemma act_one (a : EuclideanSpace 𝕜 ν) : act (1 : Matrix ν ν 𝕜) a = a := by
  ext j
  simp [act_apply, Matrix.one_apply, Finset.sum_ite_eq]

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

/-! ### Running gates in sequence -/

omit [DecidableEq ι] [DecidableEq μ] in
/-- Running two matrices in sequence is running their product. -/
lemma actJoint_mul (M N : Matrix (ι × μ) (ι × μ) 𝕜) (x : EuclideanSpace 𝕜 (ι × μ)) :
    actJoint (M * N) x = actJoint M (actJoint N x) := by
  ext p
  simp only [actJoint_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring

@[simp] lemma actJoint_one (x : EuclideanSpace 𝕜 (ι × μ)) :
    actJoint (1 : Matrix (ι × μ) (ι × μ) 𝕜) x = x := by
  ext p; simp [Matrix.one_apply, Finset.sum_ite_eq]

/-- Concatenation of bodies: `p` then `q`. -/
def Body.append : Body 𝕜 ι μ → Body 𝕜 ι μ → Body 𝕜 ι μ
  | .halt, q => q
  | .gate U r, q => .gate U (r.append q)

@[simp] lemma Body.run_append (p q : Body 𝕜 ι μ) : (p.append q).run = q.run * p.run := by
  induction p with
  | halt => simp [Body.append, Body.run]
  | gate U r ih => simp [Body.append, Body.run, ih, Matrix.mul_assoc]

lemma Body.WellTyped.append {p q : Body 𝕜 ι μ} (hp : p.WellTyped) (hq : q.WellTyped) :
    (p.append q).WellTyped := by
  induction p with
  | halt => exact hq
  | gate U r ih =>
    cases hp with
    | gate hU hr => exact .gate hU (ih hr)

omit [DecidableEq μ] in
/-- Allocation is tensoring with a basis state of the temporary. -/
lemma alloc_eq_tens (i₀ : ι) (v : EuclideanSpace 𝕜 μ) :
    alloc i₀ v = tens (EuclideanSpace.single i₀ (1 : 𝕜)) v := by
  ext p
  by_cases h : p.1 = i₀ <;> simp [h, EuclideanSpace.single_apply]

omit [DecidableEq μ] in
@[simp] lemma norm_alloc (i₀ : ι) (v : EuclideanSpace 𝕜 μ) : ‖alloc i₀ (𝕜 := 𝕜) v‖ = ‖v‖ := by
  rw [alloc_eq_tens, norm_tens]
  simp

/-- The denotation, peeled at the first gate. -/
lemma denote_gate (i₀ : ι) (U : Matrix (ι × μ) (ι × μ) 𝕜) (r : Body 𝕜 ι μ)
    (v : EuclideanSpace 𝕜 μ) :
    denote i₀ (.gate U r) v = actJoint r.run (actJoint U (alloc i₀ v)) := by
  simp [denote, Body.run, actJoint_mul]

@[simp] lemma denote_halt (i₀ : ι) (v : EuclideanSpace 𝕜 μ) :
    denote i₀ (.halt : Body 𝕜 ι μ) v = alloc i₀ v := by
  simp [denote, Body.run]

/-- A well-typed body acts by an isometry on the joint register. -/
lemma norm_actJoint_run {p : Body 𝕜 ι μ} (hp : p.WellTyped) (x : EuclideanSpace 𝕜 (ι × μ)) :
    ‖actJoint p.run x‖ = ‖x‖ :=
  norm_act_of_unitary (Body.run_isometric hp) x

/-! ### Classical reversible gates -/

/-- The gate that permutes the joint basis according to `σ`. -/
def permGate (σ : Equiv.Perm (ι × μ)) : Matrix (ι × μ) (ι × μ) 𝕜 :=
  Matrix.of fun p q => if p = σ q then 1 else 0

/-- Every classical reversible gate is well-typed. -/
lemma permGate_unitary (σ : Equiv.Perm (ι × μ)) :
    (permGate (𝕜 := 𝕜) σ)ᴴ * permGate σ = 1 := by
  ext q' q
  simp only [Matrix.mul_apply, conjTranspose_apply, permGate, Matrix.of_apply, Matrix.one_apply]
  have hterm : ∀ p : ι × μ,
      star (if p = σ q' then (1 : 𝕜) else 0) * (if p = σ q then (1 : 𝕜) else 0)
        = if p = σ q' then (if p = σ q then (1 : 𝕜) else 0) else 0 := by
    intro p; by_cases h : p = σ q' <;> simp [h]
  rw [Finset.sum_congr rfl fun p _ => hterm p,
    Finset.sum_eq_single (σ q') (fun b _ hb => by simp [hb]) (by simp)]
  simp [σ.injective.eq_iff]

/-- A classical reversible gate permutes the coordinates. -/
@[simp] lemma actJoint_permGate (σ : Equiv.Perm (ι × μ)) (x : EuclideanSpace 𝕜 (ι × μ))
    (p : ι × μ) : actJoint (permGate σ) x p = x (σ.symm p) := by
  simp only [actJoint_apply, permGate, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ.symm p)
    (fun b _ hb => by
      have : p ≠ σ b := fun hc => hb (by rw [hc, Equiv.symm_apply_apply])
      simp [this])
    (by simp)]
  simp

/-- The action of a classical reversible gate on a basis vector. -/
@[simp] lemma actJoint_permGate_single (σ : Equiv.Perm (ι × μ)) (q : ι × μ) (c : 𝕜) :
    actJoint (permGate σ) (EuclideanSpace.single q c) = EuclideanSpace.single (σ q) c := by
  ext p
  simp only [actJoint_apply, permGate, Matrix.of_apply, EuclideanSpace.single_apply]
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (by simp)]
  by_cases h : p = σ q <;> simp [h]

/-! ### Local gates -/

/-- The gate `V ⊗ W`: `V` on the temporary, `W` on the visible register, with no
interaction between them. -/
def localGate (V : Matrix ι ι 𝕜) (W : Matrix μ μ 𝕜) : Matrix (ι × μ) (ι × μ) 𝕜 :=
  Matrix.of fun p q => V p.1 q.1 * W p.2 q.2

omit [DecidableEq ι] [DecidableEq μ] in
omit [Fintype ι] [Fintype μ] in
@[simp] lemma localGate_apply (V : Matrix ι ι 𝕜) (W : Matrix μ μ 𝕜) (p q : ι × μ) :
    localGate V W p q = V p.1 q.1 * W p.2 q.2 := rfl

omit [DecidableEq ι] [DecidableEq μ] in
/-- Local gates compose. -/
lemma localGate_mul (V V' : Matrix ι ι 𝕜) (W W' : Matrix μ μ 𝕜) :
    localGate V W * localGate V' W' = localGate (V * V') (W * W') := by
  ext p q
  simp only [Matrix.mul_apply, localGate_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

omit [Fintype ι] [Fintype μ] in
@[simp] lemma localGate_one : localGate (1 : Matrix ι ι 𝕜) (1 : Matrix μ μ 𝕜) = 1 := by
  ext p q
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [localGate, Matrix.one_apply, h1, h2, Prod.ext_iff]

omit [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ] in
lemma localGate_conjTranspose (V : Matrix ι ι 𝕜) (W : Matrix μ μ 𝕜) :
    (localGate V W)ᴴ = localGate Vᴴ Wᴴ := by
  ext p q
  simp [localGate, conjTranspose_apply]

/-- A local gate of two unitaries is well-typed. -/
lemma localGate_unitary {V : Matrix ι ι 𝕜} {W : Matrix μ μ 𝕜}
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) : (localGate V W)ᴴ * localGate V W = 1 := by
  rw [localGate_conjTranspose, localGate_mul, hV, hW, localGate_one]

omit [DecidableEq ι] [DecidableEq μ] in
/-- A local gate maps a product to a product.  This is the whole reason the
type system works. -/
lemma actJoint_localGate_tens (V : Matrix ι ι 𝕜) (W : Matrix μ μ 𝕜)
    (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 μ) :
    actJoint (localGate V W) (tens a b) = tens (act V a) (act W b) := by
  ext p
  simp only [actJoint_apply, localGate_apply, tens_apply, act_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end SourceLanguage
