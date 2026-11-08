import Mathlib

/-!
# Milne, *Class Field Theory*, Remark VIII.3.2: a norm from a split étale algebra

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, Remark 3.2,
p. 234.

Algebraic lemma for the local half of Remark VIII.3.2. Let $A$ be a commutative algebra of finite dimension $n$ over a
field $F$ with $2 \ne 0$, $\delta \in A$ with $\delta^2 = r^2$ for some $r \in F^\times$, and $\tau$ an $F$-algebra
automorphism of $A$ with $\tau(\delta) = -\delta$. Then $e = (r + \delta)/(2r)$ is an idempotent with
$\tau(e) = 1 - e$, so $A = eA \oplus (1-e)A$ with both summands of dimension $n/2$, and for $c \in F$ the element
$ce + (1 - e)$ has norm $c^{n/2}$ (`R32.norm_smul_idem_add`).
-/

open Module

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.R32

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [FiniteDimensional F A]

/-- The idempotent $e = (r + \delta)/(2r)$ attached to a square root $\delta$ of $r^2$. -/
def idem (r : F) (δ : A) : A := algebraMap F A (2 * r)⁻¹ * (algebraMap F A r + δ)

theorem idem_mul_self {r : F} (hr : r ≠ 0) (h2 : (2 : F) ≠ 0) {δ : A} (hδ : δ ^ 2 = algebraMap F A (r ^ 2)) :
    idem r δ * idem r δ = idem r δ := by
  unfold idem
  have key : (algebraMap F A r + δ) * (algebraMap F A r + δ) =
      algebraMap F A (2 * r) * (algebraMap F A r + δ) := by
    rw [map_pow] at hδ
    simp only [map_mul, map_ofNat]
    linear_combination hδ
  have hu : algebraMap F A (2 * r)⁻¹ * algebraMap F A (2 * r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (mul_ne_zero h2 hr), map_one]
  generalize algebraMap F A (2 * r)⁻¹ = u at hu ⊢
  generalize algebraMap F A (2 * r) = v at hu key ⊢
  generalize algebraMap F A r + δ = w at key ⊢
  calc u * w * (u * w) = u * (u * (w * w)) := by ring
    _ = u * w := by rw [key, ← mul_assoc u v, hu, one_mul]

theorem tau_idem {r : F} (hr : r ≠ 0) (h2 : (2 : F) ≠ 0) {δ : A} (τ : A ≃ₐ[F] A) (hτ : τ δ = -δ) :
    τ (idem r δ) = 1 - idem r δ := by
  unfold idem
  rw [map_mul, map_add, AlgEquiv.commutes, AlgEquiv.commutes, hτ]
  have h1 : (1 : A) = algebraMap F A (2 * r)⁻¹ * algebraMap F A (2 * r) := by
    rw [← map_mul, inv_mul_cancel₀ (mul_ne_zero h2 hr), map_one]
  rw [h1]
  simp only [map_mul, map_ofNat]
  ring

/-- The summand $eA$ for an idempotent $e$. -/
def summand (e : A) : Submodule F A := LinearMap.range (LinearMap.mulLeft F e)

theorem mem_summand_iff {e : A} (he : e * e = e) (x : A) : x ∈ summand (F := F) e ↔ e * x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    simp only [LinearMap.mulLeft_apply]
    rw [← mul_assoc, he]
  · intro h
    exact ⟨x, h⟩

theorem isCompl_summand {e : A} (he : e * e = e) : IsCompl (summand (F := F) e) (summand (1 - e)) := by
  have he' : (1 - e) * (1 - e) = 1 - e := by
    have : (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
    rw [this, he]; ring
  constructor
  · rw [Submodule.disjoint_def]
    intro x h1 h2
    rw [mem_summand_iff he] at h1
    rw [mem_summand_iff he'] at h2
    have : e * x = e * ((1 - e) * x) := by rw [h2]
    rw [h1, ← mul_assoc, mul_sub, mul_one, he, sub_self, zero_mul] at this
    exact this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = e * x + (1 - e) * x := by ring
    rw [hx]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

theorem finrank_summand_eq {e : A} (τ : A ≃ₐ[F] A) (hτ : τ e = 1 - e) :
    finrank F (summand (F := F) e) = finrank F (summand (F := F) (1 - e)) := by
  have hmap : (summand (F := F) e).map τ.toLinearEquiv.toLinearMap = summand (1 - e) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨τ z, ?_⟩
      simp [LinearMap.mulLeft_apply, map_mul, hτ]
    · rintro ⟨z, rfl⟩
      refine ⟨e * τ.symm z, ⟨τ.symm z, rfl⟩, ?_⟩
      simp [map_mul, hτ]
  rw [← hmap]
  exact (LinearEquiv.finrank_map_eq τ.toLinearEquiv _).symm

theorem det_mul_idem {e : A} (he : e * e = e) (c : F) :
    LinearMap.det (Algebra.lmul F A (algebraMap F A c * e + (1 - e))) =
      c ^ finrank F (summand (F := F) e) := by
  set P := summand (F := F) e
  set Q := summand (F := F) (1 - e)
  have hc := isCompl_summand (F := F) he
  set eq := Submodule.prodEquivOfIsCompl P Q hc
  set f := Algebra.lmul F A (algebraMap F A c * e + (1 - e))
  have hconj : (eq.symm.toLinearMap ∘ₗ f ∘ₗ eq.toLinearMap) =
      LinearMap.prodMap (c • LinearMap.id) LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨p, q⟩
    apply eq.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    simp only [eq, Submodule.coe_prodEquivOfIsCompl', f, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Submodule.coe_smul,
      Algebra.smul_def]
    have hp : e * (p : A) = p := (mem_summand_iff he _).mp p.2
    have he' : (1 - e) * (1 - e) = 1 - e := by
      have : (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
      rw [this, he]; ring
    have hq : (1 - e) * (q : A) = q := (mem_summand_iff he' _).mp q.2
    have hpq : e * (q : A) = 0 := by
      rw [← hq, ← mul_assoc, mul_sub, mul_one, he, sub_self, zero_mul]
    have hqp : (1 - e) * (p : A) = 0 := by
      rw [← hp, ← mul_assoc, sub_mul, one_mul, he, sub_self, zero_mul]
    calc (algebraMap F A c * e + (1 - e)) * ((p : A) + q)
        = algebraMap F A c * (e * p) + algebraMap F A c * (e * q) + ((1 - e) * p) + ((1 - e) * q) := by ring
      _ = _ := by rw [hp, hpq, hqp, hq]; ring
  have := LinearMap.det_conj f eq.symm
  rw [← this]
  change LinearMap.det (eq.symm.toLinearMap ∘ₗ f ∘ₗ eq.toLinearMap) = _
  rw [hconj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

/-- **Norm of $ce + (1-e)$.** With $e = (r + \delta)/(2r)$ as above, $\mathrm{N}_{A/F}(ce + (1 - e))^2$ … precisely:
$\mathrm{N}_{A/F}(ce + (1-e)) = c^{k}$ where $2k = \dim_F A$. -/
theorem norm_smul_idem_add {r : F} (hr : r ≠ 0) (h2 : (2 : F) ≠ 0) {δ : A}
    (hδ : δ ^ 2 = algebraMap F A (r ^ 2)) (τ : A ≃ₐ[F] A) (hτ : τ δ = -δ) {k : ℕ} (hk : finrank F A = 2 * k)
    (c : F) :
    Algebra.norm F (algebraMap F A c * idem r δ + (1 - idem r δ)) = c ^ k := by
  have he := idem_mul_self hr h2 hδ
  have hτe := tau_idem hr h2 τ hτ
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_summand (F := F) he)
  have heq := finrank_summand_eq (F := F) τ hτe
  rw [Algebra.norm_apply, det_mul_idem he]
  congr 1
  omega

end NumberFieldKB.MilneCFT.Ch8.R32
