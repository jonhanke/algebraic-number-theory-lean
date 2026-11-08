import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch4Thm429Basic

/-!
# Milne, *Algebraic Number Theory*, Theorem 4.29, p. 82: injectivity

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Theorem 4.29, p. 82; bib key `milne2020ant`.

If two oriented bases `b` of `𝔞` and `c` of `𝔟` give `SL₂(ℤ)`-equivalent forms, then `𝔞` and `𝔟` have the same
image in the narrow class group (`mk_eq_of_sLEquiv`).
-/

open NumberField Polynomial Module
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT.Thm429

section Inj

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- Membership in a fractional ideal in terms of a `ℤ`-basis. -/
theorem mem_iff_exists_int (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) (y : K) :
    y ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ↔ ∃ m n : ℤ, y = (m : K) * (b 0 : K) + (n : K) * (b 1 : K) := by
  constructor
  · intro hy
    have h := congrArg (fun z : ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) => (z : K))
      (b.sum_repr ⟨y, hy⟩)
    simp only [Fin.sum_univ_two, Submodule.coe_add] at h
    refine ⟨b.repr ⟨y, hy⟩ 0, b.repr ⟨y, hy⟩ 1, ?_⟩
    exact h.symm.trans (by simp [zsmul_eq_mul])
  · rintro ⟨m, n, rfl⟩
    have := (m • b 0 + n • b 1).2
    simpa [zsmul_eq_mul] using this

variable (hK : Module.finrank ℚ K = 2) (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1)

include hK hσ in
theorem sigma_sigma (x : K) : σ (σ x) = x := by
  classical
  have : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  have hu := aut_univ_eq hK σ hσ
  have hm : σ * σ ∈ (Finset.univ : Finset (K ≃ₐ[ℚ] K)) := Finset.mem_univ _
  rw [hu] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h
  · simpa using congrArg (fun f : K ≃ₐ[ℚ] K => f x) h
  · exfalso
    apply hσ
    have : σ * σ = σ * 1 := by rw [h, mul_one]
    exact mul_left_cancel this

include hK in
theorem norm_lin (u0 u1 : K) (hu0 : u0 ≠ 0) (x y : ℚ) :
    Algebra.norm ℚ (u0 * (x : K) + u1 * (y : K)) =
      Algebra.norm ℚ u0 * (x ^ 2 + Algebra.norm ℚ (u1 / u0) * y ^ 2
        + Algebra.trace ℚ K (u1 / u0) * (x * y)) := by
  have h1 : u0 * (x : K) + u1 * (y : K) = u0 * ((1 : K) * (x : K) + (u1 / u0) * (y : K)) := by
    field_simp
  have ht1 : Algebra.trace ℚ K (1 : K) = 2 := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, hK]; simp
  rw [h1, map_mul, NormForm.norm_expand hK, map_one, ht1, one_mul]
  ring

include hK hσ in
/-- The core algebraic step of injectivity. -/
theorem core (δ : K) (hδ0 : δ ≠ 0) (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (u0 u1 c0 c1 : K)
    (hu0 : u0 ≠ 0) (hc0 : c0 ≠ 0)
    (hform : ∀ x y : ℤ, A⁻¹ * Algebra.norm ℚ (u0 * ((x : ℚ) : K) + u1 * ((y : ℚ) : K)) =
      B⁻¹ * Algebra.norm ℚ (c0 * ((x : ℚ) : K) + c1 * ((y : ℚ) : K)))
    (hou : orient σ u0 u1 = δ * (A : K)) (hoc : orient σ c0 c1 = δ * (B : K)) :
    c1 * u0 = c0 * u1 ∧ Algebra.norm ℚ (c0 / u0) = B / A := by
  have hNu : Algebra.norm ℚ u0 ≠ 0 := by simpa [Algebra.norm_eq_zero_iff] using hu0
  have hNc : Algebra.norm ℚ c0 ≠ 0 := by simpa [Algebra.norm_eq_zero_iff] using hc0
  set t := u1 / u0 with ht
  set s := c1 / c0 with hs
  have e : ∀ x y : ℤ, A⁻¹ * (Algebra.norm ℚ u0 * (((x : ℤ) : ℚ) ^ 2 + Algebra.norm ℚ t * ((y : ℤ) : ℚ) ^ 2
        + Algebra.trace ℚ K t * (((x : ℤ) : ℚ) * ((y : ℤ) : ℚ)))) =
      B⁻¹ * (Algebra.norm ℚ c0 * (((x : ℤ) : ℚ) ^ 2 + Algebra.norm ℚ s * ((y : ℤ) : ℚ) ^ 2
        + Algebra.trace ℚ K s * (((x : ℤ) : ℚ) * ((y : ℤ) : ℚ)))) := by
    intro x y
    have := hform x y
    rwa [norm_lin hK u0 u1 hu0, norm_lin hK c0 c1 hc0] at this
  set k : ℚ := A⁻¹ * Algebra.norm ℚ u0 with hkdef
  have hk0 : k ≠ 0 := mul_ne_zero (inv_ne_zero hA) hNu
  have e10 := e 1 0
  have e01 := e 0 1
  have e11 := e 1 1
  push_cast at e10 e01 e11
  have hk : k = B⁻¹ * Algebra.norm ℚ c0 := by linear_combination e10
  have hNt : Algebra.norm ℚ t = Algebra.norm ℚ s := by
    apply mul_left_cancel₀ hk0
    linear_combination e01 - Algebra.norm ℚ s * hk
  have hTt : Algebra.trace ℚ K t = Algebra.trace ℚ K s := by
    apply mul_left_cancel₀ hk0
    linear_combination e11 - (1 + Algebra.norm ℚ s + Algebra.trace ℚ K s) * hk - k * hNt
  have hNK : t * σ t = s * σ s := by
    have := congrArg (fun q : ℚ => (q : K)) hNt
    simpa only [norm_eq_mul_sigma hK σ hσ] using this
  have hTK : t + σ t = s + σ s := by
    have := congrArg (fun q : ℚ => (q : K)) hTt
    simpa only [trace_eq_add_sigma hK σ hσ] using this
  have hprod : (s - t) * (s - σ t) = 0 := by linear_combination (-s) * hTK + hNK
  have hsig := sigma_sigma hK σ hσ
  -- orientation in terms of k
  have hu1 : u1 = t * u0 := by rw [ht]; field_simp
  have hc1 : c1 = s * c0 := by rw [hs]; field_simp
  have hNuK : ((Algebra.norm ℚ u0 : ℚ) : K) = u0 * σ u0 := norm_eq_mul_sigma hK σ hσ u0
  have hNcK : ((Algebra.norm ℚ c0 : ℚ) : K) = c0 * σ c0 := norm_eq_mul_sigma hK σ hσ c0
  have hNu' : Algebra.norm ℚ u0 = A * k := by rw [hkdef]; field_simp
  have hNc' : Algebra.norm ℚ c0 = B * k := by rw [hk]; field_simp
  have hAK : (A : K) ≠ 0 := Rat.cast_ne_zero.2 hA
  have hBK : (B : K) ≠ 0 := Rat.cast_ne_zero.2 hB
  have hδt : δ = (k : K) * (σ t - t) := by
    apply mul_right_cancel₀ hAK
    have h1 : orient σ u0 u1 = ((Algebra.norm ℚ u0 : ℚ) : K) * (σ t - t) := by
      rw [hNuK, hu1]; unfold orient; simp only [map_mul]; ring
    rw [← hou, h1, hNu']; push_cast; ring
  have hδs : δ = (k : K) * (σ s - s) := by
    apply mul_right_cancel₀ hBK
    have h1 : orient σ c0 c1 = ((Algebra.norm ℚ c0 : ℚ) : K) * (σ s - s) := by
      rw [hNcK, hc1]; unfold orient; simp only [map_mul]; ring
    rw [← hoc, h1, hNc']; push_cast; ring
  have hst : s = t := by
    rcases mul_eq_zero.1 hprod with h | h
    · exact sub_eq_zero.1 h
    · exfalso
      have h' : s = σ t := sub_eq_zero.1 h
      have : σ s = t := by rw [h', hsig]
      rw [this, h'] at hδs
      apply hδ0
      have : δ + δ = 0 := by linear_combination hδt + hδs
      have h2 : (2 : K) * δ = 0 := by linear_combination this
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd h3 two_ne_zero
      · exact h3
  refine ⟨?_, ?_⟩
  · rw [hc1, hu1, hst]; ring
  · have hm : Algebra.norm ℚ (c0 / u0) * Algebra.norm ℚ u0 = Algebra.norm ℚ c0 := by
      rw [← map_mul, div_mul_cancel₀ _ hu0]
    rw [eq_div_iff hA]
    apply mul_right_cancel₀ hk0
    linear_combination hm - Algebra.norm ℚ (c0 / u0) * hNu' + hNc'

end Inj

section Real

variable {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (σ : K ≃ₐ[ℚ] K)
  (hσ : σ ≠ 1)

theorem spanUnit_neg (l : K) (hl : l ≠ 0) : spanUnit (-l) (neg_ne_zero.2 hl) = spanUnit l hl := by
  apply Units.ext
  show FractionalIdeal.spanSingleton (𝓞 K)⁰ (-l) = FractionalIdeal.spanSingleton (𝓞 K)⁰ l
  ext y
  rw [FractionalIdeal.mem_spanSingleton, FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨-z, by rw [← hz, neg_smul, smul_neg]⟩
  · rintro ⟨z, hz⟩
    exact ⟨-z, by rw [← hz, neg_smul, smul_neg, neg_neg]⟩

include hK hσ in
/-- `(l)` with `N(l) > 0` is generated by a totally positive element. -/
theorem spanUnit_mem_tpp (l : K) (hl : l ≠ 0) (hpos : 0 < Algebra.norm ℚ l) :
    spanUnit l hl ∈ totallyPositivePrincipal K := by
  classical
  have hN := norm_eq_mul_sigma hK σ hσ l
  have hGal := isGalois_of_quadratic hK σ hσ
  have key : ∀ ρ : K →+* ℝ, 0 < ρ l * ρ (σ l) := by
    intro ρ
    have h := congrArg ρ hN
    rw [map_mul] at h
    have h2 : ρ ((Algebra.norm ℚ l : ℚ) : K) = ((Algebra.norm ℚ l : ℚ) : ℝ) := map_ratCast ρ _
    rw [h2] at h
    rw [← h]
    exact_mod_cast hpos
  by_cases hne : Nonempty (K →+* ℝ)
  · obtain ⟨ρ0⟩ := hne
    have : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
    have hu := aut_univ_eq hK σ hσ
    have hall : ∀ ρ : K →+* ℝ, ∀ x, ρ x = ρ0 x ∨ ρ x = ρ0 (σ x) := by
      intro ρ x
      obtain ⟨τ, hτ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ)
        (Complex.ofRealHom.comp ρ0) (Complex.ofRealHom.comp ρ) (RingHom.ext_rat _ _)
      have hx : ρ0 (τ.symm x) = ρ x := by
        have := congrArg (fun f : K →+* ℂ => f x) hτ
        simpa using this
      have hm : τ.symm ∈ (Finset.univ : Finset (K ≃ₐ[ℚ] K)) := Finset.mem_univ _
      rw [hu] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · left; rw [← hx, h]; rfl
      · right; rw [← hx, h]
    have hρ := key ρ0
    by_cases ha : 0 < ρ0 l
    · have hb : 0 < ρ0 (σ l) := (pos_iff_pos_of_mul_pos hρ).1 ha
      refine Subgroup.subset_closure ⟨l, hl, fun ρ => ?_, rfl⟩
      rcases hall ρ l with h | h
      · rw [h]; exact ha
      · rw [h]; exact hb
    · have ha' : ρ0 l ≤ 0 := not_lt.1 ha
      have hb : ρ0 (σ l) < 0 := by
        by_contra hb
        nlinarith [not_lt.1 hb]
      rw [← spanUnit_neg l hl]
      refine Subgroup.subset_closure ⟨-l, neg_ne_zero.2 hl, fun ρ => ?_, rfl⟩
      rw [map_neg]
      rcases hall ρ l with h | h
      · rw [h]
        have : ρ0 l < 0 := lt_of_le_of_ne ha' (by intro h0; rw [h0] at hρ; simp at hρ)
        linarith
      · rw [h]; linarith
  · exact Subgroup.subset_closure ⟨l, hl, fun ρ => (hne ⟨ρ⟩).elim, rfl⟩

end Real

section Main

variable {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (σ : K ≃ₐ[ℚ] K)
  (hσ : σ ≠ 1) (δ : K) (hδ : δ ^ 2 = (NumberField.discr K : K))

include hK hσ hδ in
/-- **Injectivity** in Milne Thm. 4.29: oriented bases with `SL₂(ℤ)`-equivalent forms come from ideals with the
same narrow class. -/
@[kb "milne2020ant" "v3.08, Thm. 4.29, p. 82"]
theorem mk_eq_of_sLEquiv (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (c : Basis (Fin 2) ℤ ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (hb : orient σ (b 0) (b 1) = δ * N 𝔞) (hc : orient σ (c 0) (c 1) = δ * N 𝔟)
    (h : QuadFormsKB.Binary.SLEquiv (formOf hK 𝔞 b) (formOf hK 𝔟 c)) :
    (QuotientGroup.mk 𝔞 : NarrowClassGroup K) = QuotientGroup.mk 𝔟 := by
  obtain ⟨p, q, r, s, hd, hsub⟩ := (QuadFormsKB.Binary.sLEquiv_iff _ _).1 h
  have hδ0 := delta_ne_zero δ hδ
  obtain ⟨A, hA⟩ : ∃ A : ℚ, A = FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℚ, B = FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) := ⟨_, rfl⟩
  have hA0 : A ≠ 0 := by rw [hA, Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  have hB0 : B ≠ 0 := by rw [hB, Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔟.ne_zero
  have hApos : 0 < A := lt_of_le_of_ne (hA ▸ FractionalIdeal.absNorm_nonneg _) (Ne.symm hA0)
  have hBpos : 0 < B := lt_of_le_of_ne (hB ▸ FractionalIdeal.absNorm_nonneg _) (Ne.symm hB0)
  have hNA : N 𝔞 = (A : K) := by rw [hA]
  have hNB : N 𝔟 = (B : K) := by rw [hB]
  rw [hNA] at hb
  rw [hNB] at hc
  obtain ⟨u0, hu0def⟩ : ∃ u0 : K, u0 = (p : K) * b 0 + (r : K) * b 1 := ⟨_, rfl⟩
  obtain ⟨u1, hu1def⟩ : ∃ u1 : K, u1 = (q : K) * b 0 + (s : K) * b 1 := ⟨_, rfl⟩
  have hdK : (p : K) * s - q * r = 1 := by exact_mod_cast hd
  have hou : orient σ u0 u1 = δ * (A : K) := by
    have := orient_comb σ p r q s (b 0 : K) (b 1 : K)
    have hd' : ((p * s - r * q : ℤ) : K) = 1 := by
      push_cast; linear_combination hdK
    rw [hb, hd', one_mul] at this
    rw [hu0def, hu1def]; exact this
  have hAδ : δ * (A : K) ≠ 0 := mul_ne_zero hδ0 (Rat.cast_ne_zero.2 hA0)
  have hBδ : δ * (B : K) ≠ 0 := mul_ne_zero hδ0 (Rat.cast_ne_zero.2 hB0)
  have hu0 : u0 ≠ 0 := by
    intro h0
    apply hAδ
    rw [← hou, h0]; unfold orient; simp
  have hc0 : (c 0 : K) ≠ 0 := by
    intro h0
    apply hBδ
    rw [← hc, h0]; unfold orient; simp
  have hform : ∀ x y : ℤ, A⁻¹ * Algebra.norm ℚ (u0 * ((x : ℚ) : K) + u1 * ((y : ℚ) : K)) =
      B⁻¹ * Algebra.norm ℚ ((c 0 : K) * ((x : ℚ) : K) + (c 1 : K) * ((y : ℚ) : K)) := by
    intro x y
    have h1 := formOf_eval hK 𝔟 c x y
    rw [← hsub, QuadFormsKB.BinQF.eval_subst, formOf_eval] at h1
    unfold idealNormForm at h1
    have h2 : u0 * ((x : ℚ) : K) + u1 * ((y : ℚ) : K) =
        (b 0 : K) * (((p * x + q * y : ℤ) : ℚ) : K) + (b 1 : K) * (((r * x + s * y : ℤ) : ℚ) : K) := by
      rw [hu0def, hu1def]; push_cast; ring
    rw [h2, hA, hB]
    exact h1
  obtain ⟨hcl, hnorm⟩ := core hK σ hσ δ hδ0 A B hA0 hB0 u0 u1 (c 0 : K) (c 1 : K) hu0 hc0 hform hou hc
  obtain ⟨l, hl⟩ : ∃ l : K, l = (c 0 : K) / u0 := ⟨_, rfl⟩
  have hl0 : l ≠ 0 := by rw [hl]; exact div_ne_zero hc0 hu0
  have hlpos : 0 < Algebra.norm ℚ l := by rw [hl, hnorm]; exact div_pos hBpos hApos
  have hc0eq : (c 0 : K) = l * u0 := by rw [hl]; field_simp
  have hc1eq : (c 1 : K) = l * u1 := by
    rw [hl]; field_simp; linear_combination hcl
  have key : 𝔟 = 𝔞 * spanUnit l hl0 := by
    apply Units.ext
    apply FractionalIdeal.ext
    intro y
    rw [mem_mul_spanUnit, mem_iff_exists_int 𝔟 c]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨(m : K) * u0 + (n : K) * u1, ?_, ?_⟩
      · rw [mem_iff_exists_int 𝔞 b]
        exact ⟨m * p + n * q, m * r + n * s, by rw [hu0def, hu1def]; push_cast; ring⟩
      · rw [hc0eq, hc1eq]; ring
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, n, rfl⟩ := (mem_iff_exists_int 𝔞 b _).1 hz
      refine ⟨m * s - n * q, -(m * r) + n * p, ?_⟩
      rw [hc0eq, hc1eq, hu0def, hu1def]
      push_cast
      linear_combination (-(l * ((m : K) * b 0 + (n : K) * b 1))) * hdK
  rw [QuotientGroup.eq, key, inv_mul_cancel_left]
  exact spanUnit_mem_tpp hK σ hσ l hl0 hlpos

end Main

end NumberFieldKB.MilneANT.Thm429
