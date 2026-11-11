import NumberFieldKB.MilneEC.Ch3Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Milne, Elliptic Curves, Chapter III §3: the `j`-invariant and Theorem 3.10

* `j(Λ)`, `j(τ)` (Milne, `milne2006ec`, pdf pp. 101–102) and their invariance;
* the surjectivity of `j : ℍ → ℂ` (Milne, Chapter V, Proposition 2.2, used in Theorem 3.10),
  proved from the fact that level-one modular forms of weight `0` are constant;
* Theorem 3.10: every elliptic curve over `ℂ` is isomorphic to some `E(Λ)`.
-/

open Complex Set Filter Topology Real UpperHalfPlane ModularForm EisensteinSeries
open scoped MatrixGroups Manifold

namespace NumberFieldKB.MilneEC.III

/-! ### The `j`-invariant and Theorem 3.10 -/

/-- `j(Λ) = 1728 g₄³/(g₄³ - 27g₆²)` (Milne, pdf p. 101). -/
noncomputable def jOf (L : PeriodPair) : ℂ := 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

/-- Milne (pdf p. 101): `E(Λ)` has `j`-invariant `j(Λ)`. -/
theorem j_curveOf (L : PeriodPair) : (curveOf L).j = jOf L := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  rw [WeierstrassCurve.j_eq, curveOf_Δ, jOf]
  have hc4 : (curveOf L).c₄ = 12 * L.g₂ := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curveOf]
    ring
  rw [hc4]
  field_simp
  ring

/-- Milne's `j(τ) = j(ℤτ + ℤ)` (pdf p. 102). -/
noncomputable def jFun (τ : ℍ) : ℂ := jOf (periodPairOf τ)

/-- Milne (pdf p. 102): `j(aτ+b / cτ+d) = j(τ)` for `(a b; c d) ∈ SL₂(ℤ)`. -/
@[kb "milne2006ec" "Ch. III, §3, j is SL2(Z)-invariant, pdf p. 102"]
theorem jFun_smul (A : SL(2, ℤ)) (τ : ℍ) : jFun (A • τ) = jFun τ := by
  set u : ℂ := (A 1 0 : ℂ) * τ + (A 1 1 : ℂ) with hu_def
  have hu : u ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) τ
    simpa [UpperHalfPlane.denom, hu_def] using this
  have hdet : (A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  have hAτ : ((A • τ : ℍ) : ℂ) = ((A 0 0 : ℂ) * τ + A 0 1) / u := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [hu_def]
  have hlat : (periodPairOf (A • τ)).lattice =
      Submodule.span ℤ {u⁻¹ * (periodPairOf τ).ω₁, u⁻¹ * (periodPairOf τ).ω₂} := by
    apply le_antisymm
    · rw [PeriodPair.lattice, Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · rw [SetLike.mem_coe, Submodule.mem_span_pair]
        refine ⟨A 0 0, A 0 1, ?_⟩
        simp only [periodPairOf, zsmul_eq_mul, hAτ]
        field_simp
      · rw [SetLike.mem_coe, Submodule.mem_span_pair]
        refine ⟨A 1 0, A 1 1, ?_⟩
        simp only [periodPairOf, zsmul_eq_mul, hu_def]
        have h1 : u⁻¹ * u = 1 := inv_mul_cancel₀ hu
        rw [hu_def] at h1
        linear_combination h1
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · rw [SetLike.mem_coe, PeriodPair.mem_lattice]
        refine ⟨A 1 1, -A 0 1, ?_⟩
        simp only [periodPairOf, hAτ]
        push_cast
        field_simp
        linear_combination (τ : ℂ) * hdet
      · rw [SetLike.mem_coe, PeriodPair.mem_lattice]
        refine ⟨-A 1 0, A 0 0, ?_⟩
        simp only [periodPairOf, hAτ]
        push_cast
        field_simp
        linear_combination (1 : ℂ) * hdet
  have hG : ∀ k, (periodPairOf (A • τ)).G k = u ^ k * (periodPairOf τ).G k := by
    intro k
    rw [G_of_lattice_eq_smul (inv_ne_zero hu) hlat k, inv_pow, inv_inv]
  have h2 : (periodPairOf (A • τ)).g₂ = u ^ 4 * (periodPairOf τ).g₂ := by
    rw [PeriodPair.g₂, PeriodPair.g₂, hG]; ring
  have h3 : (periodPairOf (A • τ)).g₃ = u ^ 6 * (periodPairOf τ).g₃ := by
    rw [PeriodPair.g₃, PeriodPair.g₃, hG]; ring
  have hK : u ^ 12 ≠ 0 := pow_ne_zero _ hu
  rw [jFun, jFun, jOf, jOf, h2, h3]
  rw [← mul_div_mul_left (1728 * (periodPairOf τ).g₂ ^ 3)
    ((periodPairOf τ).g₂ ^ 3 - 27 * (periodPairOf τ).g₃ ^ 2) hK]
  congr 1 <;> ring

/-- `j = 1728 E₄³/(E₄³ - E₆²)`. -/
theorem jFun_eq (τ : ℍ) : jFun τ = 1728 * E₄ τ ^ 3 / (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  have h2 : (periodPairOf τ).g₂ = 4 * (π : ℂ) ^ 4 / 3 * E₄ τ := by
    have h := eisensteinG_eq_E (k := 4) (by norm_num) τ
    rw [eisensteinG_eq_G] at h
    rw [PeriodPair.g₂, h]
    have z4 := riemannZeta_four
    norm_num at z4 ⊢
    rw [z4]
    ring
  have h3 : (periodPairOf τ).g₃ = 8 * (π : ℂ) ^ 6 / 27 * E₆ τ := by
    have h := eisensteinG_eq_E (k := 6) (by norm_num) τ
    rw [eisensteinG_eq_G] at h
    rw [PeriodPair.g₃, h]
    have z6 := riemannZeta_six
    norm_num at z6 ⊢
    rw [z6]
    ring
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [jFun, jOf, h2, h3]
  have hK : (64 * (π : ℂ) ^ 12 / 27) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hπ)) (by norm_num)
  rw [← mul_div_mul_left (1728 * E₄ τ ^ 3) (E₄ τ ^ 3 - E₆ τ ^ 2) hK]
  congr 1 <;> ring

/-- Milne, Chapter V, Proposition 2.2 (cited in the proof of Theorem 3.10, pdf p. 102):
`j : ℍ → ℂ` is surjective.  Proof here: for `c ∈ ℂ` the weight-12 form `F = E₄³ - (c/1728)·1728Δ`
has a zero in `ℍ`, since otherwise `Δ/F` would be a level-one modular form of weight `0`
tending to `0` at `i∞`, hence `0`. -/
@[kb "milne2006ec" "Ch. V, Prop. 2.2 (j surjective), used in Ch. III, Thm. 3.10, pdf p. 102"]
theorem jFun_surjective : Function.Surjective jFun := by
  intro c
  set a : ℂ := 1 - c / 1728 with ha
  set b : ℂ := c / 1728 with hb
  have hab : a + b = 1 := by rw [ha, hb]; ring
  let Fz : ℍ → ℂ := fun z => a * E₄ z ^ 3 + b * E₆ z ^ 2
  by_cases h : ∃ τ, Fz τ = 0
  · obtain ⟨τ, hτ⟩ := h
    refine ⟨τ, ?_⟩
    have hΔ := ModularForm.discriminant_ne_zero τ
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq] at hΔ
    have hne : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := fun h0 => hΔ (by rw [h0]; simp)
    rw [jFun_eq, div_eq_iff hne]
    have : a * E₄ τ ^ 3 + b * E₆ τ ^ 2 = 0 := hτ
    rw [ha, hb] at this
    linear_combination 1728 * this
  · exfalso
    push Not at h
    -- transformation laws
    have hγ : ∀ γ : SL(2, ℤ), (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := fun γ => ⟨γ, rfl⟩
    have hmod : ∀ {k : ℤ} (f : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (z : ℍ),
        f (γ • z) = (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z) ^ k * f z := by
      intro k f γ z
      exact SlashInvariantForm.slash_action_eqn'' f (γ := (γ : GL (Fin 2) ℝ)) (hγ γ) z
    have hΔmod : ∀ (γ : SL(2, ℤ)) (z : ℍ), ModularForm.discriminant (γ • z) =
        (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z) ^ (12 : ℤ) * ModularForm.discriminant z := by
      intro γ z
      exact SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant
        (γ := (γ : GL (Fin 2) ℝ)) (hγ γ) z
    have hFmod : ∀ (γ : SL(2, ℤ)) (z : ℍ),
        Fz (γ • z) = (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z) ^ (12 : ℕ) * Fz z := by
      intro γ z
      have h4 := hmod E₄ γ z
      have h6 := hmod E₆ γ z
      simp only [Fz, h4, h6]
      simp only [zpow_ofNat]
      ring
    have hΔmod' : ∀ (γ : SL(2, ℤ)) (z : ℍ), ModularForm.discriminant (γ • z) =
        (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z) ^ (12 : ℕ) * ModularForm.discriminant z := by
      intro γ z
      rw [hΔmod]; simp
    have hFmdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Fz := by
      have h4 := E₄.holo'
      have h6 := E₆.holo'
      exact ((h4.pow 3).const_smul a).add ((h6.pow 2).const_smul b)
    have hlimF : Tendsto Fz atImInfty (𝓝 1) := by
      have h4 : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := EisensteinSeries.tendsto_E_atImInfty
      have h6 : Tendsto (E₆ : ℍ → ℂ) atImInfty (𝓝 1) := EisensteinSeries.tendsto_E_atImInfty
      have := ((h4.pow 3).const_mul a).add ((h6.pow 2).const_mul b)
      simpa [hab] using this
    let f : ℍ → ℂ := fun z => ModularForm.discriminant z / Fz z
    have hlim : Tendsto f atImInfty (𝓝 0) := by
      have := ModularForm.discriminant_isZeroAtImInfty.div hlimF one_ne_zero
      have h' : Tendsto (ModularForm.discriminant / Fz) atImInfty (𝓝 0) := by simpa using this
      exact h'
    have hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f := by
      intro γ
      ext z
      rw [SL_slash_apply]
      simp only [f, hFmod, hΔmod']
      rw [mul_div_mul_left _ _ (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _))]
      simp
    let g : ModularForm 𝒮ℒ 0 :=
      { toFun := f
        slash_action_eq' := by
          rintro _ ⟨γ, rfl⟩
          exact hslash γ
        holo' := CuspForm.discriminant.holo'.div hFmdiff (fun z => h z)
        bdd_at_cusps' {c} hc := by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
          rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
          intro γ _
          rw [hslash γ]
          exact hlim.isBigO_one ℝ }
    obtain ⟨c0, hc0⟩ := ModularFormClass.levelOne_weight_zero_const g
    have hg : Tendsto (⇑g) atImInfty (𝓝 0) := hlim
    rw [hc0] at hg
    have hc00 : c0 = 0 := tendsto_const_nhds_iff.mp hg
    have h1 : f UpperHalfPlane.I = c0 := congr_fun hc0 UpperHalfPlane.I
    rw [hc00] at h1
    rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact ModularForm.discriminant_ne_zero _ h2
    · exact h _ h2

/-- Theorem 3.10 (Milne, pdf p. 101): every elliptic curve `E` over `ℂ` is isomorphic to `E(Λ)`
for some lattice `Λ`.  Elliptic curves are Mathlib's Weierstrass curves with `Δ ≠ 0`, and an
isomorphism is a change of variables (`WeierstrassCurve.VariableChange`). -/
@[kb "milne2006ec" "Ch. III, Thm. 3.10, pdf p. 101"]
theorem thm_3_10 (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ L : PeriodPair, ∃ C : WeierstrassCurve.VariableChange ℂ, C • E = curveOf L := by
  obtain ⟨τ, hτ⟩ := jFun_surjective E.j
  refine ⟨periodPairOf τ, ?_⟩
  exact WeierstrassCurve.exists_variableChange_of_j_eq E (curveOf (periodPairOf τ))
    (by rw [j_curveOf]; exact hτ.symm)

end NumberFieldKB.MilneEC.III
