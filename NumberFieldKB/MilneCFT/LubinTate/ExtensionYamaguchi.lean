import NumberFieldKB.MilneCFT.LubinTate.TorsionYamaguchi
import NumberFieldKB.MilneCFT.LocalCFT.TotallyRamifiedTauCeti

/-!
# Proposition 3.4 and Theorem 3.6 (Milne, *CFT*, I, §3), proved

`lubinTateTorsionModule`: the named statement `LubinTateTorsionModule K Ω` (Proposition 3.4), and
`lubinTateExtensionTheorem`: the named statement `LubinTateExtensionTheorem K Ω` (Theorem 3.6), for `K : Type`.

Proof of Theorem 3.6 at level `n + 1`, from `LubinTate/TorsionYamaguchi.lean` (`x₀ = ι λ_n`):
* `K_{π,n+1} = K(x₀)`, since every point of `Λ_{n+1}` is `[a] x₀`, a polynomial in `x₀`;
* `x₀` is a root of Yamaguchi's irreducible `P = (f^{(n)})^{q-1} + π` of degree `(q-1) q^n`, so this is the degree;
* `N(-x₀) = π` from the constant term of `P`, so `π` is a norm, and the extension is totally ramified by
  Exercise 1.16 (`totallyRamifiedNormInput`);
* the extension is Galois (all roots of `P` divide `f^{(n+1)} = f^{(n)} P`, so lie in `Λ_{n+1} ⊆ K(x₀)`), and
  `σ ↦ (a mod π^{n+1})` for `σ x₀ = [a] x₀` is an injective homomorphism `Gal → (A/𝔪^{n+1})^×` between groups of the
  same order; its inverse is the `χ` of the theorem, and `χ(u)` acts on all of `Λ_{n+1}` by `[u]`.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT.LocalCFT

/-! ## Level `0` (any `K`) -/

section Zero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem ltTorsion_zero (π : 𝒪[K]) : ltTorsion Ω π 0 = {0} := by
  ext α
  simp [ltTorsion, ltPolyIter, mem_rootSet]

theorem ltAct_zero_level {π : 𝒪[K]} (hπ : Irreducible π) (a : 𝒪[K]) : ltAct hπ 0 a (0 : Ω) = 0 := by
  rw [ltAct, ltEval_eq_of_ringHom hπ 0 ((algebraMap 𝒪[K] Ω).comp PowerSeries.constantCoeff) 0]
  · simp [(lubinTateEnd _ (ltPoly_mem hπ) a).constantCoeff_eq_zero]
  · intro p
    simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, IsScalarTower.algebraMap_apply 𝒪[K] K Ω]
  · simp [ltPolyIter]

end Zero

/-! ## Level `n + 1` -/

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "𝔽" => LubinTate.standardLocalField K
local notation "𝔢" => LubinTate.standardLocalFieldIntegerEquiv K

variable (K) in
/-- **Proposition 3.4, proved** (Milne, *CFT*, I, Proposition 3.4): `Λ_n ≅ A/(π^n)` through `a ↦ [a] x₀`. -/
@[kb "milne2020cft" "Ch. I, Proposition 3.4"]
theorem lubinTateTorsionModule : LubinTateTorsionModule K Ω := by
  refine ⟨fun {π} hπ n => ?_⟩
  cases n with
  | zero =>
    refine ⟨0, by rw [ltTorsion_zero]; rfl, fun a b => ?_, fun α hα => ?_⟩
    · simp [ltAct_zero_level hπ]
    · rw [ltTorsion_zero] at hα
      exact ⟨0, by rw [hα, ltAct_zero_level hπ]⟩
  | succ n =>
    exact ⟨x0 Ω hπ n, x0_mem Ω hπ n, ltAct_x0_eq_iff Ω hπ n, exists_ltAct_x0 Ω hπ n⟩

/-- Evaluation commutes with the inclusion of an intermediate field. -/
theorem coe_aeval_intermediate (L : IntermediateField K Ω) (y : L) (r : K[X]) :
    ((aeval y r : L) : Ω) = aeval (y : Ω) r :=
  (aeval_algebraMap_apply Ω y r).symm

/-- Evaluation commutes with a `K`-automorphism. -/
theorem algEquiv_aeval {L : Type*} [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (y : L) (r : K[X]) :
    σ (aeval y r) = aeval (σ y) r :=
  (aeval_algHom_apply (σ : L →ₐ[K] L) y r).symm

section Level

variable {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)

local notation "𝔥" => isUniformizer_of_irreducible hπ

include hπ

/-- Yamaguchi's primitive polynomial `P = (f^{(n)})^{q-1} + π` over `K`. -/
abbrev primPoly (π : 𝒪[K]) (n : ℕ) : K[X] := LubinTate.standardLubinTatePrimitivePolynomialOverField 𝔽 (𝔢 π) n

theorem aeval_x0_primPoly : aeval (x0 Ω hπ n) (primPoly π n) = 0 := by
  have h1 : aeval ((LubinTate.standardLubinTateLevelGenerator 𝔥 n : LevF hπ n) : SeparableClosure K)
      (primPoly π n) = 0 := by
    rw [LubinTate.standardLubinTateLevelGenerator_coe, aeval_def, ← eval_map]
    exact LubinTate.chosenStandardLubinTatePrimitiveRoot_isRoot 𝔥 n
  have h2 : aeval (LubinTate.standardLubinTateLevelGenerator 𝔥 n : LevF hπ n) (primPoly π n) = 0 := by
    apply Subtype.val_injective
    rw [IntermediateField.coe_zero, ← h1]
    exact (aeval_algebraMap_apply (R := K) (SeparableClosure K)
      (LubinTate.standardLubinTateLevelGenerator 𝔥 n : LevF hπ n) (primPoly π n)).symm
  have : x0 Ω hπ n = levEmb Ω hπ n (LubinTate.standardLubinTateLevelGenerator 𝔥 n) := rfl
  rw [this, aeval_algHom_apply, h2, map_zero]

theorem minpoly_x0 : minpoly K (x0 Ω hπ n) = primPoly π n :=
  (minpoly.eq_of_irreducible_of_monic (LubinTate.standardLubinTatePrimitivePolynomialOverField_irreducible 𝔥 n)
    (aeval_x0_primPoly Ω hπ n) (LubinTate.standardLubinTatePrimitivePolynomialOverField_monic _ _ n)).symm

theorem isIntegral_x0 : IsIntegral K (x0 Ω hπ n) :=
  ⟨_, LubinTate.standardLubinTatePrimitivePolynomialOverField_monic _ _ n, by
    rw [← aeval_def]; exact aeval_x0_primPoly Ω hπ n⟩

/-- `ltAct a α` is a polynomial in `α` with coefficients in `K` (independent of `α`). -/
theorem ltAct_eq_aeval (m : ℕ) (a : 𝒪[K]) (α : Ω) :
    ltAct hπ m a α = aeval α (((lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) (ltPoly_mem hπ)
      a).toPowerSeries %ʷ ((ltPolyIter π m : 𝒪[K][X]) : PowerSeries 𝒪[K])).map (algebraMap 𝒪[K] K)) := rfl

/-- **`K_{π,n+1} = K(x₀)`.** -/
theorem ltField_eq_adjoin : ltField Ω π (n + 1) = IntermediateField.adjoin K {x0 Ω hπ n} := by
  apply le_antisymm
  · rw [ltField, IntermediateField.adjoin_le_iff]
    intro α hα
    obtain ⟨a, rfl⟩ := exists_ltAct_x0 Ω hπ n α hα
    rw [ltAct_eq_aeval]
    exact IntermediateField.algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact mem_ltField (x0_mem Ω hπ n)

theorem finrank_ltField : Module.finrank K (ltField Ω π (n + 1)) = (resCard K - 1) * resCard K ^ n := by
  rw [ltField_eq_adjoin Ω hπ n, IntermediateField.adjoin.finrank (isIntegral_x0 Ω hπ n), minpoly_x0,
    LubinTate.standardLubinTatePrimitivePolynomialOverField_natDegree]
  rfl

/-! ### `π` is a norm; total ramification -/

theorem norm_eq_of_eq {L₁ L₂ : IntermediateField K Ω} (h : L₁ = L₂) (x : Ω) (h1 : x ∈ L₁) (h2 : x ∈ L₂) :
    Algebra.norm K (⟨x, h1⟩ : L₁) = Algebra.norm K (⟨x, h2⟩ : L₂) := by
  subst h; rfl

theorem norm_neg_x0_adjoin :
    Algebra.norm K (-(IntermediateField.AdjoinSimple.gen K (x0 Ω hπ n))) = (π : K) := by
  set pb := IntermediateField.adjoin.powerBasis (isIntegral_x0 Ω hπ n)
  have hgen : pb.gen = IntermediateField.AdjoinSimple.gen K (x0 Ω hπ n) := IntermediateField.adjoin.powerBasis_gen _
  have hmin : minpoly K pb.gen = primPoly π n := by
    rw [hgen, IntermediateField.minpoly_gen, minpoly_x0]
  rw [LocalFieldTheory.algebraNorm_neg, ← hgen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hmin,
    LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero, pb.finrank, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul]
  simp

theorem isNorm_succ : primeUnit hπ ∈ normGroup (ltField Ω π (n + 1)) := by
  have hmem : x0 Ω hπ n ∈ ltField Ω π (n + 1) := mem_ltField (x0_mem Ω hπ n)
  have hN : Algebra.norm K (⟨-(x0 Ω hπ n), neg_mem hmem⟩ : ltField Ω π (n + 1)) = π := by
    rw [norm_eq_of_eq Ω hπ (ltField_eq_adjoin Ω hπ n) _ _ (neg_mem (IntermediateField.mem_adjoin_simple_self K _))]
    exact norm_neg_x0_adjoin Ω hπ n
  have hne : (⟨-(x0 Ω hπ n), neg_mem hmem⟩ : ltField Ω π (n + 1)) ≠ 0 := by
    intro h
    rw [h, Algebra.norm_zero] at hN
    exact hπ.ne_zero (Subtype.ext hN.symm)
  refine ⟨Units.mk0 _ hne, ?_⟩
  ext
  simp [hN]

theorem isNorm_zero : primeUnit hπ ∈ normGroup (ltField Ω π 0) := by
  have h1 : Module.finrank K (ltField Ω π 0) = 1 := by
    rw [IntermediateField.finrank_eq_one_iff, ltField, ltTorsion_zero]
    exact IntermediateField.adjoin_zero
  refine ⟨Units.map (algebraMap K (ltField Ω π 0) : K →* ltField Ω π 0) (primeUnit hπ), ?_⟩
  ext
  simp [Algebra.norm_algebraMap, h1]

theorem totallyRamified_succ : IsTotallyRamifiedExt (ltField Ω π (n + 1)) :=
  ((totallyRamifiedNormInput K Ω).iff (ltField Ω π (n + 1))).2 ⟨π, hπ, isNorm_succ Ω hπ n⟩

/-! ### The Galois group -/

theorem resCard_pos : 1 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt.le

theorem ltPolyIter_succ_eq_mul : (ltPolyIter π (n + 1)).map (algebraMap 𝒪[K] K) =
    (ltPolyIter π n).map (algebraMap 𝒪[K] K) * primPoly π n := by
  have hc : (algebraMap (𝔽).valuationSubring K).comp (𝔢 : 𝒪[K] →+* (𝔽).valuationSubring) =
      algebraMap 𝒪[K] K := by ext; rfl
  rw [primPoly, LubinTate.standardLubinTatePrimitivePolynomialOverField_formula, polynomialIterate_eq_map,
    Polynomial.map_map, hc, resCard_eq, ltPolyIter_succ]
  obtain ⟨r, hr⟩ : ∃ r, resCard K = r + 1 := ⟨resCard K - 1, by have := resCard_pos hπ; omega⟩
  simp only [ltPoly, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.X_pow_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, hr,
    Nat.add_sub_cancel]
  have hπK : ((𝔢 π : (𝔽).valuationSubring) : K) = algebraMap 𝒪[K] K π := rfl
  rw [hπK]
  ring

theorem primPoly_root_mem (β : Ω) (hβ : aeval β (primPoly π n) = 0) : β ∈ ltTorsion Ω π (n + 1) := by
  rw [ltTorsion, mem_rootSet]
  refine ⟨((ltPolyIter_aux hπ (n + 1)).1.map _).ne_zero, ?_⟩
  rw [ltPolyIter_succ_eq_mul hπ n, map_mul, hβ, mul_zero]

theorem isGalois_ltField : IsGalois K (ltField Ω π (n + 1)) := by
  have hsep := LubinTate.standardLubinTatePrimitivePolynomialOverField_separable 𝔥 n
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hspl : ((primPoly π n).map (algebraMap K Ω)).Splits := IsSepClosed.splits_codomain _ hsep
  have heq : IntermediateField.adjoin K ((primPoly π n).rootSet Ω) = ltField Ω π (n + 1) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro β hβ
      rw [mem_rootSet] at hβ
      exact mem_ltField (primPoly_root_mem Ω hπ n β hβ.2)
    · rw [ltField_eq_adjoin Ω hπ n]
      apply IntermediateField.adjoin.mono
      rintro _ rfl
      rw [mem_rootSet]
      exact ⟨(LubinTate.standardLubinTatePrimitivePolynomialOverField_monic _ _ n).ne_zero,
        aeval_x0_primPoly Ω hπ n⟩
  haveI := IntermediateField.adjoin_rootSet_isSplittingField hspl
  rw [← heq]
  exact IsGalois.of_separable_splitting_field hsep

local notation "𝕃" => ltField Ω π (n + 1)

/-- `x₀` as an element of `K_{π,n+1}`. -/
def x0L : 𝕃 := ⟨x0 Ω hπ n, mem_ltField (x0_mem Ω hπ n)⟩

/-- A `K`-automorphism of `K_{π,n+1}` commutes with `[c]`. -/
theorem galois_ltAct (σ : 𝕃 ≃ₐ[K] 𝕃) (c : 𝒪[K]) (y : 𝕃) (hy : ltAct hπ (n + 1) c (y : Ω) ∈ 𝕃) :
    ((σ ⟨ltAct hπ (n + 1) c (y : Ω), hy⟩ : 𝕃) : Ω) = ltAct hπ (n + 1) c ((σ y : 𝕃) : Ω) := by
  set R := (((lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) (ltPoly_mem hπ)
      c).toPowerSeries %ʷ ((ltPolyIter π (n + 1) : 𝒪[K][X]) : PowerSeries 𝒪[K])).map (algebraMap 𝒪[K] K))
  have h1 : (⟨ltAct hπ (n + 1) c (y : Ω), hy⟩ : 𝕃) = aeval y R :=
    Subtype.ext (by rw [coe_aeval_intermediate Ω _]; rfl)
  rw [h1, algEquiv_aeval, coe_aeval_intermediate Ω _]
  rfl

theorem galois_x0_mem (σ : 𝕃 ≃ₐ[K] 𝕃) : ((σ (x0L Ω hπ n) : 𝕃) : Ω) ∈ ltTorsion Ω π (n + 1) := by
  have h := x0_mem Ω hπ n
  rw [ltTorsion, mem_rootSet] at h ⊢
  refine ⟨h.1, ?_⟩
  have h0 : aeval (x0L Ω hπ n) ((ltPolyIter π (n + 1)).map (algebraMap 𝒪[K] K)) = 0 :=
    Subtype.ext (by rw [coe_aeval_intermediate Ω _]; exact h.2)
  rw [← coe_aeval_intermediate Ω _, ← algEquiv_aeval, h0, map_zero]
  rfl

/-- The `a` with `σ x₀ = [a] x₀`. -/
def galA (σ : 𝕃 ≃ₐ[K] 𝕃) : 𝒪[K] := (exists_ltAct_x0 Ω hπ n _ (galois_x0_mem Ω hπ n σ)).choose

theorem galA_spec (σ : 𝕃 ≃ₐ[K] 𝕃) :
    ((σ (x0L Ω hπ n) : 𝕃) : Ω) = ltAct hπ (n + 1) (galA Ω hπ n σ) (x0 Ω hπ n) :=
  (exists_ltAct_x0 Ω hπ n _ (galois_x0_mem Ω hπ n σ)).choose_spec

theorem galois_ltAct_x0 (σ : 𝕃 ≃ₐ[K] 𝕃) (c : 𝒪[K]) :
    ((σ ⟨ltAct hπ (n + 1) c (x0 Ω hπ n), mem_ltField (ltAct_x0_mem Ω hπ n c)⟩ : 𝕃) : Ω) =
      ltAct hπ (n + 1) (c * galA Ω hπ n σ) (x0 Ω hπ n) := by
  refine (galois_ltAct Ω hπ n σ c (x0L Ω hπ n) _).trans ?_
  rw [galA_spec, ltAct_ltAct_x0]

theorem maxIdeal_pow_eq (k : ℕ) : 𝓂[K] ^ k = Ideal.span {π ^ k} := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem pow_not_mem : π ^ n ∉ Ideal.span {π ^ (n + 1)} := by
  rw [Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h1 : π ^ n * 1 = π ^ n * (π * c) := by
    calc π ^ n * 1 = π ^ n := mul_one _
      _ = π ^ (n + 1) * c := hc
      _ = π ^ n * (π * c) := by ring
  have := mul_left_cancel₀ (pow_ne_zero n hπ.ne_zero) h1
  exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨c, this.symm⟩)

theorem galA_isUnit (σ : 𝕃 ≃ₐ[K] 𝕃) : IsUnit (galA Ω hπ n σ) := by
  by_contra hu
  have hm : galA Ω hπ n σ ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal _).2 hu
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  obtain ⟨c, hc⟩ := hm
  set F := (ltPolyIter π n).map (algebraMap 𝒪[K] K)
  have h1 : aeval ((σ (x0L Ω hπ n) : 𝕃) : Ω) F = 0 := by
    rw [galA_spec, aeval_iter_ltAct_x0, hc, ← ltAct_zero_x0 Ω hπ n, ltAct_x0_eq_iff, sub_zero]
    exact Ideal.mem_span_singleton.2 ⟨c, by ring⟩
  have h2 : aeval (x0L Ω hπ n) F = 0 := by
    apply σ.injective
    apply Subtype.val_injective
    rw [map_zero, algEquiv_aeval, coe_aeval_intermediate Ω _]
    exact h1
  have h3 : aeval (x0 Ω hπ n) F = 0 := by
    have := coe_aeval_intermediate Ω _ (x0L Ω hπ n) F
    rw [h2] at this
    exact this.symm
  rw [← ltAct_one_x0 Ω hπ n, aeval_iter_ltAct_x0, mul_one, ← ltAct_zero_x0 Ω hπ n, ltAct_x0_eq_iff,
    sub_zero] at h3
  exact pow_not_mem hπ n h3

theorem galA_mk_eq_iff (σ : 𝕃 ≃ₐ[K] 𝕃) (a : 𝒪[K]) :
    Ideal.Quotient.mk (𝓂[K] ^ (n + 1)) (galA Ω hπ n σ) = Ideal.Quotient.mk (𝓂[K] ^ (n + 1)) a ↔
      ((σ (x0L Ω hπ n) : 𝕃) : Ω) = ltAct hπ (n + 1) a (x0 Ω hπ n) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, maxIdeal_pow_eq hπ, ← ltAct_x0_eq_iff Ω hπ n, galA_spec]

/-- `σ ↦ (galA σ mod 𝔪^{n+1})`, a homomorphism `Gal(K_{π,n+1}/K) → (A/𝔪^{n+1})^×`. -/
def galPsi : (𝕃 ≃ₐ[K] 𝕃) →* (𝒪[K] ⧸ 𝓂[K] ^ (n + 1))ˣ where
  toFun σ := Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom (galA_isUnit Ω hπ n σ).unit
  map_one' := by
    ext
    simp only [Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
    rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))), galA_mk_eq_iff, ltAct_one_x0]
    rfl
  map_mul' σ τ := by
    ext
    simp only [Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mul]
    rw [← map_mul, galA_mk_eq_iff, AlgEquiv.mul_apply]
    have hτ : τ (x0L Ω hπ n) = ⟨ltAct hπ (n + 1) (galA Ω hπ n τ) (x0 Ω hπ n),
        mem_ltField (ltAct_x0_mem Ω hπ n _)⟩ := Subtype.ext (galA_spec Ω hπ n τ)
    rw [hτ, galois_ltAct_x0, mul_comm]

theorem galPsi_apply (σ : 𝕃 ≃ₐ[K] 𝕃) :
    ((galPsi Ω hπ n σ : (𝒪[K] ⧸ 𝓂[K] ^ (n + 1))ˣ) : 𝒪[K] ⧸ 𝓂[K] ^ (n + 1)) =
      Ideal.Quotient.mk (𝓂[K] ^ (n + 1)) (galA Ω hπ n σ) := rfl

theorem galPsi_injective : Function.Injective (galPsi Ω hπ n) := by
  intro σ τ h
  have h' := congrArg (fun u : (𝒪[K] ⧸ 𝓂[K] ^ (n + 1))ˣ => (u : 𝒪[K] ⧸ 𝓂[K] ^ (n + 1))) h
  simp only [galPsi_apply] at h'
  have hx : ((σ (x0L Ω hπ n) : 𝕃) : Ω) = ((τ (x0L Ω hπ n) : 𝕃) : Ω) := by
    rw [(galA_mk_eq_iff Ω hπ n σ _).1 h', galA_spec]
  apply AlgEquiv.coe_algHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K (ltField_eq_adjoin Ω hπ n) ?_
  rintro x rfl
  exact Subtype.ext hx

theorem galPsi_bijective : Function.Bijective (galPsi Ω hπ n) := by
  haveI := isGalois_ltField Ω hπ n
  have hfin : Finite (𝒪[K] ⧸ 𝓂[K] ^ (n + 1)) := by
    rw [maxIdeal_pow_eq hπ]
    exact Nat.finite_of_card_ne_zero (by rw [card_quot_span_pow hπ]; exact pow_ne_zero _ (by have := resCard_pos hπ; omega))
  refine (galPsi_injective Ω hπ n).bijective_of_nat_card_le ?_
  rw [card_units_quot_maximalIdeal_pow (n + 1) (by omega), IsGalois.card_aut_eq_finrank, finrank_ltField Ω hπ n]
  simp

/-- **Theorem 3.6 (b) at level `n + 1`**: the isomorphism `χ : (A/𝔪^{n+1})^× ≃ Gal(K_{π,n+1}/K)`, the class of a
unit `u` acting by `[u]` on `Λ_{n+1}`. -/
theorem galois_succ : ∃ χ : (𝒪[K] ⧸ 𝓂[K] ^ (n + 1))ˣ ≃* (𝕃 ≃ₐ[K] 𝕃),
    ∀ (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π (n + 1)),
      ((χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom u) ⟨α, mem_ltField hα⟩ : 𝕃) : Ω) =
        ltAct hπ (n + 1) u α := by
  refine ⟨(MulEquiv.ofBijective (galPsi Ω hπ n) (galPsi_bijective Ω hπ n)).symm, fun u α hα => ?_⟩
  set σ := (MulEquiv.ofBijective (galPsi Ω hπ n) (galPsi_bijective Ω hπ n)).symm
    (Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom u)
  have hσ : galPsi Ω hπ n σ = Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom u :=
    (MulEquiv.ofBijective (galPsi Ω hπ n) (galPsi_bijective Ω hπ n)).apply_symm_apply _
  have hmk : Ideal.Quotient.mk (𝓂[K] ^ (n + 1)) (galA Ω hπ n σ) = Ideal.Quotient.mk (𝓂[K] ^ (n + 1)) u := by
    rw [← galPsi_apply, hσ]; rfl
  have hsub : galA Ω hπ n σ - u ∈ Ideal.span {π ^ (n + 1)} := by
    rw [← maxIdeal_pow_eq hπ]; exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 hmk
  obtain ⟨c, rfl⟩ := exists_ltAct_x0 Ω hπ n α hα
  have hα' : (⟨ltAct hπ (n + 1) c (x0 Ω hπ n), mem_ltField hα⟩ : 𝕃) =
      ⟨ltAct hπ (n + 1) c (x0 Ω hπ n), mem_ltField (ltAct_x0_mem Ω hπ n c)⟩ := rfl
  rw [hα', galois_ltAct_x0, ltAct_ltAct_x0, ltAct_x0_eq_iff]
  have : c * galA Ω hπ n σ - (u : 𝒪[K]) * c = c * (galA Ω hπ n σ - u) := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hsub

end Level

variable (K) in
/-- **Theorem 3.6, proved** (Milne, *CFT*, I, Theorem 3.6), for `K : Type`: for `n ≥ 1`, `K_{π,n}/K` is totally
ramified of degree `(q-1)q^{n-1}`, `(A/𝔪^n)^× ≅ Gal(K_{π,n}/K)` with `u` acting by `[u]` on `Λ_n`, and `π` is a
norm from `K_{π,n}`. -/
@[kb "milne2020cft" "Ch. I, Theorem 3.6"]
theorem lubinTateExtensionTheorem : LubinTateExtensionTheorem K Ω where
  totallyRamified := fun {π} hπ n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact totallyRamified_succ Ω hπ m
  finrank_eq := fun {π} hπ n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [finrank_ltField Ω hπ m, Nat.add_sub_cancel]
  galois := fun {π} hπ n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact galois_succ Ω hπ m
  isNorm := fun {π} hπ n => by
    cases n with
    | zero => exact isNorm_zero Ω hπ
    | succ m => exact isNorm_succ Ω hπ m

end NumberFieldKB.MilneCFT.LocalCFT
