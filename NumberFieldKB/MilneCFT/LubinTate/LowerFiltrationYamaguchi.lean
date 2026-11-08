import NumberFieldKB.MilneCFT.LubinTate.ExtensionYamaguchi
import NumberFieldKB.MilneCFT.LubinTate.KroneckerWeber
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement

/-!
# Proposition 4.1 (the lower ramification filtration of `K_{π,n}`) (Milne, *CFT*, I, §4), proved

`lubinTateLowerFiltration`: the named statement `LubinTateLowerFiltration K Ω h` for every `h` (for `K : Type`).

Through the embedding `ι` of Yamaguchi's level field (`LubinTate/TorsionYamaguchi.lean`):
* `ι` maps Yamaguchi's level valuation ring `R` (the integral closure of `𝒪_K`, `IsIntegralClosure`) onto
  `integers L`, `L = K_{π,n+1}` (`levRingEquiv`), and `𝔪_L = ι(𝔪_R)` (`mem_maxIdealL_pow_iff_addVal`): membership
  in `𝔪_L^k` is `k ≤ v_R`;
* `integers L = 𝒪_K[x₀]` (Yamaguchi's `standardLubinTatePrimitivePointInteger_adjoin_eq_top`), so
  `σ ∈ G_j ⟺ v(σ x₀ - x₀) ≥ j + 1` (`mem_ramificationGroup_iff`);
* `χ(u) x₀ - x₀ = ι([u]λ - λ)` and Yamaguchi's displacement valuations
  (`standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem` and its interval form) give
  `χ(U^{(i)}) = G_{q^i - 1}` and `χ(u) ∉ G_{q^i}` for `u ∈ U^{(i)} \ U^{(i+1)}`.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "𝔽" => LubinTate.standardLocalField K
local notation "𝔢" => LubinTate.standardLocalFieldIntegerEquiv K

/-! ### Discrete valuation rings -/

/-- In a discrete valuation ring, a nonzero non-unit generates an ideal with radical the maximal ideal. -/
theorem radical_span_eq_maximalIdeal {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {c : R}
    (hc0 : c ≠ 0) (hc : c ∈ IsLocalRing.maximalIdeal R) :
    (Ideal.span {c}).radical = IsLocalRing.maximalIdeal R := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hne : Ideal.span {c} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.span_singleton_one] at hk
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.1 (hk ▸ Ideal.span_le.2 (Set.singleton_subset_iff.2 hc)))
  rw [hk, ← Ideal.span_singleton_pow, ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.radical_pow _ hk0, (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical]

theorem mem_maximalIdeal_pow_iff_addVal {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (r : R) (k : ℕ) : r ∈ IsLocalRing.maximalIdeal R ^ k ↔ (k : ℕ∞) ≤ IsDiscreteValuationRing.addVal R r := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_eq_mul, mul_one]

section Level

variable {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)

local notation "𝔥" => isUniformizer_of_irreducible hπ
local notation "𝕃" => ltField Ω π (n + 1)

include hπ

/-! ### The level field and the level ring inside `Ω` -/

theorem levEmb_fieldRange : (levEmb Ω hπ n).fieldRange = 𝕃 := by
  haveI : FiniteDimensional K (LevF hπ n) := LubinTate.standardLubinTateLevelField_finiteDimensional 𝔥 n
  haveI : FiniteDimensional K (levEmb Ω hπ n).fieldRange :=
    (AlgEquiv.ofInjectiveField (levEmb Ω hπ n)).toLinearEquiv.finiteDimensional
  symm
  apply IntermediateField.eq_of_le_of_finrank_eq
  · rw [ltField_eq_adjoin Ω hπ n, IntermediateField.adjoin_simple_le_iff]
    exact ⟨LubinTate.standardLubinTateLevelGenerator 𝔥 n, rfl⟩
  · rw [finrank_ltField Ω hπ n]
    have h := (AlgEquiv.ofInjectiveField (levEmb Ω hπ n)).toLinearEquiv.finrank_eq
    rw [LubinTate.standardLubinTateLevelField_finrank] at h
    exact h

theorem toΩ_mem (r : LevR hπ n) : toΩ Ω hπ n r ∈ 𝕃 := by
  rw [← levEmb_fieldRange Ω hπ n]
  exact ⟨r.1, rfl⟩

/-- Integrality over `𝒪_𝔽` and over `𝒪[K]` agree. -/
theorem isIntegral_vs_iff (y : LevF hπ n) :
    IsIntegral (𝔽).valuationSubring y ↔ IsIntegral 𝒪[K] y := by
  constructor
  · intro h
    exact IsIntegral.map_of_comp_eq ((𝔢).symm : (𝔽).valuationSubring →+* 𝒪[K]) (RingHom.id _)
      (by ext a; rfl) h
  · intro h
    exact IsIntegral.map_of_comp_eq (𝔢 : 𝒪[K] →+* (𝔽).valuationSubring) (RingHom.id _) (by ext a; rfl) h

theorem isIntegral_toΩ (r : LevR hπ n) : IsIntegral 𝒪[K] (toΩ Ω hπ n r) := by
  haveI := LubinTate.standardLubinTateLevelCompleteDVF_isIntegralClosure 𝔥 n
  have h1 : IsIntegral (𝔽).valuationSubring (r.1 : LevF hπ n) :=
    IsIntegralClosure.isIntegral_iff.2 ⟨r, rfl⟩
  have h1' := (isIntegral_vs_iff hπ n _).1 h1
  exact h1'.map ((levEmb Ω hπ n).restrictScalars 𝒪[K])

/-- The level ring, as a map into `integers L`. -/
def levRingHom : LevR hπ n →+* integers 𝕃 where
  toFun r := ⟨⟨toΩ Ω hπ n r, toΩ_mem Ω hπ n r⟩, by
    have h := isIntegral_toΩ Ω hπ n r
    exact (isIntegral_algHom_iff ((IsScalarTower.toAlgHom 𝒪[K] 𝕃 Ω)) (algebraMap 𝕃 Ω).injective).1 h⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (toΩ Ω hπ n)))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul (toΩ Ω hπ n) a b))
  map_zero' := Subtype.ext (Subtype.ext (map_zero (toΩ Ω hπ n)))
  map_add' a b := Subtype.ext (Subtype.ext (map_add (toΩ Ω hπ n) a b))

theorem coe_levRingHom (r : LevR hπ n) : (((levRingHom Ω hπ n r : integers 𝕃) : 𝕃) : Ω) = toΩ Ω hπ n r := rfl

theorem levRingHom_bijective : Function.Bijective (levRingHom Ω hπ n) := by
  refine ⟨fun a b h => toΩ_injective Ω hπ n (by
    have := congrArg (fun x : integers 𝕃 => ((x : 𝕃) : Ω)) h
    simpa [coe_levRingHom] using this), ?_⟩
  rintro ⟨⟨a, haL⟩, haI⟩
  haveI := LubinTate.standardLubinTateLevelCompleteDVF_isIntegralClosure 𝔥 n
  rw [← levEmb_fieldRange Ω hπ n] at haL
  obtain ⟨y, rfl⟩ := haL
  have h1 : IsIntegral 𝒪[K] (levEmb Ω hπ n y) :=
    (isIntegral_algHom_iff ((IsScalarTower.toAlgHom 𝒪[K] 𝕃 Ω)) (algebraMap 𝕃 Ω).injective).2 haI
  have h2 : IsIntegral 𝒪[K] y :=
    (isIntegral_algHom_iff ((levEmb Ω hπ n).restrictScalars 𝒪[K]) (levEmb Ω hπ n).injective).1 h1
  obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := LevR hπ n)).1 ((isIntegral_vs_iff hπ n y).2 h2)
  refine ⟨r, ?_⟩
  ext
  rw [coe_levRingHom]
  change levEmb Ω hπ n r.1 = _
  rw [show r.1 = y from hr]
  rfl

/-- **The level ring is `integers L`.** -/
def levRingEquiv : LevR hπ n ≃+* integers 𝕃 := RingEquiv.ofBijective _ (levRingHom_bijective Ω hπ n)

theorem coe_levRingEquiv (r : LevR hπ n) : (((levRingEquiv Ω hπ n r : integers 𝕃) : 𝕃) : Ω) = toΩ Ω hπ n r := rfl

/-! ### The maximal ideal -/

theorem X_dvd_ltPolyIter (m : ℕ) : X ∣ ltPolyIter π m := by
  induction m with
  | zero => exact dvd_rfl
  | succ m ih =>
    rw [ltPolyIter_succ]
    obtain ⟨g, hg⟩ := ih
    have hq : 1 ≤ resCard K := resCard_pos hπ
    refine ⟨C π * g + X ^ (resCard K - 1) * g ^ resCard K, ?_⟩
    rw [hg]
    simp only [ltPoly, add_comp, mul_comp, C_comp, X_comp, X_pow_comp]
    obtain ⟨r, hr⟩ : ∃ r, resCard K = r + 1 := ⟨resCard K - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel]
    ring

/-- The image of `π` in the level ring. -/
abbrev piR : LevR hπ n := LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n (𝔢 π)

theorem toΩ_piR : toΩ Ω hπ n (piR hπ n) = algebraMap K Ω (π : K) := toΩ_coeff Ω hπ n π

theorem piR_mem_maximalIdeal : piR hπ n ∈ IsLocalRing.maximalIdeal (LevR hπ n) := by
  -- `π = -(f^{(n)}(λ))^{q-1}` and `f^{(n)}(λ) ∈ λ R`
  set lam := LubinTate.standardLubinTatePrimitivePointInteger 𝔥 n
  have hlam : lam ∈ IsLocalRing.maximalIdeal (LevR hπ n) :=
    (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).uniformizer_mem_maximalIdeal
      (LubinTate.standardLubinTatePrimitivePoint_isUniformizer 𝔥 n)
  set y := eval₂ (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n) lam
    (LubinTate.standardLubinTatePolynomialIterate 𝔽 (𝔢 π) n)
  have hy : y ∈ IsLocalRing.maximalIdeal (LevR hπ n) := by
    obtain ⟨g, hg⟩ := X_dvd_ltPolyIter hπ n
    simp only [y, polynomialIterate_eq_map, hg, Polynomial.map_mul, Polynomial.map_X, eval₂_mul, eval₂_X]
    exact Ideal.mul_mem_right _ _ hlam
  have hrel : piR hπ n = -(y ^ (resCard K - 1)) := by
    apply toΩ_injective (SeparableClosure K) hπ n
    have h := aeval_x0_primPoly (SeparableClosure K) hπ n
    rw [primPoly, LubinTate.standardLubinTatePrimitivePolynomialOverField_formula, map_add, map_pow, aeval_C,
      polynomialIterate_eq_map, Polynomial.map_map] at h
    have hc : (algebraMap (𝔽).valuationSubring K).comp (𝔢 : 𝒪[K] →+* (𝔽).valuationSubring) =
        algebraMap 𝒪[K] K := by ext; rfl
    rw [hc] at h
    have hy' : toΩ (SeparableClosure K) hπ n y = aeval (x0 (SeparableClosure K) hπ n) ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) := by
      simp only [y, polynomialIterate_eq_map]; exact toΩ_eval₂ (SeparableClosure K) hπ n _ _
    rw [RingHom.map_neg, RingHom.map_pow, hy', toΩ_piR]
    have : algebraMap K (SeparableClosure K) ((𝔢 π : (𝔽).valuationSubring) : K) = algebraMap K (SeparableClosure K) (π : K) := rfl
    rw [this, resCard_eq] at h
    linear_combination h
  rw [hrel]
  have h2 : 1 < resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  have hq : 1 ≤ resCard K - 1 := by omega
  exact (Ideal.neg_mem_iff _).2 (Ideal.pow_mem_of_mem _ hy _ (by omega))

theorem piR_ne_zero : piR hπ n ≠ 0 := by
  intro h
  have := toΩ_piR (SeparableClosure K) hπ n
  rw [h, map_zero, eq_comm, map_eq_zero_iff _ (algebraMap K (SeparableClosure K)).injective] at this
  exact hπ.ne_zero (Subtype.ext this)

theorem levRingEquiv_piR :
    levRingEquiv Ω hπ n (piR hπ n) = algebraMap 𝒪[K] (integers 𝕃) π := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_levRingEquiv, toΩ_piR]
  exact (IsScalarTower.algebraMap_apply 𝒪[K] K Ω π).symm

set_option maxHeartbeats 1600000 in
/-- **`𝔪_L` corresponds to the maximal ideal of the level ring.** -/
theorem comap_maxIdealL_lev :
    (maxIdealL 𝕃).comap (levRingEquiv Ω hπ n : LevR hπ n →+* integers 𝕃) =
      IsLocalRing.maximalIdeal (LevR hπ n) := by
  have hJ : Ideal.map (algebraMap 𝒪[K] (integers 𝕃)) 𝓂[K] =
      Ideal.span {levRingEquiv Ω hπ n (piR hπ n)} := by
    rw [levRingEquiv_piR, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hJ' : Ideal.comap (levRingEquiv Ω hπ n : LevR hπ n →+* integers 𝕃)
      (Ideal.span {levRingEquiv Ω hπ n (piR hπ n)}) = Ideal.span {piR hπ n} := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton, RingEquiv.coe_toRingHom]
    exact map_dvd_iff (levRingEquiv Ω hπ n)
  rw [maxIdealL, Ideal.comap_radical, hJ, hJ']
  exact radical_span_eq_maximalIdeal (piR_ne_zero hπ n) (piR_mem_maximalIdeal hπ n)

theorem mem_maxIdealL_pow_iff_addVal (r : LevR hπ n) (k : ℕ) :
    levRingEquiv Ω hπ n r ∈ maxIdealL 𝕃 ^ k ↔ (k : ℕ∞) ≤ IsDiscreteValuationRing.addVal (LevR hπ n) r := by
  have h1 : maxIdealL 𝕃 = (IsLocalRing.maximalIdeal (LevR hπ n)).map (levRingEquiv Ω hπ n : LevR hπ n →+* integers 𝕃) := by
    rw [← comap_maxIdealL_lev Ω hπ n]
    exact (Ideal.map_comap_of_surjective (levRingEquiv Ω hπ n : LevR hπ n →+* integers 𝕃) (levRingEquiv Ω hπ n).surjective _).symm
  rw [h1, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap, ← mem_maximalIdeal_pow_iff_addVal (R := LevR hπ n)]
  simp

/-! ### `integers L = 𝒪_K[x₀]` and the ramification groups -/

/-- `x₀` as an element of `integers L`. -/
abbrev x0I : integers 𝕃 := levRingEquiv Ω hπ n (LubinTate.standardLubinTatePrimitivePointInteger 𝔥 n)

theorem levRingEquiv_comp_algebraMap :
    ((levRingEquiv Ω hπ n : LevR hπ n →+* integers 𝕃)).comp (algebraMap (𝔽).valuationSubring (LevR hπ n)) =
      (algebraMap 𝒪[K] (integers 𝕃)).comp ((𝔢).symm : (𝔽).valuationSubring →+* 𝒪[K]) := by
  ext a
  change toΩ Ω hπ n (algebraMap (𝔽).valuationSubring (LevR hπ n) a) = algebraMap K Ω ((((𝔢).symm a : 𝒪[K])) : K)
  exact (levEmb Ω hπ n).commutes (a : K)

/-- Every element of `integers L` is a polynomial in `x₀` with coefficients in `𝒪[K]`. -/
theorem exists_poly (a : integers 𝕃) : ∃ p : 𝒪[K][X], a = eval₂ (algebraMap 𝒪[K] (integers 𝕃)) (x0I Ω hπ n) p := by
  obtain ⟨r, rfl⟩ := (levRingEquiv Ω hπ n).surjective a
  have hr : r ∈ Algebra.adjoin (𝔽).valuationSubring {LubinTate.standardLubinTatePrimitivePointInteger 𝔥 n} := by
    rw [LubinTate.standardLubinTatePrimitivePointInteger_adjoin_eq_top]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
  obtain ⟨p, rfl⟩ := hr
  refine ⟨p.map ((𝔢).symm : (𝔽).valuationSubring →+* 𝒪[K]), ?_⟩
  rw [eval₂_map, ← levRingEquiv_comp_algebraMap Ω hπ n]
  change (levRingEquiv Ω hπ n : LevR hπ n →+* integers 𝕃) (eval₂ _ _ p) = _
  rw [Polynomial.hom_eval₂]
  rfl

theorem galRestrictInt_comp_algebraMap (σ : Gal(𝕃/K)) :
    (galRestrictInt 𝕃 σ).comp (algebraMap 𝒪[K] (integers 𝕃)) = algebraMap 𝒪[K] (integers 𝕃) := by
  refine RingHom.ext fun r => Subtype.ext ?_
  show σ (algebraMap 𝒪[K] 𝕃 r) = algebraMap 𝒪[K] 𝕃 r
  have : algebraMap 𝒪[K] 𝕃 r = algebraMap K 𝕃 (r : K) := rfl
  rw [this]; exact σ.commutes _

/-- **`σ ∈ G_j` iff `v(σ x₀ - x₀) ≥ j + 1`.** -/
theorem mem_ramificationGroup_iff (σ : Gal(𝕃/K)) (j : ℕ) (r : LevR hπ n)
    (hr : levRingEquiv Ω hπ n r = galRestrictInt 𝕃 σ (x0I Ω hπ n) - x0I Ω hπ n) :
    σ ∈ ramificationGroup 𝕃 j ↔ ((j + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal (LevR hπ n) r := by
  rw [← mem_maxIdealL_pow_iff_addVal Ω hπ n, hr]
  constructor
  · intro hσ
    obtain ⟨b, hb, hba⟩ := hσ ((x0I Ω hπ n : integers 𝕃) : 𝕃) (x0I Ω hπ n).2
    have : b = galRestrictInt 𝕃 σ (x0I Ω hπ n) - x0I Ω hπ n := Subtype.ext hba
    rwa [← this]
  · intro hmem a ha
    obtain ⟨p, hp⟩ := exists_poly Ω hπ n ⟨a, ha⟩
    obtain ⟨w, hw⟩ := Polynomial.sub_dvd_eval_sub (galRestrictInt 𝕃 σ (x0I Ω hπ n)) (x0I Ω hπ n)
      (p.map (algebraMap 𝒪[K] (integers 𝕃)))
    refine ⟨(galRestrictInt 𝕃 σ (x0I Ω hπ n) - x0I Ω hπ n) * w, Ideal.mul_mem_right _ _ hmem, ?_⟩
    rw [← hw, eval_map, eval_map, ← hp, ← galRestrictInt_comp_algebraMap Ω hπ n σ, ← Polynomial.hom_eval₂, ← hp]
    rfl

/-! ### Displacements -/

theorem galRestrictInt_x0I_sub {χ : (𝒪[K] ⧸ 𝓂[K] ^ (n + 1))ˣ ≃* Gal(𝕃/K)}
    (hχ : ∀ (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π (n + 1)),
      ((χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom u) ⟨α, mem_ltField hα⟩ : 𝕃) : Ω) =
        ltAct hπ (n + 1) u α) (u : 𝒪[K]ˣ) :
    galRestrictInt 𝕃 (χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom u)) (x0I Ω hπ n) -
        x0I Ω hπ n =
      levRingEquiv Ω hπ n (LubinTate.standardLubinTatePrimitivePointIntegerAction 𝔥 n
        (LubinTate.standardLocalFieldIntegerUnitsEquiv K u) - LubinTate.standardLubinTatePrimitivePointInteger 𝔥 n) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((χ _ ⟨x0 Ω hπ n, _⟩ : 𝕃) : Ω) - x0 Ω hπ n = toΩ Ω hπ n (_ - _)
  rw [RingHom.map_sub, hχ u (x0 Ω hπ n) (x0_mem Ω hπ n), ltAct_x0]
  rfl

theorem principal_iff (u : 𝒪[K]ˣ) (k : ℕ) (hk : k ≤ n + 1) :
    ((resCard K ^ k : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal (LevR hπ n)
        (LubinTate.standardLubinTatePrimitivePointIntegerAction 𝔥 n (LubinTate.standardLocalFieldIntegerUnitsEquiv K u) -
          LubinTate.standardLubinTatePrimitivePointInteger 𝔥 n) ↔ (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ k := by
  rw [← resCard_eq, LubinTate.standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem 𝔥 n _ k hk,
    LubinTate.standardLocalFieldIntegerUnitsEquiv_mem_higherPrincipalUnitGroup_iff]
  rfl

theorem principal_iff_interval (u : 𝒪[K]ˣ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n + 1) :
    ((resCard K ^ (k - 1) + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal (LevR hπ n)
        (LubinTate.standardLubinTatePrimitivePointIntegerAction 𝔥 n (LubinTate.standardLocalFieldIntegerUnitsEquiv K u) -
          LubinTate.standardLubinTatePrimitivePointInteger 𝔥 n) ↔ (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ k := by
  have hq : 1 < resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  rw [LubinTate.standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem_of_pow_interval 𝔥 n _ k
      (resCard K ^ (k - 1)) hk1 hk le_rfl (by
        rw [resCard_eq]
        exact Nat.pow_lt_pow_right hq (by omega)),
    LubinTate.standardLocalFieldIntegerUnitsEquiv_mem_higherPrincipalUnitGroup_iff]
  rfl

end Level

end NumberFieldKB.MilneCFT.LocalCFT
