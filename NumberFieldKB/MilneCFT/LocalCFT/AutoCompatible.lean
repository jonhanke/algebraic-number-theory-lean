import NumberFieldKB.MilneCFT.LocalCFT.Basic
import QuadFormsKB.Citation
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Henselian
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.NormalizedValuation

/-!
# Automatic compatibility of local field structures on a finite extension

Let `E / K` be a finite extension of fields, both carrying the structure of a nonarchimedean local
field (a valuative relation and a topology). Then the valuative relation of `E` restricts to that of
`K`, with no continuity hypothesis on `algebraMap K E` (`valuativeExtension_of_finite`).

The argument (Hensel plus discreteness; cf. Milne, *CFT*, III, Lemma 3.2 setting): let `F` be the
normalized valuation of `E`, with values in `ℤᵐ⁰`.
1. `F` is nontrivial on `K`: otherwise `F ≤ 1` on `K`, hence on `E` (integrality), which is absurd.
2. For `y` in the maximal ideal of `K` and a prime `ℓ` larger than the residue characteristic, `1 + y`
   is an `ℓ`-th power in `𝒪[K]` (Hensel), so `log F (1 + y)` is divisible by `ℓ` for all large `ℓ`,
   hence `F (1 + y) = 1`, hence `F y ≤ 1`.
3. For a unit `u`, `u ^ (q - 1) ∈ 1 + 𝓂[K]`, so `F u ≤ 1`. Thus `F ≤ 1` on `𝒪[K]`.
4. As `𝓂[K] = (π)` and `F π ≠ 1` by step 1, `F ≤ 1` exactly on `𝒪[K]`.
-/

open scoped ValuativeRel WithZero

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

section AutoCompatible

variable (K E : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The normalized `ℤᵐ⁰`-valued valuation of a nonarchimedean local field. -/
private def intVal (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] : Valuation E ℤᵐ⁰ :=
  (ValuativeRel.valuation E).map
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E :
      ValuativeRel.ValueGroupWithZero E →*₀o ℤᵐ⁰)

private theorem intVal_le_one_iff {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (x : E) : intVal E x ≤ 1 ↔ ValuativeRel.valuation E x ≤ 1 := by
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E (ValuativeRel.valuation E x) ≤ 1 ↔ _
  simpa only [map_one] using
    (OrderIsoClass.map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E)
      (a := ValuativeRel.valuation E x) (b := 1))


variable {K E}

open IsLocalRing in
private theorem valuation_lt_one_of_mem_maximalIdeal {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) :
    ValuativeRel.valuation K (x : K) < 1 := by
  refine lt_of_le_of_ne x.2 fun h => ?_
  exact (mem_nonunits_iff.mp hx)
    ((Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (ValuativeRel.valuation K))).mpr h)

open IsLocalRing in
private theorem mem_maximalIdeal_of_valuation_lt_one {x : 𝒪[K]}
    (hx : ValuativeRel.valuation K (x : K) < 1) : x ∈ 𝓂[K] := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hx.ne ((Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (ValuativeRel.valuation K))).mp hu)

section

variable [Algebra K E]

open IsLocalRing in
/-- Step 2: the normalized valuation of `E` is `≤ 1` on the maximal ideal of `𝒪[K]`. -/
private theorem intVal_le_one_of_mem_maximalIdeal (y : 𝒪[K]) (hy : y ∈ 𝓂[K]) :
    intVal E (algebraMap K E (y : K)) ≤ 1 := by
  set g : ℤᵐ⁰ := intVal E (algebraMap K E (1 + (y : K))) with hg
  have hunit : IsUnit (1 + y) := by
    by_contra h
    have h1 : (1 + y) ∈ 𝓂[K] := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    have : (1 : 𝒪[K]) ∈ 𝓂[K] := by simpa using (𝓂[K]).sub_mem h1 hy
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hg0 : g ≠ 0 := by
    rw [hg, Ne, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K E).injective]
    exact fun h => hunit.ne_zero (Subtype.ext (by simpa using h))
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField 𝒪[K])
  have hg1 : g = 1 := by
    have hdiv : ∀ ℓ : ℕ, ℓ.Prime → p < ℓ → (ℓ : ℤ) ∣ WithZero.log g := by
      intro ℓ hℓ hpℓ
      have hℓk : ((ℓ : ℕ) : ResidueField 𝒪[K]) ≠ 0 := by
        intro h
        rw [CharP.cast_eq_zero_iff (ResidueField 𝒪[K]) p] at h
        rcases (Nat.dvd_prime hℓ).mp h with h1 | h1
        · exact CharP.char_ne_one (ResidueField 𝒪[K]) p h1
        · exact absurd h1 hpℓ.ne
      have hℓu : IsUnit ((ℓ : ℕ) : 𝒪[K]) := by
        refine isUnit_of_map_unit (residue 𝒪[K]) _ ?_
        rw [map_natCast]
        exact (hℓk.isUnit : IsUnit _)
      obtain ⟨x, hx, -⟩ := TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq
        hℓu (x₀ := 1) (u := 1 + y) isUnit_one (by
          rw [map_one, one_pow, map_add, map_one, (residue_eq_zero_iff y).mpr hy, add_zero])
      have : g = intVal E (algebraMap K E (x : K)) ^ ℓ := by
        rw [hg, ← map_pow, ← map_pow]
        congr 2
        have := congrArg (fun z : 𝒪[K] => (z : K)) hx
        simpa using this.symm
      rw [this, WithZero.log_pow, nsmul_eq_mul]
      exact dvd_mul_right _ _
    by_contra hne
    have hm : WithZero.log g ≠ 0 := by
      intro h
      exact hne (by rw [← WithZero.exp_log hg0, h]; simp)
    obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (max (p + 1) ((WithZero.log g).natAbs + 1))
    have hpℓ := le_max_left (p + 1) ((WithZero.log g).natAbs + 1)
    have h1 := Int.natAbs_dvd_natAbs.mpr (hdiv ℓ hℓ (by omega))
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) (by simpa using h1)
    have := le_max_right (p + 1) ((WithZero.log g).natAbs + 1)
    omega
  by_contra hlt
  push Not at hlt
  have : g = intVal E (algebraMap K E (y : K)) := by
    rw [hg, map_add, map_one, Valuation.map_add_eq_of_lt_right]
    rwa [map_one]
  rw [hg1] at this
  exact absurd hlt (by rw [← this]; exact lt_irrefl _)

open IsLocalRing in
/-- Step 3: the normalized valuation of `E` is `≤ 1` on `𝒪[K]`. -/
private theorem intVal_le_one_of_mem_integer (x : 𝒪[K]) :
    intVal E (algebraMap K E (x : K)) ≤ 1 := by
  by_cases hx : IsUnit x
  · have hk : (Nat.card (ResidueField 𝒪[K]) - 1) ≠ 0 := by
      have : 1 < Nat.card (ResidueField 𝒪[K]) := Finite.one_lt_card
      omega
    have := Fintype.ofFinite (ResidueField 𝒪[K])
    have hres : residue 𝒪[K] (x ^ (Nat.card (ResidueField 𝒪[K]) - 1) - 1) = 0 := by
      rw [map_sub, map_pow, map_one, Nat.card_eq_fintype_card,
        FiniteField.pow_card_sub_one_eq_one, sub_self]
      exact (hx.map (residue 𝒪[K])).ne_zero
    have hz := intVal_le_one_of_mem_maximalIdeal (E := E) _ ((residue_eq_zero_iff _).mp hres)
    have hpow : intVal E (algebraMap K E ((x : K) ^ (Nat.card (ResidueField 𝒪[K]) - 1))) ≤ 1 := by
      have hz' : intVal E (algebraMap K E ((x : K) ^ (Nat.card (ResidueField 𝒪[K]) - 1) - 1))
          ≤ 1 := by simpa using hz
      have h2 := (intVal E).map_add
        (algebraMap K E ((x : K) ^ (Nat.card (ResidueField 𝒪[K]) - 1) - 1)) (algebraMap K E 1)
      rw [← map_add, sub_add_cancel, map_one, map_one] at h2
      exact h2.trans (max_le hz' le_rfl)
    rw [map_pow, map_pow] at hpow
    exact (pow_le_one_iff hk).mp hpow
  · exact intVal_le_one_of_mem_maximalIdeal x ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hx))

/-- Step 1 and 4: the normalized valuation of `E` is `< 1` at a uniformizer of `K`. -/
private theorem intVal_lt_one_of_irreducible [FiniteDimensional K E] {π : 𝒪[K]}
    (hπ : Irreducible π) : intVal E (algebraMap K E (π : K)) < 1 := by
  refine lt_of_le_of_ne (intVal_le_one_of_mem_integer π) fun h1 => ?_
  have hall : ∀ x : K, intVal E (algebraMap K E x) ≤ 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    obtain ⟨u, n, hu, hx⟩ := TauCeti.exists_eq_mul_zpow_of_irreducible hπ (Units.mk0 x hx0)
    have hx' : x = (u : K) * (π : K) ^ n := by
      simpa using congrArg Units.val hx
    rw [hx', map_mul, map_mul, map_zpow₀, map_zpow₀, h1, one_zpow, mul_one]
    exact intVal_le_one_of_mem_integer (E := E) ⟨(u : K), hu.le⟩
  obtain ⟨γ, h0, hlt⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := E)
  obtain ⟨e₀, he₀⟩ := ValuativeRel.valuation_surjective γ
  have he0 : e₀ ≠ 0 := by
    rintro rfl
    simp at he₀
    exact h0.ne he₀
  have hbig : 1 < ValuativeRel.valuation E e₀⁻¹ := by
    rw [map_inv₀, he₀]
    exact one_lt_inv₀ h0 |>.mpr hlt
  -- every element of `E` would be integral over the valuation ring, hence of value `≤ 1`
  have hint : IsIntegral (intVal E).integer e₀⁻¹ := by
    obtain ⟨q, hmon, hq⟩ := (Algebra.IsIntegral.isIntegral (R := K) e₀⁻¹ : IsIntegral K e₀⁻¹)
    let φ : K →+* (intVal E).integer := (algebraMap K E).codRestrict _ hall
    refine ⟨q.map φ, hmon.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hq
  have := Valuation.Integers.mem_of_integral (Valuation.integer.integers (intVal E)) hint
  exact absurd ((intVal_le_one_iff _).mp this) (not_le.mpr hbig)

/-- The unit balls of `K` and `E` correspond. -/
private theorem valuation_le_one_iff [FiniteDimensional K E] (x : K) :
    ValuativeRel.valuation K x ≤ 1 ↔ ValuativeRel.valuation E (algebraMap K E x) ≤ 1 := by
  rw [← intVal_le_one_iff (algebraMap K E x)]
  refine ⟨fun h => intVal_le_one_of_mem_integer (⟨x, h⟩ : 𝒪[K]), fun h => ?_⟩
  by_contra hx
  push Not at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hinv : ValuativeRel.valuation K x⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
  have hm : (⟨x⁻¹, hinv.le⟩ : 𝒪[K]) ∈ 𝓂[K] := mem_maximalIdeal_of_valuation_lt_one hinv
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨z, hz⟩ := hm
  have hz' : x⁻¹ = (z : K) * (π : K) := congrArg (fun w : 𝒪[K] => (w : K)) hz.symm
  have hlt : intVal E (algebraMap K E x⁻¹) < 1 := by
    rw [hz', map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (intVal_le_one_of_mem_integer z))
      (intVal_lt_one_of_irreducible hπ)
  have hprod : intVal E (algebraMap K E x) * intVal E (algebraMap K E x⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one]
  have : intVal E (algebraMap K E x) * intVal E (algebraMap K E x⁻¹) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left' h) hlt
  exact absurd hprod this.ne

end

/-- **Any two nonarchimedean local field structures on a finite extension are compatible**, with no
continuity hypothesis on the structure map.

The argument (Hensel plus discreteness; cf. Milne, *CFT*, III, Lemma 3.2 setting): for `y` in the
maximal ideal of `K`, `1 + y` is an `ℓ`-th power for every prime `ℓ` larger than the residue
characteristic (Hensel's lemma in the complete discrete valuation ring `𝒪[K]`), so the normalized
`E`-valuation of `1 + y` is divisible by all large primes, hence trivial; so `𝒪[K]` is contained in
the valuation ring of `E` restricted to `K`. That restriction is nontrivial since `E` is integral
over `K`, and `𝒪[K]` is a discrete valuation ring, so the two valuation rings of `K` agree. -/
@[kb "milne2020cft" "v4.03, Ch. III, §3 (finite extensions of local fields; compatibility of valuations)"]
theorem valuativeExtension_of_finite (K E : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra K E] [FiniteDimensional K E] :
    ValuativeExtension K E := by
  refine ⟨fun a b => ?_⟩
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation E),
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hb' : algebraMap K E b ≠ 0 := by simpa using hb
    have hvb : 0 < ValuativeRel.valuation K b := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hb)
    have hvb' : 0 < ValuativeRel.valuation E (algebraMap K E b) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hb')
    have e1 : ValuativeRel.valuation K a ≤ ValuativeRel.valuation K b ↔
        ValuativeRel.valuation K (a / b) ≤ 1 := by rw [map_div₀, div_le_one₀ hvb]
    have e2 : ValuativeRel.valuation E (algebraMap K E a) ≤ ValuativeRel.valuation E (algebraMap K E b)
        ↔ ValuativeRel.valuation E (algebraMap K E (a / b)) ≤ 1 := by
      rw [map_div₀, map_div₀, div_le_one₀ hvb']
    rw [e1, e2]
    exact (valuation_le_one_iff (K := K) (E := E) (a / b)).symm

end AutoCompatible

end NumberFieldKB.MilneCFT.LocalCFT
