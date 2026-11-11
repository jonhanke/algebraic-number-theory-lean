import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.PowerSubgroup.Basic
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# Local lemmas for Chevalley's congruence theorem

Steps 1 and 4 of the proof of Chevalley's theorem:
* `exists_pow_eq_of_valued_sub_one_lt` (Hensel): an element of a number field `F` congruent to `1` at a finite
  place `v` not dividing `n` is an `n`-th power in the completion `F_v` (Tau Ceti
  `unitFiltration_one_le_range_powMonoidHom_of_isUnit`).
* `valued_sub_one_lt_of_liesOver`: a congruence `a ≡ 1 mod v` persists at every place `w` above `v`.
* `valuation_eq_one_of_valued_sub_one_lt`: an element congruent to `1` at `v` is a `v`-unit.
* `exists_pow_prime_eq_of_pow_eq` (pure field algebra): if `ζ` is a primitive `w`-th root of unity, `w ∣ n`,
  `ξ ^ w = 1` and `ξ` is an `n`-th power, then for every prime `ℓ` dividing the order of `ξ`, `ζ` is an `ℓ`-th
  power.
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch8.Chevalley

open scoped WithZero
open ValuativeRel Valued.integer

private theorem lt_one_le {x : ℤᵐ⁰} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  induction x using WithZero.recZeroCoe with
  | zero => exact zero_le
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    have h' : Multiplicative.toAdd a < 0 := h
    have : Multiplicative.toAdd a ≤ -1 := by omega
    have : a ≤ Multiplicative.ofAdd (-1 : ℤ) := this
    exact WithZero.coe_le_coe.mpr this

/-- **Hensel's lemma for principal units.** -/
theorem exists_pow_eq_of_valued_sub_one_lt {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (hn : (n : 𝓞 F) ∉ v.asIdeal) {a : F}
    (ha : Valued.v (algebraMap F (v.adicCompletion F) a - 1) < 1) :
    ∃ b : v.adicCompletion F, b ^ n = algebraMap F (v.adicCompletion F) a := by
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have hu : IsUnit (n : 𝒪[v.adicCompletion F]) := by
    rw [IsLocalRing.isUnit_natCast_iff_not_dvd]
    rwa [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
  set x := algebraMap F (v.adicCompletion F) a with hx
  have h1 : Valued.v x = 1 := by
    have : x = 1 + (x - 1) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left]
    · simp
    · simpa using ha
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hmem : (Units.mk0 x hx0) ∈ TauCeti.unitFiltration (v.adicCompletion F) 1 := by
    rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff]
    refine ⟨h1, ?_⟩
    simpa using lt_one_le ha
  obtain ⟨b, hb⟩ := TauCeti.unitFiltration_one_le_range_powMonoidHom_of_isUnit hu hmem
  refine ⟨b, ?_⟩
  have := congrArg Units.val hb
  simpa using this

/-- **Congruences go up.** -/
theorem valued_sub_one_lt_of_liesOver {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 F))
    [w.asIdeal.LiesOver v.asIdeal] {a : K}
    (ha : Valued.v (algebraMap K (v.adicCompletion K) a - 1) < 1) :
    Valued.v (algebraMap F (w.adicCompletion F) (algebraMap K F a) - 1) < 1 := by
  have h := HeightOneSpectrum.valued_adicCompletionExtension K F v w (algebraMap K (v.adicCompletion K) a - 1)
  have e : HeightOneSpectrum.adicCompletionExtension K F v w (algebraMap K (v.adicCompletion K) a - 1) = algebraMap F (w.adicCompletion F) (algebraMap K F a) - 1 := by
    rw [map_sub, map_one]
    congr 1
    exact HeightOneSpectrum.adicCompletionExtension_coe K F v w a
  rw [e] at h
  rw [h]
  exact pow_lt_one' ha (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

/-- An element congruent to `1` at `v` is a `v`-unit. -/
theorem valuation_eq_one_of_valued_sub_one_lt {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {a : F}
    (ha : Valued.v (algebraMap F (v.adicCompletion F) a - 1) < 1) : v.valuation F a = 1 := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have : algebraMap F (v.adicCompletion F) a = 1 + (algebraMap F (v.adicCompletion F) a - 1) := by
    ring
  rw [show (a : v.adicCompletion F) = algebraMap F (v.adicCompletion F) a from rfl, this,
    Valuation.map_add_eq_of_lt_left]
  · simp
  · simpa using ha

/-- **Roots of unity that are `n`-th powers.** -/
theorem exists_pow_prime_eq_of_pow_eq {F : Type*} [Field F] {w n ℓ : ℕ} (hw : 0 < w) (hℓ : ℓ.Prime)
    {ζ : F} (hζ : IsPrimitiveRoot ζ w) (hwn : w ∣ n) {ξ y : F} (hξ : ξ ^ w = 1) (hy : y ^ n = ξ)
    (hℓξ : ℓ ∣ orderOf ξ) : ∃ z : F, z ^ ℓ = ζ := by
  have hF : ℓ ≠ 1 := hℓ.ne_one
  have hw0 : w ≠ 0 := hw.ne'
  obtain ⟨c, hc⟩ := hwn
  obtain ⟨s, u, hu, hwu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hw0 ℓ hF
  have hordw : orderOf ξ ∣ w := orderOf_dvd_of_pow_eq_one hξ
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exfalso
      have : ℓ ∣ u := by
        have := hℓξ.trans hordw
        rwa [hwu, h0, pow_zero, one_mul] at this
      exact hu this
    · exact h0
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hwu
    exact hw0 hwu
  -- t is a `w`-th root of ξ
  set t : F := y ^ c with ht
  have htw : t ^ w = ξ := by
    rw [ht, ← pow_mul, mul_comm, ← hc, hy]
  have hTpos : 0 < orderOf t := by
    refine orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨w * w, by positivity, ?_⟩)
    rw [pow_mul, htw, hξ]
  set T := orderOf t with hT
  have hm : orderOf ξ = T / Nat.gcd T w := by
    rw [← htw, orderOf_pow' _ hw0]
  -- ℓ^(s+1) ∣ T
  have hdvdT : ℓ ^ (s + 1) ∣ T := by
    by_contra hnot
    obtain ⟨e, T', hT', hTe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hTpos.ne' ℓ hF
    have hes : e ≤ s := by
      by_contra h
      exact hnot (hTe ▸ Dvd.dvd.mul_right (pow_dvd_pow ℓ (by omega)) _)
    have hew : ℓ ^ e ∣ w := hwu ▸ Dvd.dvd.mul_right (pow_dvd_pow ℓ hes) _
    have heT : ℓ ^ e ∣ T := hTe ▸ Dvd.intro _ rfl
    obtain ⟨g', hg'⟩ := Nat.dvd_gcd heT hew
    have hgT : T = Nat.gcd T w * (T / Nat.gcd T w) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left T w)).symm
    have hcancel : T' = g' * (T / Nat.gcd T w) := by
      have h1 : ℓ ^ e * T' = ℓ ^ e * (g' * (T / Nat.gcd T w)) := by
        have h2 : T = ℓ ^ e * (g' * (T / Nat.gcd T w)) := by
          rw [← mul_assoc, ← hg']
          exact hgT
        rw [← hTe]
        exact h2
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hℓ.pos e) h1
    apply hT'
    have : ℓ ∣ T / Nat.gcd T w := hm ▸ hℓξ
    rw [hcancel]
    exact Dvd.dvd.mul_left this _
  have hT0 : T ≠ 0 := hTpos.ne'
  obtain ⟨ρ, hρ⟩ : ∃ ρ : F, IsPrimitiveRoot ρ (ℓ ^ (s + 1)) := by
    have hp0 : T / ℓ ^ (s + 1) ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd hTpos hdvdT) (pow_pos hℓ.pos _)).ne'
    have := (IsPrimitiveRoot.orderOf t).pow_of_dvd hp0 (Nat.div_dvd_of_dvd hdvdT)
    rw [Nat.div_div_self hdvdT hT0] at this
    exact ⟨_, this⟩
  have hρ' : IsPrimitiveRoot (ρ ^ ℓ) (ℓ ^ s) := by
    have := hρ.pow_of_dvd hℓ.ne_zero (dvd_pow_self ℓ (Nat.succ_ne_zero s))
    rwa [pow_succ, Nat.mul_div_cancel _ hℓ.pos] at this
  have hη : IsPrimitiveRoot (ζ ^ u) (ℓ ^ s) := by
    have := hζ.pow_of_dvd hu0 (Dvd.intro_left _ hwu.symm)
    rwa [hwu, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hu0)] at this
  have : NeZero (ℓ ^ s) := ⟨(pow_pos hℓ.pos s).ne'⟩
  obtain ⟨i, -, hi⟩ := hρ'.eq_pow_of_pow_eq_one (ξ := ζ ^ u)
    (by rw [← pow_mul, mul_comm, ← hwu]; exact hζ.pow_eq_one)
  have hcop : IsCoprime (u : ℤ) ((ℓ ^ s : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.Coprime.pow_right s ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hu).symm)
  obtain ⟨a, b, hab⟩ := hcop
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hw0
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  refine ⟨ρ ^ ((i : ℤ) * a) * ζ ^ (((ℓ ^ s' : ℕ) : ℤ) * b), ?_⟩
  have e1 : (ρ ^ ((i : ℤ) * a)) ^ ℓ = (ζ ^ u) ^ a := by
    rw [← hi, ← zpow_natCast, ← zpow_natCast (ρ ^ ℓ) i, ← zpow_natCast ρ ℓ, ← zpow_mul, ← zpow_mul,
      ← zpow_mul]
    congr 1
    ring
  have e2 : (ζ ^ (((ℓ ^ s' : ℕ) : ℤ) * b)) ^ ℓ = ζ ^ (b * ((ℓ ^ (s' + 1) : ℕ) : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, e1, e2, ← zpow_natCast ζ u, ← zpow_mul, ← zpow_add₀ hζ0]
  have : (u : ℤ) * a + b * ((ℓ ^ (s' + 1) : ℕ) : ℤ) = 1 := by
    rw [← hab]; ring
  rw [this, zpow_one]

end NumberFieldKB.MilneCFT.Ch8.Chevalley
