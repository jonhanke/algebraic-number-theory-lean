import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.NormTrace
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import QuadFormsKB.Citation

namespace NumberFieldKB.MilneCFT.Ch8

open Polynomial in
/-- The trace of a primitive `p`-th root of unity in a `p`-th cyclotomic field is `-1`. -/
lemma trace_primitiveRoot_eq_neg_one {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {p} ℚ K] {η : K} (hη : IsPrimitiveRoot η p) :
    Algebra.trace ℚ K η = -1 := by
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.out.pos
  have hmin := hη.minpoly_eq_cyclotomic_of_irreducible hirr
  have h := PowerBasis.trace_gen_eq_nextCoeff_minpoly (hη.powerBasis ℚ)
  rw [IsPrimitiveRoot.powerBasis_gen] at h
  rw [h, ← hmin]
  have hp2 := hp.out.two_le
  have hdeg : (cyclotomic p ℚ).natDegree = p - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp.out]
  have hne : (cyclotomic p ℚ).natDegree ≠ 0 := by omega
  rw [nextCoeff_of_natDegree_pos (by omega), hdeg, cyclotomic_prime, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_eq_single (p - 1 - 1)]
  · simp
  · intro b hb hne'
    simp [Ne.symm hne']
  · intro h'
    exfalso; apply h'
    simp; omega

/-- `Tr_{K/ℚ}((ζ - 1)^(p-1)) = p`. -/
lemma trace_sub_one_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Algebra.trace ℚ K ((ζ - 1) ^ (p - 1)) = p := by
  have hp1 := hp.out
  have hp2' := hp1.two_le
  have key : (ζ - 1) ^ (p - 1) =
      ∑ j ∈ Finset.range p, ((-1 : ℚ) ^ (p - 1 - j) * ((p - 1).choose j : ℚ)) • ζ ^ j := by
    have hpp : p - 1 + 1 = p := by omega
    rw [sub_eq_add_neg, add_pow, hpp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Rat.smul_def]
    push_cast
    ring
  have : NeZero p := ⟨hp1.ne_zero⟩
  have ht : ∀ j ∈ Finset.range p,
      Algebra.trace ℚ K (ζ ^ j) = -1 + if j = 0 then (p : ℚ) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases h0 : j = 0
    · subst h0
      rw [pow_zero, ← map_one (algebraMap ℚ K), Algebra.trace_algebraMap,
        IsCyclotomicExtension.Rat.finrank p K, Nat.totient_prime hp1]
      simp
      rw [Nat.cast_sub (by omega)]
      simp
      ring
    · have hcop : Nat.Coprime j p :=
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp1).2
          (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)))
      rw [trace_primitiveRoot_eq_neg_one (hζ.pow_of_coprime j hcop)]
      simp [h0]
  rw [key, map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_congr rfl (fun j hj => by rw [ht j hj])]
  have hbin : ∑ j ∈ Finset.range p, ((-1 : ℚ) ^ (p - 1 - j) * ((p - 1).choose j : ℚ)) = 0 := by
    have := add_pow (1 : ℚ) (-1) (p - 1)
    have hpp : p - 1 + 1 = p := by omega
    rw [hpp] at this
    simp only [add_neg_cancel, one_pow, one_mul] at this
    rw [zero_pow (by omega)] at this
    exact this.symm
  simp only [smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (Finset.range p) 0 (fun j => (-1 : ℚ) ^ (p - 1 - j) * ((p - 1).choose j : ℚ) * (p : ℚ))]
  simp only [mul_neg, mul_one, Finset.sum_neg_distrib, hbin]
  simp [Finset.mem_range, hp1.pos]
  have hev : (-1 : ℚ) ^ (p - 1) = 1 := by
    obtain ⟨k, hk⟩ := hp1.odd_of_ne_two hp2
    have h2 : p - 1 = 2 * k := by omega
    rw [h2, pow_mul]
    simp
  rw [hev, one_mul]

open IsCyclotomicExtension.Rat NumberField in
/-- For $p$ an odd prime, $\zeta$ a primitive $p$-th root of unity in a $p$-th cyclotomic field $K$ over $\mathbb Q$,
and $\lambda = 1 - \zeta$: $N_{K/\mathbb Q}(1 - \lambda^{p-1})$ is an integer congruent to $1 - p$ modulo $p^2$.
(Used for the normalization $(\eta_p, \lambda) = \zeta$ in Milne, *Class Field Theory*, VIII, Prop. 5.12.) -/
theorem norm_one_sub_lam_pow_modEq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∃ N : ℤ, Algebra.norm ℚ (1 - (1 - ζ) ^ (p - 1)) = N ∧ N ≡ 1 - p [ZMOD (p : ℤ) ^ 2] := by
  have hp1 := hp.out
  obtain ⟨k, hk⟩ := hp1.odd_of_ne_two hp2
  have h2 : p - 1 = 2 * k := by omega
  obtain ⟨u, hu⟩ := associated_zeta_sub_one_pow_prime p hζ
  set z : 𝓞 K := hζ.toInteger with hz
  have hzK : algebraMap (𝓞 K) K z = ζ := hζ.coe_toInteger
  set w : 𝓞 K := -((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) with hw
  have hpow : (z - 1) ^ (p - 1) = (p : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [← hu, mul_assoc]
    simp
  have hev : (1 - z) ^ (p - 1) = (z - 1) ^ (p - 1) := by
    rw [h2, pow_mul, pow_mul]
    congr 1
    ring
  have h1 : (1 : 𝓞 K) - (1 - z) ^ (p - 1) = 1 + (p : ℤ) • w := by
    rw [hev, hpow, hw]
    simp
    ring
  have hcoe : (1 - (1 - ζ) ^ (p - 1) : K) = ((1 + (p : ℤ) • w : 𝓞 K) : K) := by
    rw [← h1]
    simp [hzK]
  have htr : Algebra.trace ℤ (𝓞 K) w = -1 := by
    have h3 : Algebra.trace ℤ (𝓞 K) ((z - 1) ^ (p - 1)) = p := by
      have : ((Algebra.trace ℤ (𝓞 K) ((z - 1) ^ (p - 1)) : ℤ) : ℚ) = p := by
        rw [Algebra.coe_trace_int]
        simpa [hzK] using trace_sub_one_pow hp2 hζ
      exact_mod_cast this
    have h4 : (z - 1) ^ (p - 1) = (p : ℤ) • (-w) := by
      rw [hpow, hw]; simp
    rw [h4, map_smul, map_neg, smul_eq_mul] at h3
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp1.ne_zero
    apply mul_left_cancel₀ hp0
    linarith
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (A := ℤ) (B := 𝓞 K) (p : ℤ) w
  refine ⟨Algebra.norm ℤ (1 + (p : ℤ) • w), ?_, ?_⟩
  · rw [hcoe, ← Algebra.coe_norm_int]
  · rw [hr, htr]
    refine Int.modEq_iff_dvd.mpr ?_
    exact ⟨-r, by ring⟩

end NumberFieldKB.MilneCFT.Ch8
