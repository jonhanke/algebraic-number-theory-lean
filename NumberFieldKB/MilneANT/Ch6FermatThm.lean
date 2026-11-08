import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch6Cyclotomic
import NumberFieldKB.MilneANT.Ch6Fermat

/-!
# Milne, *Algebraic Number Theory*, Theorem 6.8: the first case of Fermat's last theorem for regular primes

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

* **Theorem 6.8** (`theorem_6_8`, `theorem_6_8_of_isRegularPrime`): let $p$ be an odd prime not dividing the class
  number of $\mathbb Q[\zeta_p]$; then $x^p + y^p = z^p$ has no integer solution with $p \nmid xyz$.

The proof follows Milne: $p = 3$ is Mathlib's `fermatLastTheoremThree_case_1`; for $p \ge 5$ the factorization
$\prod_i (x + \zeta^i y) = z^p$ into pairwise coprime factors (Lemma 6.9), the class number hypothesis, the unit
lemma (Proposition 6.7, `proposition_6_7`), Lemma 6.10 and Lemma 6.11 give a contradiction.
-/

open NumberField Polynomial

namespace NumberFieldKB.MilneANT

section Aux

set_option linter.unusedSectionVars false

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- The product `∏_{i<p} (x + ω^i y) = z^p` in the ring of integers. -/
lemma prod_range_eq (hodd : p ≠ 2) (hζ : IsPrimitiveRoot ζ p) {x y z : ℤ}
    (hxyz : x ^ p + y ^ p = z ^ p) :
    ∏ i ∈ Finset.range p, ((x : 𝓞 K) + hζ.toInteger ^ i * y) = (z : 𝓞 K) ^ p := by
  classical
  have hω := hζ.toInteger_isPrimitiveRoot
  have hodd' : Odd p := hp.out.odd_of_ne_two hodd
  have h1 := hω.pow_add_pow_eq_prod_add_mul (x := (x : 𝓞 K)) (y := (y : 𝓞 K)) hodd'
  have h2 : (x : 𝓞 K) ^ p + (y : 𝓞 K) ^ p = (z : 𝓞 K) ^ p := by exact_mod_cast hxyz
  have himg : (Finset.range p).image (fun i => hζ.toInteger ^ i) = Polynomial.nthRootsFinset p (1 : 𝓞 K) := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      rw [Polynomial.mem_nthRootsFinset hp.out.pos]
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    · rw [hω.card_nthRootsFinset, Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hω.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij
  rw [← h2, h1, ← himg, Finset.prod_image]
  intro i hi j hj hij
  exact hω.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij


lemma exists_unit_mul_pow (hodd : p ≠ 2) (hζ : IsPrimitiveRoot ζ p) {x y z : ℤ}
    (hxyz : x ^ p + y ^ p = z ^ p) (hxy : IsCoprime x y) (hz : ¬ (p : ℤ) ∣ z)
    (hreg : ¬ p ∣ classNumber K) :
    ∃ (α : 𝓞 K) (u : (𝓞 K)ˣ), (x : 𝓞 K) + hζ.toInteger * y = u * α ^ p := by
  classical
  have hprod := prod_range_eq hodd hζ hxyz
  have hp1 : 1 ∈ Finset.range p := Finset.mem_range.2 hp.out.one_lt
  have hcop : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range p, i ≠ j →
      IsCoprime (Ideal.span {(x : 𝓞 K) + hζ.toInteger ^ i * y})
        (Ideal.span {(x : 𝓞 K) + hζ.toInteger ^ j * y}) := by
    intro i hi j hj hij
    rw [Ideal.isCoprime_span_singleton_iff]
    exact lemma_6_9 hodd hζ hxyz hxy hz (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij
  have hprodI : ∏ i ∈ Finset.range p, Ideal.span {(x : 𝓞 K) + hζ.toInteger ^ i * y}
      = (Ideal.span {(z : 𝓞 K)}) ^ p := by
    rw [Ideal.span_singleton_pow, ← hprod, Ideal.prod_span_singleton]
  obtain ⟨I, hI⟩ := Finset.exists_eq_pow_of_mul_eq_pow_of_coprime hcop hprodI 1 hp1
  have hpc : p.Coprime (Fintype.card (ClassGroup (𝓞 K))) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).2 hreg
  have hpr : (I ^ p).IsPrincipal := by
    rw [← hI]; simp only [pow_one]; exact ⟨⟨_, rfl⟩⟩
  obtain ⟨α, hα⟩ := (Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime hpc hpr).principal
  have hα' : I = Ideal.span {α} := by rw [hα]
  simp only [pow_one] at hI
  rw [hα', Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hI
  obtain ⟨u, hu⟩ := hI
  refine ⟨α, u⁻¹, ?_⟩
  rw [← hu, mul_comm (_ + _), ← mul_assoc]
  simp


/-- A torsion unit of the cyclotomic field is `± ω^t`. -/
lemma torsion_eq_pm_pow (hodd : p ≠ 2) (hζ : IsPrimitiveRoot ζ p) {η : (𝓞 K)ˣ}
    (hη : η ∈ NumberField.Units.torsion K) :
    ∃ t : ℕ, (η : 𝓞 K) = hζ.toInteger ^ t ∨ (η : 𝓞 K) = - hζ.toInteger ^ t := by
  have hω := hζ.toInteger_isPrimitiveRoot
  have hodd' : Odd p := hp.out.odd_of_ne_two hodd
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h1 := NumberField.Units.pow_torsionOrder_eq_one K hη
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := p) (K := K), if_neg (Nat.not_even_iff_odd.2 hodd')] at h1
  have h2 : ((η : 𝓞 K) ^ 2) ^ p = 1 := by
    have := congrArg (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) h1
    simpa [← pow_mul, mul_comm] using this
  obtain ⟨s, -, hs⟩ := hω.eq_pow_of_pow_eq_one h2
  obtain ⟨m, hm⟩ := hodd'
  have hsq : (η : 𝓞 K) ^ 2 = (hζ.toInteger ^ (s * (m + 1))) ^ 2 := by
    rw [← hs, ← pow_mul]
    have : s * (m + 1) * 2 = s + p * s := by rw [hm]; ring
    rw [this, pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  refine ⟨s * (m + 1), ?_⟩
  have := sq_eq_sq_iff_eq_or_eq_neg.1 hsq
  exact this


lemma exists_conj_form [IsCMField K] (hodd : p ≠ 2) (hp5 : 2 < p) (hζ : IsPrimitiveRoot ζ p)
    {A α : 𝓞 K} {u : (𝓞 K)ˣ} (hA : A = u * α ^ p) :
    ∃ (t : ℕ) (w : 𝓞 K), A = hζ.toInteger ^ t * w * α ^ p ∧
      IsCMField.ringOfIntegersComplexConj K w = w := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨η, hη, v, hv, huv⟩ := proposition_6_7 hp.out.isPrimePow hp5 hζ u
  obtain ⟨t, ht⟩ := torsion_eq_pm_pow hodd hζ hη
  have hvfix : IsCMField.ringOfIntegersComplexConj K (v : 𝓞 K) = v := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_eq_self_iff,
      ← maximalRealSubfield_eq_adjoin hp5 hζ]
    exact hv
  have hu : (u : 𝓞 K) = η * v := by rw [huv, Units.val_mul]
  rcases ht with ht | ht
  · refine ⟨t, v, ?_, hvfix⟩
    rw [hA, hu, ht]
  · refine ⟨t, -v, ?_, by simp [hvfix]⟩
    rw [hA, hu, ht]; ring


lemma conj_zeta [IsCMField K] (hζ : IsPrimitiveRoot ζ p) :
    IsCMField.ringOfIntegersComplexConj K hζ.toInteger = hζ.toInteger ^ (p - 1) := by
  have hω := hζ.toInteger_isPrimitiveRoot
  have hunit : IsUnit hζ.toInteger := hω.isUnit hp.out.ne_zero
  have hmem : hunit.unit ∈ NumberField.Units.torsion K := by
    unfold NumberField.Units.torsion
    rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨p, hp.out.pos, ?_⟩
    ext
    simp [hω.pow_eq_one]
  have h := IsCMField.complexConj_torsion (K := K) ⟨hunit.unit, hmem⟩
  have hinv : hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.pos, hω.pow_eq_one]
  have hz : ζ ≠ 0 := hζ.ne_zero hp.out.ne_zero
  have h3 : IsCMField.ringOfIntegersComplexConj K hζ.toInteger * hζ.toInteger = 1 := by
    apply RingOfIntegers.ext
    simp only [Subgroup.coe_mk, IsUnit.unit_spec] at h
    simp [IsCMField.coe_ringOfIntegersComplexConj, h, hz]
    exact inv_mul_cancel₀ hz
  exact (mul_left_injective₀ hunit.ne_zero) (h3.trans hinv.symm)

lemma congr_rel [IsCMField K] (hζ : IsPrimitiveRoot ζ p) {x y : ℤ} {t : ℕ} {w α : 𝓞 K}
    (hA : (x : 𝓞 K) + hζ.toInteger * y = hζ.toInteger ^ t * w * α ^ p)
    (hw : IsCMField.ringOfIntegersComplexConj K w = w) :
    ∃ q : 𝓞 K, ((x : 𝓞 K) + hζ.toInteger * y) -
      hζ.toInteger ^ (2 * t) * ((x : 𝓞 K) + hζ.toInteger ^ (p - 1) * y) = p * q := by
  have hω := hζ.toInteger_isPrimitiveRoot
  obtain ⟨a, hq⟩ := lemma_6_10 hζ α
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hq
  have hα : α ^ p = a + p * c := by linear_combination -hc
  have hσA : (x : 𝓞 K) + hζ.toInteger ^ (p - 1) * y
      = hζ.toInteger ^ ((p - 1) * t) * w * (a + p * IsCMField.ringOfIntegersComplexConj K c) := by
    have := congrArg (IsCMField.ringOfIntegersComplexConj K) hA
    simpa [map_add, map_mul, map_pow, conj_zeta hζ, hw, hα, pow_mul] using this
  refine ⟨hζ.toInteger ^ t * w * (c - IsCMField.ringOfIntegersComplexConj K c), ?_⟩
  have hp1 : hζ.toInteger ^ (2 * t) * hζ.toInteger ^ ((p - 1) * t) = hζ.toInteger ^ t := by
    rw [← pow_add]
    have : 2 * t + (p - 1) * t = t + p * t := by
      obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
      rw [hk]; simp only [Nat.add_sub_cancel]; ring
    rw [this, pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  rw [hA, hσA, hα]
  linear_combination (-(w * ((a : 𝓞 K) + p * IsCMField.ringOfIntegersComplexConj K c))) * hp1


lemma sum_single (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk : k < p) (m : ℤ) :
    ∑ i : Fin p, (((if (i : ℕ) = k then m else 0 : ℤ)) : 𝓞 K) * hζ.toInteger ^ (i : ℕ)
      = m * hζ.toInteger ^ k := by
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin p)]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ k := fun h => hb (Fin.ext h)
    simp [this]
  · simp

lemma pow_eq_pow_mod (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    hζ.toInteger ^ n = hζ.toInteger ^ (n % p) := by
  have hω := hζ.toInteger_isPrimitiveRoot
  conv_lhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]

/-- Residues of `2t` and `2t - 1` modulo `p`. -/
lemma mod_facts (t : ℕ) (hp : 0 < p) :
    (2 * t) % p < p ∧ (2 * t + p - 1) % p < p ∧
    ((2 * t) % p = 0 → (2 * t + p - 1) % p = p - 1) ∧
    (0 < (2 * t) % p → (2 * t + p - 1) % p = (2 * t) % p - 1) := by
  refine ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, fun h => ?_, fun h => ?_⟩
  · have h2 := Nat.div_add_mod (2 * t) p
    have : 2 * t + p - 1 = (p - 1) + p * (2 * t / p) := by
      generalize p * (2 * t / p) = P at h2 ⊢
      generalize 2 * t % p = r at h2 h ⊢
      omega
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  · have h2 := Nat.div_add_mod (2 * t) p
    have h3 := Nat.mod_lt (2 * t) hp
    have : 2 * t + p - 1 = ((2 * t) % p - 1) + p * (2 * t / p + 1) := by
      rw [mul_add, mul_one]; generalize p * (2 * t / p) = P at h2 ⊢
      generalize 2 * t % p = r at h2 h h3 ⊢; omega
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)


lemma contra_of_rel (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p) {x y : ℤ} {t : ℕ}
    (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (hxy : ¬ (p : ℤ) ∣ x - y)
    (hdiv : (p : 𝓞 K) ∣ ((x : 𝓞 K) + hζ.toInteger * y) -
      hζ.toInteger ^ (2 * t) * ((x : 𝓞 K) + hζ.toInteger ^ (p - 1) * y)) : False := by
  have hω := hζ.toInteger_isPrimitiveRoot
  have hp0 := hp.out.pos
  obtain ⟨hc, hd, hc0, hc1⟩ := mod_facts t hp0
  generalize hcdef : (2 * t) % p = c at hc hc0 hc1
  generalize hddef : (2 * t + p - 1) % p = d at hd hc0 hc1
  let a : Fin p → ℤ := fun i => (if (i : ℕ) = 0 then x else 0) + (if (i : ℕ) = 1 then y else 0)
    - (if (i : ℕ) = c then x else 0) - (if (i : ℕ) = d then y else 0)
  have hsum : ∑ i : Fin p, (a i : 𝓞 K) * hζ.toInteger ^ (i : ℕ)
      = ((x : 𝓞 K) + hζ.toInteger * y) -
      hζ.toInteger ^ (2 * t) * ((x : 𝓞 K) + hζ.toInteger ^ (p - 1) * y) := by
    simp only [a, Int.cast_add, Int.cast_sub, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [sum_single hζ hp0 x, sum_single hζ (by omega : 1 < p) y, sum_single hζ hc x,
      sum_single hζ hd y]
    have e1 : hζ.toInteger ^ (2 * t) = hζ.toInteger ^ c := by rw [pow_eq_pow_mod hζ, hcdef]
    have e2 : hζ.toInteger ^ (2 * t) * hζ.toInteger ^ (p - 1) = hζ.toInteger ^ d := by
      have : 2 * t + (p - 1) = 2 * t + p - 1 := by omega
      rw [← pow_add, pow_eq_pow_mod hζ, this, hddef]
    linear_combination (y : 𝓞 K) * e2 + (x : 𝓞 K) * e1
  have hex : ∃ i : Fin p, a i = 0 := by
    obtain ⟨e, he, hne⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, 1, c, d} : Finset ℕ)) (t := Finset.range p)
      (lt_of_le_of_lt Finset.card_le_four (by simpa using (by omega : 4 < p)))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    refine ⟨⟨e, Finset.mem_range.1 he⟩, ?_⟩
    simp [a, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2]
  have hall := lemma_6_11 hζ a hex p (by rw [hsum, Int.cast_natCast]; exact hdiv)
  have h0 : (0 : ℕ) < p := hp0
  have h1 : (1 : ℕ) < p := by omega
  by_cases hc00 : c = 0
  · have hd' := hc0 hc00
    have := hall ⟨1, h1⟩
    simp only [a] at this
    simp [hc00, show (1:ℕ) ≠ d by omega] at this
    exact hy this
  · by_cases hc01 : c = 1
    · have hd' := hc1 (by omega)
      have := hall ⟨0, h0⟩
      simp only [a] at this
      simp [hc01, show d = 0 by omega] at this
      exact hxy this
    · have hd' := hc1 (by omega)
      have := hall ⟨0, h0⟩
      simp only [a] at this
      simp [Ne.symm hc00, show (0:ℕ) ≠ d by omega] at this
      exact hx this


lemma core (hp5 : 5 ≤ p) (hreg : ¬ p ∣ classNumber K) (hζ : IsPrimitiveRoot ζ p) {x y z : ℤ}
    (hxyz : x ^ p + y ^ p = z ^ p) (hcop : IsCoprime x y) (hx : ¬ (p : ℤ) ∣ x)
    (hy : ¬ (p : ℤ) ∣ y) (hz : ¬ (p : ℤ) ∣ z) (hxy : ¬ (p : ℤ) ∣ x - y) : False := by
  have hodd : p ≠ 2 := by omega
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {p}) ⟨p, rfl, by omega⟩
  obtain ⟨α, u, hA⟩ := exists_unit_mul_pow hodd hζ hxyz hcop hz hreg
  obtain ⟨t, w, hA', hw⟩ := exists_conj_form hodd (by omega) hζ hA
  obtain ⟨q, hq⟩ := congr_rel hζ hA' hw
  exact contra_of_rel hp5 hζ hx hy hxy ⟨q, hq⟩

lemma wlog_step (hp5 : 5 ≤ p) {x y z : ℤ} (h : x ^ p + y ^ p = z ^ p)
    (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (hz : ¬ (p : ℤ) ∣ z) :
    ∃ x' y' z' : ℤ, x' ^ p + y' ^ p = z' ^ p ∧ ¬ (p : ℤ) ∣ x' ∧ ¬ (p : ℤ) ∣ y' ∧
      ¬ (p : ℤ) ∣ z' ∧ ¬ (p : ℤ) ∣ x' - y' := by
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  by_cases h1 : (p : ℤ) ∣ x - y
  · by_cases h2 : (p : ℤ) ∣ x + z
    · exfalso
      have hc := congrArg (fun a : ℤ => (a : ZMod p)) h
      simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card] at hc
      have e1 : (x : ZMod p) = y := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h1
        push_cast at this; exact sub_eq_zero.1 this
      have e2 : (z : ZMod p) = -x := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h2
        push_cast at this; exact eq_neg_of_add_eq_zero_right this
      rw [e1, e2] at hc
      rw [← e1] at hc
      have h3 : (3 : ZMod p) * x = 0 := by linear_combination hc
      rcases mul_eq_zero.1 h3 with h3 | h3
      · have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.le_of_dvd (by norm_num) this
        omega
      · exact hx ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h3)
    · refine ⟨x, -z, -y, ?_, hx, ?_, ?_, ?_⟩
      · rw [hodd.neg_pow, hodd.neg_pow]; linear_combination h
      · simpa using hz
      · simpa using hy
      · rw [sub_neg_eq_add]; exact h2
  · exact ⟨x, y, z, h, hx, hy, hz, h1⟩

lemma gcd_step {x y z : ℤ} (h : x ^ p + y ^ p = z ^ p)
    (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (hz : ¬ (p : ℤ) ∣ z) (hxy : ¬ (p : ℤ) ∣ x - y) :
    ∃ x' y' z' : ℤ, x' ^ p + y' ^ p = z' ^ p ∧ IsCoprime x' y' ∧ ¬ (p : ℤ) ∣ x' ∧
      ¬ (p : ℤ) ∣ y' ∧ ¬ (p : ℤ) ∣ z' ∧ ¬ (p : ℤ) ∣ x' - y' := by
  have hg : 0 < Int.gcd x y := Int.gcd_pos_of_ne_zero_left _ (fun h0 => hx (h0 ▸ dvd_zero _))
  obtain ⟨g, x', y', hg0, hgcd, rfl, rfl⟩ := Int.exists_gcd_one' hg
  have hg0' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hdz : (g : ℤ) ∣ z := by
    rw [← Int.pow_dvd_pow_iff hp.out.ne_zero, ← h]
    exact ⟨x' ^ p + y' ^ p, by ring⟩
  obtain ⟨z', rfl⟩ := hdz
  have h' : x' ^ p + y' ^ p = z' ^ p := by
    have : (g : ℤ) ^ p * (x' ^ p + y' ^ p) = (g : ℤ) ^ p * z' ^ p := by linear_combination h
    exact mul_left_cancel₀ (pow_ne_zero _ hg0') this
  refine ⟨x', y', z', h', Int.isCoprime_iff_gcd_eq_one.2 hgcd, ?_, ?_, ?_, ?_⟩
  · exact fun d => hx (Dvd.dvd.mul_right d _)
  · exact fun d => hy (Dvd.dvd.mul_right d _)
  · exact fun d => hz (Dvd.dvd.mul_left d _)
  · exact fun d => hxy (by rw [← sub_mul]; exact Dvd.dvd.mul_right d _)

end Aux

/-- **Theorem 6.8** (the first case of Fermat's last theorem for regular primes, Kummer). Let $p$ be an odd prime.
If the class number of $\mathbb Q[\zeta]$ ($\zeta$ a primitive $p$th root of $1$) is not divisible by $p$, then
there is no integer solution $(x, y, z)$ of $X^p + Y^p = Z^p$ with $p$ relatively prime to $xyz$. -/
@[kb "milne2020ant" "v3.08, Theorem 6.8, p. 102"]
theorem theorem_6_8 (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (hreg : ¬ p ∣ classNumber (CyclotomicField p ℚ)) :
    ¬ ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧ ¬ (p : ℤ) ∣ x * y * z := by
  rintro ⟨x, y, z, h, hxyz⟩
  by_cases h3 : p = 3
  · subst h3
    have hx0 : x ≠ 0 := fun h0 => hxyz (by simp [h0])
    have hy0 : y ≠ 0 := fun h0 => hxyz (by simp [h0])
    have hz0 : z ≠ 0 := fun h0 => hxyz (by simp [h0])
    exact fermatLastTheoremFor_iff_int.1 fermatLastTheoremThree x y z hx0 hy0 hz0 h
  · have hp5 : 5 ≤ p := by
      have h2 := (Fact.out : p.Prime).two_le
      have h4 : p ≠ 4 := by rintro rfl; exact absurd (Fact.out : Nat.Prime 4) (by norm_num)
      omega
    have hx : ¬ (p : ℤ) ∣ x := fun d => hxyz (Dvd.dvd.mul_right (Dvd.dvd.mul_right d _) _)
    have hy : ¬ (p : ℤ) ∣ y := fun d => hxyz (Dvd.dvd.mul_right (Dvd.dvd.mul_left d _) _)
    have hz : ¬ (p : ℤ) ∣ z := fun d => hxyz (Dvd.dvd.mul_left d _)
    obtain ⟨x, y, z, h, hx, hy, hz, hxy⟩ := wlog_step hp5 h hx hy hz
    obtain ⟨x, y, z, h, hcop, hx, hy, hz, hxy⟩ := gcd_step h hx hy hz hxy
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : NeZero (p : ℚ) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
    haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
      CyclotomicField.isCyclotomicExtension p ℚ
    exact core (K := CyclotomicField p ℚ) hp5 hreg
      (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)) h hcop hx hy hz hxy

/-- Theorem 6.8 in the language of regular primes: for an odd regular prime $p$, $x^p + y^p = z^p$ has no
integer solution with $p \nmid xyz$. -/
@[kb "milne2020ant" "v3.08, Theorem 6.8, p. 102"]
theorem theorem_6_8_of_isRegularPrime (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hreg : IsRegularPrime p) :
    ¬ ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧ ¬ (p : ℤ) ∣ x * y * z :=
  theorem_6_8 p hodd hreg

end NumberFieldKB.MilneANT
