import NumberFieldKB.MilneCFT.Intro.Theorems
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat

/-!
# Introduction of Milne, *Class Field Theory*: Theorem 0.10 and Exercise 0.13

* **Theorem 0.10 (Dedekind)**: the factorization part is Mathlib's Kummer–Dedekind theorem
  (`KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map`), restated here as
  `dedekind_factorization`; the link with the discriminant over $\mathbb Z$ is Mathlib's
  `NumberField.not_dvd_discr_iff_isUnramifiedIn`.
* **Exercise 0.13** (`rayClassGroup_rat`): the ray class group of $\mathbb Q$ for the modulus $m\infty$ is
  $(\mathbb Z/m\mathbb Z)^\times$.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

attribute [local instance] Ideal.Quotient.field

open Ideal Polynomial UniqueFactorizationMonoid in
open scoped Classical in
/-- **Theorem 0.10 (Dedekind), the factorization** (Milne, *CFT*, Introduction, Theorem 0.10 (c) ⇒ factorization):
let $A$ be an integrally closed domain, $B$ a Dedekind domain containing $A$, $\beta \in B$ integral over $A$ with
the conductor of $A[\beta]$ prime to $\mathfrak p$ (Milne: $\mathcal O_L = A[\beta]$ locally at $\mathfrak p$, e.g.
$\mathfrak p \nmid \mathrm{disc}(f)$), and $f$ the minimal polynomial of $\beta$. If
$\bar f = \prod \bar f_i^{e_i}$ in $(A/\mathfrak p)[X]$, then $\mathfrak p B = \prod \mathfrak P_i^{e_i}$ with
$\mathfrak P_i = (\mathfrak p, f_i(\beta))$. This is Mathlib's Kummer–Dedekind theorem. -/
@[kb "milne2020cft" "Introduction, Theorem 0.10 (factorization; Mathlib)"]
theorem dedekind_factorization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
    [IsIntegrallyClosed R] [IsDedekindDomain S] [Module.IsTorsionFree R S] {x : S} {I : Ideal R}
    (hI : IsMaximal I) (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f => ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f :
          Ideal S))
        (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach :=
  KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx'

/-- The modulus $m\infty$ of $\mathbb Q$ ($m \ge 1$): finite part $(m)$, infinite part the real place. -/
def ratModulus (m : ℕ) (hm : m ≠ 0) : Modulus ℚ where
  finite := Ideal.span {(m : 𝓞 ℚ)}
  finite_ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  infinite := {v | v.IsReal}
  isReal_of_mem := fun _ h => h

section RatHelpers

open HeightOneSpectrum WithZero

theorem dvd_of_intValuation_le {R : Type*} [CommRing R] [IsDedekindDomain R] {x m : R}
    (hm : m ≠ 0) (h : ∀ v : HeightOneSpectrum R, v.intValuation x ≤ v.intValuation m) : m ∣ x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · exact dvd_zero _
  have hm' : (Ideal.span {m} : Ideal R) ≠ 0 := by simpa using hm
  have hx' : (Ideal.span {x} : Ideal R) ≠ 0 := by simpa using hx
  rw [← Ideal.span_singleton_le_span_singleton, ← Ideal.dvd_iff_le,
    UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hm' hx',
    Multiset.le_iff_count]
  intro p
  by_cases hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {m})
  · have hpp : Prime p := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
    have hpr : p.IsPrime := Ideal.isPrime_of_prime hpp
    let v : HeightOneSpectrum R := ⟨p, hpr, hpp.ne_zero⟩
    have h1 := h v
    rw [v.intValuation_if_neg hx, v.intValuation_if_neg hm, exp_le_exp, neg_le_neg_iff,
      Int.ofNat_le, Ideal.count_associates_factors_eq hx' hpr hpp.ne_zero,
      Ideal.count_associates_factors_eq hm' hpr hpp.ne_zero] at h1
    exact h1
  · rw [Multiset.count_eq_zero_of_notMem hp]; exact Nat.zero_le _


theorem intCast_dvd_iff_ratInt (a b : ℤ) : ((a : 𝓞 ℚ) ∣ (b : 𝓞 ℚ)) ↔ a ∣ b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Rat.ringOfIntegersEquiv c, ?_⟩
    have := congrArg Rat.ringOfIntegersEquiv hc
    simpa using this
  · rintro ⟨c, rfl⟩
    exact ⟨(c : 𝓞 ℚ), by push_cast; rfl⟩

theorem exists_heightOne_of_prime (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ∀ k : ℤ, ((k : 𝓞 ℚ) ∈ v.asIdeal ↔ (ℓ : ℤ) ∣ k) := by
  have hp : Prime ((ℓ : ℤ) : 𝓞 ℚ) := by
    have := (Nat.prime_iff_prime_int.mp hℓ)
    have h2 : Prime (Rat.ringOfIntegersEquiv (((ℓ : ℤ) : 𝓞 ℚ))) := by simpa using this
    exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃* ℤ)).1 h2
  refine ⟨⟨Ideal.span {((ℓ : ℤ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime hp.ne_zero).2 hp,
    by simpa using hp.ne_zero⟩, fun k => ?_⟩
  simp only [Ideal.mem_span_singleton]
  exact intCast_dvd_iff_ratInt _ _


theorem val_rat (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) :
    v.valuation ℚ q = v.intValuation ((q.num : ℤ) : 𝓞 ℚ) / v.intValuation ((q.den : ℤ) : 𝓞 ℚ) := by
  have hd : (((q.den : ℤ) : 𝓞 ℚ)) ∈ (𝓞 ℚ)⁰ := mem_nonZeroDivisors_of_ne_zero (by simp)
  have h := HeightOneSpectrum.valuation_of_mk' (K := ℚ) (v := v) (r := ((q.num : ℤ) : 𝓞 ℚ))
    (s := ⟨((q.den : ℤ) : 𝓞 ℚ), hd⟩)
  have e : IsLocalization.mk' ℚ (((q.num : ℤ) : 𝓞 ℚ)) (⟨((q.den : ℤ) : 𝓞 ℚ), hd⟩ : (𝓞 ℚ)⁰) = q := by
    rw [IsFractionRing.mk'_eq_div]
    simp [Rat.num_div_den]
  rw [e] at h
  exact h

theorem not_mem_of_coprime (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) (m : ℕ)
    (h : Nat.Coprime k.natAbs m) (hv : (m : 𝓞 ℚ) ∈ v.asIdeal) : ((k : ℤ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hk
  have hc : IsCoprime k (m : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using h
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (1 : 𝓞 ℚ) = (a : 𝓞 ℚ) * k + (b : 𝓞 ℚ) * m := by exact_mod_cast hab.symm
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, h1]
  exact add_mem (Ideal.mul_mem_left _ _ hk) (Ideal.mul_mem_left _ _ hv)

theorem cop_iff (m : ℕ) (q : ℚ) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), (m : 𝓞 ℚ) ∈ v.asIdeal → v.valuation ℚ q = 1) ↔
      Nat.Coprime q.num.natAbs m ∧ Nat.Coprime q.den m := by
  constructor
  · intro H
    have hred := q.reduced
    constructor
    · by_contra hn
      obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hn
      obtain ⟨v, hv⟩ := exists_heightOne_of_prime ℓ hℓ
      have hℓm : ℓ ∣ m := hℓd.trans (Nat.gcd_dvd_right _ _)
      have hℓn : ℓ ∣ q.num.natAbs := hℓd.trans (Nat.gcd_dvd_left _ _)
      have hmv : (m : 𝓞 ℚ) ∈ v.asIdeal := by
        have := (hv (m : ℤ)).2 (by exact_mod_cast hℓm)
        simpa using this
      have h1 := H v hmv
      rw [val_rat] at h1
      have hnum : ((q.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := (hv _).2 (Int.natCast_dvd.2 hℓn)
      have hden : ((q.den : ℤ) : 𝓞 ℚ) ∉ v.asIdeal := by
        intro hd
        have := (hv _).1 hd
        have h2 : ℓ ∣ q.den := by exact_mod_cast this
        exact hℓ.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hred hℓn h2)
      have h3 : v.intValuation ((q.den : ℤ) : 𝓞 ℚ) = 1 := intValuation_eq_one_iff.2 hden
      rw [h3, div_one] at h1
      exact absurd h1 (ne_of_lt ((intValuation_lt_one_iff_mem _ _).2 hnum))
    · by_contra hn
      obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hn
      obtain ⟨v, hv⟩ := exists_heightOne_of_prime ℓ hℓ
      have hℓm : ℓ ∣ m := hℓd.trans (Nat.gcd_dvd_right _ _)
      have hℓn : ℓ ∣ q.den := hℓd.trans (Nat.gcd_dvd_left _ _)
      have hmv : (m : 𝓞 ℚ) ∈ v.asIdeal := by
        have := (hv (m : ℤ)).2 (by exact_mod_cast hℓm)
        simpa using this
      have h1 := H v hmv
      rw [val_rat] at h1
      have hden : ((q.den : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := (hv _).2 (by exact_mod_cast hℓn)
      have hnum : ((q.num : ℤ) : 𝓞 ℚ) ∉ v.asIdeal := by
        intro hd
        have := (hv _).1 hd
        have h2 : ℓ ∣ q.num.natAbs := Int.natCast_dvd.1 this
        exact hℓ.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hred h2 hℓn)
      have h3 : v.intValuation ((q.num : ℤ) : 𝓞 ℚ) = 1 := intValuation_eq_one_iff.2 hnum
      have h4 : v.intValuation ((q.den : ℤ) : 𝓞 ℚ) ≠ 0 :=
        v.intValuation_ne_zero _ (by simp)
      rw [h3, div_eq_one_iff_eq h4] at h1
      exact absurd h1.symm (ne_of_lt ((intValuation_lt_one_iff_mem _ _).2 hden))
  · rintro ⟨h1, h2⟩ v hv
    rw [val_rat]
    have a1 := not_mem_of_coprime v q.num m h1 hv
    have a2 := not_mem_of_coprime v (q.den : ℤ) m (by simpa using h2) hv
    rw [intValuation_eq_one_iff.2 a1, intValuation_eq_one_iff.2 a2]
    simp


theorem pos_iff (m : ℕ) (hm : m ≠ 0) (q : ℚ) :
    (∀ v (hv : v ∈ (ratModulus m hm).infinite), IsPositiveAt ℚ v ((ratModulus m hm).isReal_of_mem v hv) q) ↔
      0 < q := by
  have key : ∀ (v : InfinitePlace ℚ) (hv : v.IsReal), IsPositiveAt ℚ v hv q ↔ 0 < q := by
    intro v hv
    unfold IsPositiveAt
    rw [Subsingleton.elim (InfinitePlace.embedding_of_isReal hv) (Rat.castHom ℝ)]
    simp
  constructor
  · intro H
    exact (key _ Rat.isReal_infinitePlace).1 (H Rat.infinitePlace Rat.isReal_infinitePlace)
  · intro H v hv
    exact (key _ _).2 H

theorem exp_neg_ord (m : ℕ) (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    WithZero.exp (-((ratModulus m hm).ord v : ℤ)) = v.intValuation (m : 𝓞 ℚ) := by
  have hmR : (m : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hm
  rw [v.intValuation_if_neg hmR]
  rfl


theorem val_sub_one (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) (hden : ((q.den : ℤ) : 𝓞 ℚ) ∉ v.asIdeal) :
    v.valuation ℚ (q - 1) = v.intValuation (((q.num - q.den : ℤ)) : 𝓞 ℚ) := by
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have hq1 : q - 1 = algebraMap (𝓞 ℚ) ℚ (((q.num - q.den : ℤ)) : 𝓞 ℚ) /
      algebraMap (𝓞 ℚ) ℚ (((q.den : ℤ)) : 𝓞 ℚ) := by
    simp only [map_intCast]
    rw [eq_div_iff (by exact_mod_cast hd)]
    push_cast
    rw [sub_mul, one_mul, Rat.mul_den_eq_num]
  rw [hq1, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) v).2 hden, div_one]

theorem fin_iff (m : ℕ) (hm : m ≠ 0) (q : ℚ) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ∣ (ratModulus m hm).finite →
        v.valuation ℚ (q - 1) ≤ WithZero.exp (-((ratModulus m hm).ord v : ℤ))) ↔
      (Nat.Coprime q.num.natAbs m ∧ Nat.Coprime q.den m ∧ (m : ℤ) ∣ q.num - q.den) := by
  have hmR : (m : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hm
  have hfin : (ratModulus m hm).finite = Ideal.span {(m : 𝓞 ℚ)} := rfl
  constructor
  · intro H
    have hcop : ∀ v : HeightOneSpectrum (𝓞 ℚ), (m : 𝓞 ℚ) ∈ v.asIdeal → v.valuation ℚ q = 1 := by
      intro v hv
      have hv' : v.asIdeal ∣ (ratModulus m hm).finite := by
        rw [hfin]; exact Ideal.dvd_span_singleton.2 hv
      exact valuation_eq_one_of_sub_lt v (valuation_sub_one_lt _ v hv' (H v hv'))
    obtain ⟨h1, h2⟩ := (cop_iff m q).1 hcop
    refine ⟨h1, h2, ?_⟩
    rw [← intCast_dvd_iff_ratInt]
    have : ((m : ℤ) : 𝓞 ℚ) = (m : 𝓞 ℚ) := by simp
    rw [this]
    refine dvd_of_intValuation_le hmR fun v => ?_
    by_cases hv : (m : 𝓞 ℚ) ∈ v.asIdeal
    · have hv' : v.asIdeal ∣ (ratModulus m hm).finite := by
        rw [hfin]; exact Ideal.dvd_span_singleton.2 hv
      have a2 := not_mem_of_coprime v (q.den : ℤ) m (by simpa using h2) hv
      have := H v hv'
      rwa [val_sub_one v q a2, exp_neg_ord] at this
    · rw [intValuation_eq_one_iff.2 hv]
      exact v.intValuation_le_one _
  · rintro ⟨h1, h2, h3⟩ v hv
    have hv' : (m : 𝓞 ℚ) ∈ v.asIdeal := by
      rw [hfin] at hv; exact Ideal.dvd_span_singleton.1 hv
    have a2 := not_mem_of_coprime v (q.den : ℤ) m (by simpa using h2) hv'
    rw [val_sub_one v q a2, exp_neg_ord]
    have h4 : ((m : ℤ) : 𝓞 ℚ) ∣ (((q.num - q.den : ℤ)) : 𝓞 ℚ) := (intCast_dvd_iff_ratInt _ _).2 h3
    have : ((m : ℤ) : 𝓞 ℚ) = (m : 𝓞 ℚ) := by simp
    rw [this] at h4
    obtain ⟨c, hc⟩ := h4
    calc v.intValuation (((q.num - q.den : ℤ)) : 𝓞 ℚ) = v.intValuation (m : 𝓞 ℚ) * v.intValuation c := by
          rw [hc, map_mul]
      _ ≤ v.intValuation (m : 𝓞 ℚ) * 1 := mul_le_mul' (le_refl _) (v.intValuation_le_one _)
      _ = _ := mul_one _


theorem T_surj : Function.Surjective (toPrincipalIdeal (𝓞 ℚ) ℚ) := by
  intro I
  have hc : NumberField.classNumber ℚ = 1 := Rat.classNumber_eq
  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) := Fintype.card_le_one_iff_subsingleton.mp hc.le
  haveI : Subsingleton ((FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ ⧸ (toPrincipalIdeal (𝓞 ℚ) ℚ).range) :=
    (ClassGroup.equiv (R := 𝓞 ℚ) ℚ).toEquiv.symm.subsingleton
  have := (QuotientGroup.eq_one_iff (N := (toPrincipalIdeal (𝓞 ℚ) ℚ).range) I).1
    (Subsingleton.elim _ _)
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

theorem T_eq_iff (a b : ℚˣ) :
    toPrincipalIdeal (𝓞 ℚ) ℚ a = toPrincipalIdeal (𝓞 ℚ) ℚ b ↔ (a : ℚ) = b ∨ (a : ℚ) = -b := by
  rw [Units.ext_iff, coe_toPrincipalIdeal, coe_toPrincipalIdeal,
    FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    have hu : IsUnit (Rat.ringOfIntegersEquiv (z : 𝓞 ℚ)) := z.isUnit.map _
    have hz' : (algebraMap (𝓞 ℚ) ℚ (z : 𝓞 ℚ)) • (a : ℚ) = b := by
      rw [← hz]; rfl
    rcases Int.isUnit_iff.1 hu with h | h
    · left
      have : algebraMap (𝓞 ℚ) ℚ (z : 𝓞 ℚ) = 1 := by
        rw [← Rat.ringOfIntegersEquiv_apply_coe, h]; simp
      rw [this] at hz'
      simpa using hz'
    · right
      have : algebraMap (𝓞 ℚ) ℚ (z : 𝓞 ℚ) = -1 := by
        rw [← Rat.ringOfIntegersEquiv_apply_coe, h]; simp
      rw [this] at hz'
      have : -(a : ℚ) = b := by simpa using hz'
      linarith
  · rintro (h | h)
    · exact ⟨1, by simp [h]⟩
    · refine ⟨-1, ?_⟩
      have : ((-1 : (𝓞 ℚ)ˣ) • (a : ℚ)) = -(a : ℚ) := by
        rw [Units.smul_def]; simp
      rw [this]; linarith

variable (m : ℕ) (hm : m ≠ 0)

/-- The subgroup of `ℚˣ` of elements prime to `m`. -/
def Gm : Subgroup ℚˣ := (coprimeIdeals (ratModulus m hm)).comap (toPrincipalIdeal (𝓞 ℚ) ℚ)

theorem mem_Gm (a : ℚˣ) :
    a ∈ Gm m hm ↔ Nat.Coprime (a : ℚ).num.natAbs m ∧ Nat.Coprime (a : ℚ).den m := by
  rw [← cop_iff m, Gm, Subgroup.mem_comap]
  show (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ∣ (ratModulus m hm).finite →
      FractionalIdeal.count ℚ v ((toPrincipalIdeal (𝓞 ℚ) ℚ a : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) = 0) ↔ _
  refine forall_congr' fun v => ?_
  have h1 : v.asIdeal ∣ (ratModulus m hm).finite ↔ (m : 𝓞 ℚ) ∈ v.asIdeal :=
    Ideal.dvd_span_singleton
  rw [h1, valuation_eq_exp_neg_count v a, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero]


/-- `num / den` reduced modulo `m` (meaningful when `den` is prime to `m`). -/
def ratMod (q : ℚ) : ZMod m := (q.num : ZMod m) * ((q.den : ZMod m))⁻¹

theorem ratMod_one : ratMod m 1 = 1 := by simp [ratMod]

theorem ratMod_mul (q1 q2 : ℚ) (c1 : Nat.Coprime q1.den m) (c2 : Nat.Coprime q2.den m)
    (c3 : Nat.Coprime (q1 * q2).den m) : ratMod m (q1 * q2) = ratMod m q1 * ratMod m q2 := by
  have h : (q1 * q2).num * (q1.den : ℤ) * q2.den = q1.num * q2.num * (q1 * q2).den := by
    have : (((q1 * q2).num : ℤ) : ℚ) * q1.den * q2.den = (q1.num : ℚ) * q2.num * (q1 * q2).den := by
      rw [← Rat.mul_den_eq_num (q1 * q2), ← Rat.mul_den_eq_num q1, ← Rat.mul_den_eq_num q2]; ring
    exact_mod_cast this
  have hz := congrArg (Int.cast : ℤ → ZMod m) h
  push_cast at hz
  have e1 := ZMod.coe_mul_inv_eq_one _ c1
  have e2 := ZMod.coe_mul_inv_eq_one _ c2
  have e3 := ZMod.coe_mul_inv_eq_one _ c3
  unfold ratMod
  generalize ((q1 * q2).num : ZMod m) = n3 at *
  generalize (q1.num : ZMod m) = n1 at *
  generalize (q2.num : ZMod m) = n2 at *
  generalize ((q1 * q2).den : ZMod m) = d3 at *
  generalize (q1.den : ZMod m) = d1 at *
  generalize (q2.den : ZMod m) = d2 at *
  generalize d1⁻¹ = a1 at *
  generalize d2⁻¹ = a2 at *
  generalize d3⁻¹ = c at *
  linear_combination (-n3 * c * d2 * a2) * e1 + (-n3 * c) * e2 + (c * a1 * a2) * hz + (n1 * n2 * a1 * a2) * e3

theorem ratMod_eq_one_iff (q : ℚ) (c : Nat.Coprime q.den m) : ratMod m q = 1 ↔ (m : ℤ) ∣ q.num - q.den := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have e := ZMod.coe_mul_inv_eq_one _ c
  unfold ratMod
  push_cast
  generalize (q.num : ZMod m) = n at *
  generalize (q.den : ZMod m) = d at *
  generalize d⁻¹ = a at *
  rw [sub_eq_zero]
  constructor
  · intro h
    calc n = n * (d * a) := by rw [e, mul_one]
      _ = (n * a) * d := by ring
      _ = d := by rw [h, one_mul]
  · intro h
    rw [h]; exact e

/-- `|·| : ℚˣ →* ℚˣ`. -/
def absU : ℚˣ →* ℚˣ := Units.map (absHom : ℚ →*₀ ℚ).toMonoidHom

theorem absU_coe (a : ℚˣ) : (absU a : ℚ) = |(a : ℚ)| := rfl

theorem T_absU (a : ℚˣ) : toPrincipalIdeal (𝓞 ℚ) ℚ (absU a) = toPrincipalIdeal (𝓞 ℚ) ℚ a := by
  rw [T_eq_iff, absU_coe]
  rcases abs_choice (a : ℚ) with h | h
  · left; exact h
  · right; exact h

theorem absU_mem (a : ℚˣ) : absU a ∈ Gm m hm ↔ a ∈ Gm m hm := by
  simp only [Gm, Subgroup.mem_comap, T_absU]

theorem absU_pos (a : ℚˣ) : 0 < (absU a : ℚ) := by
  rw [absU_coe]; exact abs_pos.2 a.ne_zero

/-- The homomorphism `Gm → ZMod m`, `a ↦ |a| mod m`. -/
def phi : Gm m hm →* ZMod m where
  toFun a := ratMod m (absU (a : ℚˣ) : ℚ)
  map_one' := by simp [ratMod_one]
  map_mul' a b := by
    have ha := (mem_Gm m hm _).1 ((absU_mem m hm _).2 a.2)
    have hb := (mem_Gm m hm _).1 ((absU_mem m hm _).2 b.2)
    have hab := (mem_Gm m hm _).1 ((absU_mem m hm _).2 (a * b).2)
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at hab ⊢
    exact ratMod_mul m _ _ ha.2 hb.2 hab.2

/-- The homomorphism `Gm → (ZMod m)ˣ`. -/
def Psi : Gm m hm →* (ZMod m)ˣ := (phi m hm).toHomUnits

theorem Psi_eq_one_iff (a : Gm m hm) :
    Psi m hm a = 1 ↔ (m : ℤ) ∣ (absU (a : ℚˣ) : ℚ).num - (absU (a : ℚˣ) : ℚ).den := by
  have ha := (mem_Gm m hm _).1 ((absU_mem m hm _).2 a.2)
  rw [← ratMod_eq_one_iff m _ ha.2, Units.ext_iff]
  rfl


theorem Psi_surj : Function.Surjective (Psi m hm) := by
  haveI : NeZero m := ⟨hm⟩
  intro u
  set r : ℕ := (u : ZMod m).val + m with hr
  have hcop : Nat.Coprime r m := by
    rw [hr]; exact (Nat.coprime_add_self_left).2 (ZMod.val_coe_unit_coprime u)
  have hrpos : 0 < r := by have := Nat.pos_of_ne_zero hm; omega
  have hrz : (r : ZMod m) = u := by
    rw [hr]; push_cast; simp
  let a : ℚˣ := Units.mk0 (r : ℚ) (by exact_mod_cast hrpos.ne')
  have ha : a ∈ Gm m hm := (mem_Gm m hm a).2 ⟨by simpa [a] using hcop, by simp [a]⟩
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Units.ext
  show phi m hm ⟨a, ha⟩ = u
  simp [phi, absU_coe, ratMod, a, hrz]

/-- The homomorphism `Gm → C_m`. -/
def Theta : Gm m hm →* RayClassGroup (ratModulus m hm) :=
  (QuotientGroup.mk' ((rayPrincipal (ratModulus m hm)).subgroupOf (coprimeIdeals (ratModulus m hm)))).comp
    (((toPrincipalIdeal (𝓞 ℚ) ℚ).comp (Gm m hm).subtype).codRestrict
      (coprimeIdeals (ratModulus m hm)) (fun a => a.2))

theorem Theta_surj : Function.Surjective (Theta m hm) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H I =>
    obtain ⟨a, ha⟩ := T_surj (I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ)
    have hmem : a ∈ Gm m hm := by
      show toPrincipalIdeal (𝓞 ℚ) ℚ a ∈ coprimeIdeals (ratModulus m hm)
      rw [ha]; exact I.2
    refine ⟨⟨a, hmem⟩, ?_⟩
    show QuotientGroup.mk (⟨toPrincipalIdeal (𝓞 ℚ) ℚ a, _⟩ : coprimeIdeals (ratModulus m hm)) = _
    congr 1
    exact Subtype.ext ha

theorem Theta_eq_one_iff (a : Gm m hm) :
    Theta m hm a = 1 ↔ ∃ c ∈ congruenceSubgroup (ratModulus m hm),
      toPrincipalIdeal (𝓞 ℚ) ℚ c = toPrincipalIdeal (𝓞 ℚ) ℚ (a : ℚˣ) := by
  unfold Theta
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  show toPrincipalIdeal (𝓞 ℚ) ℚ (a : ℚˣ) ∈ (congruenceSubgroup (ratModulus m hm)).map _ ↔ _
  rw [Subgroup.mem_map]

theorem Theta_iff_Psi (a : Gm m hm) : Theta m hm a = 1 ↔ Psi m hm a = 1 := by
  rw [Theta_eq_one_iff, Psi_eq_one_iff]
  have ha := (mem_Gm m hm _).1 ((absU_mem m hm _).2 a.2)
  constructor
  · rintro ⟨c, hc, hca⟩
    obtain ⟨hpos, hfin⟩ := hc
    have h0 : 0 < (c : ℚ) := (pos_iff m hm _).1 hpos
    obtain ⟨-, -, hd⟩ := (fin_iff m hm _).1 hfin
    have habs : (absU (a : ℚˣ) : ℚ) = c := by
      rw [absU_coe]
      rcases (T_eq_iff _ _).1 hca with h | h
      · rw [← h, abs_of_pos h0]
      · rw [show (a : ℚˣ).val = -(c : ℚ) by rw [h]; ring, abs_neg, abs_of_pos h0]
    rw [habs]; exact hd
  · intro hd
    refine ⟨absU (a : ℚˣ), ⟨(pos_iff m hm _).2 (absU_pos _), (fin_iff m hm _).2 ⟨ha.1, ha.2, hd⟩⟩,
      T_absU _⟩


end RatHelpers

/-- **Exercise 0.13** (Milne, *CFT*, Introduction): for $m \ge 1$, the map $I^{S(m)} \to (\mathbb Z/m\mathbb Z)^\times$
sending the ideal $(r)$, $r > 0$ a rational number prime to $m$, to $r \bmod m$ has kernel $P_{m\infty}$, so it induces
an isomorphism $C_{m\infty} \cong (\mathbb Z/m\mathbb Z)^\times$. -/
@[kb "milne2020cft" "Introduction, Exercise 0.13"]
theorem rayClassGroup_rat (m : ℕ) (hm : m ≠ 0) :
    Nonempty (RayClassGroup (ratModulus m hm) ≃* (ZMod m)ˣ) := by
  have hker : (Theta m hm).ker = (Psi m hm).ker := by
    ext a
    simp only [MonoidHom.mem_ker]
    exact Theta_iff_Psi m hm a
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective _ (Theta_surj m hm)).symm).trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (Psi_surj m hm)))⟩

end NumberFieldKB.MilneCFT
