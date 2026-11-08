import NumberFieldKB.MilneCFT.LubinTate.FormalGroup
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.MahlerBasis

/-!
# Lubin–Tate theory over local fields and over $\mathbb Z_p$ (Milne, *Class Field Theory*, Chapter I, §2)

The book's setting satisfies the hypotheses `LubinTateHyp` (`lubinTateHyp_of_isNonarchimedeanLocalField`), and the
$p$-adic examples: $(1+X)^p - 1 \in \mathcal F_p$ (Example 2.10 (b)), its Lubin–Tate formal group law is the
multiplicative one (Example 2.13), and $[a]_f = (1+T)^a - 1$ for $a \in \mathbb Z_p$ (Example 2.18).
-/

open MvPowerSeries

noncomputable section

namespace NumberFieldKB.MilneCFT

open IsLocalRing in
/-- Helper: `LubinTateHyp` for a local domain with finite residue field of cardinality `q`. -/
theorem lubinTateHyp_of_local (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [Finite (ResidueField A)] {π : A} (hπ0 : π ≠ 0) (hπ : maximalIdeal A = Ideal.span {π})
    {q : ℕ} (hq : Nat.card (ResidueField A) = q) : LubinTateHyp A π q := by
  have hmem : ∀ x : A, x ∈ Ideal.span {π} ↔ residue A x = 0 := fun x => by
    rw [← hπ, residue_eq_zero_iff]
  have hπm : π ∈ maximalIdeal A := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  have : Fintype (ResidueField A) := Fintype.ofFinite _
  have hcard : Fintype.card (ResidueField A) = q := by rw [← hq, Nat.card_eq_fintype_card]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hq]; exact Finite.one_lt_card
  · exact fun x y h => mul_left_cancel₀ hπ0 h
  · intro r hr
    have : π ^ r ∈ maximalIdeal A := Ideal.pow_mem_of_mem _ hπm r (by omega)
    have h := isUnit_one_sub_self_of_mem_nonunits (π ^ r) this
    simpa using h.neg
  · intro a
    rw [hmem, map_sub, map_pow, ← hcard, FiniteField.pow_card, sub_self]
  · intro k hk0 hkq
    rw [hmem]
    obtain ⟨p, hpc⟩ : ∃ p, CharP (ResidueField A) p := ⟨_, ringChar.charP _⟩
    obtain ⟨n, hp, hn⟩ := FiniteField.card (ResidueField A) p
    have hpp : p.Prime := hp
    rw [hcard] at hn
    subst hn
    have hd : p ∣ (p ^ (n : ℕ)).choose k :=
      hpp.dvd_choose_pow (by omega) (by omega)
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    push_cast
    have : ((p : ℕ) : ResidueField A) = 0 := CharP.cast_eq_zero _ p
    have h2 : residue A (p : A) = 0 := by rw [map_natCast]; exact this
    rw [map_mul, h2, zero_mul]

open scoped ValuativeRel in
/-- **The book's setting** (Milne, *CFT*, I, §2): for a nonarchimedean local field $K$ with ring of integers $A$, a
prime element $\pi$ and $q = |A/\mathfrak m|$, the hypotheses `LubinTateHyp A π q` hold. -/
@[kb "milne2020cft" "Ch. I, §2 (A = O_K, π a prime element, q = |k|)"]
theorem lubinTateHyp_of_isNonarchimedeanLocalField (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {π : 𝒪[K]} (hπ : Irreducible π) :
    LubinTateHyp 𝒪[K] π (Nat.card 𝓀[K]) := by
  refine lubinTateHyp_of_local 𝒪[K] hπ.ne_zero ?_ rfl
  exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ)

/-- The hypotheses `LubinTateHyp ℤ_[p] p p` ($K = \mathbb Q_p$, $\pi = p$, $q = p$). -/
theorem lubinTateHyp_padicInt (p : ℕ) [Fact p.Prime] : LubinTateHyp ℤ_[p] (p : ℤ_[p]) p := by
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) := Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  refine lubinTateHyp_of_local ℤ_[p] (NeZero.ne _) PadicInt.maximalIdeal_eq_span_p ?_
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_zmod]

/-- Helper: the coefficients of $(1+X)^m$ are binomial coefficients. -/
theorem coeff_one_add_X_pow' {R : Type*} [CommRing R] (m n : ℕ) :
    PowerSeries.coeff n ((1 + PowerSeries.X : PowerSeries R) ^ m) = (m.choose n : R) := by
  have h : ((1 + PowerSeries.X : PowerSeries R) ^ m) =
      (((1 + Polynomial.X) ^ m : Polynomial R) : PowerSeries R) := by
    simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- **Example 2.10 (b)** (Milne, *CFT*, I): for $K = \mathbb Q_p$ and $\pi = p$ (so $q = p$),
$(1+X)^p - 1 \in \mathcal F_p$. -/
@[kb "milne2020cft" "Ch. I, Example 2.10 (b)"]
theorem one_add_X_pow_sub_one_mem (p : ℕ) [Fact p.Prime] :
    (1 + PowerSeries.X) ^ p - 1 ∈ lubinTateSeries (p : ℤ_[p]) p := by
  have hp := (Fact.out : p.Prime)
  refine ⟨by simp, ?_, ?_⟩
  · simp [coeff_one_add_X_pow', PowerSeries.coeff_one]
  · intro n
    rw [map_sub, coeff_one_add_X_pow', PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : (0 : ℕ) ≠ p := hp.ne_zero.symm
      simp [this]
    rcases lt_trichotomy n p with h | rfl | h
    · have h1 : n ≠ 0 := by omega
      have h2 : n ≠ p := by omega
      simp only [h1, h2, ite_false, sub_zero]
      exact (lubinTateHyp_padicInt p).choose_mem n hn h
    · have h1 : n ≠ 0 := by omega
      simp [h1]
    · have h1 : n ≠ 0 := by omega
      have h2 : n ≠ p := by omega
      simp [Nat.choose_eq_zero_of_lt h, h1, h2]

/-- **Example 2.13** (Milne, *CFT*, I): for $K = \mathbb Q_p$, $\pi = p$ and $f = (1+T)^p - 1$, the Lubin–Tate
formal group law $F_f$ is the multiplicative formal group law $X + Y + XY$. -/
@[kb "milne2020cft" "Ch. I, Example 2.13"]
theorem lubinTateFormalGroup_padicInt (p : ℕ) [Fact p.Prime] :
    lubinTateFormalGroup (lubinTateHyp_padicInt p) (one_add_X_pow_sub_one_mem p) = FormalGroup.𝔾ₘ :=
  (eq_lubinTateFormalGroup (lubinTateHyp_padicInt p) (one_add_X_pow_sub_one_mem p) FormalGroup.𝔾ₘ
    (gmPow (A := ℤ_[p]) p).map_add).symm

section Binomial

variable (p : ℕ) [Fact p.Prime]

/-- Helper: substitution of `g` (with `g(0) = 0`) in `(1+X)^m` gives `(1+g)^m`. -/
theorem subst_one_add_X_pow {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg : PowerSeries.HasSubst g) (m : ℕ) :
    ((1 + PowerSeries.X : PowerSeries R) ^ m).subst g = (1 + g) ^ m := by
  rw [PowerSeries.subst_pow hg, PowerSeries.subst_add hg, PowerSeries.subst_X hg]
  congr 2
  rw [← PowerSeries.coe_substAlgHom hg, map_one]

/-- Helper: `(B_a)^n = B_{n a}` for the binomial series. -/
theorem binomialSeries_pow_nat (a : ℤ_[p]) (n : ℕ) :
    PowerSeries.binomialSeries ℤ_[p] a ^ n = PowerSeries.binomialSeries ℤ_[p] ((n : ℤ_[p]) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← PowerSeries.binomialSeries_add]
    congr 1
    push_cast
    ring

/-- Helper: coefficient of $B_a \circ f$ as a finite sum, for `f(0) = 0`. -/
theorem coeff_subst_binomialSeries {f : PowerSeries ℤ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    (n : ℕ) (a : ℤ_[p]) :
    PowerSeries.coeff n ((PowerSeries.binomialSeries ℤ_[p] a).subst f) =
      ∑ d ∈ Finset.range (n + 1), Ring.choose a d * PowerSeries.coeff n (f ^ d) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hf),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    have : PowerSeries.coeff n (f ^ d) = 0 := by
      apply PowerSeries.coeff_of_lt_order
      have := PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hf
      have h2 : ((n : ℕ) : ℕ∞) < d := by exact_mod_cast (by omega : n < d)
      exact lt_of_lt_of_le h2 this
    simp [this]

/-- Helper: $B_a \circ ((1+X)^p - 1) = B_{pa}$, i.e. $((1+T)^p)^a = (1+T)^{pa}$, by density of $\mathbb N$
in $\mathbb Z_p$ and continuity of the coefficients in `a`. -/
theorem binomialSeries_subst (a : ℤ_[p]) :
    (PowerSeries.binomialSeries ℤ_[p] a).subst ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p - 1) =
      PowerSeries.binomialSeries ℤ_[p] ((p : ℤ_[p]) * a) := by
  have hf0 : PowerSeries.constantCoeff ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p - 1) = 0 := by
    simp
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  refine PowerSeries.ext fun n => ?_
  have key : (fun a : ℤ_[p] => PowerSeries.coeff n
      ((PowerSeries.binomialSeries ℤ_[p] a).subst ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p - 1))) =
      fun a : ℤ_[p] => PowerSeries.coeff n (PowerSeries.binomialSeries ℤ_[p] ((p : ℤ_[p]) * a)) := by
    refine DenseRange.equalizer (f := (Nat.cast : ℕ → ℤ_[p])) PadicInt.denseRange_natCast ?_ ?_ ?_
    · simp_rw [coeff_subst_binomialSeries p hf0 n]
      exact continuous_finsetSum _ fun d _ => (PadicInt.continuous_choose d).mul continuous_const
    · simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
      exact (PadicInt.continuous_choose n).comp (continuous_const.mul continuous_id)
    · funext m
      simp only [Function.comp]
      rw [PowerSeries.binomialSeries_nat, subst_one_add_X_pow hs]
      have : (1 + ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p - 1)) ^ m =
          PowerSeries.binomialSeries ℤ_[p] ((p * m : ℕ) : ℤ_[p]) := by
        rw [PowerSeries.binomialSeries_nat, pow_mul]
        congr 1
        ring
      rw [this]
      congr 3
      push_cast
      rfl
  exact congrFun key a

end Binomial

/-- **Example 2.18** (Milne, *CFT*, I): for $K = \mathbb Q_p$, $f = (1+T)^p - 1$ and $a \in \mathbb Z_p$,
$[a]_f = (1+T)^a - 1 = \sum_{m \ge 1} \binom a m T^m$ (Mathlib's `PowerSeries.binomialSeries`, using the binomial
ring structure of $\mathbb Z_p$). -/
@[kb "milne2020cft" "Ch. I, Example 2.18"]
theorem lubinTateEnd_padicInt (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    (lubinTateEnd (lubinTateHyp_padicInt p) (one_add_X_pow_sub_one_mem p) a).toPowerSeries =
      PowerSeries.binomialSeries ℤ_[p] a - 1 := by
  have hf0 : PowerSeries.constantCoeff ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p - 1) = 0 := by
    simp
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hP0 : PowerSeries.constantCoeff (PowerSeries.binomialSeries ℤ_[p] a - 1) = 0 := by simp
  have hPs := PowerSeries.HasSubst.of_constantCoeff_zero' hP0
  refine (eq_lubinTateSeriesHom (lubinTateHyp_padicInt p) (one_add_X_pow_sub_one_mem p)
    (one_add_X_pow_sub_one_mem p) a hP0 ?_ ?_).symm
  · simp [PowerSeries.coeff_one]
  · rw [PowerSeries.subst_sub hPs, PowerSeries.subst_sub hs, subst_one_add_X_pow hPs,
      binomialSeries_subst p a]
    have h1 : ∀ {g : PowerSeries ℤ_[p]} (hg : PowerSeries.HasSubst g), PowerSeries.subst g (1 : PowerSeries ℤ_[p]) = 1 := by
      intro g hg
      rw [← PowerSeries.coe_substAlgHom hg, map_one]
    rw [h1 hPs, h1 hs, add_sub_cancel, binomialSeries_pow_nat]

end NumberFieldKB.MilneCFT
