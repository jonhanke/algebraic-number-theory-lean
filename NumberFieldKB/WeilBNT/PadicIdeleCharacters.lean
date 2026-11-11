import NumberFieldKB.WeilBNT.LocalPowers
import NumberFieldKB.WeilBNT.LocalPPowers
import NumberFieldKB.WeilBNT.IdeleCharacterExtension
import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Weil, *Basic Number Theory*, VII.§8, Prop. 16: morphisms of the ideles into $K^\times$, $K$ a $p$-field

$k$ is a number field (`K`). The target is a $p$-field of characteristic $0$, taken here as the completion
$L_w$ (`w.adicCompletion L`) of a number field $L$ at a finite place $w$ lying over the rational prime $p$
(`(p : 𝓞 L) ∈ w.asIdeal`). (Every $p$-field of characteristic $0$ is such a completion; that fact is not used.)
A *morphism* is a continuous homomorphism. For a finite place $v$ of $k$, $k_v$ is a $p$-field exactly when
$v\mid p$, i.e. `(p : 𝓞 K) ∈ v.asIdeal`; the infinite places are never $p$-fields.

* **`weil_VII_8_prop16_almost_all`**: a morphism $\omega:k_{\mathbb A}^\times\to L_w^\times$ is trivial on $r_v^\times$
  for almost all $v$.
* **`weil_VII_8_prop16_finite`**: for a finite place $v\nmid p$, $\omega$ is locally constant on $k_v^\times$ (trivial
  on an open subgroup: its kernel there is open).
* **`weil_VII_8_prop16_infinite`**: for an infinite place $v$, $\omega$ is locally constant on $k_v^\times$.

Weil's proof: (infinite places) a morphism of a connected group into the totally disconnected $L_w^\times$ is trivial,
so $\omega$ is trivial on $\mathbb R_+^\times$ or $\mathbb C^\times$; (finite $v\nmid p$) choose $m$ with
$\omega(1+\mathfrak p_v^m)\subseteq1+P$; every $z\in1+\mathfrak p_v^m$ is $z'^{p^n}$ with $z'\in1+\mathfrak p_v^m$
(II.3 Prop. 8, `weil_II_3_prop8_bijOn`), so $\omega(z)\in(1+P)^{p^n}\subseteq1+P^{n+1}$ (I.4 Lemma 5) for all $n$, and
$\omega(z)=1$; (almost all $v$) a neighbourhood of $1$ mapped into $1+P^\nu$ contains $r_v^\times$ for almost all $v$,
and for $\nu$ large $1+P^\nu$ contains no root of unity other than $1$, while $r_v^\times/(1+\mathfrak p_v)$ is finite.
-/

open IsDedekindDomain NumberField Topology NumberFieldKB.MilneCFT

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]

theorem eq_zero_of_forall_le_exp {a : WithZero (Multiplicative ℤ)}
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))) : a = 0 := by
  by_contra ha
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(WithZero.log a) < n := ⟨(-(WithZero.log a)).toNat + 1, by omega⟩
  have := h n
  rw [← WithZero.exp_log ha, WithZero.exp_le_exp] at this
  omega

theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) :
    a ≤ WithZero.exp (-1) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  · rw [← WithZero.exp_log ha] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem unitsOnePlusPow_anti (v : HeightOneSpectrum (𝓞 K)) {a b : ℕ} (h : a ≤ b) :
    unitsOnePlusPow (K := K) v b ≤ unitsOnePlusPow (K := K) v a := by
  rintro u ⟨h1, h2⟩
  exact ⟨h1, h2.trans (WithZero.exp_le_exp.2 (by omega))⟩

theorem trivial_of_maps_into_onePlusPow (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 L) ∈ w.asIdeal) (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∉ v.asIdeal)
    (f : (v.adicCompletion K)ˣ →* (w.adicCompletion L)ˣ) {m : ℕ} (hm : 1 ≤ m)
    (h : ∀ u ∈ unitsOnePlusPow (K := K) v m, f u ∈ unitsOnePlusPow (K := L) w 1) :
    ∀ z ∈ unitsOnePlusPow (K := K) v m, f z = 1 := by
  intro z hz
  have key : ∀ n : ℕ, Valued.v ((f z : w.adicCompletion L) - 1) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro n
    have hpn : ((p ^ n : ℕ) : 𝓞 K) ∉ v.asIdeal := by
      rw [Nat.cast_pow]; exact fun h => hv (v.isPrime.mem_of_pow_mem _ h)
    obtain ⟨z', hz', hzz'⟩ := (weil_II_3_prop8_bijOn v hpn hm).surjOn hz
    have hzz'' : z' ^ (p ^ n) = z := hzz'
    have : f z ∈ unitsOnePlusPow (K := L) w (n + 1) := by
      rw [← hzz'', map_pow]; exact weil_I_4_lemma5 w p hp n (h z' hz')
    exact this.2
  have := eq_zero_of_forall_le_exp key
  have h0 : (f z : w.adicCompletion L) - 1 = 0 := (Valuation.zero_iff _).1 this
  exact Units.ext (sub_eq_zero.1 h0)

theorem exists_nu_pow_lt (ρ : WithZero (Multiplicative ℤ)) (hρ : ρ ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    ∃ ν : ℕ, 1 ≤ ν ∧ WithZero.exp (-(ν : ℤ)) ^ k < ρ := by
  refine ⟨(-(WithZero.log ρ)).toNat + 1, by omega, ?_⟩
  rw [← WithZero.exp_nsmul]
  conv_rhs => rw [← WithZero.exp_log hρ]
  rw [WithZero.exp_lt_exp, nsmul_eq_mul]
  have h1 : -(WithZero.log ρ) < (((-(WithZero.log ρ)).toNat + 1 : ℕ) : ℤ) := by omega
  have h2 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem eq_one_of_pow_prime_eq_one (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [hpf : Fact p.Prime]
    {ν : ℕ} (hν : 1 ≤ ν)
    (hcond : WithZero.exp (-(ν : ℤ)) ^ (p - 1) < Valued.v ((p : ℕ) : w.adicCompletion L))
    {z : (w.adicCompletion L)ˣ} (hz : z ∈ unitsOnePlusPow (K := L) w ν) (hzp : z ^ p = 1) : z = 1 := by
  by_contra hne
  obtain ⟨hz1, hz2⟩ := hz
  set t : w.adicCompletion L := (z : w.adicCompletion L) - 1 with ht
  have hxt : (z : w.adicCompletion L) = 1 + t := by rw [ht]; ring
  have ht0 : t ≠ 0 := by
    intro h0
    apply hne
    apply Units.ext
    rw [hxt, h0]; simp
  set r := Valued.v t with hr
  have hr0 : r ≠ 0 := by rw [hr]; simpa using ht0
  have hrν : r ≤ WithZero.exp (-(ν : ℤ)) := hz2
  have hr1 : r < 1 := by
    refine lt_of_le_of_lt hrν ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  set ρ := Valued.v ((p : ℕ) : w.adicCompletion L) with hρ
  have hρ0 : ρ ≠ 0 := by
    rw [hρ]; simpa using hpf.out.ne_zero
  have hexp : ((z ^ p : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
      ∑ i ∈ Finset.range p, ((p.choose (i + 1) : ℕ) : w.adicCompletion L) * t ^ (i + 1) := by
    rw [Units.val_pow_eq_pow_val, hxt, add_comm, add_pow]
    rw [Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hzp] at hexp
  simp only [Units.val_one, sub_self] at hexp
  have h0mem : 0 ∈ Finset.range p := Finset.mem_range.2 hpf.out.pos
  rw [← Finset.add_sum_erase _ _ h0mem] at hexp
  simp only [zero_add, pow_one, Nat.choose_one_right] at hexp
  have hmul : 0 < ρ * r := zero_lt_iff.2 (mul_ne_zero hρ0 hr0)
  have hrr : ∀ j : ℕ, 2 ≤ j → r ^ j < r := by
    intro j hj
    calc r ^ j ≤ r ^ 2 := pow_le_pow_right_of_le_one' hr1.le hj
      _ = r * r := sq r
      _ < r * 1 := mul_lt_mul_of_pos_left hr1 (zero_lt_iff.2 hr0)
      _ = r := mul_one r
  have hS : Valued.v (∑ i ∈ (Finset.range p).erase 0,
      ((p.choose (i + 1) : ℕ) : w.adicCompletion L) * t ^ (i + 1)) < ρ * r := by
    refine Valuation.map_sum_lt' _ hmul fun i hi => ?_
    rw [Finset.mem_erase, Finset.mem_range] at hi
    obtain ⟨hi0, hip⟩ := hi
    rw [map_mul, map_pow]
    by_cases hpi : i + 1 = p
    · rw [hpi, Nat.choose_self, Nat.cast_one, map_one, one_mul]
      calc r ^ p = r ^ (p - 1) * r := by
            rw [← pow_succ]; congr 1; have := hpf.out.pos; omega
        _ ≤ WithZero.exp (-(ν : ℤ)) ^ (p - 1) * r := mul_le_mul' (pow_le_pow_left' hrν _) le_rfl
        _ < ρ * r := mul_lt_mul_of_pos_right hcond (zero_lt_iff.2 hr0)
    · have hdvd : p ∣ p.choose (i + 1) := hpf.out.dvd_choose_self (by omega) (by omega)
      obtain ⟨c, hc⟩ := hdvd
      have hcv : Valued.v ((p.choose (i + 1) : ℕ) : w.adicCompletion L) ≤ ρ := by
        rw [hc, Nat.cast_mul, map_mul]
        have hc1 : Valued.v ((c : ℕ) : w.adicCompletion L) ≤ 1 := by
          have e : ((c : ℕ) : w.adicCompletion L) =
              algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (c : 𝓞 L)) := by simp
          rw [e]
          erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (K := L) (v := w)
            (algebraMap (𝓞 L) L (c : 𝓞 L))]
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact w.intValuation_le_one _
        calc _ ≤ ρ * 1 := mul_le_mul' le_rfl hc1
          _ = ρ := mul_one _
      calc Valued.v ((p.choose (i + 1) : ℕ) : w.adicCompletion L) * r ^ (i + 1) ≤ ρ * r ^ (i + 1) :=
            mul_le_mul' hcv le_rfl
        _ < ρ * r := mul_lt_mul_of_pos_left (hrr _ (by omega)) (zero_lt_iff.2 hρ0)
  have hfirst : Valued.v (((p : ℕ) : w.adicCompletion L) * t) = ρ * r := by
    rw [map_mul]
  have hsum : Valued.v (((p : ℕ) : w.adicCompletion L) * t + ∑ i ∈ (Finset.range p).erase 0,
      ((p.choose (i + 1) : ℕ) : w.adicCompletion L) * t ^ (i + 1)) =
      Valued.v (((p : ℕ) : w.adicCompletion L) * t) :=
    Valuation.map_add_eq_of_lt_left _ (by rw [hfirst]; exact hS)
  rw [← hexp, map_zero, hfirst] at hsum
  exact hmul.ne hsum

theorem eq_one_of_pow_eq_one (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [hpf : Fact p.Prime]
    (hp : (p : 𝓞 L) ∈ w.asIdeal) {ν : ℕ} (hν : 1 ≤ ν)
    (hcond : WithZero.exp (-(ν : ℤ)) ^ (p - 1) < Valued.v ((p : ℕ) : w.adicCompletion L))
    {N : ℕ} (hN : N ≠ 0) {x : (w.adicCompletion L)ˣ} (hx : x ∈ unitsOnePlusPow (K := L) w ν)
    (hxN : x ^ N = 1) : x = 1 := by
  obtain ⟨a, m, hpm, hNam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hpf.out.ne_one
  have hmw : (m : 𝓞 L) ∉ w.asIdeal := by
    intro hm
    have hcop : IsCoprime (p : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hpf.out).2 hpm)
    obtain ⟨s, t, hst⟩ := hcop
    have h1 : (1 : 𝓞 L) = (s : 𝓞 L) * (p : 𝓞 L) + (t : 𝓞 L) * (m : 𝓞 L) := by
      have := congrArg (Int.cast : ℤ → 𝓞 L) hst
      push_cast at this
      exact this.symm
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hm)
  have hy : x ^ (p ^ a) ∈ unitsOnePlusPow (K := L) w 1 :=
    unitsOnePlusPow_anti w hν (Subgroup.pow_mem _ hx _)
  have hym : (x ^ (p ^ a)) ^ m = 1 := by rw [← pow_mul, ← hNam]; exact hxN
  have hy1 : x ^ (p ^ a) = 1 :=
    (weil_II_3_prop8_bijOn w hmw le_rfl).injOn hy (Subgroup.one_mem _) (by simpa using hym)
  clear hNam hxN hym hy
  induction a with
  | zero => simpa using hy1
  | succ a ih =>
    refine ih ?_
    refine eq_one_of_pow_prime_eq_one w p hν hcond (Subgroup.pow_mem _ hx _) ?_
    rw [← pow_mul, ← pow_succ]; exact hy1

theorem exists_pow_mem_unitsOnePlusPow_one (v : HeightOneSpectrum (𝓞 K)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ u ∈ unitsInt (K := K) v, u ^ N ∈ unitsOnePlusPow (K := K) v 1 := by
  classical
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  let _ : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  have := Fintype.ofFinite (𝓞 K ⧸ v.asIdeal)
  have hq : 2 ≤ Fintype.card (𝓞 K ⧸ v.asIdeal) := Fintype.one_lt_card
  refine ⟨Fintype.card (𝓞 K ⧸ v.asIdeal) - 1, by omega, fun u hu => ?_⟩
  set N := Fintype.card (𝓞 K ⧸ v.asIdeal) - 1 with hN
  have hu1 : Valued.v (u : v.adicCompletion K) = 1 := hu
  have hint : ∀ b : 𝓞 K, Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K b)) =
      v.intValuation b := by
    intro b
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v)
      (algebraMap (𝓞 K) K b)]
    exact HeightOneSpectrum.valuation_of_algebraMap _ b
  -- approximate `u` by `k ∈ K`, then by `a ∈ 𝓞 K`
  have hnhds := QuadFormsKB.Lattices.valued_le_mem_nhds v (u : v.adicCompletion K) 1
  obtain ⟨_, hk0, k, rfl⟩ := mem_closure_iff_nhds.1
    ((HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K v) (u : v.adicCompletion K)) _ hnhds
  have hk : Valued.v (algebraMap K (v.adicCompletion K) k - (u : v.adicCompletion K)) < 1 :=
    lt_of_le_of_lt hk0 (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hk' : Valued.v (algebraMap K (v.adicCompletion K) k) = 1 := by
    have := Valuation.map_eq_of_sub_lt (Valued.v (R := v.adicCompletion K))
      (x := (u : v.adicCompletion K)) (y := algebraMap K (v.adicCompletion K) k) (by rw [hu1]; exact hk)
    rw [this, hu1]
  have hkint : v.valuation K k ≤ 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v) k
    rw [← this]
    exact hk'.le
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hkint 1
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) -
      algebraMap K (v.adicCompletion K) k) < 1 := by
    rw [← map_sub]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v)
      (algebraMap (𝓞 K) K a - k)]
    simpa using ha
  set A := algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) with hA
  have hAu : Valued.v (A - (u : v.adicCompletion K)) < 1 := by
    have : A - (u : v.adicCompletion K) = (A - algebraMap K (v.adicCompletion K) k) +
        (algebraMap K (v.adicCompletion K) k - u) := by ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha' hk)
  have hA1 : Valued.v A = 1 := by
    have := Valuation.map_eq_of_sub_lt (Valued.v (R := v.adicCompletion K))
      (x := (u : v.adicCompletion K)) (y := A) (by rw [hu1]; exact hAu)
    rw [this, hu1]
  have hanv : a ∉ v.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← hint, ← hA]; exact hA1
  have hmk : (Ideal.Quotient.mk v.asIdeal a) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hanv
  have hpow : a ^ N - 1 ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hN,
      FiniteField.pow_card_sub_one_eq_one _ hmk, map_one, sub_self]
  have hAN : Valued.v (A ^ N - 1) < 1 := by
    have : A ^ N - 1 = algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (a ^ N - 1)) := by
      simp [hA]
    rw [this, hint]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 hpow
  have huN : Valued.v ((u : v.adicCompletion K) ^ N - A ^ N) < 1 := by
    rw [← geom_sum₂_mul, map_mul]
    have hs : Valued.v (∑ i ∈ Finset.range N, (u : v.adicCompletion K) ^ i * A ^ (N - 1 - i)) ≤ 1 := by
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul, map_pow, map_pow, hu1, hA1]; simp
    calc _ ≤ 1 * Valued.v ((u : v.adicCompletion K) - A) := mul_le_mul' hs le_rfl
      _ = Valued.v (A - (u : v.adicCompletion K)) := by rw [one_mul, Valuation.map_sub_swap]
      _ < 1 := hAu
  have hfin : Valued.v ((u : v.adicCompletion K) ^ N - 1) < 1 := by
    have : (u : v.adicCompletion K) ^ N - 1 = ((u : v.adicCompletion K) ^ N - A ^ N) + (A ^ N - 1) := by ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt huN hAN)
  refine ⟨by rw [Units.val_pow_eq_pow_val, map_pow, hu1, one_pow], ?_⟩
  rw [Units.val_pow_eq_pow_val]
  exact le_exp_neg_one_of_lt_one hfin

/-- **Weil, VII.§8, Prop. 16, first assertion.** Let $\omega$ be a morphism of $k_{\mathbb A}^\times$ into $L_w^\times$,
a $p$-field. Then $\omega$ is trivial on $r_v^\times$ for all but finitely many finite places $v$ of $k$. -/
@[kb "weil1973bnt" "Ch. VII, §8, Prop. 16, first assertion (target a completion of a number field)"]
theorem weil_VII_8_prop16_almost_all (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 L) ∈ w.asIdeal) (ω : IdeleGroup (𝓞 K) K →* (w.adicCompletion L)ˣ) (hω : Continuous ω) :
    {v : HeightOneSpectrum (𝓞 K) |
      ¬ ∀ u ∈ unitsInt (K := K) v, ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1}.Finite := by
  classical
  have hpf : p.Prime := Fact.out
  obtain ⟨ν, hν1, hνc⟩ : ∃ ν : ℕ, 1 ≤ ν ∧
      WithZero.exp (-(ν : ℤ)) ^ (p - 1) < Valued.v ((p : ℕ) : w.adicCompletion L) :=
    exists_nu_pow_lt _ (by simpa using hpf.ne_zero) (p - 1) (by have := hpf.two_le; omega)
  have hU : ω ⁻¹' (unitsOnePlusPow (K := L) w ν : Set (w.adicCompletion L)ˣ) ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K) :=
    ((isOpen_unitsOnePlusPow w ν).preimage hω).mem_nhds (by simp)
  obtain ⟨T, n, hT⟩ := idele_nhds_one hU
  have hPfin : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.Finite := by
    have hne : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hpf.ne_zero
    refine (Ideal.finite_factors hne).subset fun v hv => ?_
    show v.asIdeal ∣ Ideal.span {(p : 𝓞 K)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hv
  refine (T.finite_toSet.union hPfin).subset ?_
  intro v hv
  by_contra hvn
  simp only [Set.mem_union, not_or, Finset.mem_coe, Set.mem_ofPred_eq] at hvn
  obtain ⟨hvT, hvP⟩ := hvn
  apply hv
  have hmaps : ∀ u ∈ unitsInt (K := K) v,
      ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) ∈ unitsOnePlusPow (K := L) w ν := by
    intro u hu
    refine hT _ (fun w' => ideleInfAt_ofAdicCompletion v u w') (fun v' hv' => ?_) (fun v' hv' => ?_)
    · have hne : v' ≠ v := fun h => hvT (h ▸ hv')
      rw [ideleFinAt_ofAdicCompletion_ne v v' hne, sub_self, map_zero]
      exact zero_le
    · by_cases h : v' = v
      · subst h
        rw [ideleFinAt_ofAdicCompletion_self]; exact hu
      · rw [ideleFinAt_ofAdicCompletion_ne v v' h, map_one]
  obtain ⟨N, hN0, hN⟩ := exists_pow_mem_unitsOnePlusPow_one (K := K) v
  have htriv := trivial_of_maps_into_onePlusPow w p hp v hvP
    (ω.comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) (m := 1) le_rfl
    (fun z hz => unitsOnePlusPow_anti w hν1 (hmaps z hz.1))
  intro u hu
  refine eq_one_of_pow_eq_one w p hp hν1 hνc hN0 (hmaps u hu) ?_
  rw [← map_pow, ← map_pow]
  exact htriv _ (hN u hu)

/-- **Weil, VII.§8, Prop. 16, second assertion, finite places.** For a finite place $v$ of $k$ with $v\nmid p$ (so
$k_v$ is not a $p$-field), a morphism $\omega:k_{\mathbb A}^\times\to L_w^\times$ is locally constant on $k_v^\times$:
its kernel on $k_v^\times$ is open. -/
@[kb "weil1973bnt" "Ch. VII, §8, Prop. 16, second assertion, finite places"]
theorem weil_VII_8_prop16_finite (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 L) ∈ w.asIdeal) (ω : IdeleGroup (𝓞 K) K →* (w.adicCompletion L)ˣ) (hω : Continuous ω)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∉ v.asIdeal) :
    IsOpen ((ω.comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)).ker : Set (v.adicCompletion K)ˣ) := by
  set f := ω.comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v) with hf
  have hfc : Continuous f := hω.comp (item_4_3.1 v).continuous
  have hU : IsOpen {u | f u ∈ unitsOnePlusPow (K := L) w 1} :=
    (isOpen_unitsOnePlusPow w 1).preimage hfc
  have hs : (Units.val '' {u | f u ∈ unitsOnePlusPow (K := L) w 1}) ∈ 𝓝 (1 : v.adicCompletion K) := by
    have := Units.isOpenEmbedding_val.isOpenMap _ hU
    exact this.mem_nhds ⟨1, by simp, rfl⟩
  obtain ⟨n, hn⟩ := exists_valued_le_of_mem_nhds_one v hs
  have hmaps : ∀ z ∈ unitsOnePlusPow (K := K) v (n + 1), f z ∈ unitsOnePlusPow (K := L) w 1 := by
    intro z hz
    obtain ⟨u, hu, hue⟩ := hn (z : v.adicCompletion K) (hz.2.trans (WithZero.exp_le_exp.2 (by omega)))
    rw [← Units.ext hue]; exact hu
  have hsub : unitsOnePlusPow (K := K) v (n + 1) ≤ f.ker := fun z hz =>
    trivial_of_maps_into_onePlusPow w p hp v hv f (m := n + 1) (by omega) hmaps z hz
  exact Subgroup.isOpen_mono hsub (isOpen_unitsOnePlusPow v (n + 1))

/-- **Weil, VII.§8, Prop. 16, second assertion, infinite places.** For an infinite place $v$ of $k$, a morphism
$\omega:k_{\mathbb A}^\times\to L_w^\times$ is locally constant on $k_v^\times$: its kernel there is open. -/
@[kb "weil1973bnt" "Ch. VII, §8, Prop. 16, second assertion, infinite places"]
theorem weil_VII_8_prop16_infinite (w : HeightOneSpectrum (𝓞 L))
    (ω : IdeleGroup (𝓞 K) K →* (w.adicCompletion L)ˣ) (hω : Continuous ω) (v : InfinitePlace K) :
    IsOpen ((ω.comp (IdeleGroup.ofCompletion (𝓞 K) K v)).ker : Set (v.Completion)ˣ) := by
  set f := ω.comp (IdeleGroup.ofCompletion (𝓞 K) K v) with hf
  have hfc : Continuous f := hω.comp (item_4_3.2 v).continuous
  have : LocallyConnectedSpace v.Completion := by
    by_cases hv : v.IsReal
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.1 hv)).toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace (v.Completion)ˣ := Units.isOpenEmbedding_val.locallyConnectedSpace
  have hker : connectedComponent (1 : (v.Completion)ˣ) ⊆ f.ker := by
    intro z hz
    have hmem : f z ∈ connectedComponent (1 : (w.adicCompletion L)ˣ) := by
      have := hfc.image_connectedComponent_subset 1 ⟨z, hz, rfl⟩
      simpa using this
    have key : ∀ n : ℕ, f z ∈ unitsOnePlusPow (K := L) w (n + 1) := fun n =>
      (IsClopen.connectedComponent_subset
        ⟨Subgroup.isClosed_of_isOpen _ (isOpen_unitsOnePlusPow w (n + 1)), isOpen_unitsOnePlusPow w (n + 1)⟩
        (Subgroup.one_mem _)) hmem
    have h0 := eq_zero_of_forall_le_exp fun n => (key n).2
    exact Units.ext (sub_eq_zero.1 ((Valuation.zero_iff _).1 h0))
  exact Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (isOpen_connectedComponent.mem_nhds mem_connectedComponent) hker)

end NumberFieldKB.WeilBNT
