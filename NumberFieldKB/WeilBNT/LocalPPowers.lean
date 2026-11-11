import NumberFieldKB.WeilBNT.RayGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Weil, *Basic Number Theory*, I.§4, Lemma 5: $(1+P)^{p^n}\subseteq1+P^{n+1}$

$K$ is the completion $L_w$ (`w.adicCompletion L`) of a number field $L$ at a finite place $w$ above the rational prime
$p$ (`(p : 𝓞 L) ∈ w.asIdeal`); it is a $p$-field of characteristic $0$. $1+P^\nu$ is `unitsOnePlusPow w ν`.

* **`weil_I_4_lemma5`**: for every $n\ge0$, $(1+P)^{p^n}\subseteq1+P^{n+1}$.

Weil: "This can be immediately verified by induction on $n$." The step: if $x=1+t$ with $\lvert t\rvert\le\lvert\pi\rvert^j$,
$j\ge1$, then $x^p-1=\sum_{0<i<p}\binom pit^i+t^p$, where $p\mid\binom pi$ gives $\lvert\binom pit^i\rvert\le
\lvert\pi\rvert^{j+1}$ and $\lvert t^p\rvert\le\lvert\pi\rvert^{2j}\le\lvert\pi\rvert^{j+1}$.
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {L : Type} [Field L] [NumberField L]

theorem valued_natCast_le_of_mem (w : HeightOneSpectrum (𝓞 L)) {m : ℕ} (hm : (m : 𝓞 L) ∈ w.asIdeal) :
    Valued.v ((m : ℕ) : w.adicCompletion L) ≤ WithZero.exp (-1) := by
  have e : ((m : ℕ) : w.adicCompletion L) =
      algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (m : 𝓞 L)) := by simp
  rw [e]
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (K := L) (v := w)
    (algebraMap (𝓞 L) L (m : 𝓞 L))]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have := (w.intValuation_le_pow_iff_mem (m : 𝓞 L) 1).2 (by simpa using hm)
  simpa using this

/-- One step of Lemma 5: $(1+P^j)^p\subseteq1+P^{j+1}$ for $j\ge1$. -/
theorem pow_prime_mem_unitsOnePlusPow (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [hp : Fact p.Prime]
    (hpw : (p : 𝓞 L) ∈ w.asIdeal) {j : ℕ} (hj : 1 ≤ j) {x : (w.adicCompletion L)ˣ}
    (hx : x ∈ unitsOnePlusPow (K := L) w j) : x ^ p ∈ unitsOnePlusPow (K := L) w (j + 1) := by
  obtain ⟨hx1, hx2⟩ := hx
  set t : w.adicCompletion L := (x : w.adicCompletion L) - 1 with ht
  have hxt : (x : w.adicCompletion L) = 1 + t := by rw [ht]; ring
  refine ⟨by simp [hx1], ?_⟩
  have hexp : ((x ^ p : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
      ∑ i ∈ Finset.range p, ((p.choose (i + 1) : ℕ) : w.adicCompletion L) * t ^ (i + 1) := by
    rw [Units.val_pow_eq_pow_val, hxt, add_comm, add_pow]
    rw [Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hexp]
  have hb : ∀ i ∈ Finset.range p, Valued.v (((p.choose (i + 1) : ℕ) : w.adicCompletion L) * t ^ (i + 1)) ≤
      WithZero.exp (-((j + 1 : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have htj : Valued.v t ≤ WithZero.exp (-(j : ℤ)) := hx2
    have ht1 : Valued.v t ≤ 1 := htj.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    rw [map_mul, map_pow]
    by_cases hip : i + 1 = p
    · -- the term t^p
      have hc : Valued.v ((p.choose (i + 1) : ℕ) : w.adicCompletion L) ≤ 1 := by
        rw [hip, Nat.choose_self, Nat.cast_one, map_one]
      have h2 : Valued.v t ^ (i + 1) ≤ Valued.v t ^ 2 :=
        pow_le_pow_right_of_le_one' ht1 (by have := hp.out.two_le; omega)
      calc Valued.v ((p.choose (i + 1) : ℕ) : w.adicCompletion L) * Valued.v t ^ (i + 1)
          ≤ 1 * Valued.v t ^ 2 := mul_le_mul' hc h2
        _ ≤ WithZero.exp (-(j : ℤ)) ^ 2 := by rw [one_mul]; exact pow_le_pow_left' htj 2
        _ ≤ WithZero.exp (-((j + 1 : ℕ) : ℤ)) := by
          rw [← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul]; push_cast; omega
    · -- p divides the binomial coefficient
      have hdvd : p ∣ p.choose (i + 1) := hp.out.dvd_choose_self (by omega) (by omega)
      obtain ⟨c, hc⟩ := hdvd
      have hcv : Valued.v ((p.choose (i + 1) : ℕ) : w.adicCompletion L) ≤ WithZero.exp (-1) := by
        rw [hc, Nat.cast_mul, map_mul]
        have hc1 : Valued.v ((c : ℕ) : w.adicCompletion L) ≤ 1 := by
          have e : ((c : ℕ) : w.adicCompletion L) =
              algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (c : 𝓞 L)) := by simp
          rw [e]
          erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (K := L) (v := w)
            (algebraMap (𝓞 L) L (c : 𝓞 L))]
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact w.intValuation_le_one _
        calc _ ≤ WithZero.exp (-1) * 1 := mul_le_mul' (valued_natCast_le_of_mem w hpw) hc1
          _ = _ := mul_one _
      have h2 : Valued.v t ^ (i + 1) ≤ Valued.v t := by
        simpa using pow_le_pow_right_of_le_one' ht1 (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero i))
      calc Valued.v ((p.choose (i + 1) : ℕ) : w.adicCompletion L) * Valued.v t ^ (i + 1)
          ≤ WithZero.exp (-1) * WithZero.exp (-(j : ℤ)) := mul_le_mul' hcv (h2.trans htj)
        _ = WithZero.exp (-((j + 1 : ℕ) : ℤ)) := by
          rw [← WithZero.exp_add]; congr 1; push_cast; ring
  exact Valuation.map_sum_le _ hb

/-- **Weil, I.§4, Lemma 5** ($K=L_w$, a $p$-field of characteristic $0$). For every $n\ge0$,
$(1+P)^{p^n}\subseteq1+P^{n+1}$. -/
@[kb "weil1973bnt" "Ch. I, §4, Lemma 5 (K the completion of a number field)"]
theorem weil_I_4_lemma5 (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [Fact p.Prime]
    (hpw : (p : 𝓞 L) ∈ w.asIdeal) (n : ℕ) {x : (w.adicCompletion L)ˣ}
    (hx : x ∈ unitsOnePlusPow (K := L) w 1) : x ^ (p ^ n) ∈ unitsOnePlusPow (K := L) w (n + 1) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ, pow_mul]
    exact pow_prime_mem_unitsOnePlusPow w p hpw (by omega) ih

end NumberFieldKB.WeilBNT
