import Mathlib.NumberTheory.Padics.RingHoms
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, Chapter IV, §2, Lemma 1

For a prime $p$, write $\mathbb Q(p)=\mathbb Z[1/p]$ for the rationals whose denominator is a power of $p$. Weil's
Lemma 1 (p. 64): $\mathbb Q_p=\mathbb Q(p)+\mathbb Z_p$ and $\mathbb Q(p)\cap\mathbb Z_p=\mathbb Z$. It is the local
step of the strong approximation statement $\mathbb Q_{\mathbb A}=\mathbb Q+\mathbb R\times\prod_p\mathbb Z_p$
(IV.§2 Lemma 2).

* **`weil_IV_2_lemma1_sum`**: every $x\in\mathbb Q_p$ is $a/p^n+y$ with $a\in\mathbb Z$, $n\in\mathbb N$, $y\in\mathbb Z_p$;
* **`weil_IV_2_lemma1_inter`**: if $a/p^n\in\mathbb Z_p$ then $a/p^n\in\mathbb Z$.

Weil's proof: write $x=p^{-n}u$ with $u\in\mathbb Z_p$, approximate $u$ by an integer $a$ modulo $p^n$ (density of
$\mathbb Z$ in $\mathbb Z_p$); for the intersection, an element $a/p^n$ with $p\nmid a$, $n>0$ has absolute value $p^n>1$.
-/

namespace NumberFieldKB.WeilBNT

/-- **Weil, IV.§2, Lemma 1, first half**: $\mathbb Q_p=\mathbb Q(p)+\mathbb Z_p$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Lemma 1 (p. 64)"]
theorem weil_IV_2_lemma1_sum (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    ∃ (a : ℤ) (n : ℕ) (y : ℤ_[p]), x = (((a : ℚ) / (p : ℚ) ^ n : ℚ) : ℚ_[p]) + (y : ℚ_[p]) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ hp
  have hu : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
    rw [inv_mul_le_iff₀ hpn, mul_one]
    exact hn.le
  set u : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * x, hu⟩ with hu_def
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n u)
  refine ⟨(u.appr n : ℤ), n, c, ?_⟩
  have hc' : (c : ℚ_[p]) * (p : ℚ_[p]) ^ n = (p : ℚ_[p]) ^ n * x - (u.appr n : ℚ_[p]) := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hc
    push_cast [u] at this
    exact this
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  push_cast
  field_simp
  linear_combination -hc'

/-- **Weil, IV.§2, Lemma 1, second half**: $\mathbb Q(p)\cap\mathbb Z_p=\mathbb Z$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Lemma 1 (p. 64)"]
theorem weil_IV_2_lemma1_inter (p : ℕ) [Fact p.Prime] (a : ℤ) (n : ℕ)
    (h : ‖(((a : ℚ) / (p : ℚ) ^ n : ℚ) : ℚ_[p])‖ ≤ 1) :
    ∃ b : ℤ, (a : ℚ) / (p : ℚ) ^ n = b := by
  have hp : p.Prime := Fact.out
  have hpp : ∀ m : ℕ, padicNorm p ((p : ℚ) ^ m) = ((p : ℚ)⁻¹) ^ m := by
    intro m
    rw [← padicNorm.padicNorm_p_of_prime (p := p)]
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]
  rw [Padic.eq_padicNorm, padicNorm.div, hpp] at h
  have hpn : (0 : ℚ) < ((p : ℚ)⁻¹) ^ n := by
    have : (0 : ℚ) < p := by exact_mod_cast hp.pos
    positivity
  have h : padicNorm p (a : ℚ) / ((p : ℚ)⁻¹) ^ n ≤ 1 := by exact_mod_cast h
  rw [div_le_iff₀ hpn, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg] at h
  obtain ⟨b, hb⟩ := (padicNorm.dvd_iff_norm_le (p := p)).mpr h
  refine ⟨b, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hb]
  push_cast
  field_simp

end NumberFieldKB.WeilBNT
