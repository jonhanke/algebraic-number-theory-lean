import NumberFieldKB.MilneANT.Ch8Dedekind
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: Remark 8.40(e)

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Proves the named statement `Remark8_40e` with an explicit polynomial: $f = X^4 - 60X^2 + 16$, the minimal polynomial
of $\sqrt{13} + \sqrt{17}$, is irreducible over $\mathbb Q$, but over every $\mathbb Q_p$ one of $13$, $17$,
$221 = 13\cdot17$ is a square (Hensel's lemma), so $f$ factors into two quadratics, and over $\mathbb R$ it has degree
$4 > 2$. (Milne's argument uses instead the solvability of Galois groups of local fields and an $S_n$-extension;
any witness proves the existence claim.)
-/

open Polynomial

namespace NumberFieldKB.MilneANT

noncomputable section

set_option linter.style.haveILetI false

/-! ### Irreducibility over the rationals -/

/-- The integer $a$ is not a root of $X^4 - 60X^2 + 16$. -/
theorem int_no_root (a : ℤ) : a ^ 4 - 60 * a ^ 2 + 16 ≠ 0 := by
  intro h
  have h1 : a ^ 2 ≤ 60 := by nlinarith [sq_nonneg (a ^ 2), sq_nonneg a]
  have h2 : a ≤ 7 := by nlinarith
  have h3 : -7 ≤ a := by nlinarith
  interval_cases a <;> omega

/-- The coefficient equations of a factorization into two monic integer quadratics of
$X^4 - 60X^2 + 16$ have no integer solution. -/
theorem int_no_quad (a b c d : ℤ) (h1 : a + c = 0) (h2 : b + d + a * c = -60)
    (h3 : a * d + b * c = 0) (h4 : b * d = 16) : False := by
  have hc : c = -a := by omega
  subst hc
  have h5 : a * (d - b) = 0 := by linarith
  rcases mul_eq_zero.1 h5 with ha | hd
  · subst ha
    have hb : b ∣ 16 := ⟨d, h4.symm⟩
    have hb1 := Int.le_of_dvd (by norm_num) hb
    have hb2 := Int.le_of_dvd (by norm_num) ((neg_dvd).2 hb)
    have hb3 : -16 ≤ b := by linarith
    have hd : d = -60 - b := by linarith
    subst hd
    interval_cases b <;> omega
  · have hdb : d = b := by linarith
    subst hdb
    have : (d - 4) * (d + 4) = 0 := by linarith
    have hd4 : d = 4 ∨ d = -4 := by
      rcases mul_eq_zero.1 this with h | h
      · left; omega
      · right; omega
    have ha : a * a = d + d + 60 := by linarith
    rcases hd4 with rfl | rfl
    · have : a ≤ 9 := by nlinarith
      have : -9 ≤ a := by nlinarith
      interval_cases a <;> omega
    · have : a ≤ 9 := by nlinarith
      have : -9 ≤ a := by nlinarith
      interval_cases a <;> omega

/-- A monic integer polynomial of degree $2$ is $X^2 + aX + b$. -/
theorem monic_quad_form {g : ℤ[X]} (hg : g.Monic) (h : g.natDegree = 2) :
    ∃ a b : ℤ, g = X ^ 2 + C a * X + C b := by
  refine ⟨g.coeff 1, g.coeff 0, ?_⟩
  conv_lhs => rw [hg.as_sum, h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, mul_one]
  ring

/-- $X^4 - 60X^2 + 16$ is irreducible over $\mathbb Z$. -/
theorem quartic_irreducible_int : Irreducible (X ^ 4 - 60 * X ^ 2 + 16 : ℤ[X]) := by
  have hm : (X ^ 4 - 60 * X ^ 2 + 16 : ℤ[X]).Monic := by monicity!
  have hd : (X ^ 4 - 60 * X ^ 2 + 16 : ℤ[X]).natDegree = 4 := by compute_degree!
  rw [hm.irreducible_iff_natDegree']
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg natDegree h
    rw [hd] at this; simp at this
  intro f g hf hg hfg hmem
  rw [hd] at hmem
  have hnd := hf.natDegree_mul hg
  rw [hfg, hd] at hnd
  have hg12 : g.natDegree = 1 ∨ g.natDegree = 2 := by
    have h := Finset.mem_Ioc.1 hmem
    omega
  rcases hg12 with h1 | h2
  · obtain ⟨a, ha⟩ : ∃ a, g = X + C a := ⟨_, hg.eq_X_add_C h1⟩
    subst ha
    have := congrArg (fun q => q.eval (-a)) hfg
    simp at this
    exact int_no_root a (by nlinarith [this])
  · have hfn : f.natDegree = 2 := by omega
    obtain ⟨a, b, eg⟩ := monic_quad_form hg h2
    obtain ⟨c, d, ef⟩ := monic_quad_form hf hfn
    rw [eg, ef] at hfg
    have e : (X ^ 2 + C c * X + C d) * (X ^ 2 + C a * X + C b) =
        X ^ 4 + C (a + c) * X ^ 3 + C (b + d + a * c) * X ^ 2 + C (a * d + b * c) * X + C (b * d) := by
      simp only [C_add, C_mul]; ring
    have hP : (X ^ 4 - 60 * X ^ 2 + 16 : ℤ[X]) =
        X ^ 4 + C 0 * X ^ 3 + C (-60) * X ^ 2 + C 0 * X + C 16 := by
      simp only [map_neg, map_zero, map_ofNat]; ring
    rw [e, hP] at hfg
    have k3 := congrArg (fun q => q.coeff 3) hfg
    have k2 := congrArg (fun q => q.coeff 2) hfg
    have k1 := congrArg (fun q => q.coeff 1) hfg
    have k0 := congrArg (fun q => q.coeff 0) hfg
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at k3 k2 k1 k0
    norm_num at k3 k2 k1 k0
    exact int_no_quad a b c d (by linarith) (by linarith) (by linarith) (by linarith)

/-- The witness polynomial $X^4 - 60X^2 + 16$ over $\mathbb Q$. -/
def quarticQ : ℚ[X] := X ^ 4 - 60 * X ^ 2 + 16

/-- The witness is irreducible over $\mathbb Q$ (Gauss's lemma from `quartic_irreducible_int`). -/
theorem quarticQ_irreducible : Irreducible quarticQ := by
  have hm : (X ^ 4 - 60 * X ^ 2 + 16 : ℤ[X]).Monic := by monicity!
  have h := (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).1 quartic_irreducible_int
  have e : (X ^ 4 - 60 * X ^ 2 + 16 : ℤ[X]).map (algebraMap ℤ ℚ) = quarticQ := by
    simp [quarticQ]
  rwa [e] at h

/-! ### Reducibility when a square root of $13$, $17$ or $221$ exists -/

/-- A product of two polynomials of degree $2$ over a field is not irreducible. -/
theorem not_irreducible_mul_of_natDegree_two {K : Type*} [Field K] {a b : K[X]}
    (ha : a.natDegree = 2) (hb : b.natDegree = 2) : ¬ Irreducible (a * b) := by
  intro h
  rcases h.isUnit_or_isUnit rfl with h | h
  · have := natDegree_eq_zero_of_isUnit h
    omega
  · have := natDegree_eq_zero_of_isUnit h
    omega

/-- If $13$, $17$ or $221$ is a square in a field $K$, then $X^4 - 60X^2 + 16$ is reducible over $K$. -/
theorem quartic_not_irreducible {K : Type*} [Field K] (s : K)
    (hs : s * s = 13 ∨ s * s = 17 ∨ s * s = 221) :
    ¬ Irreducible (X ^ 4 - 60 * X ^ 2 + 16 : K[X]) := by
  have hC : C s * C s = C (s * s) := (C_mul).symm
  rcases hs with hs | hs | hs
  · have h : C s * C s = 13 := by rw [hC, hs]; exact map_ofNat C _
    have e : (X ^ 4 - 60 * X ^ 2 + 16 : K[X]) =
        (X ^ 2 - 2 * C s * X - 4) * (X ^ 2 + 2 * C s * X - 4) := by
      linear_combination (4 * X ^ 2) * h
    rw [e]
    exact not_irreducible_mul_of_natDegree_two (by compute_degree!) (by compute_degree!)
  · have h : C s * C s = 17 := by rw [hC, hs]; exact map_ofNat C _
    have e : (X ^ 4 - 60 * X ^ 2 + 16 : K[X]) =
        (X ^ 2 - 2 * C s * X + 4) * (X ^ 2 + 2 * C s * X + 4) := by
      linear_combination (4 * X ^ 2) * h
    rw [e]
    exact not_irreducible_mul_of_natDegree_two (by compute_degree!) (by compute_degree!)
  · have h : C s * C s = 221 := by rw [hC, hs]; exact map_ofNat C _
    have e : (X ^ 4 - 60 * X ^ 2 + 16 : K[X]) =
        (X ^ 2 - 30 - 2 * C s) * (X ^ 2 - 30 + 2 * C s) := by
      linear_combination 4 * h
    rw [e]
    exact not_irreducible_mul_of_natDegree_two (by compute_degree!) (by compute_degree!)

/-- The image of the witness under a ring map from $\mathbb Q$ is $X^4 - 60X^2 + 16$. -/
theorem quarticQ_map {K : Type*} [Field K] [Algebra ℚ K] :
    quarticQ.map (algebraMap ℚ K) = (X ^ 4 - 60 * X ^ 2 + 16 : K[X]) := by
  simp [quarticQ]

/-! ### Square roots in $\mathbb Q_p$ -/

/-- Hensel step for odd primes: a nonzero square modulo $p$ is a square in $\mathbb Q_p$. -/
theorem exists_sqrt_padic_of_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (n : ℤ)
    (hn : (n : ZMod p) ≠ 0) (hs : IsSquare (n : ZMod p)) : ∃ s : ℚ_[p], s * s = n := by
  obtain ⟨y, hy⟩ := hs
  set x : ℤ := (y.val : ℤ) with hx
  have hxy : (x : ZMod p) = y := by simp [hx]
  have hdvd : (p : ℤ) ∣ x * x - n := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hxy, ← hy]; ring
  have hndvd : ¬ (p : ℤ) ∣ 2 * x := by
    intro h
    rcases (Int.Prime.dvd_mul' hp.out (by exact h)) with h2 | h2
    · have : p ∣ 2 := by exact_mod_cast h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
    · apply hn
      have : (x : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
      rw [hy, ← hxy, this]; ring
  let F : ℤ_[p][X] := X ^ 2 - C (n : ℤ_[p])
  have h1 : F.aeval (x : ℤ_[p]) = ((x * x - n : ℤ) : ℤ_[p]) := by
    simp [F]; ring
  have h2 : F.derivative.aeval (x : ℤ_[p]) = ((2 * x : ℤ) : ℤ_[p]) := by
    simp [F]; norm_num
  have hn1 : ‖F.derivative.aeval (x : ℤ_[p])‖ = 1 := by
    rw [h2]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    exact hndvd ((PadicInt.norm_int_lt_one_iff_dvd _).1 (not_le.1 hlt))
  have hlt : ‖F.aeval (x : ℤ_[p])‖ < ‖F.derivative.aeval (x : ℤ_[p])‖ ^ 2 := by
    rw [hn1, h1]; simpa using (PadicInt.norm_int_lt_one_iff_dvd _).2 hdvd
  obtain ⟨z, hz, -⟩ := hensels_lemma hlt
  refine ⟨(z : ℚ_[p]), ?_⟩
  have : z * z = n := by simp [F] at hz; linear_combination hz
  exact_mod_cast congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) this

/-- Hensel step for $p = 2$: $17$ is a square in $\mathbb Q_2$. -/
theorem exists_sqrt_17_padic_two : ∃ s : ℚ_[2], s * s = 17 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : ℤ_[2][X] := X ^ 2 - C (17 : ℤ_[2])
  have h1 : F.aeval (1 : ℤ_[2]) = ((-16 : ℤ) : ℤ_[2]) := by simp [F]; norm_num
  have h2 : F.derivative.aeval (1 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by simp [F]; norm_num
  have hlt : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [h1, h2]
    have e1 : ((-16 : ℤ) : ℤ_[2]) = -((2 : ℤ_[2]) ^ 4) := by norm_num
    have e2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℕ) := rfl
    rw [e1, norm_neg, e2]
    have := PadicInt.norm_p_pow (p := 2) 4
    have h3 := PadicInt.norm_p (p := 2)
    push_cast at this h3 ⊢
    rw [this, h3]; norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma hlt
  refine ⟨(z : ℚ_[2]), ?_⟩
  have : z * z = 17 := by simp [F] at hz; linear_combination hz
  exact_mod_cast congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) this

/-- For an odd prime $p$, one of $13$, $17$, $221$ is a nonzero square modulo $p$. -/
theorem exists_nonzero_square_mod (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ n : ℤ, (n = 13 ∨ n = 17 ∨ n = 221) ∧ (n : ZMod p) ≠ 0 ∧ IsSquare (n : ZMod p) := by
  by_cases h13 : p = 13
  · subst h13
    exact ⟨17, by norm_num, by decide +revert, 2, by decide +revert⟩
  by_cases h17 : p = 17
  · subst h17
    exact ⟨13, by norm_num, by decide +revert, 8, by decide +revert⟩
  have hne : ∀ q : ℕ, q.Prime → q ≠ p → ((q : ℕ) : ZMod p) ≠ 0 := by
    intro q hq hqp h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).1 h).symm
  have n13 : ((13 : ℤ) : ZMod p) ≠ 0 := by
    have := hne 13 (by norm_num) (Ne.symm h13); simpa using this
  have n17 : ((17 : ℤ) : ZMod p) ≠ 0 := by
    have := hne 17 (by norm_num) (Ne.symm h17); simpa using this
  have n221 : ((221 : ℤ) : ZMod p) ≠ 0 := by
    have : ((221 : ℤ) : ZMod p) = ((13 : ℤ) : ZMod p) * ((17 : ℤ) : ZMod p) := by norm_num
    rw [this]; exact mul_ne_zero n13 n17
  by_cases s13 : IsSquare ((13 : ℤ) : ZMod p)
  · exact ⟨13, by norm_num, n13, s13⟩
  by_cases s17 : IsSquare ((17 : ℤ) : ZMod p)
  · exact ⟨17, by norm_num, n17, s17⟩
  refine ⟨221, by norm_num, n221, ?_⟩
  have c13 := quadraticChar_neg_one_iff_not_isSquare.2 s13
  have c17 := quadraticChar_neg_one_iff_not_isSquare.2 s17
  have : ((221 : ℤ) : ZMod p) = ((13 : ℤ) : ZMod p) * ((17 : ℤ) : ZMod p) := by norm_num
  rw [← quadraticChar_one_iff_isSquare n221, this, map_mul, c13, c17]
  norm_num

/-- For every prime $p$, one of $13$, $17$, $221$ is a square in $\mathbb Q_p$. -/
theorem exists_sqrt_padic (p : ℕ) [hp : Fact p.Prime] :
    ∃ s : ℚ_[p], s * s = 13 ∨ s * s = 17 ∨ s * s = 221 := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨s, hs⟩ := exists_sqrt_17_padic_two
    exact ⟨s, Or.inr (Or.inl hs)⟩
  obtain ⟨n, hn, hn0, hsq⟩ := exists_nonzero_square_mod p hp2
  obtain ⟨s, hs⟩ := exists_sqrt_padic_of_odd p hp2 n hn0 hsq
  refine ⟨s, ?_⟩
  rcases hn with rfl | rfl | rfl
  · left; simpa using hs
  · right; left; simpa using hs
  · right; right; simpa using hs

/-- **Remark 8.40(e) holds**, with the witness $X^4 - 60X^2 + 16$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(e), p. 150"]
theorem remark_8_40e : Remark8_40e := by
  refine ⟨⟨quarticQ, quarticQ_irreducible, ?_, ?_⟩⟩
  · intro p hp
    haveI := Fact.mk hp
    rw [quarticQ_map]
    obtain ⟨s, hs⟩ := exists_sqrt_padic p
    exact quartic_not_irreducible s hs
  · rw [quarticQ_map]
    exact quartic_not_irreducible (Real.sqrt 13)
      (Or.inl (Real.mul_self_sqrt (by norm_num)))

end

end NumberFieldKB.MilneANT
