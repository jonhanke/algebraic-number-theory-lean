import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Algebra.Order.Star.Real
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V §4: Euler products of Dirichlet series (Proposition 4.5, Remark 4.6)

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §4, pdf pp. 206–207.

Proposition 4.5 is a statement about the coefficients $c(n)$ only; it is stated for any sequence of complex numbers
of polynomial growth (the coefficients of a modular form satisfy $|c(n)| \le Cn^k$, pdf p. 205), with the
normalisation $c(1) = 1$. Milne states it without $c(1) = 1$; it is needed: $c = 0$ satisfies $(*)$ but its
$L$-series is not the Euler product (erratum), and an Euler product has first coefficient $1$.
-/

open Complex Filter Topology

namespace NumberFieldKB.MilneEC.V

/-- The conditions $(*)$ of Proposition 4.5 (pdf p. 206) on $c : \mathbb N \to \mathbb C$, for level $N$ and
weight $2k$: $c(mn) = c(m)c(n)$ for coprime $m$, $n$; $c(p)c(p^r) = c(p^{r+1}) + p^{2k-1}c(p^{r-1})$ for $r \ge 1$
and $p \nmid N$; $c(p^r) = c(p)^r$ for $r \ge 1$ and $p \mid N$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.5, conditions (*), pdf p. 206"]
def HeckeRecurrence (N k : ℕ) (c : ℕ → ℂ) : Prop :=
  (∀ m n : ℕ, m.Coprime n → c (m * n) = c m * c n) ∧
  (∀ p r : ℕ, p.Prime → ¬ p ∣ N → 1 ≤ r →
    c p * c (p ^ r) = c (p ^ (r + 1)) + (p : ℂ) ^ (2 * k - 1) * c (p ^ (r - 1))) ∧
  (∀ p r : ℕ, p.Prime → p ∣ N → 1 ≤ r → c (p ^ r) = c p ^ r)

/-- The Euler factor at $p$ of Proposition 4.5: $(1 - c(p)p^{-s})^{-1}$ if $p \mid N$ and
$(1 - c(p)p^{-s} + p^{2k-1-2s})^{-1}$ otherwise. -/
noncomputable def eulerFactor (N k : ℕ) (c : ℕ → ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  if p ∣ N then (1 - c p * (p : ℂ) ^ (-s))⁻¹
  else (1 - c p * (p : ℂ) ^ (-s) + (p : ℂ) ^ ((2 * k - 1 : ℕ) - 2 * s))⁻¹

/-- Helper: a summable sequence with a two-term linear recurrence sums to the inverse of the characteristic
polynomial. -/
lemma tsum_rec2 (u : ℕ → ℂ) (hu : Summable u) (α β : ℂ) (h0 : u 0 = 1) (h1 : u 1 = α)
    (hrec : ∀ e, u (e + 2) = α * u (e + 1) - β * u e) : (1 - α + β) * ∑' e, u e = 1 := by
  have hu1 : Summable (fun e => u (e + 1)) := (summable_nat_add_iff 1).mpr hu
  have e1 : ∑' e, u e = u 0 + ∑' e, u (e + 1) := hu.tsum_eq_zero_add
  have e2 : ∑' e, u (e + 1) = u 1 + ∑' e, u (e + 1 + 1) := hu1.tsum_eq_zero_add
  have e3 : ∑' e, u (e + 1 + 1) = α * ∑' e, u (e + 1) - β * ∑' e, u e := by
    rw [← hu1.tsum_mul_left, ← hu.tsum_mul_left, ← (hu1.mul_left α).tsum_sub (hu.mul_left β)]
    exact tsum_congr hrec
  rw [h0] at e1
  rw [h1] at e2
  linear_combination e1 + e2 + e3 - α * e1

/-- Helper: a summable geometric-type sequence sums to the inverse of the characteristic polynomial. -/
lemma tsum_rec1 (u : ℕ → ℂ) (hu : Summable u) (α : ℂ) (h0 : u 0 = 1)
    (hrec : ∀ e, u (e + 1) = α * u e) : (1 - α) * ∑' e, u e = 1 := by
  have e1 : ∑' e, u e = u 0 + ∑' e, u (e + 1) := hu.tsum_eq_zero_add
  have e3 : ∑' e, u (e + 1) = α * ∑' e, u e := by
    rw [← hu.tsum_mul_left]; exact tsum_congr hrec
  rw [h0, e3] at e1
  linear_combination e1

/-- Helper: the Dirichlet series term at a prime power. -/
lemma term_prime_pow (c : ℕ → ℂ) (s : ℂ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    LSeries.term c s (p ^ e) = c (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [LSeries.term_of_ne_zero (pow_ne_zero _ hp.ne_zero), Nat.cast_pow, div_eq_mul_inv]
  congr 1
  rw [cpow_neg, inv_pow, ← cpow_nat_mul, ← natCast_cpow_natCast_mul]

/-- Helper: the local Euler factor equals the sum of the local Dirichlet series terms. -/
lemma local_factor (N k : ℕ) (c : ℕ → ℂ) (hc1 : c 1 = 1) (hrec : HeckeRecurrence N k c)
    (s : ℂ) (p : ℕ) (hp : p.Prime) (hsum : Summable (fun e => LSeries.term c s (p ^ e))) :
    ∑' e, LSeries.term c s (p ^ e) = eulerFactor N k c p s := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set X : ℂ := (p : ℂ) ^ (-s) with hX
  have hu : ∀ e, LSeries.term c s (p ^ e) = c (p ^ e) * X ^ e := fun e => term_prime_pow c s p hp e
  unfold eulerFactor
  split_ifs with hN
  · have key := tsum_rec1 (fun e => LSeries.term c s (p ^ e)) hsum (c p * X)
      (by simp [hc1]) (by
        intro e
        rw [hu, hu]
        rcases Nat.eq_zero_or_pos e with rfl | he
        · simp [hc1]
        · rw [hrec.2.2 p (e + 1) hp hN (by omega), hrec.2.2 p e hp hN he]; ring)
    exact (inv_eq_of_mul_eq_one_right key).symm
  · have h2 : (p : ℂ) ^ (-(2 * s)) = X ^ 2 := by
      rw [hX, show -(2 * s) = ((2 : ℕ) : ℂ) * (-s) by push_cast; ring, cpow_nat_mul]
    have hq : (p : ℂ) ^ (((2 * k - 1 : ℕ) : ℂ) - 2 * s) = (p : ℂ) ^ (2 * k - 1) * X ^ 2 := by
      rw [sub_eq_add_neg, cpow_add _ _ hp0, cpow_natCast, h2]
    have key := tsum_rec2 (fun e => LSeries.term c s (p ^ e)) hsum (c p * X)
      ((p : ℂ) ^ (2 * k - 1) * X ^ 2) (by simp [hc1]) (by simpa using hu 1)
      (by
        intro e
        have := hrec.2.1 p (e + 1) hp hN (by omega)
        simp only [Nat.add_sub_cancel] at this
        rw [hu, hu, hu]
        linear_combination (-X ^ (e + 2)) * this)
    rw [hq]
    have : 1 - c p * X + (p : ℂ) ^ (2 * k - 1) * X ^ 2 = 1 - c p * X + (p : ℂ) ^ (2 * k - 1) * X ^ 2 := rfl
    exact (inv_eq_of_mul_eq_one_right key).symm

/-- Helper: the Euler product direction of Proposition 4.5. -/
lemma euler_of_rec (N k : ℕ) (c : ℕ → ℂ) (hc1 : c 1 = 1) (hrec : HeckeRecurrence N k c)
    (C A : ℝ) (hb : ∀ n : ℕ, ‖c n‖ ≤ C * (n : ℝ) ^ A) (s : ℂ) (hs : A + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ eulerFactor N k c p s) (LSeries c s) := by
  have hsm : LSeriesSummable c s :=
    LSeriesSummable_of_le_const_mul_rpow (x := A + 1) hs ⟨C, fun n _ => by simpa using hb n⟩
  have hnorm : Summable (fun n => ‖LSeries.term c s n‖) := hsm.norm
  have hmul : ∀ {m n : ℕ}, m.Coprime n →
      LSeries.term c s (m * n) = LSeries.term c s m * LSeries.term c s n := by
    intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · have : n = 1 := by simpa using hmn
      subst this; simp
    rcases eq_or_ne n 0 with rfl | hn
    · have : m = 1 := by simpa using hmn
      subst this; simp
    rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
      LSeries.term_of_ne_zero (mul_ne_zero hm hn), hrec.1 m n hmn, Nat.cast_mul,
      natCast_mul_natCast_cpow, div_mul_div_comm]
  have h1 : LSeries.term c s 1 = 1 := by simp [hc1]
  have := EulerProduct.eulerProduct_hasProd h1 hmul hnorm (LSeries.term_zero c s)
  have e : LSeries c s = ∑' n, LSeries.term c s n := rfl
  rw [e]
  convert this using 1
  funext p
  exact (local_factor N k c hc1 hrec s p p.prop
    (hnorm.of_norm.comp_injective (Nat.pow_right_injective p.prop.one_lt))).symm

/-- Helper: the local coefficients $a_0 = 1$, $a_1 = c(p)$, $a_{e+2} = c(p)a_{e+1} - \beta a_e$ with
$\beta = 0$ if $p \mid N$ and $\beta = p^{2k-1}$ otherwise. -/
noncomputable def locSeq (N k : ℕ) (c : ℕ → ℂ) (p : ℕ) : ℕ → ℂ
  | 0 => 1
  | 1 => c p
  | e + 2 => c p * locSeq N k c p (e + 1) -
      (if p ∣ N then 0 else (p : ℂ) ^ (2 * k - 1)) * locSeq N k c p e

/-- Helper: the multiplicative sequence built from the local coefficients (value $0$ at $0$). -/
noncomputable def multSeq (N k : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else n.factorization.prod fun p e => locSeq N k c p e

/-- The multiplicative sequence takes the value $1$ at $n = 1$. -/
lemma multSeq_one (N k : ℕ) (c : ℕ → ℂ) : multSeq N k c 1 = 1 := by simp [multSeq]

/-- At a prime power $p^e$ the multiplicative sequence equals the local coefficient $a_e$. -/
lemma multSeq_primePow (N k : ℕ) (c : ℕ → ℂ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    multSeq N k c (p ^ e) = locSeq N k c p e := by
  simp only [multSeq, pow_eq_zero_iff', hp.ne_zero, false_and, ite_false, hp.factorization_pow]
  exact Finsupp.prod_single_index (by simp [locSeq])

/-- The multiplicative sequence is multiplicative on coprime arguments. -/
lemma multSeq_mul (N k : ℕ) (c : ℕ → ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    multSeq N k c (m * n) = multSeq N k c m * multSeq N k c n := by
  rcases eq_or_ne m 0 with rfl | hm
  · have : n = 1 := by simpa using hmn
    subst this; simp [multSeq]
  rcases eq_or_ne n 0 with rfl | hn
  · have : m = 1 := by simpa using hmn
    subst this; simp [multSeq]
  simp only [multSeq, hm, hn, mul_ne_zero hm hn, ite_false]
  rw [Nat.factorization_mul_of_coprime hmn, Finsupp.prod_add_index_of_disjoint]
  exact hmn.disjoint_primeFactors

/-- If $p \mid N$ then the local coefficients are the powers $a_e = c(p)^e$. -/
lemma locSeq_dvd (N k : ℕ) (c : ℕ → ℂ) (p : ℕ) (hN : p ∣ N) (e : ℕ) :
    locSeq N k c p e = c p ^ e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    match e, ih with
    | 0, _ => simp [locSeq]
    | 1, _ => simp [locSeq]
    | e + 2, ih => simp only [locSeq, hN, ite_true, zero_mul, sub_zero]; rw [ih (e + 1) (by omega)]; ring

/-- At a prime $p$ the multiplicative sequence equals $c(p)$. -/
lemma multSeq_prime (N k : ℕ) (c : ℕ → ℂ) (p : ℕ) (hp : p.Prime) : multSeq N k c p = c p := by
  simpa [locSeq] using multSeq_primePow N k c p hp 1

/-- The multiplicative sequence satisfies the Hecke recurrence of level $N$ and weight $2k$. -/
lemma multSeq_rec (N k : ℕ) (c : ℕ → ℂ) : HeckeRecurrence N k (multSeq N k c) := by
  refine ⟨fun m n h => multSeq_mul N k c h, ?_, ?_⟩
  · intro p r hp hN hr
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [multSeq_prime N k c p hp, multSeq_primePow N k c p hp, multSeq_primePow N k c p hp,
      multSeq_primePow N k c p hp]
    simp only [Nat.add_sub_cancel, locSeq, hN, ite_false]
    ring
  · intro p r hp hN hr
    rw [multSeq_prime N k c p hp, multSeq_primePow N k c p hp, locSeq_dvd N k c p hN]

/-- Helper: crude exponential bound for the local coefficients. -/
lemma locSeq_bound (N k : ℕ) (c : ℕ → ℂ) (p : ℕ) (R : ℝ) (hR : 0 ≤ R) (hc : ‖c p‖ ≤ R)
    (hβ : (p : ℝ) ^ (2 * k - 1) ≤ R ^ 2) :
    ∀ e, ‖locSeq N k c p e‖ ≤ (2 * R) ^ e := by
  have hb : ‖(if p ∣ N then 0 else (p : ℂ) ^ (2 * k - 1))‖ ≤ R ^ 2 := by
    split_ifs
    · simpa using sq_nonneg R
    · simpa using hβ
  have key : ∀ e, ‖locSeq N k c p e‖ ≤ (2 * R) ^ e ∧ ‖locSeq N k c p (e + 1)‖ ≤ (2 * R) ^ (e + 1) := by
    intro e
    induction e with
    | zero => exact ⟨by simp [locSeq], by simpa [locSeq] using hc.trans (by linarith)⟩
    | succ e ih =>
      refine ⟨ih.2, ?_⟩
      have h2 : locSeq N k c p (e + 2) = c p * locSeq N k c p (e + 1) -
          (if p ∣ N then 0 else (p : ℂ) ^ (2 * k - 1)) * locSeq N k c p e := rfl
      rw [h2]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have a1 : ‖c p‖ * ‖locSeq N k c p (e + 1)‖ ≤ R * (2 * R) ^ (e + 1) :=
        mul_le_mul hc ih.2 (norm_nonneg _) hR
      have a2 : ‖(if p ∣ N then 0 else (p : ℂ) ^ (2 * k - 1))‖ * ‖locSeq N k c p e‖
          ≤ R ^ 2 * (2 * R) ^ e := mul_le_mul hb ih.1 (norm_nonneg _) (sq_nonneg R)
      have a3 : 0 ≤ R ^ 2 * (2 * R) ^ e := by positivity
      calc _ ≤ R * (2 * R) ^ (e + 1) + R ^ 2 * (2 * R) ^ e := add_le_add a1 a2
        _ = 3 * (R ^ 2 * (2 * R) ^ e) := by ring
        _ ≤ 4 * (R ^ 2 * (2 * R) ^ e) := by linarith
        _ = (2 * R) ^ (e + 1 + 1) := by ring
  exact fun e => (key e).1

/-- Helper: polynomial growth of the constructed multiplicative sequence. -/
lemma multSeq_bound (N k : ℕ) (c : ℕ → ℂ) (C A : ℝ) (hb : ∀ n : ℕ, ‖c n‖ ≤ C * (n : ℝ) ^ A) :
    ∃ B : ℝ, ∀ n : ℕ, ‖multSeq N k c n‖ ≤ 1 * (n : ℝ) ^ B := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 1)
  set A' : ℝ := max A k with hA'
  set m : ℕ := ⌈2 * (C + 1)⌉₊ with hm
  refine ⟨(m : ℝ) + A', fun n => ?_⟩
  -- the bound at a prime power
  have hprime : ∀ p : ℕ, p.Prime → ∀ e, ‖locSeq N k c p e‖ ≤ (((p : ℝ) ^ ((m : ℝ) + A')) ^ e) := by
    intro p hp e
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    set R : ℝ := ‖c p‖ + (p : ℝ) ^ k with hR
    have hR0 : 0 ≤ R := by positivity
    have hcR : ‖c p‖ ≤ R := le_add_of_nonneg_right (by positivity)
    have hβ : (p : ℝ) ^ (2 * k - 1) ≤ R ^ 2 := by
      calc (p : ℝ) ^ (2 * k - 1) ≤ (p : ℝ) ^ (2 * k) := pow_le_pow_right₀ hp1 (by omega)
        _ = ((p : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
        _ ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) (le_add_of_nonneg_left (norm_nonneg _)) 2
    refine (locSeq_bound N k c p R hR0 hcR hβ e).trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ e
    have h1 : ‖c p‖ ≤ C * (p : ℝ) ^ A' :=
      (hb p).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 (le_max_left _ _)) hC)
    have h2 : (p : ℝ) ^ k ≤ (p : ℝ) ^ A' := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hp1 (le_max_right _ _)
    have h3 : 2 * (C + 1) ≤ (p : ℝ) ^ m := by
      calc 2 * (C + 1) ≤ (m : ℝ) := Nat.le_ceil _
        _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_two_pow_self).le
        _ = (2 : ℝ) ^ m := by push_cast; ring
        _ ≤ (p : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) hp2 m
    have h4 : (p : ℝ) ^ ((m : ℝ) + A') = (p : ℝ) ^ m * (p : ℝ) ^ A' := by
      rw [Real.rpow_add hp0, Real.rpow_natCast]
    rw [h4]
    have h5 : 0 ≤ (p : ℝ) ^ A' := by positivity
    nlinarith
  rcases eq_or_ne n 0 with rfl | hn
  · simp [multSeq]
    exact Real.rpow_nonneg (by norm_num) _
  simp only [multSeq, hn, ite_false, Finsupp.prod, one_mul]
  rw [norm_prod]
  calc ∏ p ∈ n.factorization.support, ‖locSeq N k c p (n.factorization p)‖
      ≤ ∏ p ∈ n.factorization.support, (((p : ℝ) ^ ((m : ℝ) + A')) ^ n.factorization p) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p hp =>
          hprime p (Nat.prime_of_mem_primeFactors (by simpa using hp)) _)
    _ = ∏ p ∈ n.factorization.support, (((p : ℝ) ^ n.factorization p) ^ ((m : ℝ) + A')) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), ← Real.rpow_natCast_mul (Nat.cast_nonneg _),
          mul_comm]
    _ = (∏ p ∈ n.factorization.support, ((p : ℝ) ^ n.factorization p)) ^ ((m : ℝ) + A') := by
        rw [Real.finsetProd_rpow]
        intro p _; positivity
    _ = (n : ℝ) ^ ((m : ℝ) + A') := by
        congr 1
        have := Nat.prod_factorization_pow_eq_self hn
        unfold Finsupp.prod at this
        exact_mod_cast this

/-- **Proposition 4.5** (pdf p. 206): for $c(1) = 1$ and $c$ of polynomial growth, the Dirichlet series
$L(s) = \sum c(n)n^{-s}$ is (on a right half-plane) the Euler product
$\prod_{p \mid N}(1 - c(p)p^{-s})^{-1}\prod_{p \nmid N}(1 - c(p)p^{-s} + p^{2k-1-2s})^{-1}$ if and only if the
conditions $(*)$ hold. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.5, pdf p. 206"]
theorem prop_4_5 (N k : ℕ) (hk : 1 ≤ k) (c : ℕ → ℂ) (hc1 : c 1 = 1)
    (hgrowth : ∃ C A : ℝ, ∀ n : ℕ, ‖c n‖ ≤ C * (n : ℝ) ^ A) :
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → HasProd (fun p : Nat.Primes ↦ eulerFactor N k c p s) (LSeries c s)) ↔
      HeckeRecurrence N k c := by
  obtain ⟨C, A, hb⟩ := hgrowth
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨B, hB⟩ := multSeq_bound N k c C A hb
    have hbp : ∀ p : ℕ, p.Prime → multSeq N k c p = c p := fun p hp => multSeq_prime N k c p hp
    have heq : ∀ s : ℂ, max σ (B + 1) < s.re → LSeries (multSeq N k c) s = LSeries c s := by
      intro s hs
      have h1 := euler_of_rec N k (multSeq N k c) (multSeq_one N k c) (multSeq_rec N k c) 1 B hB s
        (lt_of_le_of_lt (le_max_right _ _) hs)
      have h2 := hσ s (lt_of_le_of_lt (le_max_left _ _) hs)
      have e : (fun p : Nat.Primes ↦ eulerFactor N k (multSeq N k c) p s) =
          fun p : Nat.Primes ↦ eulerFactor N k c p s := by
        funext p
        simp [eulerFactor, hbp p p.prop]
      rw [e] at h1
      exact h1.unique h2
    have hac : LSeries.abscissaOfAbsConv c < ⊤ :=
      lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow ⟨C, fun n _ => hb n⟩)
        (EReal.coe_lt_top _)
    have hab : LSeries.abscissaOfAbsConv (multSeq N k c) < ⊤ :=
      lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
        ⟨1, fun n _ => hB n⟩) (EReal.coe_lt_top _)
    have hev : (fun x : ℝ ↦ LSeries c x) =ᶠ[atTop] fun x ↦ LSeries (multSeq N k c) x := by
      filter_upwards [eventually_gt_atTop (max σ (B + 1))] with x hx
      exact (heq x (by simpa using hx)).symm
    have hcb : ∀ n : ℕ, n ≠ 0 → c n = multSeq N k c n :=
      fun n hn => LSeries.eq_of_LSeries_eventually_eq hac hab hev hn
    have hR := multSeq_rec N k c
    refine ⟨?_, ?_, ?_⟩
    · intro m n hmn
      rcases eq_or_ne m 0 with rfl | hm
      · have : n = 1 := by simpa using hmn
        subst this; simp [hc1]
      rcases eq_or_ne n 0 with rfl | hn
      · have : m = 1 := by simpa using hmn
        subst this; simp [hc1]
      rw [hcb _ (mul_ne_zero hm hn), hcb m hm, hcb n hn]
      exact hR.1 m n hmn
    · intro p r hp hN hr
      have := hR.2.1 p r hp hN hr
      rwa [← hcb p hp.ne_zero, ← hcb _ (pow_ne_zero _ hp.ne_zero),
        ← hcb _ (pow_ne_zero _ hp.ne_zero), ← hcb _ (pow_ne_zero _ hp.ne_zero)] at this
    · intro p r hp hN hr
      have := hR.2.2 p r hp hN hr
      rwa [← hcb p hp.ne_zero, ← hcb _ (pow_ne_zero _ hp.ne_zero)] at this
  · intro hrec
    exact ⟨A + 1, fun s hs => euler_of_rec N k c hc1 hrec C A hb s hs⟩

/-- Helper: the conditions $(*)$ determine $c(p^r)$ from $c(1)$ and $c(p)$. -/
lemma heckeRecurrence_primePow_eq (N k : ℕ) {c c' : ℕ → ℂ} (h : HeckeRecurrence N k c)
    (h' : HeckeRecurrence N k c') (hc1 : c 1 = 1) (hc1' : c' 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → c p = c' p) (p : ℕ) (hpp : p.Prime) :
    ∀ r : ℕ, c (p ^ r) = c' (p ^ r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [hc1, hc1']
    | 1, _ => simpa using hp p hpp
    | r + 2, ih =>
      by_cases hN : p ∣ N
      · rw [h.2.2 p (r + 2) hpp hN (by omega), h'.2.2 p (r + 2) hpp hN (by omega), hp p hpp]
      · have e1 := h.2.1 p (r + 1) hpp hN (by omega)
        have e2 := h'.2.1 p (r + 1) hpp hN (by omega)
        simp only [Nat.add_sub_cancel] at e1 e2
        have a := ih (r + 1) (by omega)
        have b := ih r (by omega)
        have : c (p ^ (r + 1 + 1)) = c' (p ^ (r + 1 + 1)) := by
          rw [hp p hpp, a, b] at e1
          linear_combination e2 - e1
        simpa using this

/-- **Remark 4.6** (pdf p. 207): with the normalisation $c(1) = 1$, the conditions $(*)$ determine all $c(n)$ from
the $c(p)$, $p$ prime. -/
@[kb "milne2006ec" "Ch. V, Remark 4.6, pdf p. 207"]
theorem remark_4_6 (N k : ℕ) {c c' : ℕ → ℂ} (h : HeckeRecurrence N k c) (h' : HeckeRecurrence N k c')
    (hc1 : c 1 = 1) (hc1' : c' 1 = 1) (hp : ∀ p : ℕ, p.Prime → c p = c' p) : ∀ n : ℕ, 1 ≤ n → c n = c' n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p r hpp _ => intro _; exact heckeRecurrence_primePow_eq N k h h' hc1 hc1' hp p hpp r
  | zero => intro h0; omega
  | one => intro _; rw [hc1, hc1']
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [h.1 a b hab, h'.1 a b hab, iha (by omega), ihb (by omega)]

end NumberFieldKB.MilneEC.V
