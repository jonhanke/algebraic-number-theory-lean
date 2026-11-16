import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter IV §8: failure of the Hasse (local-global) principle

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 8, pdf pp. 151–154.
Locators give the pdf page of the text `ectext6` (printed page = pdf page − 8).

Propositions 8.1 and 8.2 (the $2$-Selmer group and the Tate–Shafarevich group of $Y^2Z = X^3 + pXZ^2$) need the
Selmer and Tate–Shafarevich groups of an elliptic curve over $\mathbb Q$, which belong to Chapter IV §§2–3;
they are not stated in this file.

## Proved
* `remark_8_3_sum_two_squares`: an odd prime is a sum of two squares if and only if $p \equiv 1 \bmod 4$.
* `remark_8_3_examples`: $17, 41, 97, 193$ are $\equiv 1 \bmod 8$, are sums of two squares $A^2 + B^2$ with
  $8 \nmid AB$, and $2$ is not a fourth power modulo each of them.
* `remark_8_4_no_rational_point`: for $p \equiv 1 \bmod 8$ such that $2$ is not a fourth power modulo $p$, the curve
  $Y^2 = 2 - 2pX^4$ has no rational point (affine, and none at infinity on the desingularization since $-2p$ is not a
  square), and it has real points.
* `theorem_8_5`: quadratic reciprocity and the supplementary law for $2$ in Milne's form (Mathlib's
  `legendreSym.quadratic_reciprocity` and `legendreSym.at_two`).
* `gaussQuarticCriterion_holds`: Gauss's criterion `GaussQuarticCriterion` (Remark 8.3; Silverman 1986, X.6.6): for
  $p \equiv 1 \bmod 8$, $p = A^2 + B^2$, $2$ is a fourth power modulo $p$ if and only if $8 \mid AB$.

## Named statements
* `Remark8_4Local` (Remark 8.4, pdf p. 154): the curve $C : Y^2 = 2 - 2pX^4$ has a point over every $\mathbb Q_q$.
-/

namespace NumberFieldKB.MilneEC

/-- **Remark 8.3, first part** (pdf p. 152): the odd primes $p$ that can be written $p = A^2 + B^2$ with
$A, B \in \mathbb Z$ are exactly those with $p \equiv 1 \bmod 4$ (Mathlib's `Nat.Prime.sq_add_sq` for one direction). -/
@[kb "milne2006ec" "Ch. IV, Remark 8.3, pdf p. 152"]
theorem remark_8_3_sum_two_squares (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (∃ A B : ℤ, (p : ℤ) = A ^ 2 + B ^ 2) ↔ p % 4 = 1 := by
  have hp2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left hodd
  constructor
  · rintro ⟨A, B, h⟩
    have hsq : ∀ x : ℤ, x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
      intro x
      have : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
      rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
    have h1 := hsq A
    have h2 := hsq B
    omega
  · intro h
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
    exact ⟨a, b, by exact_mod_cast hab.symm⟩

/-- **Gauss's criterion** (named statement; Milne, Remark 8.3, pdf p. 152, citing Silverman 1986, X.6.6): for a prime
$p \equiv 1 \bmod 8$ written $p = A^2 + B^2$, $2$ is a fourth power modulo $p$ if and only if $8 \mid AB$. -/
@[kb "milne2006ec" "Ch. IV, Remark 8.3, pdf p. 152 (input)"]
structure GaussQuarticCriterion : Prop where
  iff : ∀ (p : ℕ) [Fact p.Prime] (A B : ℤ), p % 8 = 1 → (p : ℤ) = A ^ 2 + B ^ 2 →
    ((∃ x : ZMod p, x ^ 4 = 2) ↔ (8 : ℤ) ∣ A * B)

/-- In a sum of two squares $p = a^2 + b^2$ with $p$ prime, $a$ and $b$ are coprime. -/
theorem gauss_coprime (p a b : ℕ) (hpp : p.Prime) (h : p = a ^ 2 + b ^ 2) :
    Nat.Coprime a b := by
  by_contra hc
  set d := Nat.gcd a b with hd
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  have hdp : d ∣ p := by
    rw [h]; exact dvd_add (dvd_pow hda two_ne_zero) (dvd_pow hdb two_ne_zero)
  have hd2 : d ^ 2 ∣ p := by
    rw [h]; exact dvd_add (pow_dvd_pow_of_dvd hda 2) (pow_dvd_pow_of_dvd hdb 2)
  rcases (Nat.dvd_prime hpp).1 hdp with h1 | h1
  · exact hc h1
  · rw [h1] at hd2
    have := Nat.le_of_dvd hpp.pos hd2
    have := hpp.two_le
    nlinarith

/-- For $p = a^2 + b^2$ prime with $p \equiv 1 \bmod 4$, $a$ odd, $b$ even: $(a/p) = 1$ and
$((a+b)/p) = (2/(a+b))$, by reciprocity for the Jacobi symbol and $p \equiv 2b^2 \bmod (a+b)$. -/
theorem gauss_legendre (p a b : ℕ) [Fact p.Prime] (h : p = a ^ 2 + b ^ 2)
    (hao : a % 2 = 1) (hbe : b % 2 = 0) (hp4 : p % 4 = 1) :
    legendreSym p (a : ℤ) = 1 ∧ legendreSym p ((a + b : ℕ) : ℤ) = ZMod.χ₈ ((a + b : ℕ) : ZMod 8) := by
  have hcop := gauss_coprime p a b Fact.out h
  constructor
  · rw [jacobiSym.legendreSym.to_jacobiSym,
      jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.2 hao) hp4]
    have : ((p : ℤ)) % (a : ℕ) = ((b : ℤ) ^ 2) % (a : ℕ) := by
      rw [show (p : ℤ) = (b : ℤ) ^ 2 + a * a by rw [h]; push_cast; ring]
      simp
    rw [jacobiSym.mod_left' this]
    apply jacobiSym.sq_one'
    show Nat.gcd b a = 1
    exact hcop.symm
  · rw [jacobiSym.legendreSym.to_jacobiSym,
      jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.2 (by omega)) hp4]
    have : ((p : ℤ)) % ((a + b : ℕ) : ℤ) = (2 * (b : ℤ) ^ 2) % ((a + b : ℕ) : ℤ) := by
      refine Int.emod_eq_emod_iff_emod_sub_eq_zero.2 ?_
      apply Int.emod_eq_zero_of_dvd
      exact ⟨(a : ℤ) - b, by rw [h]; push_cast; ring⟩
    rw [jacobiSym.mod_left' this, jacobiSym.mul_left, jacobiSym.at_two (Nat.odd_iff.2 (by omega))]
    have : jacobiSym ((b : ℤ) ^ 2) (a + b) = 1 := by
      apply jacobiSym.sq_one'
      show Nat.gcd b (a + b) = 1
      rw [Nat.gcd_add_self_right]
      exact hcop.symm
    rw [this, mul_one]

/-- Residues modulo $16$: for $a$ odd, $b$ even, $a^2 + b^2 \equiv 1 \bmod 8$, the sign pattern
($p \bmod 16$ together with $(a+b) \bmod 8$) that makes $2^{(p-1)/4} = 1$ occurs exactly when $8 \mid b$. -/
theorem gauss_arith (a b : ℕ) (hao : a % 2 = 1) (hbe : b % 2 = 0) (h8 : (a ^ 2 + b ^ 2) % 8 = 1) :
    (((a ^ 2 + b ^ 2) % 16 = 1 ∧ ((a + b) % 8 = 1 ∨ (a + b) % 8 = 7)) ∨
      ((a ^ 2 + b ^ 2) % 16 = 9 ∧ ((a + b) % 8 = 3 ∨ (a + b) % 8 = 5))) ↔ b % 8 = 0 := by
  have e : (a ^ 2 + b ^ 2) % 16 = ((a % 16) ^ 2 + (b % 16) ^ 2) % 16 := by
    simp [Nat.add_mod, Nat.pow_mod]
  have ha : a % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb : b % 16 < 16 := Nat.mod_lt _ (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r, r = a % 16 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = b % 16 := ⟨_, rfl⟩
  rw [← hr, ← hs] at e
  rw [← hr] at ha
  rw [← hs] at hb
  interval_cases r <;> interval_cases s <;> omega

/-- Core of the elementary proof: for $p = a^2 + b^2 \equiv 1 \bmod 8$ with $a$ odd and $b$ even,
$2^{(p-1)/4} = 1$ in $\mathbb Z/p$ if and only if $8 \mid b$.  Uses $2 \cdot ab \equiv (a+b)^2$, $b^2 \equiv -a^2$,
so $2^{(p-1)/4} = (-1)^{(p-1)/8} ((a+b)/p)$, and the Jacobi symbol computation of `gauss_legendre`. -/
theorem gauss_core (p a b : ℕ) [Fact p.Prime] (h : p = a ^ 2 + b ^ 2)
    (hao : a % 2 = 1) (hbe : b % 2 = 0) (hp8 : p % 8 = 1) :
    (2 : ZMod p) ^ ((p - 1) / 4) = 1 ↔ b % 8 = 0 := by
  have hp4 : p % 4 = 1 := by omega
  obtain ⟨hL1, hL2⟩ := gauss_legendre p a b h hao hbe hp4
  have hab : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    have h' : ((a ^ 2 + b ^ 2 : ℕ) : ZMod p) = 0 := by
      rw [← h]; exact ZMod.natCast_self p
    push_cast at h'
    exact h'
  have hb2 : (b : ZMod p) ^ 2 = -(a : ZMod p) ^ 2 := by linear_combination hab
  have hq : (p - 1) / 4 = 2 * ((p - 1) / 8) := by omega
  have hq2 : p / 2 = 2 * ((p - 1) / 4) := by omega
  set m := (p - 1) / 8 with hm
  set q := (p - 1) / 4 with hqdef
  have hLa : (a : ZMod p) ^ (p / 2) = 1 := by
    have := legendreSym.eq_pow p (a : ℤ)
    rw [hL1] at this
    simpa using this.symm
  have hLab : ((a + b : ℕ) : ZMod p) ^ (p / 2) = (ZMod.χ₈ ((a + b : ℕ) : ZMod 8) : ZMod p) := by
    have := legendreSym.eq_pow p ((a + b : ℕ) : ℤ)
    rw [hL2] at this
    simpa using this.symm
  have hbq : (b : ZMod p) ^ q = (-1) ^ m * (a : ZMod p) ^ q := by
    rw [hq, pow_mul, hb2, neg_pow, ← pow_mul]
  have h2ab : (2 : ZMod p) * ((a : ZMod p) * b) = ((a : ZMod p) + b) ^ 2 := by
    linear_combination (-1 : ZMod p) * hab
  have habq : ((a : ZMod p) * b) ^ q = (-1) ^ m := by
    rw [mul_pow, hbq, ← mul_assoc, mul_comm ((a : ZMod p) ^ q), mul_assoc, ← pow_add, ← two_mul, ← hq2, hLa]
    ring
  have hmain : (2 : ZMod p) ^ q * (-1) ^ m = (ZMod.χ₈ ((a + b : ℕ) : ZMod 8) : ZMod p) := by
    rw [← habq, ← mul_pow, h2ab, ← pow_mul, ← hq2]
    rw [← hLab, Nat.cast_add]
  have hsq : ((-1 : ZMod p) ^ m) * (-1) ^ m = 1 := by
    rw [← mul_pow]; simp
  have h2q : (2 : ZMod p) ^ q = (ZMod.χ₈ ((a + b : ℕ) : ZMod 8) : ZMod p) * (-1) ^ m := by
    calc (2 : ZMod p) ^ q = (2 : ZMod p) ^ q * (((-1 : ZMod p) ^ m) * (-1) ^ m) := by rw [hsq, mul_one]
      _ = ((2 : ZMod p) ^ q * (-1) ^ m) * (-1) ^ m := by ring
      _ = _ := by rw [hmain]
  have hint : (2 : ZMod p) ^ q =
      (((ZMod.χ₈ ((a + b : ℕ) : ZMod 8)) * (-1) ^ m : ℤ) : ZMod p) := by
    rw [h2q]; push_cast; ring
  have h8 : (a ^ 2 + b ^ 2) % 8 = 1 := by rw [← h]; exact hp8
  have hodd : (a + b) % 2 = 1 := by omega
  have hχ : ZMod.χ₈ ((a + b : ℕ) : ZMod 8) =
      if (a + b) % 8 = 1 ∨ (a + b) % 8 = 7 then 1 else -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]
  rw [← gauss_arith a b hao hbe h8, hint, hχ]
  have : Fact (2 < p) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  have hne : ((-1 : ℤ) : ZMod p) ≠ 1 := by simpa using (ZMod.neg_one_ne_one (n := p))
  have hp16 : p % 16 = 1 ∨ p % 16 = 9 := by omega
  have hmpar : (p % 16 = 1 → (-1 : ℤ) ^ m = 1) ∧ (p % 16 = 9 → (-1 : ℤ) ^ m = -1) := by
    constructor
    · intro h16
      exact Even.neg_one_pow ⟨m / 2, by omega⟩
    · intro h16
      exact Odd.neg_one_pow ⟨m / 2, by omega⟩
  rw [← h]
  rcases hp16 with h16 | h16
  · rw [hmpar.1 h16]
    by_cases hc : (a + b) % 8 = 1 ∨ (a + b) % 8 = 7
    · rw [if_pos hc]
      exact iff_of_true (by simp) (Or.inl ⟨h16, hc⟩)
    · rw [if_neg hc]
      exact iff_of_false (by simpa using hne) (by omega)
  · rw [hmpar.2 h16]
    by_cases hc : (a + b) % 8 = 1 ∨ (a + b) % 8 = 7
    · rw [if_pos hc]
      exact iff_of_false (by simpa using hne) (by omega)
    · rw [if_neg hc]
      exact iff_of_true (by simp) (Or.inr ⟨h16, by omega⟩)

/-- For $p \equiv 1 \bmod 8$, $2$ is a fourth power modulo $p$ if and only if $2^{(p-1)/4} = 1$
(the unit group is cyclic of order $p - 1$, divisible by $4$). -/
theorem gauss_fourth_pow_iff (p : ℕ) [Fact p.Prime] (hp : p % 8 = 1) :
    (∃ x : ZMod p, x ^ 4 = 2) ↔ (2 : ZMod p) ^ ((p - 1) / 4) = 1 := by
  have hp2 : p ≠ 2 := by omega
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this
    exact hp2 this
  constructor
  · rintro ⟨x, hx⟩
    by_cases hx0 : x = 0
    · exact absurd (by rw [← hx, hx0]; norm_num) h20
    · rw [← hx, ← pow_mul, show 4 * ((p - 1) / 4) = p - 1 by omega]
      exact ZMod.pow_card_sub_one_eq_one hx0
  · intro h1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    set u : (ZMod p)ˣ := Units.mk0 2 h20 with hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg u)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    have hu1 : u ^ ((p - 1) / 4) = 1 := by
      apply Units.ext; simpa [hu] using h1
    rw [← hk, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord] at hu1
    obtain ⟨c, hc⟩ := hu1
    have hq : 0 < (p - 1) / 4 := by have := (Fact.out : p.Prime).two_le; omega
    have h4k : (4 : ℤ) ∣ k := by
      have hpq : ((p - 1 : ℕ) : ℤ) = 4 * (((p - 1) / 4 : ℕ) : ℤ) := by omega
      rw [hpq] at hc
      have : (((p - 1) / 4 : ℕ) : ℤ) * k = (((p - 1) / 4 : ℕ) : ℤ) * (4 * c) := by linarith
      have := mul_left_cancel₀ (by exact_mod_cast hq.ne') this
      exact ⟨c, this⟩
    obtain ⟨j, hj⟩ := h4k
    refine ⟨((g ^ j : (ZMod p)ˣ) : ZMod p), ?_⟩
    have : (g ^ j) ^ 4 = u := by rw [← hk, hj, ← zpow_natCast, ← zpow_mul]; ring_nf
    have := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) this
    simpa [hu] using this

/-- Natural-number form of Gauss's criterion: for $p = x^2 + y^2 \equiv 1 \bmod 8$ with $x$ odd and $y$ even,
$2$ is a fourth power modulo $p$ if and only if $8 \mid xy$. -/
theorem gauss_nat (p x y : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) (h : p = x ^ 2 + y ^ 2)
    (hx : x % 2 = 1) (hy : y % 2 = 0) : (∃ z : ZMod p, z ^ 4 = 2) ↔ 8 ∣ x * y := by
  rw [gauss_fourth_pow_iff p hp8, gauss_core p x y h hx hy hp8]
  have hcop : Nat.Coprime 8 x := by
    have : Nat.Coprime (2 ^ 3) x :=
      Nat.Coprime.pow_left 3 (Nat.prime_two.coprime_iff_not_dvd.2 (by omega))
    simpa using this
  rw [Nat.Coprime.dvd_mul_left hcop]
  omega

/-- **Gauss's criterion is true** (proof: elementary; write $p = a^2 + b^2$ with $a$ odd, $b$ even, so that
$2 ab \equiv (a+b)^2$ and $b^2 \equiv -a^2$ modulo $p$.  Then $2^{(p-1)/4} = (-1)^{(p-1)/8} ((a+b)/p)$, where
$(a/p) = 1$ and $((a+b)/p) = (2/(a+b))$ by Jacobi reciprocity since $p \equiv 2b^2 \bmod (a+b)$; a residue
computation modulo $16$ shows this equals $1$ exactly when $8 \mid b$; finally $2$ is a fourth power
if and only if $2^{(p-1)/4} = 1$ since the unit group is cyclic of order $p - 1$). -/
@[kb "milne2006ec" "Ch. IV, Remark 8.3, pdf p. 152"]
theorem gaussQuarticCriterion_holds : GaussQuarticCriterion := by
  refine ⟨fun p _ A B hp8 hAB => ?_⟩
  have h : p = A.natAbs ^ 2 + B.natAbs ^ 2 := by
    have : ((p : ℕ) : ℤ) = ((A.natAbs ^ 2 + B.natAbs ^ 2 : ℕ) : ℤ) := by
      rw [hAB]; push_cast; simp [sq_abs]
    exact_mod_cast this
  have hd : (8 : ℤ) ∣ A * B ↔ 8 ∣ A.natAbs * B.natAbs := by
    rw [← Int.natAbs_mul]
    exact_mod_cast Int.natCast_dvd (m := 8) (n := A * B)
  rw [hd]
  have hpar : (A.natAbs ^ 2 + B.natAbs ^ 2) % 2 = 1 := by omega
  have hx := Nat.mod_two_eq_zero_or_one A.natAbs
  have hy := Nat.mod_two_eq_zero_or_one B.natAbs
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · simp [Nat.add_mod, Nat.pow_mod, hx, hy] at hpar
  · rw [mul_comm]
    exact (gauss_nat p _ _ hp8 (by rw [h]; ring) hy hx).trans (by rw [mul_comm])
  · exact gauss_nat p _ _ hp8 h hx hy
  · simp [Nat.add_mod, Nat.pow_mod, hx, hy] at hpar

/-- If $2^{(p-1)/4} \ne 1$ in $\mathbb Z/p$ (with $4 \mid p - 1$ and $2 \ne 0$), then $2$ is not a fourth power
modulo $p$ (a fourth power $x^4 = 2$ would give $2^{(p-1)/4} = x^{p-1} = 1$). -/
theorem not_fourth_pow_of_pow_ne_one (p : ℕ) [Fact p.Prime] (h4 : (p - 1) % 4 = 0) (h20 : (2 : ZMod p) ≠ 0)
    (h : (2 : ZMod p) ^ ((p - 1) / 4) ≠ 1) : ∀ x : ZMod p, x ^ 4 ≠ 2 := by
  intro x hx
  by_cases hx0 : x = 0
  · apply h20
    rw [← hx, hx0]; norm_num
  · apply h
    rw [← hx, ← pow_mul, show 4 * ((p - 1) / 4) = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one hx0

/-- **Remark 8.3, examples** (pdf p. 152): $17 = 1^2 + 4^2$, $41 = 5^2 + 4^2$, $97 = 9^2 + 4^2$, $193 = 7^2 + 12^2$ are
primes $\equiv 1 \bmod 8$ with $8 \nmid AB$, and $2$ is not a fourth power modulo any of them (checked directly). -/
@[kb "milne2006ec" "Ch. IV, Remark 8.3, pdf p. 152"]
theorem remark_8_3_examples :
    (17 % 8 = 1 ∧ 17 = 1 ^ 2 + 4 ^ 2 ∧ ¬ 8 ∣ 1 * 4 ∧ ∀ x : ZMod 17, x ^ 4 ≠ 2) ∧
    (41 % 8 = 1 ∧ 41 = 5 ^ 2 + 4 ^ 2 ∧ ¬ 8 ∣ 5 * 4 ∧ ∀ x : ZMod 41, x ^ 4 ≠ 2) ∧
    (97 % 8 = 1 ∧ 97 = 9 ^ 2 + 4 ^ 2 ∧ ¬ 8 ∣ 9 * 4 ∧ ∀ x : ZMod 97, x ^ 4 ≠ 2) ∧
    (193 % 8 = 1 ∧ 193 = 7 ^ 2 + 12 ^ 2 ∧ ¬ 8 ∣ 7 * 12 ∧ ∀ x : ZMod 193, x ^ 4 ≠ 2) := by
  have a17 : (2 : ZMod 17) ≠ 0 := by decide
  have b17 : (2 : ZMod 17) ^ ((17 - 1) / 4) ≠ 1 := by decide
  have a41 : (2 : ZMod 41) ≠ 0 := by decide
  have b41 : (2 : ZMod 41) ^ ((41 - 1) / 4) ≠ 1 := by decide
  have a97 : (2 : ZMod 97) ≠ 0 := by decide
  have b97 : (2 : ZMod 97) ^ ((97 - 1) / 4) ≠ 1 := by decide
  have a193 : (2 : ZMod 193) ≠ 0 := by decide
  have b193 : (2 : ZMod 193) ^ ((193 - 1) / 4) ≠ 1 := by decide
  have f17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have f41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have f97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  have f193 : Fact (Nat.Prime 193) := ⟨by norm_num⟩
  exact ⟨⟨by norm_num, by norm_num, by norm_num, not_fourth_pow_of_pow_ne_one 17 (by norm_num) a17 b17⟩,
    ⟨by norm_num, by norm_num, by norm_num, not_fourth_pow_of_pow_ne_one 41 (by norm_num) a41 b41⟩,
    ⟨by norm_num, by norm_num, by norm_num, not_fourth_pow_of_pow_ne_one 97 (by norm_num) a97 b97⟩,
    ⟨by norm_num, by norm_num, by norm_num, not_fourth_pow_of_pow_ne_one 193 (by norm_num) a193 b193⟩⟩

/-- **Theorem 8.5, quadratic reciprocity law** (pdf p. 153): for distinct odd primes $p, q$,
$\left(\frac pq\right)\left(\frac qp\right) = (-1)^{\frac{p-1}2 \frac{q-1}2}$, and
$\left(\frac 2p\right) = (-1)^{(p^2-1)/8}$.  (Mathlib: `legendreSym.quadratic_reciprocity`, `legendreSym.at_two`.) -/
@[kb "milne2006ec" "Ch. IV, Theorem 8.5, pdf p. 153"]
theorem theorem_8_5 (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) :
    (p ≠ q → legendreSym q p * legendreSym p q = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))) ∧
    legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  have hp2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hp
  have hq2 : q % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hq
  refine ⟨fun hpq => ?_, ?_⟩
  · rw [legendreSym.quadratic_reciprocity hp hq hpq]
    have e1 : (p - 1) / 2 = p / 2 := by omega
    have e2 : (q - 1) / 2 = q / 2 := by omega
    rw [e1, e2]
  · rw [legendreSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight]
    have key : ∀ k r c : ℕ, p = 8 * k + r → (r ^ 2 = 8 * c + 1) →
        (p ^ 2 - 1) / 8 = 8 * k ^ 2 + 2 * k * r + c := by
      intro k r c hk hc
      have : p ^ 2 - 1 = 8 * (8 * k ^ 2 + 2 * k * r + c) := by
        apply Nat.sub_eq_of_eq_add
        subst hk
        nlinarith
      rw [this]; omega
    have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases h8 with h | h | h | h
    · rw [key (p/8) 1 0 (by omega) (by norm_num)]
      have : Even (8 * (p / 8) ^ 2 + 2 * (p / 8) * 1 + 0) := by
        exact ⟨4 * (p / 8) ^ 2 + (p / 8), by ring⟩
      rw [this.neg_one_pow]; simp [h, hp2]
    · rw [key (p/8) 3 1 (by omega) (by norm_num)]
      have : Odd (8 * (p / 8) ^ 2 + 2 * (p / 8) * 3 + 1) :=
        ⟨4 * (p / 8) ^ 2 + 3 * (p / 8), by ring⟩
      rw [this.neg_one_pow]; simp [h, hp2]
    · rw [key (p/8) 5 3 (by omega) (by norm_num)]
      have : Odd (8 * (p / 8) ^ 2 + 2 * (p / 8) * 5 + 3) :=
        ⟨4 * (p / 8) ^ 2 + 5 * (p / 8) + 1, by ring⟩
      rw [this.neg_one_pow]; simp [h, hp2]
    · rw [key (p/8) 7 6 (by omega) (by norm_num)]
      have : Even (8 * (p / 8) ^ 2 + 2 * (p / 8) * 7 + 6) :=
        ⟨4 * (p / 8) ^ 2 + 7 * (p / 8) + 3, by ring⟩
      rw [this.neg_one_pow]; simp [h, hp2]

/-- Core of Milne's argument (Remark 8.4, pdf p. 154): if $p \equiv 1 \bmod 8$ and integers $r, t, s$ with $r, t$
coprime satisfy $2 s^2 = t^4 - p r^4$, then $2$ is a fourth power modulo $p$.  The odd part $s'$ of $s$ has Jacobi
symbol $(p / s') = 1$ (because $p r^4 \equiv t^4$ modulo $s'$), so by reciprocity $s'$ is a square modulo $p$; so are $2$
and $-1$, hence so is $s$, and $2 = (t^2 / s)^2$ is a fourth power. -/
theorem hasse_core (p : ℕ) [hpf : Fact p.Prime] (h8 : p % 8 = 1) (r t s : ℤ) (hcop : IsCoprime r t)
    (h : 2 * s ^ 2 = t ^ 4 - p * r ^ 4) : ∃ x : ZMod p, x ^ 4 = 2 := by
  have hp : p.Prime := hpf.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro hd
    have h1 : p ∣ 2 := by exact_mod_cast hd
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 := hp.two_le
    omega
  have hpt : ¬ (p : ℤ) ∣ t := by
    intro hd
    have h1 : (p : ℤ) ∣ 2 * s ^ 2 := by
      rw [h]; exact dvd_sub (dvd_pow hd (by norm_num)) (dvd_mul_right _ _)
    have h2 : (p : ℤ) ∣ s := by
      rcases hpZ.dvd_or_dvd h1 with h | h
      · exact absurd h hp2
      · exact hpZ.dvd_of_dvd_pow h
    obtain ⟨a, ha⟩ := h2
    obtain ⟨b, hb⟩ := hd
    have h3 : (p : ℤ) * r ^ 4 = (p : ℤ) * ((p : ℤ) * ((p : ℤ) ^ 2 * b ^ 4 - 2 * a ^ 2)) := by
      rw [ha, hb] at h
      linear_combination h
    have h4 : r ^ 4 = (p : ℤ) * ((p : ℤ) ^ 2 * b ^ 4 - 2 * a ^ 2) :=
      mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero) h3
    have h5 : (p : ℤ) ∣ r := hpZ.dvd_of_dvd_pow (⟨_, h4⟩ : (p : ℤ) ∣ r ^ 4)
    exact hpZ.not_isUnit (hcop.isUnit_of_dvd' h5 ⟨b, hb⟩)
  have hps : ¬ (p : ℤ) ∣ s := by
    intro hd
    apply hpt
    have h1 : (p : ℤ) ∣ t ^ 4 := by
      have e : t ^ 4 = 2 * s ^ 2 + p * r ^ 4 := by linarith
      rw [e]
      exact dvd_add (Dvd.dvd.mul_left (dvd_pow hd (by norm_num)) _) (dvd_mul_right _ _)
    exact hpZ.dvd_of_dvd_pow h1
  have hrs : IsCoprime r s := by
    have h1 : IsCoprime r (2 * s ^ 2 + r * (p * r ^ 3)) := by
      have e : 2 * s ^ 2 + r * (p * r ^ 3) = t ^ 4 := by linear_combination h
      rw [e]; exact hcop.pow_right
    have h2 : IsCoprime r (2 * s ^ 2) := IsCoprime.add_mul_left_right_iff.mp h1
    exact (IsCoprime.pow_right_iff (by norm_num)).mp (IsCoprime.of_mul_right_right h2)
  have htp : IsCoprime t (p : ℤ) :=
    ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hpt).symm
  have hts : IsCoprime t s := by
    have h1 : IsCoprime t ((p : ℤ) * r ^ 4) := htp.mul_right hcop.symm.pow_right
    have e : (p : ℤ) * r ^ 4 = -(2 * s ^ 2) + t * t ^ 3 := by linear_combination h
    rw [e] at h1
    have h2 : IsCoprime t (-(2 * s ^ 2)) := IsCoprime.add_mul_left_right_iff.mp h1
    have h3 : IsCoprime t (2 * s ^ 2) := IsCoprime.neg_right_iff _ _ |>.mp h2
    exact (IsCoprime.pow_right_iff (by norm_num)).mp (IsCoprime.of_mul_right_right h3)
  have hs0 : s ≠ 0 := by
    intro h0; apply hps; rw [h0]; exact dvd_zero _
  have hn0 : s.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hs0
  obtain ⟨a, s', hodd, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hs'dvd : (s' : ℤ) ∣ s := by
    rw [Int.natCast_dvd, hn]; exact dvd_mul_left _ _
  obtain ⟨c, hc⟩ := hs'dvd
  have hrs' : IsCoprime r (s' : ℤ) := by
    rw [hc] at hrs; exact hrs.of_mul_right_left
  have hts' : IsCoprime t (s' : ℤ) := by
    rw [hc] at hts; exact hts.of_mul_right_left
  have hs'dvd : (s' : ℤ) ∣ s := ⟨c, hc⟩
  have hJ : jacobiSym (p : ℤ) s' = 1 := by
    have hdiv : (s' : ℤ) ∣ t ^ 4 - p * r ^ 4 := by
      rw [← h]; exact Dvd.dvd.mul_left (dvd_pow hs'dvd two_ne_zero) 2
    have e1 : (p : ℤ) * r ^ 4 % s' = t ^ 4 % s' := (Int.modEq_iff_dvd.mpr hdiv)
    have e2 : jacobiSym ((p : ℤ) * r ^ 4) s' = jacobiSym (t ^ 4) s' := jacobiSym.mod_left' e1
    rw [jacobiSym.mul_left] at e2
    have e3 : jacobiSym (r ^ 4) s' = 1 := by
      rw [show r ^ 4 = (r ^ 2) ^ 2 by ring]
      exact jacobiSym.sq_one' (Int.isCoprime_iff_gcd_eq_one.mp hrs'.pow_left)
    have e4 : jacobiSym (t ^ 4) s' = 1 := by
      rw [show t ^ 4 = (t ^ 2) ^ 2 by ring]
      exact jacobiSym.sq_one' (Int.isCoprime_iff_gcd_eq_one.mp hts'.pow_left)
    rw [e3, e4] at e2
    simpa using e2
  have hp4 : p % 4 = 1 := by omega
  have hJ2 : jacobiSym (s' : ℤ) p = 1 := by
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four hp4 hodd]; exact hJ
  have hL : legendreSym p (s' : ℤ) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hJ2
  have hs'0 : ((s' : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    exact hps (h0.trans hs'dvd)
  have hsq' : IsSquare ((s' : ℤ) : ZMod p) := (legendreSym.eq_one_iff p hs'0).mp hL
  have h2sq : IsSquare (2 : ZMod p) :=
    (ZMod.exists_sq_eq_two_iff (by omega)).mpr (Or.inl h8)
  have hm1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have hN : IsSquare (((s.natAbs : ℤ)) : ZMod p) := by
    rw [hn]; push_cast
    have : IsSquare ((s' : ℤ) : ZMod p) := hsq'
    push_cast at this
    exact (h2sq.pow a).mul this
  have hssq : IsSquare ((s : ℤ) : ZMod p) := by
    rcases Int.natAbs_eq s with h' | h'
    · rw [h']; exact hN
    · rw [h']; push_cast
      have := hm1.mul hN
      push_cast at this
      simpa using this
  obtain ⟨v, hv⟩ := hssq
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 : ((s : ℤ) : ZMod p) = 0 := by rw [hv, h0, mul_zero]
    exact hps ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1)
  have hmod : (2 : ZMod p) * ((s : ℤ) : ZMod p) ^ 2 = ((t : ℤ) : ZMod p) ^ 4 := by
    have := congrArg (Int.cast : ℤ → ZMod p) h
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this
  refine ⟨((t : ℤ) : ZMod p) / v, ?_⟩
  rw [div_pow, div_eq_iff (pow_ne_zero 4 hv0)]
  rw [hv] at hmod
  linear_combination -hmod

/-- **Remark 8.4** (pdf pp. 153–154): let $p \equiv 1 \bmod 8$ be a prime such that $2$ is not a fourth power modulo
$p$.  The curve $C : Y^2 = 2 - 2pX^4$ has no point with coordinates in $\mathbb Q$: no affine rational point, and no
rational point at infinity on its desingularization (the two points over $(0 : 1 : 0)$ are rational only if $-2p$ is
a square).  It has real points. -/
@[kb "milne2006ec" "Ch. IV, Remark 8.4, pdf p. 154"]
theorem remark_8_4_no_rational_point (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 1) (h2 : ∀ x : ZMod p, x ^ 4 ≠ 2) :
    (∀ x y : ℚ, y ^ 2 ≠ 2 - 2 * p * x ^ 4) ∧ ¬ IsSquare (-2 * p : ℚ) ∧
    ∃ x y : ℝ, y ^ 2 = 2 - 2 * p * x ^ 4 := by
  have hp : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    have hx : x * (x.den : ℚ) = x.num := Rat.mul_den_eq_num x
    have hN : ((2 * (x.den : ℤ) ^ 4 - 2 * p * x.num ^ 4 : ℤ) : ℚ) = (y * (x.den : ℚ) ^ 2) ^ 2 := by
      push_cast
      rw [← hx]
      have e : (y * (x.den : ℚ) ^ 2) ^ 2 = y ^ 2 * (x.den : ℚ) ^ 4 := by ring
      rw [e, hxy]; ring
    have hsq : IsSquare (2 * (x.den : ℤ) ^ 4 - 2 * p * x.num ^ 4) := by
      rw [← Rat.isSquare_intCast_iff, hN]; exact ⟨y * (x.den : ℚ) ^ 2, sq _⟩
    obtain ⟨m, hm⟩ := hsq
    have hev : Even (m * m) := ⟨(x.den : ℤ) ^ 4 - p * x.num ^ 4, by linarith⟩
    have hmeven : Even m := (Int.even_mul.mp hev).elim id id
    obtain ⟨s, hs⟩ := hmeven
    have key : 2 * s ^ 2 = (x.den : ℤ) ^ 4 - p * x.num ^ 4 := by
      subst hs; linarith
    have hcop : IsCoprime x.num (x.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using x.reduced
    obtain ⟨z, hz⟩ := hasse_core p h8 x.num x.den s hcop key
    exact h2 z hz
  · rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]
  · exact ⟨0, Real.sqrt 2, by simp⟩

/-- **Remark 8.4, local points** (named statement; pdf p. 154): for $p$ as in `remark_8_4_no_rational_point`, the
curve $C : Y^2 = 2 - 2pX^4$ (its desingularization) has a point over $\mathbb Q_q$ for every prime $q$: an affine point,
or a point at infinity, which exists exactly when $-2p$ is a square in $\mathbb Q_q$.  (Milne: Hensel's lemma and
Corollary 9.3 for $q \neq 2, p$; the cases $q = 2, p$ "left to the reader".)  So $C$ violates the Hasse principle. -/
@[kb "milne2006ec" "Ch. IV, Remark 8.4, pdf p. 154 (input)"]
structure Remark8_4Local : Prop where
  local_point : ∀ (p : ℕ) [Fact p.Prime], p % 8 = 1 → (∀ x : ZMod p, x ^ 4 ≠ 2) →
    ∀ (q : ℕ) [Fact q.Prime],
      (∃ x y : ℚ_[q], y ^ 2 = 2 - 2 * p * x ^ 4) ∨ IsSquare (-2 * p : ℚ_[q])

end NumberFieldKB.MilneEC
