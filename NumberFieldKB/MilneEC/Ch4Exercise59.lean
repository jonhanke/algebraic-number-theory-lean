import NumberFieldKB.MilneEC.Ch4TwoDescent
import NumberFieldKB.MilneEC.Ch4Exercises
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Milne, Elliptic Curves, Chapter IV, Exercise 5.9: the ranks of $Y^2 = X^3 - 4X$ and $Y^2 = X^3 - p^2X$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Exercise 5.9 (pdf p. 139).  This
file proves the two named statements `Exercise5_9_1` and `Exercise5_9_2` of `Ch4Exercises.lean`.

**Method** (the 2-descent of Proposition 5.6, with Remark 3.7).  Let $E : Y^2 = (X + q)X(X - q)$, with $q = 2$ or
$q = p$ an odd prime, and let $T$ be a set of $k$ rational 2-torsion points such that every $P \in E(\mathbb Q)$ has
$\varphi_\alpha(P + t) = 1$ for some $t \in T$ (`card_quot_two_le_split`).  If $D$ is a finite set containing all the
values $\varphi_\beta(Q)$ with $\varphi_\alpha(Q) = 1$, then $P \mapsto (t, \varphi_\beta(P + t))$ separates the cosets
of $2E(\mathbb Q)$ (kernel of $(\varphi_\alpha, \varphi_\beta)$, Remark 3.7), so $\#E(\mathbb Q)/2E(\mathbb Q) \le k\,\#D$.
Together with $\#E(\mathbb Q)/2E(\mathbb Q) \ge 2^{r+2}$ this bounds the rank $r$.

The set $D$ is found by classifying $x$ for a point $(x, y)$ with $\varphi_\alpha = 1$: $x + q = u^2$, and by the
valuation statement of Remark 3.7 the class of $x$ is that of $d \in \{\pm 1, \pm 2, \pm p, \pm 2p\}$.  Writing
$u = n/c$ in lowest terms, $d(n^2 - q c^2)$ and $d(n^2 - 2 q c^2)$ are integral squares (`Sys`), and elementary
congruences (modulo $8$, or modulo $p$ using that $-1$ is a nonresidue for $p \equiv 3 \pmod 4$ and $2$ a nonresidue for
$p \equiv 3, 5 \pmod 8$) rule out the unwanted $d$ (`excl_even`, `excl_p_three`, `excl_neg_one_three`, `excl_neg_p`,
`excl_p_five`, `excl_two_neg_one`, `excl_two_neg_two`).
-/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace NumberFieldKB.MilneEC

namespace Exercise59


/-! ### Integral exclusion lemmas -/

/-- Residues of squares of integers modulo `8`, together with the parity of the integer. -/
theorem sq_facts (n : ℤ) :
    (n % 2 = 0 ∧ n ^ 2 % 4 = 0 ∧ (n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 4)) ∨ (n % 2 = 1 ∧ n ^ 2 % 8 = 1) := by
  have h : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨
      n % 8 = 7 := by omega
  have key : n ^ 2 % 8 = (n % 8) * (n % 8) % 8 := by rw [pow_two, Int.mul_emod]
  rcases h with h | h | h | h | h | h | h | h <;> rw [h] at key <;> omega

/-- Exclusion for the curve `Y² = X³ - 4X`, `d = -1`. -/
theorem excl_two_neg_one (n c V W : ℤ) (hcop : ¬ (2 ∣ n ∧ 2 ∣ c))
    (hV : V ^ 2 = -1 * (n ^ 2 - 2 * c ^ 2)) (hW : W ^ 2 = -1 * (n ^ 2 - 2 * 2 * c ^ 2)) : False := by
  have h1 := sq_facts n
  have h2 := sq_facts c
  have h3 := sq_facts V
  have h4 := sq_facts W
  omega

/-- Exclusion for the curve `Y² = X³ - 4X`, `d = -2`. -/
theorem excl_two_neg_two (n c V W : ℤ) (hcop : ¬ (2 ∣ n ∧ 2 ∣ c))
    (hV : V ^ 2 = -2 * (n ^ 2 - 2 * c ^ 2)) (hW : W ^ 2 = -2 * (n ^ 2 - 2 * 2 * c ^ 2)) : False := by
  have h3 := sq_facts V
  have hV2 : V % 2 = 0 := by
    have := sq_facts n; have := sq_facts c; omega
  obtain ⟨V1, rfl⟩ : ∃ V1, V = 2 * V1 := ⟨V / 2, by omega⟩
  have e1 : 2 * V1 ^ 2 = -n ^ 2 + 2 * c ^ 2 := by nlinarith
  have hn : n % 2 = 0 := by
    have := sq_facts n; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hc : c % 2 = 1 := by omega
  have e2 : V1 ^ 2 = c ^ 2 - 2 * m ^ 2 := by nlinarith
  have hW2 : W % 2 = 0 := by
    have := sq_facts W; have := sq_facts c; have := sq_facts m; omega
  obtain ⟨W1, rfl⟩ : ∃ W1, W = 2 * W1 := ⟨W / 2, by omega⟩
  have e3 : W1 ^ 2 = 2 * (c ^ 2 - m ^ 2) := by nlinarith
  have hW1 : W1 % 2 = 0 := by
    have := sq_facts W1; have := sq_facts c; have := sq_facts m; omega
  have := sq_facts V1; have := sq_facts c; have := sq_facts m; have := sq_facts W1
  omega


/-- Exclusion of `d = ±2, ±2p` (a `2`-adic argument), `p` odd. -/
theorem excl_even (p e n c V W : ℤ) (hp : p % 2 = 1) (he : e % 2 = 1) (hcop : ¬ (2 ∣ n ∧ 2 ∣ c))
    (hV : V ^ 2 = 2 * e * (n ^ 2 - p * c ^ 2)) (hW : W ^ 2 = 2 * e * (n ^ 2 - 2 * p * c ^ 2)) :
    False := by
  have hm1 := Int.mul_emod e (n ^ 2 - p * c ^ 2) 2
  have hm2 := Int.mul_emod p (c ^ 2) 2
  have hm3 := Int.mul_emod e (n ^ 2 - 2 * p * c ^ 2) 2
  have hm4 := Int.mul_emod (2 * p) (c ^ 2) 2
  rw [he] at hm1 hm3
  rw [hp] at hm2
  have hV2 : V % 2 = 0 := by
    have := sq_facts V
    have h' : V ^ 2 = 2 * (e * (n ^ 2 - p * c ^ 2)) := by rw [hV]; ring
    omega
  obtain ⟨V1, rfl⟩ : ∃ V1, V = 2 * V1 := ⟨V / 2, by omega⟩
  have e1 : e * (n ^ 2 - p * c ^ 2) = 2 * V1 ^ 2 := by nlinarith
  have hn := sq_facts n
  have hc := sq_facts c
  have hM : (n ^ 2 - p * c ^ 2) % 2 = 0 := by omega
  have hnn : n % 2 = 1 ∧ c % 2 = 1 := by omega
  have hN : e * (n ^ 2 - 2 * p * c ^ 2) % 2 = 1 := by
    have : (n ^ 2 - 2 * p * c ^ 2) % 2 = 1 := by
      have : (2 * p * c ^ 2) % 2 = 0 := by rw [mul_assoc]; exact Int.mul_emod_right 2 _
      omega
    omega
  have hW2 : W % 2 = 0 := by
    have := sq_facts W
    have h' : W ^ 2 = 2 * (e * (n ^ 2 - 2 * p * c ^ 2)) := by rw [hW]; ring
    omega
  obtain ⟨W1, rfl⟩ : ∃ W1, W = 2 * W1 := ⟨W / 2, by omega⟩
  have e2 : e * (n ^ 2 - 2 * p * c ^ 2) = 2 * W1 ^ 2 := by nlinarith
  omega


/-- If `p ≡ 3 (mod 4)` divides `A² + B²` then it divides both `A` and `B`. -/
theorem dvd_of_dvd_sq_add_sq {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {A B : ℤ}
    (h : (p : ℤ) ∣ A ^ 2 + B ^ 2) : (p : ℤ) ∣ A ∧ (p : ℤ) ∣ B := by
  have := Fact.mk hp
  have hz : ((A : ZMod p)) ^ 2 + (B : ZMod p) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
    push_cast at this
    exact this
  have hB : (B : ZMod p) = 0 := by
    by_contra hB
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hB (x := (A : ZMod p)) (by linear_combination hz) h3
  have hA : (A : ZMod p) = 0 := by
    rw [hB] at hz
    simpa using hz
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hA, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hB⟩

/-- `2` is a nonresidue modulo `p ≡ 3, 5 (mod 8)`. -/
theorem not_dvd_sq_sub_two_mul_sq {p : ℕ} (hp : p.Prime) (h : p % 8 = 3 ∨ p % 8 = 5) {W c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) (hW : (p : ℤ) ∣ W ^ 2 - 2 * c ^ 2) : False := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hz : ((W : ZMod p)) ^ 2 = 2 * (c : ZMod p) ^ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hW
    push_cast at this
    linear_combination this
  have hc0 : (c : ZMod p) ≠ 0 := fun h0 => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0)
  have hsq : IsSquare (2 : ZMod p) := ⟨(W : ZMod p) / c, by field_simp; linear_combination -hz⟩
  have := (ZMod.exists_sq_eq_two_iff hp2).1 hsq
  omega

/-- Exclusion of `d = p` for `p ≡ 3 (mod 4)`. -/
theorem excl_p_three {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (n c V : ℤ)
    (hcop : ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ c)) (hV : V ^ 2 = p * (n ^ 2 - p * c ^ 2)) : False := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hp0 : (p : ℤ) ≠ 0 := hpp.ne_zero
  obtain ⟨V1, rfl⟩ : (p : ℤ) ∣ V := hpp.dvd_of_dvd_pow (n := 2) ⟨_, hV⟩
  have e1 : (p : ℤ) * V1 ^ 2 = n ^ 2 - p * c ^ 2 :=
    mul_left_cancel₀ hp0 (by linear_combination hV)
  obtain ⟨n1, rfl⟩ : (p : ℤ) ∣ n := hpp.dvd_of_dvd_pow (n := 2) ⟨V1 ^ 2 + c ^ 2, by linarith⟩
  have e2 : p * (V1 ^ 2 + c ^ 2) = p * (p * n1 ^ 2) := by linear_combination e1
  have e3 : V1 ^ 2 + c ^ 2 = p * n1 ^ 2 := mul_left_cancel₀ hp0 e2
  have := (dvd_of_dvd_sq_add_sq hp h3 (A := V1) (B := c) ⟨n1 ^ 2, e3⟩).2
  exact hcop ⟨dvd_mul_right _ _, this⟩

/-- Exclusion of `d = -1` for `p ≡ 3 (mod 4)`. -/
theorem excl_neg_one_three {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (n c V : ℤ)
    (hcop : ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ c)) (hV : V ^ 2 = -1 * (n ^ 2 - p * c ^ 2)) : False := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hp0 : (p : ℤ) ≠ 0 := hpp.ne_zero
  obtain ⟨hn, hV'⟩ := dvd_of_dvd_sq_add_sq hp h3 (A := n) (B := V) ⟨c ^ 2, by linear_combination hV⟩
  obtain ⟨n1, rfl⟩ := hn
  obtain ⟨V1, rfl⟩ := hV'
  have e1 : p * (p * (n1 ^ 2 + V1 ^ 2)) = p * c ^ 2 := by linear_combination hV
  have e2 : p * (n1 ^ 2 + V1 ^ 2) = c ^ 2 := mul_left_cancel₀ hp0 e1
  have : (p : ℤ) ∣ c := hpp.dvd_of_dvd_pow (n := 2) ⟨_, e2.symm⟩
  exact hcop ⟨dvd_mul_right _ _, this⟩

/-- Exclusion of `d = -p` for `p ≡ 3, 5 (mod 8)`. -/
theorem excl_neg_p {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3 ∨ p % 8 = 5) (n c V W : ℤ)
    (hcop : ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ c)) (hV : V ^ 2 = -(p : ℤ) * (n ^ 2 - p * c ^ 2))
    (hW : W ^ 2 = -(p : ℤ) * (n ^ 2 - 2 * p * c ^ 2)) : False := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hp0 : (p : ℤ) ≠ 0 := hpp.ne_zero
  obtain ⟨V1, rfl⟩ : (p : ℤ) ∣ V := hpp.dvd_of_dvd_pow (n := 2) ⟨-(n ^ 2 - p * c ^ 2), by rw [hV]; ring⟩
  have e1 : (p : ℤ) * V1 ^ 2 = -(n ^ 2 - p * c ^ 2) :=
    mul_left_cancel₀ hp0 (by linear_combination hV)
  obtain ⟨n1, rfl⟩ : (p : ℤ) ∣ n := hpp.dvd_of_dvd_pow (n := 2) ⟨c ^ 2 - V1 ^ 2, by linarith⟩
  have hW' : W ^ 2 = p * (p * (2 * c ^ 2 - p * n1 ^ 2)) := by rw [hW]; ring
  obtain ⟨W1, rfl⟩ : (p : ℤ) ∣ W := hpp.dvd_of_dvd_pow (n := 2) ⟨_, hW'⟩
  have e2 : (p : ℤ) * (p * W1 ^ 2) = p * (p * (2 * c ^ 2 - p * n1 ^ 2)) := by
    rw [← hW']; ring
  have e3 : W1 ^ 2 = 2 * c ^ 2 - p * n1 ^ 2 := by
    have := mul_left_cancel₀ hp0 (mul_left_cancel₀ hp0 e2)
    exact this
  have hc : ¬ (p : ℤ) ∣ c := fun h => hcop ⟨dvd_mul_right _ _, h⟩
  exact not_dvd_sq_sub_two_mul_sq hp h8 (W := W1) hc ⟨-n1 ^ 2, by linear_combination e3⟩

/-- Exclusion of `d = p` for `p ≡ 5 (mod 8)`. -/
theorem excl_p_five {p : ℕ} (hp : p.Prime) (h5 : p % 8 = 5) (n c V W : ℤ)
    (hcop : ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ c)) (hcop2 : ¬ (2 ∣ n ∧ 2 ∣ c))
    (hV : V ^ 2 = (p : ℤ) * (n ^ 2 - p * c ^ 2)) (hW : W ^ 2 = (p : ℤ) * (n ^ 2 - 2 * p * c ^ 2)) :
    False := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hp0 : (p : ℤ) ≠ 0 := hpp.ne_zero
  obtain ⟨V1, rfl⟩ : (p : ℤ) ∣ V := hpp.dvd_of_dvd_pow (n := 2) ⟨_, hV⟩
  have e1 : (p : ℤ) * V1 ^ 2 = n ^ 2 - p * c ^ 2 :=
    mul_left_cancel₀ hp0 (by linear_combination hV)
  obtain ⟨n1, rfl⟩ : (p : ℤ) ∣ n := hpp.dvd_of_dvd_pow (n := 2) ⟨V1 ^ 2 + c ^ 2, by linarith⟩
  have e2 : V1 ^ 2 + c ^ 2 = p * n1 ^ 2 :=
    mul_left_cancel₀ hp0 (by linear_combination e1)
  have hW' : W ^ 2 = p * (p * (p * n1 ^ 2 - 2 * c ^ 2)) := by rw [hW]; ring
  obtain ⟨W1, rfl⟩ : (p : ℤ) ∣ W := hpp.dvd_of_dvd_pow (n := 2) ⟨_, hW'⟩
  have e3 : W1 ^ 2 = p * n1 ^ 2 - 2 * c ^ 2 := by
    have : (p : ℤ) * (p * W1 ^ 2) = p * (p * (p * n1 ^ 2 - 2 * c ^ 2)) := by rw [← hW']; ring
    exact mul_left_cancel₀ hp0 (mul_left_cancel₀ hp0 this)
  have hc3 : ¬ (2 ∣ n1 ∧ 2 ∣ c) := fun ⟨h1, h2⟩ => hcop2 ⟨Dvd.dvd.mul_left h1 _, h2⟩
  have hp8 : (p : ℤ) % 8 = 5 := by omega
  have hm := Int.mul_emod (p : ℤ) (n1 ^ 2) 8
  rw [hp8] at hm
  have := sq_facts V1
  have := sq_facts c
  have := sq_facts n1
  have := sq_facts W1
  omega


/-! ### Classes in $\mathbb Q^\times/\mathbb Q^{\times 2}$ -/

/-- The class of a rational in $\mathbb Q^\times/\mathbb Q^{\times 2}$ (the class of `0` is, by convention, `1`). -/
noncomputable def cls (q : ℚ) : RatModSquares :=
  if h : q = 0 then 1 else QuotientGroup.mk (Units.mk0 q h)

theorem descentMap_eq_cls {α β γ : ℤ} (r c : ℚ) (P : (cubicCurve α β γ).toAffine.Point) :
    descentMap r c P = cls (descentRep r c P) := rfl

theorem cls_one : cls 1 = 1 := by
  simp [cls]

theorem cls_mul {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : cls (a * b) = cls a * cls b := by
  simp only [cls, ha, hb, mul_ne_zero ha hb, ↓reduceDIte]
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Units.ext rfl

theorem cls_eq_one_iff {a : ℚ} (ha : a ≠ 0) : cls a = 1 ↔ IsSquare a := by
  simp only [cls, ha, ↓reduceDIte]
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨v, hv⟩
    have := congrArg Units.val hv
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0] at this
    exact ⟨v, by rw [← this, pow_two]⟩
  · rintro ⟨q, hq⟩
    have hq0 : q ≠ 0 := by rintro rfl; exact ha (by simpa using hq)
    exact ⟨Units.mk0 q hq0, Units.ext (by simp [hq, pow_two])⟩

theorem cls_eq_iff {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : cls a = cls b ↔ IsSquare (a * b) := by
  rw [← cls_eq_one_iff (mul_ne_zero ha hb), cls_mul ha hb]
  constructor
  · intro h
    rw [h]
    exact ratModSquares_mul_self _
  · intro h
    exact (eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right (ratModSquares_mul_self _))

/-! ### Valuations and the classification of the classes -/

theorem padicValRat_prime_ne {ℓ ℓ0 : ℕ} (hℓ : ℓ.Prime) (h0 : ℓ0.Prime) (hne : ℓ ≠ ℓ0) :
    padicValRat ℓ (ℓ0 : ℚ) = 0 := by
  have := Fact.mk hℓ
  have := Fact.mk h0
  rw [padicValRat.of_nat, padicValNat_primes hne]
  simp

/-- Multiplying by $\ell_0$ if necessary makes the $\ell_0$-adic valuation even and changes no other valuation. -/
theorem exists_adjust {ℓ0 : ℕ} (h0 : ℓ0.Prime) {r : ℚ} (hr : r ≠ 0) :
    ∃ e : ℕ, e ≤ 1 ∧ Even (padicValRat ℓ0 ((ℓ0 : ℚ) ^ e * r)) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ℓ0 → padicValRat ℓ ((ℓ0 : ℚ) ^ e * r) = padicValRat ℓ r := by
  have := Fact.mk h0
  have hℓ0 : (ℓ0 : ℚ) ≠ 0 := by exact_mod_cast h0.ne_zero
  by_cases hev : Even (padicValRat ℓ0 r)
  · exact ⟨0, by norm_num, by simpa using hev, fun ℓ _ _ => by simp⟩
  · refine ⟨1, le_rfl, ?_, fun ℓ hℓ hne => ?_⟩
    · rw [pow_one, padicValRat.mul hℓ0 hr, padicValRat.self h0.one_lt]
      rw [Int.not_even_iff_odd] at hev
      exact odd_one.add_odd hev
    · have := Fact.mk hℓ
      rw [pow_one, padicValRat.mul hℓ0 hr, padicValRat_prime_ne hℓ h0 hne, zero_add]

theorem exists_class_pos_two {x : ℚ} (hx : 0 < x)
    (hev : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → Even (padicValRat ℓ x)) :
    ∃ d : ℤ, (d = 1 ∨ d = 2) ∧ IsSquare ((d : ℚ) * x) := by
  obtain ⟨e, he, he2, he3⟩ := exists_adjust Nat.prime_two hx.ne'
  have hpos : 0 < ((2 : ℕ) : ℚ) ^ e * x := by positivity
  have hsq : IsSquare (((2 : ℕ) : ℚ) ^ e * x) := by
    rw [Rat.isSquare_iff_even_factorization]
    refine ⟨hpos.le, fun ℓ hℓ => ?_⟩
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2; exact he2
    · rw [he3 ℓ hℓ hℓ2]; exact hev ℓ hℓ hℓ2
  refine ⟨2 ^ e, ?_, ?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with rfl | rfl <;> simp
  · convert hsq using 1
    push_cast
    ring

theorem exists_class_pos_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : ℚ} (hx : 0 < x)
    (hev : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p → Even (padicValRat ℓ x)) :
    ∃ d : ℤ, (d = 1 ∨ d = 2 ∨ d = p ∨ d = 2 * p) ∧ IsSquare ((d : ℚ) * x) := by
  obtain ⟨e, he, he2, he3⟩ := exists_adjust Nat.prime_two hx.ne'
  have hx1 : ((2 : ℕ) : ℚ) ^ e * x ≠ 0 := by positivity
  obtain ⟨f, hf, hf2, hf3⟩ := exists_adjust hp hx1
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpos : 0 < (p : ℚ) ^ f * (((2 : ℕ) : ℚ) ^ e * x) := by positivity
  have hsq : IsSquare ((p : ℚ) ^ f * (((2 : ℕ) : ℚ) ^ e * x)) := by
    rw [Rat.isSquare_iff_even_factorization]
    refine ⟨hpos.le, fun ℓ hℓ => ?_⟩
    by_cases hℓp : ℓ = p
    · subst hℓp; exact hf2
    · rw [hf3 ℓ hℓ hℓp]
      by_cases hℓ2 : ℓ = 2
      · subst hℓ2; exact he2
      · rw [he3 ℓ hℓ hℓ2]; exact hev ℓ hℓ hℓ2 hℓp
  refine ⟨2 ^ e * p ^ f, ?_, ?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hf with rfl | rfl <;> simp
  · convert hsq using 1
    push_cast
    ring

theorem exists_class_two {x : ℚ} (hx : x ≠ 0)
    (hev : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → Even (padicValRat ℓ x)) :
    ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2) ∧ IsSquare ((d : ℚ) * x) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · obtain ⟨d, hd, hsq⟩ := exists_class_pos_two (neg_pos.2 hneg) (fun ℓ hℓ h2 => by
      have := Fact.mk hℓ
      rw [padicValRat.neg]; exact hev ℓ hℓ h2)
    refine ⟨-d, ?_, ?_⟩
    · rcases hd with rfl | rfl <;> simp
    · convert hsq using 1
      push_cast
      ring
  · obtain ⟨d, hd, hsq⟩ := exists_class_pos_two hpos hev
    exact ⟨d, by rcases hd with rfl | rfl <;> simp, hsq⟩

theorem exists_class_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : ℚ} (hx : x ≠ 0)
    (hev : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p → Even (padicValRat ℓ x)) :
    ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = p ∨ d = -(p : ℤ) ∨ d = 2 ∨ d = -2 ∨ d = 2 * p ∨ d = -(2 * (p : ℤ))) ∧
      IsSquare ((d : ℚ) * x) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · obtain ⟨d, hd, hsq⟩ := exists_class_pos_two_p hp hp2 (neg_pos.2 hneg) (fun ℓ hℓ h2 h3 => by
      have := Fact.mk hℓ
      rw [padicValRat.neg]; exact hev ℓ hℓ h2 h3)
    refine ⟨-d, ?_, ?_⟩
    · rcases hd with rfl | rfl | rfl | rfl <;> simp
    · convert hsq using 1
      push_cast
      ring
  · obtain ⟨d, hd, hsq⟩ := exists_class_pos_two_p hp hp2 hpos hev
    exact ⟨d, by rcases hd with rfl | rfl | rfl | rfl <;> simp, hsq⟩

theorem not_isSquare_of_odd_val {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (h : ¬ Even (padicValRat ℓ r)) :
    ¬ IsSquare r := fun hs => h ((Rat.isSquare_iff_even_factorization.1 hs).2 ℓ hℓ)

/-- `p` is not a square in `ℚ`. -/
theorem not_isSquare_prime {p : ℕ} (hp : p.Prime) : ¬ IsSquare (p : ℚ) := by
  refine not_isSquare_of_odd_val hp ?_
  have := Fact.mk hp
  rw [padicValRat.of_nat]
  simp

/-- `2 p` is not a square in `ℚ` for an odd prime `p`. -/
theorem not_isSquare_two_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsSquare (2 * (p : ℚ)) := by
  refine not_isSquare_of_odd_val Nat.prime_two ?_
  have := Fact.mk Nat.prime_two
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [padicValRat.mul (by norm_num) hp0, padicValRat_prime_ne Nat.prime_two hp (Ne.symm hp2)]
  have : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [this]
  decide

/-- `2 p²` is not a square in `ℚ` for an odd prime `p`. -/
theorem not_isSquare_two_mul_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsSquare (2 * (p : ℚ) ^ 2) := by
  refine not_isSquare_of_odd_val Nat.prime_two ?_
  have := Fact.mk Nat.prime_two
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [padicValRat.mul (by norm_num) (pow_ne_zero 2 hp0), padicValRat.pow (p : ℚ),
    padicValRat_prime_ne Nat.prime_two hp (Ne.symm hp2)]
  have : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [this]
  norm_num

/-! ### From a rational point to an integral system -/

/-- The integral system attached to a point with `x + q = u²`, `d x` and `d (x - q)` squares: `x + q = (n/c)²`
in lowest terms, `d (n² - q c²)` and `d (n² - 2 q c²)` squares. -/
def Sys (q d : ℤ) : Prop :=
  ∃ n c V W : ℤ, Int.gcd n c = 1 ∧ V ^ 2 = d * (n ^ 2 - q * c ^ 2) ∧ W ^ 2 = d * (n ^ 2 - 2 * q * c ^ 2)

theorem exists_sys {q d : ℤ} {x : ℚ} (hu : IsSquare (x + q)) (hdx : IsSquare ((d : ℚ) * x))
    (hdx2 : IsSquare ((d : ℚ) * (x - q))) : Sys q d := by
  obtain ⟨u, hu⟩ := hu
  obtain ⟨s, hs⟩ := hdx
  obtain ⟨t, ht⟩ := hdx2
  have hc : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have hn : (u.num : ℚ) = u * u.den := (Rat.mul_den_eq_num u).symm
  have hx : x = u * u - q := by linarith
  have e1 : (d : ℚ) * ((u.num : ℚ) ^ 2 - q * (u.den : ℚ) ^ 2) = (s * u.den) ^ 2 := by
    rw [hn]
    have : (d : ℚ) * ((u * u.den) ^ 2 - q * (u.den : ℚ) ^ 2) = (d * x) * (u.den : ℚ) ^ 2 := by
      rw [hx]; ring
    rw [this, hs]; ring
  have e2 : (d : ℚ) * ((u.num : ℚ) ^ 2 - 2 * q * (u.den : ℚ) ^ 2) = (t * u.den) ^ 2 := by
    rw [hn]
    have : (d : ℚ) * ((u * u.den) ^ 2 - 2 * q * (u.den : ℚ) ^ 2) = (d * (x - q)) * (u.den : ℚ) ^ 2 := by
      rw [hx]; ring
    rw [this, ht]; ring
  obtain ⟨V, hV⟩ := Rat.isSquare_intCast_iff.1
    (⟨s * u.den, by push_cast; rw [e1]; ring⟩ : IsSquare (((d * (u.num ^ 2 - q * (u.den : ℤ) ^ 2) : ℤ)) : ℚ))
  obtain ⟨W, hW⟩ := Rat.isSquare_intCast_iff.1
    (⟨t * u.den, by push_cast; rw [e2]; ring⟩ : IsSquare (((d * (u.num ^ 2 - 2 * q * (u.den : ℤ) ^ 2) : ℤ)) : ℚ))
  refine ⟨u.num, u.den, V, W, ?_, by rw [pow_two, ← hV], by rw [pow_two, ← hW]⟩
  rw [Int.gcd, Int.natAbs_natCast]
  exact u.reduced

theorem not_dvd_both {n c : ℤ} (h : Int.gcd n c = 1) {k : ℤ} (hk : ¬ k ∣ 1) : ¬ (k ∣ n ∧ k ∣ c) :=
  fun ⟨h1, h2⟩ => hk (by simpa [h] using Int.dvd_coe_gcd h1 h2)


/-! ### The curves $Y^2 = (X + p)X(X - p)$ -/

theorem hdist {p : ℕ} (hp : p.Prime) :
    (-(p : ℤ)) ≠ 0 ∧ (0 : ℤ) ≠ (p : ℤ) ∧ (p : ℤ) ≠ -(p : ℤ) := by
  have := hp.pos
  omega

theorem curve_eqn {p : ℕ} {x y : ℚ} (h : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Nonsingular x y) :
    y ^ 2 = (x + p) * x * (x - p) := by
  have := cubicCurve_equation_iff.1 h.1
  push_cast at this
  linear_combination this

theorem phiAlpha_some {p : ℕ} (x y : ℚ) (h : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Nonsingular x y)
    (hx : x ≠ -(p : ℚ)) : phiAlpha (-(p : ℤ)) 0 p (Point.some x y h) = cls (x + p) := by
  have hc : ¬ (x = ((-(p : ℤ) : ℤ) : ℚ)) := by push_cast; exact hx
  unfold phiAlpha
  rw [descentMap_eq_cls, descentRep_some]
  simp only [hc, ↓reduceIte]
  congr 1
  push_cast
  ring

theorem phiAlpha_root {p : ℕ} (x y : ℚ) (h : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Nonsingular x y)
    (hx : x = -(p : ℚ)) : phiAlpha (-(p : ℤ)) 0 p (Point.some x y h) = cls (2 * (p : ℚ) ^ 2) := by
  have hc : x = ((-(p : ℤ) : ℤ) : ℚ) := by push_cast; exact hx
  unfold phiAlpha
  rw [descentMap_eq_cls, descentRep_some]
  simp only [hc, ↓reduceIte]
  congr 1
  push_cast
  ring

theorem phiBeta_some {p : ℕ} (x y : ℚ) (h : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Nonsingular x y)
    (hx : x ≠ 0) : phiBeta (-(p : ℤ)) 0 p (Point.some x y h) = cls x := by
  have hc : ¬ (x = ((0 : ℤ) : ℚ)) := by push_cast; exact hx
  unfold phiBeta
  rw [descentMap_eq_cls, descentRep_some]
  simp only [hc, ↓reduceIte]
  congr 1
  push_cast
  ring

theorem not_dvd_disc {p : ℕ} (hp : p.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) (hpℓ : ℓ ≠ p) :
    ¬ (ℓ : ℤ) ∣ 2 * cubicDisc (-(p : ℤ)) 0 p := by
  have e : 2 * cubicDisc (-(p : ℤ)) 0 p = ((2 ^ 3 * p ^ 6 : ℕ) : ℤ) := by
    unfold cubicDisc
    push_cast
    ring
  rw [e, Int.natCast_dvd_natCast]
  intro h
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h))
  · exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow h))

theorem even_val_alpha_some {p : ℕ} (hp : p.Prime) (x y : ℚ)
    (h : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Nonsingular x y) (hx : x ≠ -(p : ℚ)) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) (hpℓ : ℓ ≠ p) : Even (padicValRat ℓ (x + p)) := by
  have hc : ¬ (x = ((-(p : ℤ) : ℤ) : ℚ)) := by push_cast; exact hx
  have := (remark_3_7.support (-(p : ℤ)) 0 p (hdist hp).1 (hdist hp).2.1 (hdist hp).2.2
    (Point.some x y h) ℓ hℓ (not_dvd_disc hp hℓ h2 hpℓ)).1
  rw [descentRep_some] at this
  simp only [hc, ↓reduceIte] at this
  convert this using 2
  push_cast
  ring

theorem even_val_beta_some {p : ℕ} (hp : p.Prime) (x y : ℚ)
    (h : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Nonsingular x y) (hx : x ≠ 0) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) (hpℓ : ℓ ≠ p) : Even (padicValRat ℓ x) := by
  have hc : ¬ (x = ((0 : ℤ) : ℚ)) := by push_cast; exact hx
  have := (remark_3_7.support (-(p : ℤ)) 0 p (hdist hp).1 (hdist hp).2.1 (hdist hp).2.2
    (Point.some x y h) ℓ hℓ (not_dvd_disc hp hℓ h2 hpℓ)).2
  rw [descentRep_some] at this
  simp only [hc, ↓reduceIte] at this
  convert this using 2
  push_cast
  ring

/-- The 2-torsion point $(x, 0)$ for $x \in \{-p, 0, p\}$. -/
noncomputable def rootPt (p : ℕ) (hp : p.Prime) (x : ℚ) (hx : x = -(p : ℚ) ∨ x = 0 ∨ x = p) :
    (cubicCurve (-(p : ℤ)) 0 p).toAffine.Point :=
  Point.some x 0 (cubicCurve_nonsingular_root (hdist hp).1 (hdist hp).2.1 (hdist hp).2.2 x
    (by push_cast; exact hx))

/-- The four 2-torsion points. -/
noncomputable def Tp (p : ℕ) (hp : p.Prime) : Fin 4 → (cubicCurve (-(p : ℤ)) 0 p).toAffine.Point :=
  ![0, rootPt p hp (-(p : ℚ)) (Or.inl rfl), rootPt p hp 0 (Or.inr (Or.inl rfl)),
    rootPt p hp p (Or.inr (Or.inr rfl))]

/-- If $P \mapsto (t, \varphi_\beta(P + t))$ takes values in a finite set, then
$\#E(\mathbb Q)/2E(\mathbb Q) \le k\,\#D$. -/
theorem card_quot_two_le_split {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) {k : ℕ}
    (T : Fin k → (cubicCurve α β γ).toAffine.Point) (D : Finset RatModSquares)
    (hF1 : ∀ P, ∃ i, phiAlpha α β γ (P + T i) = 1)
    (hF2 : ∀ Q, phiAlpha α β γ Q = 1 → phiBeta α β γ Q ∈ D) :
    Nat.card ((cubicCurve α β γ).toAffine.Point ⧸ multiples (cubicCurve α β γ).toAffine.Point 2) ≤
      k * D.card := by
  choose i hi using hF1
  let g : (cubicCurve α β γ).toAffine.Point → Fin k × D := fun P =>
    (i P, ⟨phiBeta α β γ (P + T (i P)), hF2 _ (hi P)⟩)
  have hg : ∀ P Q, g P = g Q → P - Q ∈ multiples (cubicCurve α β γ).toAffine.Point 2 := by
    intro P Q hPQ
    have h1 : i P = i Q := congrArg Prod.fst hPQ
    have h2' : phiBeta α β γ (P + T (i P)) = phiBeta α β γ (Q + T (i Q)) :=
      congrArg Subtype.val (congrArg Prod.snd hPQ)
    have hQ := hi Q
    rw [← h1] at h2' hQ
    have := sub_mem_multiples_of_phi_eq remark_3_7 hαβ hβγ hγα (P + T (i P)) (Q + T (i P))
      (by rw [hi P, hQ]) h2'
    simpa using this
  have h := card_quot_two_le g hg
  have hc : Nat.card (Fin k × D) = k * D.card := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simp
  exact h.trans hc.le

theorem point_sys (p : ℕ) (x y : ℚ)
    (h : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Nonsingular x y)
    (hx1 : x ≠ -(p : ℚ)) (hx2 : x ≠ 0)
    (hα : phiAlpha (-(p : ℤ)) 0 p (Point.some x y h) = 1) {d : ℤ} (hd : d ≠ 0)
    (hdx : IsSquare ((d : ℚ) * x)) : Sys (p : ℤ) d := by
  have hu0 : x + p ≠ 0 := fun h0 => hx1 (by linarith)
  rw [phiAlpha_some x y h hx1, cls_eq_one_iff hu0] at hα
  have hy := curve_eqn h
  obtain ⟨u, hu⟩ := hα
  obtain ⟨s, hs⟩ := hdx
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hu' : u ≠ 0 := by
    rintro rfl
    exact hu0 (by simpa using hu)
  have hs' : s ≠ 0 := by
    rintro rfl
    have : (d : ℚ) * x = 0 := by simpa using hs
    rcases mul_eq_zero.1 this with h | h
    · exact hd' h
    · exact hx2 h
  have hsq : IsSquare ((d : ℚ) * (x - p)) := by
    refine ⟨y * d / (u * s), ?_⟩
    have e : (y * d / (u * s)) * (y * d / (u * s)) = y ^ 2 * d ^ 2 / ((u * u) * (s * s)) := by
      field_simp
    rw [e, ← hu, ← hs, hy]
    field_simp
  exact exists_sys (q := (p : ℤ)) ⟨u, by push_cast; exact hu⟩ ⟨s, hs⟩ (by push_cast; exact hsq)

/-! ### Part (2): odd primes -/

theorem hF1_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Point) :
    ∃ i : Fin 4, phiAlpha (-(p : ℤ)) 0 p (P + Tp p hp i) = 1 := by
  have hd := hdist hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hppos := hp.pos
  obtain ⟨r, hr0, hrcls, hrev⟩ : ∃ r : ℚ, 0 < r ∧ phiAlpha (-(p : ℤ)) 0 p P = cls r ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p → Even (padicValRat ℓ r) :=
    ⟨_, descentRep_alpha_pos (by omega) (by omega) P, rfl, fun ℓ hℓ h2 hpℓ =>
      (remark_3_7.support _ _ _ hd.1 hd.2.1 hd.2.2 P ℓ hℓ (not_dvd_disc hp hℓ h2 hpℓ)).1⟩
  obtain ⟨d, hdl, hsq⟩ := exists_class_pos_two_p hp hp2 hr0 hrev
  rcases hdl with rfl | rfl | rfl | rfl
  · refine ⟨0, ?_⟩
    have : Tp p hp 0 = 0 := rfl
    rw [this, add_zero, hrcls, cls_eq_one_iff hr0.ne']
    simpa using hsq
  · refine ⟨1, ?_⟩
    have : Tp p hp 1 = rootPt p hp (-(p : ℚ)) (Or.inl rfl) := rfl
    have hc : (2 : ℚ) * (p : ℚ) ^ 2 ≠ 0 := by positivity
    rw [this, remark_3_7.hom_alpha _ _ _ hd.1 hd.2.1 hd.2.2, hrcls,
      show phiAlpha (-(p : ℤ)) 0 p (rootPt p hp (-(p : ℚ)) (Or.inl rfl)) = cls (2 * (p : ℚ) ^ 2) from
        phiAlpha_root _ _ _ rfl,
      ← cls_mul hr0.ne' hc, cls_eq_one_iff (mul_ne_zero hr0.ne' hc)]
    obtain ⟨s, hs⟩ := hsq
    push_cast at hs
    exact ⟨s * p, by linear_combination (p : ℚ) ^ 2 * hs⟩
  · refine ⟨2, ?_⟩
    have : Tp p hp 2 = rootPt p hp 0 (Or.inr (Or.inl rfl)) := rfl
    have hx1 : (0 : ℚ) ≠ -(p : ℚ) := by
      intro h; apply hp0; linarith
    have hc : (0 : ℚ) + p ≠ 0 := by simpa using hp0
    rw [this, remark_3_7.hom_alpha _ _ _ hd.1 hd.2.1 hd.2.2, hrcls,
      show phiAlpha (-(p : ℤ)) 0 p (rootPt p hp 0 (Or.inr (Or.inl rfl))) = cls (0 + (p : ℚ)) from
        phiAlpha_some _ _ _ hx1,
      ← cls_mul hr0.ne' hc, cls_eq_one_iff (mul_ne_zero hr0.ne' hc)]
    obtain ⟨s, hs⟩ := hsq
    push_cast at hs
    exact ⟨s, by linear_combination hs⟩
  · refine ⟨3, ?_⟩
    have : Tp p hp 3 = rootPt p hp p (Or.inr (Or.inr rfl)) := rfl
    have hx1 : (p : ℚ) ≠ -(p : ℚ) := by
      intro h; apply hp0; linarith
    have hc : (p : ℚ) + p ≠ 0 := by
      intro h; apply hp0; linarith
    rw [this, remark_3_7.hom_alpha _ _ _ hd.1 hd.2.1 hd.2.2, hrcls,
      show phiAlpha (-(p : ℤ)) 0 p (rootPt p hp p (Or.inr (Or.inr rfl))) = cls ((p : ℚ) + p) from
        phiAlpha_some _ _ _ hx1,
      ← cls_mul hr0.ne' hc, cls_eq_one_iff (mul_ne_zero hr0.ne' hc)]
    obtain ⟨s, hs⟩ := hsq
    push_cast at hs
    exact ⟨s, by linear_combination hs⟩

theorem hF2_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (A : Finset ℤ) (h1 : (1 : ℤ) ∈ A)
    (hex : ∀ d : ℤ, (d = 1 ∨ d = -1 ∨ d = p ∨ d = -(p : ℤ)) → d ∉ A → ¬ Sys (p : ℤ) d)
    (Q : (cubicCurve (-(p : ℤ)) 0 p).toAffine.Point) (hQ : phiAlpha (-(p : ℤ)) 0 p Q = 1) :
    ∃ d ∈ A, phiBeta (-(p : ℤ)) 0 p Q = cls d := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2' : (p : ℤ) % 2 = 1 := by
    have := hp.eq_two_or_odd
    omega
  cases Q with
  | zero =>
    refine ⟨1, h1, ?_⟩
    unfold phiBeta
    rw [descentMap_eq_cls, ← Point.zero_def, descentRep_zero, Int.cast_one, cls_one]
  | some x y h =>
    by_cases hx1 : x = -(p : ℚ)
    · exfalso
      rw [phiAlpha_root x y h hx1, cls_eq_one_iff (by positivity)] at hQ
      exact not_isSquare_two_mul_sq hp hp2 hQ
    by_cases hx2 : x = 0
    · exfalso
      rw [phiAlpha_some x y h hx1, cls_eq_one_iff (by rw [hx2]; simpa using hp0)] at hQ
      rw [hx2, zero_add] at hQ
      exact not_isSquare_prime hp hQ
    by_cases hx3 : x = p
    · exfalso
      rw [phiAlpha_some x y h hx1, cls_eq_one_iff (by rw [hx3]; intro h0; apply hp0; linarith)] at hQ
      rw [hx3, ← two_mul] at hQ
      exact not_isSquare_two_mul hp hp2 hQ
    obtain ⟨d, hdl, hsq⟩ := exists_class_two_p hp hp2 hx2
      (fun ℓ hℓ h2 hpℓ => even_val_beta_some hp x y h hx2 hℓ h2 hpℓ)
    have hd0 : d ≠ 0 := by
      have := hp.pos
      rcases hdl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hS := point_sys p x y h hx1 hx2 hQ hd0 hsq
    have hφ : phiBeta (-(p : ℤ)) 0 p (Point.some x y h) = cls d := by
      rw [phiBeta_some x y h hx2, cls_eq_iff hx2 (by exact_mod_cast hd0), mul_comm]
      exact hsq
    rcases hdl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, h1, hφ⟩
    · by_cases hm : (-1 : ℤ) ∈ A
      · exact ⟨-1, hm, hφ⟩
      · exact absurd hS (hex _ (Or.inr (Or.inl rfl)) hm)
    · by_cases hm : (p : ℤ) ∈ A
      · exact ⟨p, hm, hφ⟩
      · exact absurd hS (hex _ (Or.inr (Or.inr (Or.inl rfl))) hm)
    · by_cases hm : -(p : ℤ) ∈ A
      · exact ⟨-(p : ℤ), hm, hφ⟩
      · exact absurd hS (hex _ (Or.inr (Or.inr (Or.inr rfl))) hm)
    · exfalso
      obtain ⟨n, c, V, W, hg, hV, hW⟩ := hS
      exact excl_even p 1 n c V W hp2' (by norm_num) (not_dvd_both hg (by omega))
        (by rw [hV]; ring) (by rw [hW]; ring)
    · exfalso
      obtain ⟨n, c, V, W, hg, hV, hW⟩ := hS
      exact excl_even p (-1) n c V W hp2' (by norm_num) (not_dvd_both hg (by omega))
        (by rw [hV]; ring) (by rw [hW]; ring)
    · exfalso
      obtain ⟨n, c, V, W, hg, hV, hW⟩ := hS
      exact excl_even p p n c V W hp2' hp2' (not_dvd_both hg (by omega))
        (by rw [hV]) (by rw [hW])
    · exfalso
      obtain ⟨n, c, V, W, hg, hV, hW⟩ := hS
      exact excl_even p (-(p : ℤ)) n c V W hp2' (by omega) (not_dvd_both hg (by omega))
        (by rw [hV]; ring) (by rw [hW]; ring)

theorem rank_le_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (A : Finset ℤ) (h1 : (1 : ℤ) ∈ A)
    (hex : ∀ d : ℤ, (d = 1 ∨ d = -1 ∨ d = p ∨ d = -(p : ℤ)) → d ∉ A → ¬ Sys (p : ℤ) d)
    {m : ℕ} (hA : A.card ≤ 2 ^ m) : rank (cubicCurve (-(p : ℤ)) 0 p) ≤ m := by
  have hd := hdist hp
  have := fg_cubicCurve hd.1 hd.2.1 hd.2.2
  have hlow := two_pow_le_card_cubic_of_fg hd.1 hd.2.1 hd.2.2
  have hup := card_quot_two_le_split hd.1 hd.2.1 hd.2.2 (Tp p hp) (A.image (fun d : ℤ => cls (d : ℚ))) (hF1_two_p hp hp2)
    (fun Q hQ => by
      obtain ⟨d, hdA, hφ⟩ := hF2_two_p hp hp2 A h1 hex Q hQ
      exact Finset.mem_image.2 ⟨d, hdA, hφ.symm⟩)
  have himg : (A.image (fun d : ℤ => cls (d : ℚ))).card ≤ A.card := Finset.card_image_le
  have h2 : 2 ^ (rank (cubicCurve (-(p : ℤ)) 0 p) + 2) ≤ 2 ^ (m + 2) := by
    calc 2 ^ (rank (cubicCurve (-(p : ℤ)) 0 p) + 2) ≤ _ := hlow
      _ ≤ 4 * (A.image (fun d : ℤ => cls (d : ℚ))).card := hup
      _ ≤ 4 * 2 ^ m := by omega
      _ = 2 ^ (m + 2) := by ring
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  omega

theorem not_dvd_prime_cast {p : ℕ} (hp : p.Prime) : ¬ ((p : ℤ) ∣ 1) := by
  intro h
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.1 (by exact_mod_cast h))

/-- Exclusions for `p ≡ 3 (mod 8)`. -/
theorem sys_excl_three {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3) (d : ℤ)
    (hd : d = -1 ∨ d = p ∨ d = -(p : ℤ)) : ¬ Sys (p : ℤ) d := by
  rintro ⟨n, c, V, W, hg, hV, hW⟩
  have hpc : ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ c) := not_dvd_both hg (not_dvd_prime_cast hp)
  rcases hd with rfl | rfl | rfl
  · exact excl_neg_one_three hp (by omega) n c V hpc hV
  · exact excl_p_three hp (by omega) n c V hpc hV
  · exact excl_neg_p hp (Or.inl h8) n c V W hpc hV hW

/-- Exclusions for `p ≡ 5 (mod 8)`. -/
theorem sys_excl_five {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 5) (d : ℤ)
    (hd : d = p ∨ d = -(p : ℤ)) : ¬ Sys (p : ℤ) d := by
  rintro ⟨n, c, V, W, hg, hV, hW⟩
  have hpc : ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ c) := not_dvd_both hg (not_dvd_prime_cast hp)
  rcases hd with rfl | rfl
  · exact excl_p_five hp h8 n c V W hpc (not_dvd_both hg (by omega)) hV hW
  · exact excl_neg_p hp (Or.inr h8) n c V W hpc hV hW

/-- Exclusions for `p ≡ 7 (mod 8)`. -/
theorem sys_excl_seven {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 7) (d : ℤ)
    (hd : d = -1 ∨ d = p) : ¬ Sys (p : ℤ) d := by
  rintro ⟨n, c, V, W, hg, hV, hW⟩
  have hpc : ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ c) := not_dvd_both hg (not_dvd_prime_cast hp)
  rcases hd with rfl | rfl
  · exact excl_neg_one_three hp (by omega) n c V hpc hV
  · exact excl_p_three hp (by omega) n c V hpc hV


/-! ### Part (1): the curve $Y^2 = X^3 - 4X$ -/

/-- `8` is not a square in `ℚ`. -/
theorem not_isSquare_two_mul_sq_two : ¬ IsSquare (2 * ((2 : ℕ) : ℚ) ^ 2) := by
  refine not_isSquare_of_odd_val Nat.prime_two ?_
  have := Fact.mk Nat.prime_two
  have h2 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have h : ((2 : ℕ) : ℚ) = 2 := by norm_num
  rw [h, padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow, h2, Int.not_even_iff_odd]
  exact ⟨1, by norm_num⟩

/-- The torsion points $O$ and $(0, 0)$ of $Y^2 = X^3 - 4X$. -/
noncomputable def T2 : Fin 2 → (cubicCurve (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ)).toAffine.Point :=
  ![0, rootPt 2 Nat.prime_two 0 (Or.inr (Or.inl rfl))]

theorem hF1_two (P : (cubicCurve (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ)).toAffine.Point) :
    ∃ i : Fin 2, phiAlpha (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ) (P + T2 i) = 1 := by
  have hd := hdist Nat.prime_two
  obtain ⟨r, hr0, hrcls, hrev⟩ : ∃ r : ℚ, 0 < r ∧
      phiAlpha (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ) P = cls r ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → Even (padicValRat ℓ r) :=
    ⟨_, descentRep_alpha_pos (by omega) (by omega) P, rfl, fun ℓ hℓ h2 =>
      (remark_3_7.support _ _ _ hd.1 hd.2.1 hd.2.2 P ℓ hℓ (not_dvd_disc Nat.prime_two hℓ h2 h2)).1⟩
  obtain ⟨d, hdl, hsq⟩ := exists_class_pos_two hr0 hrev
  rcases hdl with rfl | rfl
  · refine ⟨0, ?_⟩
    have : T2 0 = 0 := rfl
    rw [this, add_zero, hrcls, cls_eq_one_iff hr0.ne']
    simpa using hsq
  · refine ⟨1, ?_⟩
    have : T2 1 = rootPt 2 Nat.prime_two 0 (Or.inr (Or.inl rfl)) := rfl
    have hx1 : (0 : ℚ) ≠ -((2 : ℕ) : ℚ) := by norm_num
    have hc : (0 : ℚ) + ((2 : ℕ) : ℚ) ≠ 0 := by norm_num
    rw [this, remark_3_7.hom_alpha _ _ _ hd.1 hd.2.1 hd.2.2, hrcls,
      show phiAlpha (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ) (rootPt 2 Nat.prime_two 0 (Or.inr (Or.inl rfl))) =
        cls (0 + ((2 : ℕ) : ℚ)) from phiAlpha_some _ _ _ hx1,
      ← cls_mul hr0.ne' hc, cls_eq_one_iff (mul_ne_zero hr0.ne' hc)]
    obtain ⟨s, hs⟩ := hsq
    exact ⟨s, by push_cast at hs ⊢; linear_combination hs⟩

theorem hF2_two (Q : (cubicCurve (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ)).toAffine.Point)
    (hQ : phiAlpha (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ) Q = 1) :
    ∃ d ∈ ({1, 2} : Finset ℤ), phiBeta (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ) Q = cls (d : ℚ) := by
  cases Q with
  | zero =>
    refine ⟨1, by simp, ?_⟩
    unfold phiBeta
    rw [descentMap_eq_cls, ← Point.zero_def, descentRep_zero, Int.cast_one, cls_one]
  | some x y h =>
    by_cases hx1 : x = -((2 : ℕ) : ℚ)
    · exfalso
      rw [phiAlpha_root x y h hx1, cls_eq_one_iff (by norm_num)] at hQ
      exact not_isSquare_two_mul_sq_two hQ
    by_cases hx2 : x = 0
    · exfalso
      rw [phiAlpha_some x y h hx1, cls_eq_one_iff (by rw [hx2]; norm_num)] at hQ
      rw [hx2, zero_add] at hQ
      exact not_isSquare_prime Nat.prime_two hQ
    by_cases hx3 : x = ((2 : ℕ) : ℚ)
    · refine ⟨2, by simp, ?_⟩
      rw [phiBeta_some x y h hx2, hx3]
      norm_num
    obtain ⟨d, hdl, hsq⟩ := exists_class_two hx2
      (fun ℓ hℓ h2 => even_val_beta_some Nat.prime_two x y h hx2 hℓ h2 h2)
    have hd0 : d ≠ 0 := by
      rcases hdl with rfl | rfl | rfl | rfl <;> omega
    have hS := point_sys 2 x y h hx1 hx2 hQ hd0 hsq
    have hφ : phiBeta (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ) (Point.some x y h) = cls (d : ℚ) := by
      rw [phiBeta_some x y h hx2, cls_eq_iff hx2 (by exact_mod_cast hd0), mul_comm]
      exact hsq
    rcases hdl with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, hφ⟩
    · exfalso
      obtain ⟨n, c, V, W, hg, hV, hW⟩ := hS
      exact excl_two_neg_one n c V W (not_dvd_both hg (by omega))
        (by rw [hV]; push_cast; ring) (by rw [hW]; push_cast; ring)
    · exact ⟨2, by simp, hφ⟩
    · exfalso
      obtain ⟨n, c, V, W, hg, hV, hW⟩ := hS
      exact excl_two_neg_two n c V W (not_dvd_both hg (by omega))
        (by rw [hV]; push_cast; ring) (by rw [hW]; push_cast; ring)

theorem rank_two : rank (cubicCurve (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ)) = 0 := by
  have hd := hdist Nat.prime_two
  have := fg_cubicCurve hd.1 hd.2.1 hd.2.2
  have hlow := two_pow_le_card_cubic_of_fg hd.1 hd.2.1 hd.2.2
  have hup := card_quot_two_le_split hd.1 hd.2.1 hd.2.2 T2
    (({1, 2} : Finset ℤ).image (fun d : ℤ => cls (d : ℚ))) hF1_two
    (fun Q hQ => by
      obtain ⟨d, hdA, hφ⟩ := hF2_two Q hQ
      exact Finset.mem_image.2 ⟨d, hdA, hφ.symm⟩)
  have himg : (({1, 2} : Finset ℤ).image (fun d : ℤ => cls (d : ℚ))).card ≤ 2 :=
    Finset.card_image_le.trans Finset.card_le_two
  have h2 : 2 ^ (rank (cubicCurve (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ)) + 2) ≤ 2 ^ 2 := by
    calc 2 ^ (rank (cubicCurve (-((2 : ℕ) : ℤ)) 0 ((2 : ℕ) : ℤ)) + 2) ≤ _ := hlow
      _ ≤ 2 * (({1, 2} : Finset ℤ).image (fun d : ℤ => cls (d : ℚ))).card := hup
      _ ≤ 2 ^ 2 := by omega
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  omega

end Exercise59

/-- **Exercise 5.9 (1)**, the rank (pdf p. 139): $E : Y^2 = X^3 - 4X$ has rank $0$. -/
theorem exercise_5_9_1_rank : rank (cubicCurve (-2) 0 2) = 0 := by
  simpa using Exercise59.rank_two

/-- **Exercise 5.9 (1)** (pdf p. 139): $E(\mathbb{Q})$ is finite for $E : Y^2 = X^3 - 4X$.  The 2-descent of
Remark 3.7 shows that $E(\mathbb{Q})/2E(\mathbb{Q})$ has at most $4$ elements, so the rank is $0$ (see the module
docstring); the torsion subgroup is finite. -/
@[kb "milne2006ec" "Ch. IV, Exercise 5.9 (1), pdf p. 139"]
theorem exercise_5_9_1 : Exercise5_9_1 := by
  refine ⟨?_⟩
  have := fg_cubicCurve (α := -2) (β := 0) (γ := 2) (by norm_num) (by norm_num) (by norm_num)
  have h0 := exercise_5_9_1_rank
  obtain ⟨e⟩ := rank_spec (cubicCurve (-2) 0 2)
  have := finite_torsion_of_fg (cubicCurve (-2) 0 2).toAffine.Point
  have : Finite (Fin (rank (cubicCurve (-2) 0 2)) → ℤ) := by
    rw [h0]
    infer_instance
  exact Finite.of_equiv _ e.symm.toEquiv

/-- **Exercise 5.9 (2)** (pdf p. 139): for an odd prime $p$ the rank of $Y^2 = X^3 - p^2X$ is at most $2$ if
$p \equiv 1 \pmod 8$, is $0$ if $p \equiv 3 \pmod 8$, and is at most $1$ if $p \equiv 5, 7 \pmod 8$. -/
@[kb "milne2006ec" "Ch. IV, Exercise 5.9 (2), pdf p. 139"]
theorem exercise_5_9_2 : Exercise5_9_2 := by
  refine ⟨fun p hp hp2 => ⟨fun h8 => ?_, fun h8 => ?_, fun h8 => ?_⟩⟩
  · refine Exercise59.rank_le_two_p hp hp2 {1, -1, (p : ℤ), -(p : ℤ)} (by simp) ?_ (m := 2)
      (Finset.card_le_four.trans (by norm_num))
    intro d hd hdA
    exact (hdA (by rcases hd with rfl | rfl | rfl | rfl <;> simp)).elim
  · refine Nat.le_zero.1 (Exercise59.rank_le_two_p hp hp2 {1} (by simp) ?_ (m := 0) (by simp))
    intro d hd hdA
    rcases hd with rfl | rfl | rfl | rfl
    · exact (hdA (by simp)).elim
    · exact Exercise59.sys_excl_three hp h8 _ (Or.inl rfl)
    · exact Exercise59.sys_excl_three hp h8 _ (Or.inr (Or.inl rfl))
    · exact Exercise59.sys_excl_three hp h8 _ (Or.inr (Or.inr rfl))
  · rcases h8 with h8 | h8
    · refine Exercise59.rank_le_two_p hp hp2 {1, -1} (by simp) ?_ (m := 1)
        (Finset.card_le_two.trans (by norm_num))
      intro d hd hdA
      rcases hd with rfl | rfl | rfl | rfl
      · exact (hdA (by simp)).elim
      · exact (hdA (by simp)).elim
      · exact Exercise59.sys_excl_five hp h8 _ (Or.inl rfl)
      · exact Exercise59.sys_excl_five hp h8 _ (Or.inr rfl)
    · refine Exercise59.rank_le_two_p hp hp2 {1, -(p : ℤ)} (by simp) ?_ (m := 1)
        (Finset.card_le_two.trans (by norm_num))
      intro d hd hdA
      rcases hd with rfl | rfl | rfl | rfl
      · exact (hdA (by simp)).elim
      · exact Exercise59.sys_excl_seven hp h8 _ (Or.inl rfl)
      · exact Exercise59.sys_excl_seven hp h8 _ (Or.inr rfl)
      · exact (hdA (by simp)).elim

end NumberFieldKB.MilneEC
