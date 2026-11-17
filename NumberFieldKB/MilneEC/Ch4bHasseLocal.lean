import NumberFieldKB.MilneEC.Ch4bHasse
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter IV, Remark 8.4: the curve $Y^2 = 2 - 2pX^4$ has a point over every $\mathbb Q_q$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Remark 8.4, pdf p. 154.
Milne treats $q \neq 2, p$ by Hensel's lemma and leaves $q = 2$ and $q = p$ to the reader.

No bound of Hasse type (on the number of points of the reduction of the curve) is needed.  Instead, for an odd prime
$q \ne p$ we count with the quadratic character $\chi$ of the field with $q$ elements:
$\sum_x \chi(c + x^4) \le q - 2 < q$ for $c \ne 0$ (`exists_quadraticChar_ne_one`), computed by counting square roots
twice and one character sum $\sum_v \chi(v(v+c)) = -1$.  Hensel's lemma then lifts a point of the reduction.

## Proved
* `exists_quadraticChar_ne_one`: for a finite field of odd characteristic and $c \neq 0$ there is $x$ with
  $\chi(c + x^4) \ne 1$.
* `exists_sq_padicInt_of_zmod`: a $q$-adic integer ($q$ odd) whose reduction is a nonzero square is a square.
* `exists_root_of_zmod`: simple roots modulo $q$ lift to $q$-adic roots (Hensel's lemma).
* `exists_fourth_root_two_adic`: every $2$-adic integer congruent to $1$ modulo $16$ is a fourth power.
* `remark_8_4_local`: the statement `Remark8_4Local`.
-/

namespace NumberFieldKB.MilneEC

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Counting square roots: for every function `h` on a finite field of odd characteristic,
$\sum_x h(x^2) = \sum_u (\chi(u) + 1)\, h(u)$, where $\chi$ is the quadratic character. -/
lemma sum_sq_eq_sum_char_add_one (hF : ringChar F ≠ 2) (h : F → ℤ) :
    ∑ x : F, h (x ^ 2) = ∑ u : F, (quadraticChar F u + 1) * h u := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x : F => x ^ 2) (fun x => h (x ^ 2))]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hc := quadraticChar_card_sqrts hF u
  rw [Set.toFinset_ofPred] at hc
  rw [Finset.sum_congr rfl (g := fun _ => h u) (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
    Finset.sum_const, nsmul_eq_mul, hc]

/-- For $c \ne 0$, $\sum_v \chi(v(c+v)) = -1$. -/
lemma sum_quadraticChar_mul_add (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) :
    ∑ v : F, quadraticChar F (v * (c + v)) = -1 := by
  have h1 : ∀ v : F, quadraticChar F (v * (c + v)) =
      (quadraticChar F (1 + c * v⁻¹)) - (if v = 0 then 1 else 0) := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · have : v * (c + v) = v ^ 2 * (1 + c * v⁻¹) := by field_simp; ring
      rw [this, map_mul, quadraticChar_sq_one' hv]
      simp [hv]
  have hinv : Function.Involutive (fun v : F => c * v⁻¹) := by
    intro v
    simp only [mul_inv, inv_inv]
    rw [mul_inv_cancel_left₀ hc]
  have h2 : ∑ v : F, quadraticChar F (1 + c * v⁻¹) = 0 := by
    rw [← quadraticChar_sum_zero hF]
    rw [Fintype.sum_bijective (fun v : F => c * v⁻¹) hinv.bijective _
      (fun w => quadraticChar F (1 + w)) (fun v => rfl)]
    exact Fintype.sum_equiv (Equiv.addLeft 1) _ _ (fun w => rfl)
  simp only [h1, Finset.sum_sub_distrib, h2]
  simp

/-- For $c \ne 0$, $\sum_u \chi(c + u^2) = -1$. -/
lemma sum_quadraticChar_add_sq (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) :
    ∑ u : F, quadraticChar F (c + u ^ 2) = -1 := by
  rw [sum_sq_eq_sum_char_add_one hF (fun u => quadraticChar F (c + u))]
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  have h0 : ∑ v : F, quadraticChar F (c + v) = 0 := by
    rw [← quadraticChar_sum_zero hF]
    exact Fintype.sum_equiv (Equiv.addLeft c) _ _ (fun w => rfl)
  rw [h0, add_zero, ← sum_quadraticChar_mul_add hF hc]
  simp [map_mul]

lemma quadraticChar_le_one (a : F) : quadraticChar F a ≤ 1 := by
  rcases quadraticChar_isQuadratic (F := F) a with h | h | h <;> rw [h] <;> norm_num

/-- **Character sum bound.**  For a finite field `F` of odd characteristic and $c \ne 0$ there is $x \in F$ with
$\chi(c + x^4) \ne 1$, where $\chi$ is the quadratic character.  (Equivalently, $c + x^4$ is not a nonzero square
for some $x$.)  This is proved by showing $\sum_x \chi(c + x^4) \le \# F - 2$. -/
theorem exists_quadraticChar_ne_one (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) :
    ∃ x : F, quadraticChar F (c + x ^ 4) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ x : F, quadraticChar F (c + x ^ 4) = Fintype.card F := by
    rw [Finset.sum_congr rfl (fun x _ => hcon x)]
    simp
  have h4 : ∀ x : F, x ^ 4 = (x ^ 2) ^ 2 := fun x => by ring
  simp only [h4] at hsum
  rw [sum_sq_eq_sum_char_add_one hF (fun u => quadraticChar F (c + u ^ 2))] at hsum
  simp only [add_mul, one_mul, Finset.sum_add_distrib] at hsum
  rw [sum_quadraticChar_add_sq hF hc] at hsum
  have hlt : ∑ u : F, quadraticChar F u * quadraticChar F (c + u ^ 2) < Fintype.card F := by
    have : ∑ u : F, quadraticChar F u * quadraticChar F (c + u ^ 2) <
        ∑ _u : F, (1 : ℤ) := by
      apply Finset.sum_lt_sum
      · intro u _
        rw [← map_mul]
        exact quadraticChar_le_one _
      · exact ⟨0, Finset.mem_univ _, by simp⟩
    simpa using this
  omega

end FiniteField

section PadicHensel

variable {q : ℕ} [Fact q.Prime]

/-- A $q$-adic integer has norm less than one if and only if its reduction modulo $q$ is zero. -/
lemma norm_lt_one_iff_toZMod (x : ℤ_[q]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

/-- The reduction modulo $q$ of the integer $2$. -/
lemma toZMod_two : PadicInt.toZMod (2 : ℤ_[q]) = 2 := map_ofNat _ 2

/-- A $q$-adic integer has norm one if and only if its reduction modulo $q$ is nonzero. -/
lemma norm_eq_one_iff_toZMod (x : ℤ_[q]) : ‖x‖ = 1 ↔ PadicInt.toZMod x ≠ 0 := by
  rw [ne_eq, ← norm_lt_one_iff_toZMod]
  have := PadicInt.norm_le_one x
  constructor
  · intro h; rw [h]; simp
  · intro h; exact le_antisymm this (not_lt.1 h)

/-- Divisibility by $q^n$ in terms of the norm. -/
lemma pow_dvd_iff_norm_le (x : ℤ_[q]) (n : ℕ) :
    (q : ℤ_[q]) ^ n ∣ x ↔ ‖x‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

/-- **Hensel's lemma, simple roots.**  If a polynomial over $\mathbb Z_q$ has a simple root modulo $q$ at the
reduction of $a \in \mathbb Z_q$ (it vanishes there and its derivative does not), then it has a root in
$\mathbb Z_q$. -/
theorem exists_root_of_zmod (F : Polynomial ℤ_[q]) (a : ℤ_[q])
    (h1 : PadicInt.toZMod (F.eval a) = 0) (h2 : PadicInt.toZMod (F.derivative.eval a) ≠ 0) :
    ∃ z : ℤ_[q], F.eval z = 0 := by
  have e : ∀ (z : ℤ_[q]) (P : Polynomial ℤ_[q]), P.aeval z = P.eval z := fun z P =>
    congrFun (Polynomial.coe_aeval_eq_eval z) P
  have hn : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [e, e, (norm_eq_one_iff_toZMod _).2 h2, one_pow]
    exact (norm_lt_one_iff_toZMod _).2 h1
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) hn
  exact ⟨z, by rw [e] at hz; exact hz⟩

/-- **Square roots in $\mathbb Z_q$, $q$ odd.**  A $q$-adic integer whose reduction modulo $q$ is a nonzero square
is a square. -/
theorem exists_sq_padicInt_of_zmod (hq : q ≠ 2) (u : ℤ_[q])
    (h : ∃ a : ZMod q, a ≠ 0 ∧ PadicInt.toZMod u = a ^ 2) : ∃ b : ℤ_[q], b ^ 2 = u := by
  obtain ⟨a0, ha0, hu⟩ := h
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := q)) a0
  have two_ne : (2 : ZMod q) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hq)
  obtain ⟨z, hz⟩ := exists_root_of_zmod (Polynomial.X ^ 2 - Polynomial.C u) a
    (by simp [ha, hu]) (by
      have hd : (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C u)).eval a = 2 * a := by
        simp [one_add_one_eq_two]
      rw [hd, map_mul, ha, map_ofNat]
      exact mul_ne_zero two_ne ha0)
  exact ⟨z, by simpa [sub_eq_zero] using hz⟩

end PadicHensel

section TwoAdic

/-- One square-root step in $\mathbb Z_2$: if $8 \mid a - 1$ then $a = b^2$ with $4 \mid b - 1$. -/
lemma exists_sq_two_adic_step (a : ℤ_[2]) (h : (8 : ℤ_[2]) ∣ a - 1) :
    ∃ b : ℤ_[2], b ^ 2 = a ∧ (4 : ℤ_[2]) ∣ b - 1 := by
  have hn2 : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by simpa using PadicInt.norm_p (p := 2)
  have h8 : ‖a - 1‖ ≤ 1 / 8 := by
    have h' : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ a - 1 := by
      have : ((2 : ℕ) : ℤ_[2]) ^ 3 = 8 := by norm_num
      rw [this]; exact h
    have h'' := (pow_dvd_iff_norm_le (q := 2) (a - 1) 3).1 h'
    have e8 : ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℤ)) = 1 / 8 := by norm_num
    rwa [e8] at h''
  have d1 : Polynomial.aeval (1 : ℤ_[2]) (Polynomial.X ^ 2 - Polynomial.C a) = -(a - 1) := by
    simp
  have d2 : Polynomial.aeval (1 : ℤ_[2])
      (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C a)) = 2 := by
    simp [one_add_one_eq_two]
  have hn : ‖Polynomial.aeval (1 : ℤ_[2]) (Polynomial.X ^ 2 - Polynomial.C a)‖ <
      ‖Polynomial.aeval (1 : ℤ_[2])
        (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C a))‖ ^ 2 := by
    rw [d1, d2, hn2, norm_neg]
    exact lt_of_le_of_lt h8 (by norm_num)
  obtain ⟨z, hz, hz1, -⟩ := hensels_lemma hn
  rw [d2, hn2] at hz1
  refine ⟨z, by simpa [sub_eq_zero] using hz, ?_⟩
  have h1 : ‖z - 1‖ < ((2 : ℕ) : ℝ) ^ (-1 : ℤ) := by simpa using hz1
  have h2 := (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one (p := 2) (z - 1) (-1)).1 h1
  have e2 : (-1 : ℤ) - 1 = -((2 : ℕ) : ℤ) := by norm_num
  rw [e2] at h2
  have h3 := (pow_dvd_iff_norm_le (q := 2) (z - 1) 2).2 h2
  have : ((2 : ℕ) : ℤ_[2]) ^ 2 = 4 := by norm_num
  rwa [this] at h3

/-- **Fourth roots in $1 + 16\mathbb Z_2$.**  A $2$-adic integer congruent to $1$ modulo $16$ is a fourth
power. -/
theorem exists_fourth_root_two_adic (a : ℤ_[2]) (h : (16 : ℤ_[2]) ∣ a - 1) :
    ∃ x : ℤ_[2], x ^ 4 = a := by
  obtain ⟨b, hb, w, hw⟩ := exists_sq_two_adic_step a (dvd_trans ⟨2, by norm_num⟩ h)
  obtain ⟨t, ht⟩ := h
  have key : 8 * (w * (1 + 2 * w)) = 8 * (2 * t) := by
    linear_combination hb + ht - (b + 1 + 4 * w) * hw
  have key2 : w * (1 + 2 * w) = 2 * t := mul_left_cancel₀ (by norm_num) key
  have hz2 : (2 : ZMod 2) = 0 := by decide
  have hw0 : PadicInt.toZMod w = 0 := by
    have h2 : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by rw [map_ofNat]; exact hz2
    have := congrArg PadicInt.toZMod key2
    simpa [h2] using this
  obtain ⟨w', hw'⟩ := (PadicInt.norm_lt_one_iff_dvd w).1 ((norm_lt_one_iff_toZMod w).2 hw0)
  obtain ⟨x, hx⟩ := exists_sq_two_adic_step b ⟨w', by
    have : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
    rw [this] at hw'
    linear_combination hw + 4 * hw'⟩
  exact ⟨x, by rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx.1, hb]⟩

/-- For odd $P$ and an integer $c$ with $P \equiv c \bmod 16$ there is $x \in \mathbb Z_2$ with $P x^4 = c$. -/
theorem exists_mul_fourth_eq_two_adic (P c : ℤ) (hP : Odd P) (hc : (16 : ℤ) ∣ P - c) :
    ∃ x : ℤ_[2], (P : ℤ_[2]) * x ^ 4 = c := by
  have hn : ‖(P : ℤ_[2])‖ = 1 := by
    by_contra hne
    have hlt : ‖(P : ℤ_[2])‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) hne
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := 2) P).1 hlt
    obtain ⟨k, hk⟩ := hP
    push_cast at this
    omega
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.2 hn
  obtain ⟨m, hm⟩ := hc
  have hm' : (P : ℤ_[2]) - c = 16 * m := by exact_mod_cast hm
  have hv : ((u⁻¹ : (ℤ_[2])ˣ) : ℤ_[2]) * P = 1 := by rw [← hu]; simp
  obtain ⟨x, hx⟩ := exists_fourth_root_two_adic (((u⁻¹ : (ℤ_[2])ˣ) : ℤ_[2]) * c)
    ⟨-(m * ((u⁻¹ : (ℤ_[2])ˣ) : ℤ_[2])), by
      linear_combination hv - ((u⁻¹ : (ℤ_[2])ˣ) : ℤ_[2]) * hm'⟩
  exact ⟨x, by linear_combination (P : ℤ_[2]) * hx + (c : ℤ_[2]) * hv⟩

end TwoAdic

section LocalPoints

/-- A point of $Y^2 = 2 - 2pX^4$ over $\mathbb Z_q$ gives a point over $\mathbb Q_q$. -/
lemma coe_point {q : ℕ} [Fact q.Prime] (p : ℕ) (x y : ℤ_[q])
    (h : y ^ 2 = 2 - 2 * (p : ℤ_[q]) * x ^ 4) :
    ∃ x y : ℚ_[q], y ^ 2 = 2 - 2 * (p : ℚ_[q]) * x ^ 4 := by
  refine ⟨x, y, ?_⟩
  have := congrArg (fun z : ℤ_[q] => (z : ℚ_[q])) h
  push_cast at this
  exact this

/-- The case $q = 2$ of Remark 8.4: $p \equiv 1 \bmod 8$ gives a $2$-adic point (with $y = 0$ if
$p \equiv 1 \bmod 16$ and $y = 4$ if $p \equiv 9 \bmod 16$). -/
theorem local_point_two (p : ℕ) (hp : p % 8 = 1) :
    ∃ x y : ℚ_[2], y ^ 2 = 2 - 2 * (p : ℚ_[2]) * x ^ 4 := by
  have hodd : Odd (p : ℤ) := Int.odd_iff.2 (by omega)
  by_cases h16 : p % 16 = 1
  · obtain ⟨x, hx⟩ := exists_mul_fourth_eq_two_adic (p : ℤ) 1 hodd (by omega)
    push_cast at hx
    exact coe_point p x 0 (by linear_combination 2 * hx)
  · obtain ⟨x, hx⟩ := exists_mul_fourth_eq_two_adic (p : ℤ) (-7) hodd (by omega)
    push_cast at hx
    exact coe_point p x 4 (by linear_combination 2 * hx)

/-- The case $q = p$ of Remark 8.4: for $p \equiv 1 \bmod 8$, $2$ is a square in $\mathbb Z_p$, so
$(x, y) = (0, \sqrt 2)$ is a point. -/
theorem local_point_self (p : ℕ) [Fact p.Prime] (hp : p % 8 = 1) :
    ∃ x y : ℚ_[p], y ^ 2 = 2 - 2 * (p : ℚ_[p]) * x ^ 4 := by
  have hp2 : p ≠ 2 := by omega
  have two_ne : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_two_iff hp2).2 (Or.inl hp)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact two_ne (by simpa using ha)
  obtain ⟨b, hb⟩ := exists_sq_padicInt_of_zmod hp2 (2 : ℤ_[p])
    ⟨a, ha0, by rw [map_ofNat, ha, sq]⟩
  exact coe_point p 0 b (by rw [hb]; ring)

/-- The case of an odd prime $q \ne p$ of Remark 8.4. -/
theorem local_point_odd (p q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (hpq : ¬ q ∣ p) :
    (∃ x y : ℚ_[q], y ^ 2 = 2 - 2 * (p : ℚ_[q]) * x ^ 4) ∨ IsSquare (-2 * p : ℚ_[q]) := by
  have hF : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq
  have two_ne : (2 : ZMod q) ≠ 0 := Ring.two_ne_zero hF
  have hpz : (p : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpq
  have hd : (-2 * (p : ZMod q)) ≠ 0 := mul_ne_zero (neg_ne_zero.2 two_ne) hpz
  by_cases hsq : IsSquare (-2 * (p : ZMod q))
  · right
    obtain ⟨a, ha⟩ := hsq
    have ha0 : a ≠ 0 := by rintro rfl; exact hd (by simpa using ha)
    obtain ⟨b, hb⟩ := exists_sq_padicInt_of_zmod hq (-2 * (p : ℤ_[q]))
      ⟨a, ha0, by
        simp only [map_mul, map_neg, map_natCast, toZMod_two, sq]
        linear_combination ha⟩
    refine ⟨b, ?_⟩
    have h := congrArg (fun z : ℤ_[q] => (z : ℚ_[q])) hb
    have h2 : ((2 : ℤ_[q]) : ℚ_[q]) = 2 := rfl
    push_cast at h
    rw [h2] at h
    rw [← h]; ring
  · left
    obtain ⟨x0, hx0⟩ := exists_quadraticChar_ne_one hF (div_ne_zero two_ne hd)
    obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := q)) x0
    have hf : (2 - 2 * (p : ZMod q) * x0 ^ 4) = (-2 * (p : ZMod q)) * (2 / (-2 * (p : ZMod q)) + x0 ^ 4) := by
      field_simp
      ring
    have hchi : quadraticChar (ZMod q) (-2 * (p : ZMod q)) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.2 hsq
    by_cases hf0 : (2 - 2 * (p : ZMod q) * x0 ^ 4) = 0
    · -- a simple root modulo q
      have hx00 : x0 ≠ 0 := by
        rintro rfl
        simp at hf0
        exact two_ne hf0
      obtain ⟨z, hz⟩ := exists_root_of_zmod
        (Polynomial.C (2 : ℤ_[q]) - Polynomial.C (2 * (p : ℤ_[q])) * Polynomial.X ^ 4) x
        (by simpa [hx, toZMod_two] using hf0)
        (by
          have hd' : (Polynomial.derivative
              (Polynomial.C (2 : ℤ_[q]) - Polynomial.C (2 * (p : ℤ_[q])) * Polynomial.X ^ 4)).eval x
              = -(2 * p * (4 * x ^ 3)) := by
            simp; norm_num
          have h4 : (4 : ZMod q) ≠ 0 := by
            have : (4 : ZMod q) = 2 * 2 := by norm_num
            rw [this]; exact mul_ne_zero two_ne two_ne
          rw [hd']
          simp only [map_neg, map_mul, map_pow, map_natCast, map_ofNat, hx]
          exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero two_ne hpz) (mul_ne_zero h4 (pow_ne_zero 3 hx00))))
      exact coe_point p z 0 (by simp at hz; linear_combination -hz)
    · -- the value is a nonzero square
      have hne : quadraticChar (ZMod q) (2 / (-2 * (p : ZMod q)) + x0 ^ 4) = -1 := by
        rcases quadraticChar_isQuadratic (ZMod q) (2 / (-2 * (p : ZMod q)) + x0 ^ 4) with h | h | h
        · exact absurd (by rw [hf, quadraticChar_eq_zero_iff.1 h, mul_zero]) hf0
        · exact absurd h hx0
        · exact h
      have hsq1 : quadraticChar (ZMod q) (2 - 2 * (p : ZMod q) * x0 ^ 4) = 1 := by
        rw [hf, map_mul, hchi, hne]
        norm_num
      obtain ⟨a, ha⟩ := (quadraticChar_one_iff_isSquare hf0).1 hsq1
      have ha0 : a ≠ 0 := by rintro rfl; exact hf0 (by simpa using ha)
      obtain ⟨b, hb⟩ := exists_sq_padicInt_of_zmod hq (2 - 2 * (p : ℤ_[q]) * x ^ 4)
        ⟨a, ha0, by
          simp only [map_sub, map_mul, map_pow, map_natCast, toZMod_two, hx]
          rw [sq]; exact ha⟩
      exact coe_point p x b hb

end LocalPoints

/-- **Remark 8.4** (Milne, *Elliptic Curves*, Ch. IV, pdf p. 154): for a prime $p \equiv 1 \bmod 8$ the curve
$Y^2 = 2 - 2pX^4$ has a point over every $\mathbb Q_q$, either affine or at infinity (the latter when $-2p$ is a
square).  The hypothesis that $2$ is not a fourth power modulo $p$ is not used, and no Hasse bound is needed:
for odd $q \ne p$ the character sum bound `exists_quadraticChar_ne_one` plus Hensel's lemma give a point,
and the primes $q = 2$ and $q = p$ are handled by `local_point_two` and `local_point_self`. -/
@[kb "milne2006ec" "Ch. IV, Remark 8.4, pdf p. 154"]
theorem remark_8_4_local : Remark8_4Local := by
  refine ⟨fun p _ hp8 _ q _ => ?_⟩
  by_cases hq2 : q = 2
  · subst hq2
    exact Or.inl (local_point_two p hp8)
  · by_cases hqp : q = p
    · subst hqp
      exact Or.inl (local_point_self q hp8)
    · exact local_point_odd p q hq2 (fun h =>
        hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).1 h))

end NumberFieldKB.MilneEC
