import NumberFieldKB.MilneEC.Ch4IsogenyDescent
import NumberFieldKB.MilneEC.Ch4bHasseLocal
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter IV, Proposition 8.1: the two isogeny Selmer groups of $Y^2 = X^3 + pX$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 8.1, pdf p. 151,
which Milne quotes from Silverman (1986), Propositions X.4.9 and X.6.2.

For $c \in \mathbb Q$ and $d \in \mathbb Q^\times$ the quartic $C_d : N^2 = dM^4 + (c/d)e^4$ is the torsor attached to the
class $d$ for the $2$-isogeny of $Y^2 = X^3 + cX$ whose connecting map is $x \bmod \mathbb Q^{\times 2}$.
`TorsorSolvable F c d` says that $C_d$ has a point over $F$ with $(M, e) \ne (0, 0)$, and `isogenySelmer c` is the
set of $d$ for which $C_d$ is solvable over $\mathbb R$ and over every $\mathbb Q_q$.  These are the Selmer groups of
the two $2$-isogenies $\varphi : E \to E'$ ($c = p$, `curveP p`) and $\hat\varphi : E' \to E$ ($c = -4p$,
`curvePDual p`) described by local solvability of the quartic torsors.  They are **not** the Galois-cohomological
`selmerGroup`; the comparison between the two is not formalized here.

## Proved
* `mem_isogenySelmer_of_point`: the $x$-coordinate of a rational point of $Y^2 = X^3 + cX$ lies in `isogenySelmer c`.
* `isogenySelmer_curveP`: for $p \equiv 1 \bmod 8$, `isogenySelmer p` is $\{d \ne 0 : d \in \{1, p\}\,\mathbb Q^{\times 2}\}$.
* `isogenySelmer_curvePDual`: `isogenySelmer (-4p)` is the set of $d \ne 0$ with even valuation at every prime
  $\ell \ne 2, p$, i.e. the eight classes $\pm 1, \pm 2, \pm p, \pm 2p$ times squares.
* `prop_8_1_explicit`: the conjunction of the last two.

The proof of the inclusion $\subseteq$ is a valuation argument (`not_torsorSolvable_of_odd`); the inclusion
$\supseteq$ for $E'$ treats the eight class representatives place by place, using the Hensel lemmas and the
character-sum lemma of `Ch4bHasseLocal` (the quartics are those of Remark 8.4, `remark_8_4_local`).
-/

namespace NumberFieldKB.MilneEC

/-- The quartic $C_d : N^2 = dM^4 + (c/d)e^4$ has a point over `F` with $(M, e) \ne (0, 0)$. -/
def TorsorSolvable (F : Type*) [Field F] [CharZero F] (c d : ℚ) : Prop :=
  ∃ N M e : F, (M ≠ 0 ∨ e ≠ 0) ∧ N ^ 2 = (d : F) * M ^ 4 + ((c / d : ℚ) : F) * e ^ 4

/-- The Selmer group of the 2-isogeny whose connecting map is $x \bmod \mathbb Q^{\times 2}$ on
$Y^2 = X^3 + cX$: the nonzero $d$ for which $C_d$ is solvable over $\mathbb R$ and over every $\mathbb Q_q$. -/
def isogenySelmer (c : ℚ) : Set ℚ :=
  {d | d ≠ 0 ∧ (∀ (q : ℕ) [Fact q.Prime], TorsorSolvable ℚ_[q] c d) ∧ TorsorSolvable ℝ c d}

namespace SelmerExplicit

/-! ### General facts about `TorsorSolvable` -/

section General

variable {F : Type*} [Field F] [CharZero F]

/-- If $d$ is a square in $F$, then $(\sqrt d, 1, 0)$ is a point of $C_d$. -/
lemma ts_of_sq_d (c d : ℚ) (h : IsSquare (d : F)) : TorsorSolvable F c d := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, 1, 0, Or.inl one_ne_zero, by rw [hm]; ring⟩

/-- If $c/d$ is a square in $F$, then $(\sqrt{c/d}, 0, 1)$ is a point of $C_d$. -/
lemma ts_of_sq_cd (c d : ℚ) (h : IsSquare ((c / d : ℚ) : F)) : TorsorSolvable F c d := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, 0, 1, Or.inr one_ne_zero, by rw [hm]; ring⟩

/-- A point of $C_{d'}$ gives a point of $C_d$ when $d = d'$ and $d'c' = c$ (so $c/d = c'$). -/
lemma ts_cast (c d d' c' : ℚ) (hd : d = d') (hd0 : d' ≠ 0) (hdc : d' * c' = c)
    (N M e : F) (hne : M ≠ 0 ∨ e ≠ 0) (heq : N ^ 2 = (d' : F) * M ^ 4 + (c' : F) * e ^ 4) :
    TorsorSolvable F c d := by
  have h1 : c / d = c' := by rw [hd, ← hdc]; field_simp
  refine ⟨N, M, e, hne, ?_⟩
  rw [h1, hd]
  exact heq

/-- **Invariance under squares.**  A point of $C_r$ gives the point $(kN, M, ke)$ of $C_{rk^2}$. -/
lemma ts_sq_inv (c r k : ℚ) (hk : k ≠ 0) (h : TorsorSolvable F c r) :
    TorsorSolvable F c (r * k ^ 2) := by
  obtain ⟨N, M, e, hne, hN⟩ := h
  have hK : (k : F) ≠ 0 := Rat.cast_ne_zero.2 hk
  refine ⟨(k : F) * N, M, (k : F) * e, ?_, ?_⟩
  · rcases hne with h | h
    · exact Or.inl h
    · exact Or.inr (mul_ne_zero hK h)
  · have e1 : ((c / (r * k ^ 2) : ℚ) : F) = ((c / r : ℚ) : F) / (k : F) ^ 2 := by
      rw [← div_div, Rat.cast_div, Rat.cast_pow]
    have e2 : ((r * k ^ 2 : ℚ) : F) = (r : F) * (k : F) ^ 2 := by
      rw [Rat.cast_mul, Rat.cast_pow]
    rw [e1, e2]
    have e3 : ((c / r : ℚ) : F) / (k : F) ^ 2 * ((k : F) * e) ^ 4 =
        (k : F) ^ 2 * (((c / r : ℚ) : F) * e ^ 4) := by
      rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hK)]; ring
    rw [e3]
    linear_combination (k : F) ^ 2 * hN

/-- Solvability depends only on the class modulo squares: if $dr$ is a square and $C_r$ is solvable, so is
$C_d$. -/
lemma ts_of_isSquare_mul (c d r : ℚ) (hd : d ≠ 0) (hr : r ≠ 0) (hsq : IsSquare (d * r))
    (h : TorsorSolvable F c r) : TorsorSolvable F c d := by
  obtain ⟨m, hm⟩ := hsq
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hd hr (by rw [hm, mul_zero])
  have hdk : d = r * (m / r) ^ 2 := by
    field_simp
    linear_combination hm
  rw [hdk]
  exact ts_sq_inv c r (m / r) (div_ne_zero hm0 hr) h

/-- A rational square is a square in any field of characteristic zero. -/
lemma isSquare_cast {x : ℚ} (h : IsSquare x) : IsSquare (x : F) := by
  obtain ⟨m, hm⟩ := h
  exact ⟨(m : F), by rw [hm, Rat.cast_mul]⟩

/-- The global point $(y/x, 1, 1)$ of $C_x$ coming from $y^2 = x^3 + cx$. -/
lemma ts_of_point (c x y : ℚ) (hx : x ≠ 0) (h : y ^ 2 = x ^ 3 + c * x) : TorsorSolvable F c x := by
  refine ⟨((y / x : ℚ) : F), 1, 1, Or.inl one_ne_zero, ?_⟩
  have hq : (y / x) ^ 2 = x * 1 ^ 4 + (c / x) * 1 ^ 4 := by
    field_simp
    linear_combination h
  have := congrArg (fun z : ℚ => (z : F)) hq
  push_cast at this ⊢
  linear_combination this

end General

/-! ### The real place -/

/-- If $c > 0$ and $d < 0$ then $C_d$ has no real point other than $M = e = 0$. -/
lemma not_ts_real_of_neg {c d : ℚ} (hc : 0 < c) (hd : d < 0) : ¬ TorsorSolvable ℝ c d := by
  rintro ⟨N, M, e, hne, h⟩
  have h1 : ((d : ℚ) : ℝ) < 0 := by exact_mod_cast hd
  have h2 : ((c / d : ℚ) : ℝ) < 0 := by exact_mod_cast div_neg_of_pos_of_neg hc hd
  have hN : 0 ≤ N ^ 2 := sq_nonneg N
  have he4 : 0 ≤ e ^ 4 := by positivity
  have hM4 : 0 ≤ M ^ 4 := by positivity
  rcases hne with hM | he
  · have : 0 < M ^ 4 := by positivity
    nlinarith [mul_neg_of_neg_of_pos h1 this, mul_nonpos_of_nonpos_of_nonneg h2.le he4]
  · have : 0 < e ^ 4 := by positivity
    nlinarith [mul_neg_of_neg_of_pos h2 this, mul_nonpos_of_nonpos_of_nonneg h1.le hM4]

/-- For $c < 0$ the quartic $C_d$ has a real point for every $d \ne 0$. -/
lemma ts_real_of_neg {c d : ℚ} (hc : c < 0) (hd : d ≠ 0) : TorsorSolvable ℝ c d := by
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · refine ts_of_sq_cd c d ?_
    have : (0 : ℚ) < c / d := div_pos_of_neg_of_neg hc hlt
    have h' : (0 : ℝ) ≤ ((c / d : ℚ) : ℝ) := by exact_mod_cast this.le
    exact ⟨Real.sqrt _, (Real.mul_self_sqrt h').symm⟩
  · refine ts_of_sq_d c d ?_
    have h' : (0 : ℝ) ≤ ((d : ℚ) : ℝ) := by exact_mod_cast hgt.le
    exact ⟨Real.sqrt _, (Real.mul_self_sqrt h').symm⟩

/-! ### The valuation lemma -/

section Valuation

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma val_neg (x : ℚ_[ℓ]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  · have h1 : (-x) = (-1) * x := by ring
    rw [h1, Padic.valuation_mul (neg_ne_zero.2 one_ne_zero) hx]
    have : ((-1 : ℚ_[ℓ])).valuation = 0 := by
      have := Padic.valuation_ratCast (p := ℓ) (-1)
      simpa using this
    rw [this, zero_add]

/-- If $v(x) < v(y)$ then $v(x + y) = v(x)$. -/
lemma val_add_of_lt {x y : ℚ_[ℓ]} (hx : x ≠ 0) (_hy : y ≠ 0) (h : x.valuation < y.valuation) :
    x + y ≠ 0 ∧ (x + y).valuation = x.valuation := by
  have hne : x + y ≠ 0 := by
    intro h0
    have : y = -x := by linear_combination h0
    rw [this, val_neg] at h
    exact lt_irrefl _ h
  refine ⟨hne, ?_⟩
  have h1 := Padic.le_valuation_add hne
  have h2 : x = (x + y) + (-y) := by ring
  have hx' : (x + y) + (-y) ≠ 0 := by rw [← h2]; exact hx
  have h3 := Padic.le_valuation_add hx'
  rw [← h2, val_neg] at h3
  omega

/-- The core of the valuation argument: if $v(A)$ is odd and $v(B) = -v(A)$, then
$N^2 = AM^4 + Be^4$ has no solution with $(M, e) \ne (0, 0)$. -/
lemma core {A B N M e : ℚ_[ℓ]} (hA : A ≠ 0) (hB : B ≠ 0) (hne : M ≠ 0 ∨ e ≠ 0)
    (hodd : A.valuation % 2 = 1) (hBv : B.valuation = -A.valuation)
    (h : N ^ 2 = A * M ^ 4 + B * e ^ 4) : False := by
  have hN2 := Padic.valuation_pow N 2
  have hM4 := Padic.valuation_pow M 4
  have he4 := Padic.valuation_pow e 4
  push_cast at hN2 hM4 he4
  by_cases hM : M = 0
  · have he : e ≠ 0 := hne.resolve_left (not_not.2 hM)
    have h' : N ^ 2 = B * e ^ 4 := by rw [h, hM]; ring
    have hBe : B * e ^ 4 ≠ 0 := mul_ne_zero hB (pow_ne_zero 4 he)
    have hv := Padic.valuation_mul hB (pow_ne_zero 4 he)
    rw [← h', hN2] at hv
    omega
  by_cases he : e = 0
  · have h' : N ^ 2 = A * M ^ 4 := by rw [h, he]; ring
    have hv := Padic.valuation_mul hA (pow_ne_zero 4 hM)
    rw [← h', hN2] at hv
    omega
  have h1 := Padic.valuation_mul hA (pow_ne_zero 4 hM)
  have h2 := Padic.valuation_mul hB (pow_ne_zero 4 he)
  have hA' : A * M ^ 4 ≠ 0 := mul_ne_zero hA (pow_ne_zero 4 hM)
  have hB' : B * e ^ 4 ≠ 0 := mul_ne_zero hB (pow_ne_zero 4 he)
  rcases lt_trichotomy (A * M ^ 4).valuation (B * e ^ 4).valuation with hlt | heq | hgt
  · obtain ⟨-, hv⟩ := val_add_of_lt hA' hB' hlt
    rw [← h, hN2] at hv
    omega
  · omega
  · obtain ⟨-, hv⟩ := val_add_of_lt hB' hA' hgt
    rw [add_comm, ← h, hN2] at hv
    omega

/-- **Valuation lemma.**  If $v_\ell(c) = 0$ and $v_\ell(d)$ is odd, the quartic $C_d$ has no $\mathbb Q_\ell$-point
with $(M, e) \ne (0, 0)$: the two terms have valuations $\equiv v(d)$ and $\equiv -v(d) \pmod 4$, which are odd and
distinct, so the sum has odd valuation, while $v(N^2)$ is even.  (The hypothesis $v_\ell(c) = 0$ is necessary:
for $v_\ell(c) \equiv 2 \bmod 4$ the two terms can have equal valuation.) -/
theorem not_torsorSolvable_of_odd {c d : ℚ} (hc : padicValRat ℓ c = 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hd : ¬ Even (padicValRat ℓ d)) : ¬ TorsorSolvable ℚ_[ℓ] c d := by
  rintro ⟨N, M, e, hne, h⟩
  rw [Int.not_even_iff] at hd
  have hdv : Padic.valuation ((d : ℚ) : ℚ_[ℓ]) = padicValRat ℓ d := Padic.valuation_ratCast d
  have hcd : Padic.valuation ((c / d : ℚ) : ℚ_[ℓ]) = - padicValRat ℓ d := by
    rw [Padic.valuation_ratCast, padicValRat.div hc0 hd0, hc]; ring
  exact core (Rat.cast_ne_zero.2 hd0) (Rat.cast_ne_zero.2 (div_ne_zero hc0 hd0)) hne
    (by rw [hdv]; exact hd) (by rw [hcd, hdv]) h

end Valuation

/-! ### Valuations of $p$ and $-4p$ -/

lemma padicValRat_two_eq_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) : padicValRat ℓ (2 : ℚ) = 0 := by
  have := IsogenyDescent.padicValRat_natCast_prime_ne hℓ Nat.prime_two h2
  exact_mod_cast this

lemma padicValRat_neg_four_mul {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (h2 : ℓ ≠ 2) (hlp : ℓ ≠ p) :
    padicValRat ℓ (-4 * (p : ℚ)) = 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : (-4 * (p : ℚ)) = -((2 : ℚ) ^ 2 * p) := by ring
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [e, padicValRat.neg, padicValRat.mul (pow_ne_zero 2 two_ne_zero) hp0,
    padicValRat.pow (2 : ℚ), padicValRat_two_eq_zero hℓ h2,
    IsogenyDescent.padicValRat_natCast_prime_ne hℓ hp hlp]
  simp

/-! ### Local solvability at odd primes not dividing $2p$ -/

section OddPrime

variable {q : ℕ} [Fact q.Prime]

/-- A $q$-adic unit-type condition: if $D, C$ are integers prime to the odd prime $q$ then
$N^2 = DM^4 + Ce^4$ has a $\mathbb Q_q$-point with $(M, e) \ne (0, 0)$, either at a square value of $D$ or at
a point where $Dx^4 + C$ is $0$ or a nonzero square modulo $q$ (by the character sum lemma and Hensel's lemma). -/
theorem exists_point_odd (hq : q ≠ 2) (D C : ℤ) (hD : ¬ (q : ℤ) ∣ D) (hC : ¬ (q : ℤ) ∣ C) :
    ∃ N M e : ℚ_[q], (M ≠ 0 ∨ e ≠ 0) ∧ N ^ 2 = (D : ℚ_[q]) * M ^ 4 + (C : ℚ_[q]) * e ^ 4 := by
  have hF : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq
  have two_ne : (2 : ZMod q) ≠ 0 := Ring.two_ne_zero hF
  have hD0 : (D : ZMod q) ≠ 0 := fun h => hD ((ZMod.intCast_zmod_eq_zero_iff_dvd D q).1 h)
  have hC0 : (C : ZMod q) ≠ 0 := fun h => hC ((ZMod.intCast_zmod_eq_zero_iff_dvd C q).1 h)
  by_cases hsq : IsSquare (D : ZMod q)
  · obtain ⟨a, ha⟩ := hsq
    have ha0 : a ≠ 0 := by rintro rfl; exact hD0 (by simpa using ha)
    obtain ⟨b, hb⟩ := exists_sq_padicInt_of_zmod hq (D : ℤ_[q])
      ⟨a, ha0, by rw [map_intCast, ha, sq]⟩
    refine ⟨b, 1, 0, Or.inl one_ne_zero, ?_⟩
    have h := congrArg (fun z : ℤ_[q] => (z : ℚ_[q])) hb
    push_cast at h
    rw [h]; ring
  · have hchi : quadraticChar (ZMod q) (D : ZMod q) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.2 hsq
    obtain ⟨x0, hx0⟩ := exists_quadraticChar_ne_one hF (div_ne_zero hC0 hD0)
    obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := q)) x0
    have hf : (D : ZMod q) * x0 ^ 4 + C = (D : ZMod q) * ((C : ZMod q) / D + x0 ^ 4) := by
      field_simp
      ring
    by_cases hf0 : (D : ZMod q) * x0 ^ 4 + C = 0
    · have hx00 : x0 ≠ 0 := by
        rintro rfl
        simp at hf0
        exact hC0 hf0
      obtain ⟨z, hz⟩ := exists_root_of_zmod
        (Polynomial.C (D : ℤ_[q]) * Polynomial.X ^ 4 + Polynomial.C (C : ℤ_[q])) x
        (by simpa [hx] using hf0)
        (by
          have hd' : (Polynomial.derivative
              (Polynomial.C (D : ℤ_[q]) * Polynomial.X ^ 4 + Polynomial.C (C : ℤ_[q]))).eval x
              = (D : ℤ_[q]) * (4 * x ^ 3) := by
            simp
            norm_num
          have h4 : (4 : ZMod q) ≠ 0 := by
            have : (4 : ZMod q) = 2 * 2 := by norm_num
            rw [this]; exact mul_ne_zero two_ne two_ne
          rw [hd']
          simp only [map_mul, map_pow, map_intCast, map_ofNat, hx]
          exact mul_ne_zero hD0 (mul_ne_zero h4 (pow_ne_zero 3 hx00)))
      refine ⟨0, z, 1, Or.inr one_ne_zero, ?_⟩
      have hz' : (D : ℤ_[q]) * z ^ 4 + C = 0 := by simpa using hz
      have h := congrArg (fun w : ℤ_[q] => (w : ℚ_[q])) hz'
      push_cast at h
      linear_combination -h
    · have hne : quadraticChar (ZMod q) ((C : ZMod q) / D + x0 ^ 4) = -1 := by
        rcases quadraticChar_isQuadratic (ZMod q) ((C : ZMod q) / D + x0 ^ 4) with h | h | h
        · exact absurd (by rw [hf, quadraticChar_eq_zero_iff.1 h, mul_zero]) hf0
        · exact absurd h hx0
        · exact h
      have hsq1 : quadraticChar (ZMod q) ((D : ZMod q) * x0 ^ 4 + C) = 1 := by
        rw [hf, map_mul, hchi, hne]
        norm_num
      obtain ⟨a, ha⟩ := (quadraticChar_one_iff_isSquare hf0).1 hsq1
      have ha0 : a ≠ 0 := by rintro rfl; exact hf0 (by simpa using ha)
      obtain ⟨b, hb⟩ := exists_sq_padicInt_of_zmod hq ((D : ℤ_[q]) * x ^ 4 + C)
        ⟨a, ha0, by
          simp only [map_add, map_mul, map_pow, map_intCast, hx]
          rw [sq]; exact ha⟩
      refine ⟨b, x, 1, Or.inr one_ne_zero, ?_⟩
      have h := congrArg (fun w : ℤ_[q] => (w : ℚ_[q])) hb
      push_cast at h
      linear_combination h

/-- Solvability at an odd prime $q$ for $c = DC$ with $D, C$ prime to $q$. -/
theorem ts_q (hq : q ≠ 2) (c : ℚ) (D C : ℤ) (hD : ¬ (q : ℤ) ∣ D) (hC : ¬ (q : ℤ) ∣ C)
    (hDC : (D : ℚ) * C = c) : TorsorSolvable ℚ_[q] c (D : ℚ) := by
  obtain ⟨N, M, e, hne, h⟩ := exists_point_odd hq D C hD hC
  have hD0 : (D : ℚ) ≠ 0 := by
    intro h0
    have : D = 0 := by exact_mod_cast h0
    exact hD (by rw [this]; exact dvd_zero _)
  have hcD : c / (D : ℚ) = C := by rw [← hDC]; field_simp
  refine ⟨N, M, e, hne, ?_⟩
  rw [hcD]
  push_cast
  exact h

end OddPrime

lemma not_dvd_rep {q p : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) (hp : p.Prime) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (a b : ℕ) : ¬ ((q : ℤ) ∣ s * 2 ^ a * (p : ℤ) ^ b) := by
  intro h
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rcases hqZ.dvd_or_dvd h with h | h
  · rcases hqZ.dvd_or_dvd h with h | h
    · rcases hs with rfl | rfl
      · exact hqZ.not_dvd_one h
      · exact hqZ.not_dvd_one ((dvd_neg).1 h)
    · have := hqZ.dvd_of_dvd_pow h
      have h' : q ∣ 2 := by exact_mod_cast this
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h')
  · have := hqZ.dvd_of_dvd_pow h
    have h' : q ∣ p := by exact_mod_cast this
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 h')

/-- The eight class representatives $s2^ap^b$ ($s = \pm 1$, $a, b < 2$) are solvable at odd $q \ne p$. -/
theorem ts_rep_q {q p : ℕ} [Fact q.Prime] (hp : p.Prime) (hq : q ≠ 2) (hqp : q ≠ p) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (a b : ℕ) (ha : a < 2) (hb : b < 2) :
    TorsorSolvable ℚ_[q] (-4 * (p : ℚ)) (((s * 2 ^ a * (p : ℤ) ^ b : ℤ)) : ℚ) := by
  refine ts_q hq _ (s * 2 ^ a * (p : ℤ) ^ b) (-s * 2 ^ (2 - a) * (p : ℤ) ^ (1 - b))
    (not_dvd_rep Fact.out hq hqp hp s hs a b)
    (not_dvd_rep Fact.out hq hqp hp (-s) (by rcases hs with rfl | rfl <;> simp) (2 - a) (1 - b)) ?_
  rcases hs with rfl | rfl <;> interval_cases a <;> interval_cases b <;> push_cast <;> norm_num <;> ring

/-! ### Squares in $\mathbb Q_q$ -/

lemma isSquare_padic_int (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (n : ℤ) (hn : IsSquare (n : ZMod q))
    (hn0 : (n : ZMod q) ≠ 0) : IsSquare ((n : ℤ) : ℚ_[q]) := by
  obtain ⟨a, ha⟩ := hn
  have ha0 : a ≠ 0 := by rintro rfl; exact hn0 (by simpa using ha)
  obtain ⟨b, hb⟩ := exists_sq_padicInt_of_zmod hq (n : ℤ_[q]) ⟨a, ha0, by rw [map_intCast, ha, sq]⟩
  refine ⟨b, ?_⟩
  have h := congrArg (fun z : ℤ_[q] => (z : ℚ_[q])) hb
  push_cast at h
  rw [← h]; ring

/-- For $p \equiv 1 \bmod 8$, $-1$ and $2$ are squares in $\mathbb Q_p$. -/
lemma isSquare_neg_one_two_padic (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) :
    IsSquare (-1 : ℚ_[p]) ∧ IsSquare (2 : ℚ_[p]) := by
  have hp2 : p ≠ 2 := by omega
  have two_ne : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have h1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have h2 : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff hp2).2 (Or.inl hp8)
  constructor
  · have := isSquare_padic_int p hp2 (-1) (by simpa using h1) (by simp)
    simpa using this
  · have := isSquare_padic_int p hp2 2 (by simpa using h2) (by simpa using two_ne)
    simpa using this

/-! ### Representatives at a place where $-1$ and $2$ are squares -/

/-- At a place where $-1$ and $2$ are squares, all eight representatives are solvable for $c = -4p$. -/
theorem ts_rep_sq {F : Type*} [Field F] [CharZero F] (p : ℕ) (hp0 : (p : ℚ) ≠ 0)
    (hm1 : IsSquare (-1 : F)) (h2 : IsSquare (2 : F)) (s : ℚ) (hs : s = 1 ∨ s = -1) (a b : ℕ)
    (ha : a < 2) (hb : b < 2) : TorsorSolvable F (-4 * (p : ℚ)) (s * 2 ^ a * (p : ℚ) ^ b) := by
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hsa : IsSquare ((s * 2 ^ a : ℚ) : F) := by
    rcases hs with rfl | rfl <;> interval_cases a
    · simp
    · simpa using h2
    · simpa using hm1
    · simpa using hm1.mul h2
  interval_cases b
  · exact ts_of_sq_d _ _ (by simpa using hsa)
  · refine ts_of_sq_cd _ _ ?_
    have hden : s * 2 ^ a ≠ 0 := mul_ne_zero hs0 (pow_ne_zero _ two_ne_zero)
    have e : (-4 * (p : ℚ)) / (s * 2 ^ a * (p : ℚ) ^ 1) = (-1 * 4) / (s * 2 ^ a) := by
      rw [pow_one, div_eq_div_iff (mul_ne_zero hden hp0) hden]
      ring
    rw [e, Rat.cast_div]
    have h4 : IsSquare (((-1 * 4 : ℚ)) : F) := by
      have : (((-1 * 4 : ℚ)) : F) = -1 * (2 * 2) := by norm_num
      rw [this]
      exact hm1.mul (IsSquare.mul_self 2)
    exact h4.div hsa

/-! ### The prime $2$ -/

/-- For $p \equiv 1 \bmod 8$, $p$ is a square in $\mathbb Z_2$. -/
lemma isSquare_nat_two_adic (p : ℕ) (hp8 : p % 8 = 1) : IsSquare (p : ℤ_[2]) := by
  have h : (p : ℤ_[2]) = 8 * ((p / 8 : ℕ) : ℤ_[2]) + 1 := by
    exact_mod_cast (by omega : p = 8 * (p / 8) + 1)
  obtain ⟨b, hb, -⟩ := exists_sq_two_adic_step (p : ℤ_[2]) ⟨((p / 8 : ℕ) : ℤ_[2]), by linear_combination h⟩
  exact ⟨b, by rw [← hb]; ring⟩

/-- For $p \equiv 1 \bmod 8$, $p$ is a square in $\mathbb Q_2$. -/
lemma isSquare_nat_padic_two (p : ℕ) (hp8 : p % 8 = 1) : IsSquare (p : ℚ_[2]) := by
  obtain ⟨b, hb⟩ := isSquare_nat_two_adic p hp8
  refine ⟨b, ?_⟩
  have h := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hb
  push_cast at h
  exact h

/-- For $p \equiv 1 \bmod 8$ there are $N, x \in \mathbb Q_2$ with $N^2 = 2p - 2x^4$ (the quartic of the classes
$-2$ and $2p$): $N = 0$, $x^4 = p$ if $p \equiv 1 \bmod 16$, and $N = 4$, $x^4 = p - 8$ otherwise. -/
theorem two_adic_neg (p : ℕ) (hp8 : p % 8 = 1) :
    ∃ N x : ℚ_[2], N ^ 2 = 2 * (p : ℚ_[2]) - 2 * x ^ 4 := by
  by_cases h16 : p % 16 = 1
  · obtain ⟨x, hx⟩ := exists_mul_fourth_eq_two_adic 1 (p : ℤ) odd_one (by omega)
    refine ⟨0, x, ?_⟩
    have h := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hx
    push_cast at h
    linear_combination 2 * h
  · obtain ⟨x, hx⟩ := exists_mul_fourth_eq_two_adic 1 ((p : ℤ) - 8) odd_one (by omega)
    refine ⟨4, x, ?_⟩
    have h := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hx
    push_cast at h
    have h8 : ((8 : ℤ_[2]) : ℚ_[2]) = 8 := rfl
    linear_combination 2 * h - 2 * h8

/-- The eight class representatives are solvable over $\mathbb Q_2$ for $c = -4p$, $p \equiv 1 \bmod 8$. -/
theorem ts_rep_two (p : ℕ) (hp0 : (p : ℚ) ≠ 0) (hp8 : p % 8 = 1) (s : ℚ) (hs : s = 1 ∨ s = -1)
    (a b : ℕ) (ha : a < 2) (hb : b < 2) :
    TorsorSolvable ℚ_[2] (-4 * (p : ℚ)) (s * 2 ^ a * (p : ℚ) ^ b) := by
  have hsqp : IsSquare (p : ℚ_[2]) := isSquare_nat_padic_two p hp8
  obtain ⟨x, y, hy⟩ := local_point_two p hp8
  obtain ⟨N, z, hN⟩ := two_adic_neg p hp8
  rcases hs with rfl | rfl <;> interval_cases a <;> interval_cases b
  · exact ts_of_sq_d _ _ (by simp)
  · exact ts_of_sq_d _ _ (by simpa using hsqp)
  · refine ts_cast _ _ 2 (-2 * p) (by ring) (by norm_num) (by ring) y 1 x (Or.inl one_ne_zero) ?_
    push_cast; linear_combination hy
  · refine ts_cast _ _ (2 * p) (-2) (by ring) (mul_ne_zero two_ne_zero hp0) (by ring) N 1 z
      (Or.inl one_ne_zero) ?_
    push_cast; linear_combination hN
  · refine ts_of_sq_cd _ _ ?_
    have e : (-4 * (p : ℚ)) / (-1 * 2 ^ 0 * (p : ℚ) ^ 0) = 4 * p := by
      rw [div_eq_iff (by norm_num)]; ring
    rw [e]
    have : ((4 * p : ℚ) : ℚ_[2]) = (2 * 2) * (p : ℚ_[2]) := by push_cast; ring
    rw [this]
    exact (IsSquare.mul_self 2).mul hsqp
  · refine ts_of_sq_cd _ _ ?_
    have e : (-4 * (p : ℚ)) / (-1 * 2 ^ 0 * (p : ℚ) ^ 1) = 4 := by
      rw [div_eq_iff (by simpa using hp0)]; ring
    rw [e]
    exact ⟨2, by norm_num⟩
  · refine ts_cast _ _ (-2) (2 * p) (by ring) (by norm_num) (by ring) N z 1 (Or.inr one_ne_zero) ?_
    push_cast; linear_combination hN
  · refine ts_cast _ _ (-2 * p) 2 (by ring) (mul_ne_zero (by norm_num) hp0) (by ring) y x 1
      (Or.inr one_ne_zero) ?_
    push_cast; linear_combination hy

/-! ### All places -/

/-- For $p \equiv 1 \bmod 8$ the eight class representatives are solvable at every $\mathbb Q_q$ for $c = -4p$. -/
theorem ts_rep_all (p : ℕ) [hpf : Fact p.Prime] (hp8 : p % 8 = 1) (s : ℚ) (hs : s = 1 ∨ s = -1)
    (a b : ℕ) (ha : a < 2) (hb : b < 2) (q : ℕ) [Fact q.Prime] :
    TorsorSolvable ℚ_[q] (-4 * (p : ℚ)) (s * 2 ^ a * (p : ℚ) ^ b) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpf.out.ne_zero
  by_cases hq2 : q = 2
  · subst hq2
    exact ts_rep_two p hp0 hp8 s hs a b ha hb
  · by_cases hqp : q = p
    · subst hqp
      obtain ⟨h1, h2⟩ := isSquare_neg_one_two_padic q hp8
      exact ts_rep_sq q hp0 h1 h2 s hs a b ha hb
    · rcases hs with rfl | rfl
      · have := ts_rep_q (q := q) hpf.out hq2 hqp 1 (Or.inl rfl) a b ha hb
        push_cast at this
        exact this
      · have := ts_rep_q (q := q) hpf.out hq2 hqp (-1) (Or.inr rfl) a b ha hb
        push_cast at this
        exact this

end SelmerExplicit

open SelmerExplicit

/-- **The $x$-coordinate of a rational point lies in the Selmer group.**  The global point
$(N, M, e) = (y/x, 1, 1)$ of $C_x$ works, since $x + c/x = y^2/x^2$. -/
theorem mem_isogenySelmer_of_point {c x y : ℚ} (hx : x ≠ 0) (h : y ^ 2 = x ^ 3 + c * x) :
    x ∈ isogenySelmer c :=
  ⟨hx, fun _ _ => ts_of_point c x y hx h, ts_of_point c x y hx h⟩

/-- **The Selmer group of $\varphi$ on $Y^2 = X^3 + pX$** is the set of classes $\{1, p\}$ (times squares). -/
theorem isogenySelmer_curveP (p : ℕ) [hpf : Fact p.Prime] (hp8 : p % 8 = 1) :
    isogenySelmer p = {d : ℚ | d ≠ 0 ∧ (IsSquare d ∨ IsSquare (p * d))} := by
  have hp : p.Prime := hpf.out
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  ext d
  constructor
  · rintro ⟨hd0, hloc, hreal⟩
    refine ⟨hd0, ?_⟩
    have hdpos : 0 < d := by
      by_contra hneg
      exact not_ts_real_of_neg hp0 (lt_of_le_of_ne (not_lt.1 hneg) hd0) hreal
    have hev : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ ({p} : Finset ℕ) → Even (padicValRat ℓ d) := by
      intro ℓ hℓ hS
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have hne : ℓ ≠ p := by simpa using hS
      by_contra hodd
      exact not_torsorSolvable_of_odd (IsogenyDescent.padicValRat_natCast_prime_ne hℓ hp hne) hp0.ne' hd0
        hodd (hloc ℓ)
    have hvpp : padicValRat p (p : ℚ) = 1 := padicValRat.self hp.one_lt
    rcases Int.emod_two_eq_zero_or_one (padicValRat p d) with he | ho
    · left
      have := isSquare_mul_of_parity {p} hd0 one_ne_zero (by simp [hdpos.not_gt])
        (by
          intro q hq
          rw [Finset.mem_singleton] at hq
          subst hq
          rw [padicValRat.one]
          exact IsogenyDescent.zmod2_cast_eq (by simpa using he))
        (fun ℓ hℓ hS => ⟨hev ℓ hℓ hS, by rw [padicValRat.one]; exact ⟨0, by simp⟩⟩)
      simpa using this
    · right
      have := isSquare_mul_of_parity {p} hd0 hp0.ne' (by simp [hdpos.not_gt, hp0.not_gt])
        (by
          intro q hq
          rw [Finset.mem_singleton] at hq
          subst hq
          rw [hvpp]
          exact IsogenyDescent.zmod2_cast_eq (by simpa using ho))
        (fun ℓ hℓ hS => ⟨hev ℓ hℓ hS, by
          rw [IsogenyDescent.padicValRat_natCast_prime_ne hℓ hp (by simpa using hS)]
          exact ⟨0, by simp⟩⟩)
      rwa [mul_comm] at this
  · rintro ⟨hd0, hsq⟩
    have key : ∀ (F : Type) [Field F] [CharZero F], TorsorSolvable F p d := by
      intro F _ _
      rcases hsq with h | ⟨m, hm⟩
      · exact ts_of_sq_d _ _ (isSquare_cast h)
      · refine ts_of_sq_cd _ _ (isSquare_cast ?_)
        refine ⟨m / d, ?_⟩
        rw [div_mul_div_comm, ← hm]
        field_simp
    exact ⟨hd0, fun q _ => key _, key ℝ⟩

/-- **The Selmer group of $\hat\varphi$ on $Y^2 = X^3 - 4pX$** consists of the eight classes
$\pm 1, \pm 2, \pm p, \pm 2p$ (times squares): every class allowed by the support is everywhere locally
solvable. -/
theorem isogenySelmer_curvePDual (p : ℕ) [hpf : Fact p.Prime] (hp8 : p % 8 = 1) :
    isogenySelmer (-4 * p) =
      {d | d ≠ 0 ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p → Even (padicValRat ℓ d)} := by
  have hp : p.Prime := hpf.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : p ≠ 2 := by omega
  ext d
  constructor
  · rintro ⟨hd0, hloc, -⟩
    refine ⟨hd0, fun ℓ hℓ h2 hlp => ?_⟩
    have : Fact ℓ.Prime := ⟨hℓ⟩
    by_contra hodd
    exact not_torsorSolvable_of_odd (padicValRat_neg_four_mul hℓ hp h2 hlp)
      (mul_ne_zero (by norm_num) hp0) hd0 hodd (hloc ℓ)
  · rintro ⟨hd0, hev⟩
    obtain ⟨s, e₂, eₚ, hs, h2, hp2', hsq⟩ := IsogenyDescent.exists_class (p := p) hp2 hd0 hev
    have hr : s * 2 ^ e₂ * (p : ℚ) ^ eₚ ≠ 0 := by
      have : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
      positivity
    have hneg : (-4 * (p : ℚ)) < 0 := by
      have : (0 : ℚ) < p := by exact_mod_cast hp.pos
      linarith
    refine ⟨hd0, fun q _ => ?_, ts_real_of_neg hneg hd0⟩
    exact ts_of_isSquare_mul _ d _ hd0 hr hsq (ts_rep_all p hp8 s hs e₂ eₚ h2 hp2' q)

/-- **Proposition 8.1** (Milne, *Elliptic Curves*, Ch. IV, pdf p. 151; Silverman X.4.9, X.6.2) for a prime
$p \equiv 1 \bmod 8$: the Selmer group of $\varphi$ on $Y^2 = X^3 + pX$ is $\{1, p\}\,\mathbb Q^{\times 2}$, and the
Selmer group of $\hat\varphi$ on $Y^2 = X^3 - 4pX$ is the set of the eight classes $\pm 1, \pm 2, \pm p, \pm 2p$.
Here the Selmer groups are defined by local solvability of the quartic torsors (`isogenySelmer`). -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.1, pdf p. 151"]
theorem prop_8_1_explicit (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) :
    isogenySelmer p = {d : ℚ | d ≠ 0 ∧ (IsSquare d ∨ IsSquare (p * d))} ∧
    isogenySelmer (-4 * p) =
      {d | d ≠ 0 ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p → Even (padicValRat ℓ d)} :=
  ⟨isogenySelmer_curveP p hp8, isogenySelmer_curvePDual p hp8⟩

end NumberFieldKB.MilneEC
