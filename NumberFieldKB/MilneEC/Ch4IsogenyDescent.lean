import NumberFieldKB.MilneEC.Ch4bStatements
import NumberFieldKB.MilneEC.Ch4bHasse
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Milne, *Elliptic Curves*, Chapter IV §8: descent by the 2-isogeny for $Y^2 = X^3 + pX$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Propositions 8.1 and 8.2
(pdf pp. 151–152), which Milne quotes from Silverman (1986), Proposition X.6.2.  Locators give the pdf page of the
text `ectext6` (printed page = pdf page − 8).

For a prime $p \equiv 1 \bmod 8$ such that $2$ is not a fourth power modulo $p$, the curve
$E : Y^2 = X^3 + pX$ (`curveP p`) has rank $0$ (`rank_curveP_eq_zero`), the first half of Proposition 8.2.  The
proof is the descent by the $2$-isogeny $\varphi : E \to E'$, $E' : Y^2 = X^3 - 4pX$ (`curvePDual p`), and its dual
$\hat\varphi : E' \to E$, $\hat\varphi(X, Y) = \bigl(Y^2/4X^2,\ Y(-4p - X^2)/8X^2\bigr)$ (Silverman X.4.9).

The argument does not use that $\varphi$ and $\hat\varphi$ are homomorphisms.  It uses only explicit formulas:
* translation by $T = (0, 0)$ on $E$ sends $x$ to $p/x$, and by $T' = (0, 0)$ on $E'$ sends $X$ to $-4p/X$, with
  $\hat\varphi(Q + T') = \hat\varphi(Q)$;
* if $x(P) = s^2$ then $P = \hat\varphi(Q)$ for an explicit $Q \in E'(\mathbb Q)$;
* if $X(Q) = t^2$ then $\hat\varphi(Q) = 2R$ for an explicit $R \in E(\mathbb Q)$ (the preimage of $Q$ under $\varphi$);
* **the images of the connecting maps** $x \bmod \mathbb Q^{\times 2}$:
  - for $E$, $x \in \{1, p\}\,\mathbb Q^{\times 2}$ (sign and valuations: `curveP_class`);
  - for $E'$, $X \in \{1, -p\}\,\mathbb Q^{\times 2}$ (`curvePDual_class`).

  The local conditions leave the eight classes $\pm 1, \pm 2, \pm p, \pm 2p$ for $E'$ (all of them are in the
  Selmer group $S^{(\hat\varphi)}(E'/\mathbb Q)$). Three classes are excluded **globally**, each by a quartic
  with no rational point:
  - $2$: $Y^2 = 2 - 2pX^4$ (Milne's Remark 8.4, `remark_8_4_no_rational_point`);
  - $-2$: $Y^2 = 2pX^4 - 2$, by the reciprocity argument of `hasse_core` with $-2$ in place of $2$
    (`hasse_core_neg_two`);
  - $p$: $Y^2 = pX^4 - 4$, by factoring $n^2 + 4m^4 = pe^4$ in $\mathbb Z[i]$: $n + 2m^2 i = u\,\pi\,\delta^4$ with
    $\delta^4 \equiv 1 \bmod 8$, so $2m^2 \equiv \pm b \bmod 8$ where $p = a^2 + b^2$, $a$ odd. Gauss's criterion
    (`gaussQuarticCriterion_holds`) gives $b \equiv 4 \bmod 8$ (`no_rat_point_p_quartic`).

  The other three classes $-2p, 2p, -1$ are translates of these by $T'$.

Hence $E(\mathbb Q) = 2E(\mathbb Q) \cup (T + 2E(\mathbb Q))$ (`curveP_mem_multiples_or`). So
$\#E(\mathbb Q)/2E(\mathbb Q) \le 2$, $E(\mathbb Q)$ is finitely generated (`fg_of_finite_quotient_two`), and
$2^{r+1} \le 2$.
-/

open WeierstrassCurve WeierstrassCurve.Affine

set_option backward.isDefEq.respectTransparency false

namespace NumberFieldKB.MilneEC

/-- The curve $E' : Y^2 = X^3 - 4pX$, the target of the $2$-isogeny $\varphi$ from Milne's curve
$E : Y^2 = X^3 + pX$ of Proposition 8.1 (Silverman 1986, X.4.9 and X.6.2). -/
def curvePDual (p : ℕ) : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -4 * p, a₆ := 0 }

theorem curvePDual_Δ (p : ℕ) : (curvePDual p).Δ = 4096 * (p : ℚ) ^ 3 := by
  simp only [curvePDual, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- For $p \ne 0$ the curve $Y^2 = X^3 - 4pX$ is elliptic (its discriminant is $4096p^3$). -/
theorem curvePDual_isElliptic {p : ℕ} (hp : p ≠ 0) : (curvePDual p).IsElliptic :=
  ⟨isUnit_iff_ne_zero.2 (by rw [curvePDual_Δ]; simp [hp])⟩

namespace IsogenyDescent

variable {p : ℕ}

/-! ### The two curves -/

theorem curveP_equation_iff {x y : ℚ} : (curveP p).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + p * x := by
  rw [Affine.equation_iff]
  simp only [curveP]
  constructor <;> intro h <;> linear_combination h

theorem curvePDual_equation_iff {x y : ℚ} :
    (curvePDual p).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - 4 * p * x := by
  rw [Affine.equation_iff]
  simp only [curvePDual]
  constructor <;> intro h <;> linear_combination h

theorem curveP_negY (x y : ℚ) : (curveP p).toAffine.negY x y = -y := by
  simp only [Affine.negY, curveP]
  ring

theorem curvePDual_negY (x y : ℚ) : (curvePDual p).toAffine.negY x y = -y := by
  simp only [Affine.negY, curvePDual]
  ring

theorem curveP_nonsingular (hp : p ≠ 0) {x y : ℚ} (h : y ^ 2 = x ^ 3 + p * x) :
    (curveP p).toAffine.Nonsingular x y := by
  have := curveP_isElliptic hp
  exact (Affine.equation_iff_nonsingular).1 (curveP_equation_iff.2 h)

theorem curvePDual_nonsingular (hp : p ≠ 0) {x y : ℚ} (h : y ^ 2 = x ^ 3 - 4 * p * x) :
    (curvePDual p).toAffine.Nonsingular x y := by
  have := curvePDual_isElliptic hp
  exact (Affine.equation_iff_nonsingular).1 (curvePDual_equation_iff.2 h)

theorem some_eq_some {W : Affine ℚ} {x y x' y' : ℚ} {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') : Point.some x y h = Point.some x' y' h' := by
  subst hx hy
  rfl

/-- Translation by $T = (0, 0)$ on $E : Y^2 = X^3 + pX$: $(x, y) + T = (p/x, -py/x^2)$. -/
theorem curveP_add_T (hp : p ≠ 0) {x y : ℚ} (h : (curveP p).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    Point.some x y h + Point.some 0 0 (curveP_nonsingular hp (by ring)) =
      Point.some (p / x) (-(p * y) / x ^ 2)
        (curveP_nonsingular hp (by
          have hy := curveP_equation_iff.1 h.1
          have hpx : (p : ℚ) = (y ^ 2 - x ^ 3) / x := by
            rw [eq_div_iff hx]; linear_combination -hy
          rw [hpx]; field_simp; ring)) := by
  have hy := curveP_equation_iff.1 h.1
  have hpx : (p : ℚ) = (y ^ 2 - x ^ 3) / x := by
    rw [eq_div_iff hx]; linear_combination -hy
  rw [Point.add_of_X_ne hx]
  apply some_eq_some
  · rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, curveP]
    rw [hpx]; field_simp; ring
  · rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, curveP]
    rw [hpx]; field_simp; ring

/-- Translation by $T' = (0, 0)$ on $E' : Y^2 = X^3 - 4pX$: $(X, Y) + T' = (-4p/X, 4pY/X^2)$. -/
theorem curvePDual_add_T (hp : p ≠ 0) {x y : ℚ} (h : (curvePDual p).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ∃ h' : (curvePDual p).toAffine.Nonsingular (-4 * p / x) (4 * p * y / x ^ 2),
      Point.some x y h + Point.some 0 0 (curvePDual_nonsingular hp (by ring)) = Point.some _ _ h' := by
  have hy := curvePDual_equation_iff.1 h.1
  have hpx : (p : ℚ) = (x ^ 3 - y ^ 2) / (4 * x) := by
    rw [eq_div_iff (mul_ne_zero four_ne_zero hx)]; linear_combination hy
  refine ⟨curvePDual_nonsingular hp (by rw [hpx]; field_simp; ring), ?_⟩
  rw [Point.add_of_X_ne hx]
  apply some_eq_some
  · rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, curvePDual]
    rw [hpx]; field_simp; ring
  · rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, curvePDual]
    rw [hpx]; field_simp; ring

/-! ### Halving: $\hat\varphi(Q) = 2R$ when $X(Q)$ is a square -/

/-- **Halving through the isogeny.** Let $(X, Y) \in E'(\mathbb Q)$ with $X = t^2 \ne 0$.  Then
$\hat\varphi(X, Y) = (Y^2/4X^2, Y(-4p - X^2)/8X^2)$ is $2R$ for $R = (\rho, t\rho)$, $\rho = (t^3 - Y)/2t$ (the point
with $\varphi(R) = (X, Y)$). -/
theorem exists_two_zsmul_eq_of_dual (hp : p ≠ 0) {X Y t : ℚ} (ht : t ≠ 0) (hX : X = t ^ 2)
    (hE : Y ^ 2 = X ^ 3 - 4 * p * X) (h : (curveP p).toAffine.Nonsingular (Y ^ 2 / (4 * X ^ 2))
      (Y * (-4 * p - X ^ 2) / (8 * X ^ 2))) :
    ∃ R : (curveP p).toAffine.Point, (2 : ℤ) • R = Point.some _ _ h := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  subst hX
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℚ, ρ = (t ^ 3 - Y) / (2 * t) := ⟨_, rfl⟩
  have hY : Y = t ^ 3 - 2 * t * ρ := by rw [hρ]; field_simp; ring
  have hpρ : (p : ℚ) = t ^ 2 * ρ - ρ ^ 2 := by
    have : (4 : ℚ) * t ^ 2 * p = 4 * t ^ 2 * (t ^ 2 * ρ - ρ ^ 2) := by
      rw [hY] at hE; linear_combination hE
    have ht2 : (4 : ℚ) * t ^ 2 ≠ 0 := by positivity
    exact mul_left_cancel₀ ht2 this
  have hρ0 : ρ ≠ 0 := by
    intro h0; exact hp' (by rw [hpρ, h0]; ring)
  have hR : (t * ρ) ^ 2 = ρ ^ 3 + p * ρ := by rw [hpρ]; ring
  have hns := curveP_nonsingular hp hR
  have hne : t * ρ ≠ (curveP p).toAffine.negY ρ (t * ρ) := by
    rw [curveP_negY]
    intro h'
    have : t * ρ = 0 := by linarith
    exact mul_ne_zero ht hρ0 this
  refine ⟨Point.some ρ (t * ρ) hns, ?_⟩
  rw [two_zsmul, Point.add_self_of_Y_ne hne]
  apply some_eq_some
  · rw [Affine.slope_of_Y_ne rfl hne, curveP_negY]
    simp only [Affine.addX, curveP]
    rw [hY, hpρ]
    field_simp
    ring
  · rw [Affine.slope_of_Y_ne rfl hne, curveP_negY]
    simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, curveP]
    rw [hY, hpρ]
    field_simp
    ring

/-- **Lifting through $\hat\varphi$.** If $(x, y) \in E(\mathbb Q)$ with $x = s^2 \ne 0$, then
$Q = (2k/s, 4k)$, $k = s^3 - y$, lies on $E'$ with $X(Q) \ne 0$ and $\hat\varphi(Q) = (x, y)$. -/
theorem lift_dual (hp : p ≠ 0) {x y s X Y : ℚ} (hs : s ≠ 0) (hx : x = s ^ 2) (hE : y ^ 2 = x ^ 3 + p * x)
    (hX : X = 2 * (s ^ 3 - y) / s) (hY : Y = 4 * (s ^ 3 - y)) :
    X ≠ 0 ∧ Y ^ 2 = X ^ 3 - 4 * p * X ∧ x = Y ^ 2 / (4 * X ^ 2) ∧ y = Y * (-4 * p - X ^ 2) / (8 * X ^ 2) := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  subst hx hX hY
  have hk : s ^ 3 - y ≠ 0 := by
    intro h0
    have : y = s ^ 3 := by linarith
    rw [this] at hE
    have : (p : ℚ) * s ^ 2 = 0 := by linear_combination -hE
    exact mul_ne_zero hp' (pow_ne_zero 2 hs) this
  have hpe : (p : ℚ) = (y ^ 2 - s ^ 6) / s ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hs)]; linear_combination -hE
  refine ⟨div_ne_zero (mul_ne_zero two_ne_zero hk) hs, ?_, ?_, ?_⟩
  · rw [hpe]; field_simp; ring
  · field_simp; ring
  · rw [hpe]; field_simp; ring

/-- $\hat\varphi(Q + T') = \hat\varphi(Q)$, in coordinates. -/
theorem dual_translate (hp : p ≠ 0) {X Y : ℚ} (hX : X ≠ 0) :
    (4 * p * Y / X ^ 2) ^ 2 / (4 * (-4 * p / X) ^ 2) = Y ^ 2 / (4 * X ^ 2) ∧
      (4 * p * Y / X ^ 2) * (-4 * p - (-4 * p / X) ^ 2) / (8 * (-4 * p / X) ^ 2) =
        Y * (-4 * p - X ^ 2) / (8 * X ^ 2) := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  constructor
  · field_simp
  · field_simp
    ring

/-! ### Valuations of the abscissa -/

/-- If $y^2 = x(x^2 + c)$ with $v_\ell(c) = 0$ and $x \ne 0$, then $v_\ell(x)$ is even. -/
theorem even_padicValRat_of_eq (ℓ : ℕ) [Fact ℓ.Prime] {c x y : ℚ} (hc : c ≠ 0) (hvc : padicValRat ℓ c = 0)
    (hx : x ≠ 0) (h : y ^ 2 = x * (x ^ 2 + c)) : Even (padicValRat ℓ x) := by
  rw [Int.even_iff]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hv2 : padicValRat ℓ (x ^ 2) = 2 * padicValRat ℓ x := by
    rw [padicValRat.pow _]; push_cast; ring
  by_cases hxc : x ^ 2 + c = 0
  · have : padicValRat ℓ (x ^ 2) = padicValRat ℓ c := by
      rw [show x ^ 2 = -c by linarith, padicValRat.neg]
    omega
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : x * (x ^ 2 + c) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hx h1
    · exact hxc h1
  have hval : 2 * padicValRat ℓ y = padicValRat ℓ x + padicValRat ℓ (x ^ 2 + c) := by
    have := congrArg (padicValRat ℓ) h
    rw [padicValRat.pow _, padicValRat.mul hx hxc] at this
    push_cast at this
    linarith
  rcases lt_trichotomy (padicValRat ℓ x) 0 with hlt | heq | hgt
  · have := padicValRat.add_eq_of_lt (p := ℓ) hxc hx2 hc (by omega)
    omega
  · omega
  · have := padicValRat.add_eq_of_lt (p := ℓ) (by rwa [add_comm]) hc hx2 (by omega)
    rw [add_comm] at this
    omega

theorem padicValRat_natCast_prime_ne {ℓ q : ℕ} (hℓ : ℓ.Prime) (hq : q.Prime) (hne : ℓ ≠ q) :
    padicValRat ℓ (q : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [padicValNat.eq_zero_of_not_dvd]
  · rfl
  · intro hd
    exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hq).1 hd)

theorem zmod2_cast_eq {a b : ℤ} (h : a % 2 = b % 2) : ((a : ℤ) : ZMod 2) = ((b : ℤ) : ZMod 2) :=
  (ZMod.intCast_eq_intCast_iff' a b 2).2 (by exact_mod_cast h)

/-- **The image of $E(\mathbb Q)$ in $\mathbb Q^\times/\mathbb Q^{\times 2}$** (the connecting map of $\varphi$):
for $(x, y) \in E(\mathbb Q)$, $E : Y^2 = X^3 + pX$, with $x \ne 0$, the class of $x$ is $1$ or $p$. -/
theorem curveP_class (hp : p.Prime) {x y : ℚ} (hx : x ≠ 0) (h : y ^ 2 = x ^ 3 + p * x) :
    IsSquare x ∨ IsSquare (p * x) := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hxpos : 0 < x := by
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exfalso
      have : x * (x ^ 2 + p) < 0 := mul_neg_of_neg_of_pos hlt (by positivity)
      nlinarith [sq_nonneg y]
    · exact hgt
  have hev : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ ({p} : Finset ℕ) → Even (padicValRat ℓ x) := by
    intro ℓ hℓ hS
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hne : ℓ ≠ p := by simpa using hS
    exact even_padicValRat_of_eq ℓ (c := p) (y := y) hp0.ne' (padicValRat_natCast_prime_ne hℓ hp hne) hx
      (by linear_combination h)
  have hvpp : padicValRat p (p : ℚ) = 1 := padicValRat.self hp.one_lt
  rcases Int.emod_two_eq_zero_or_one (padicValRat p x) with he | ho
  · left
    have := isSquare_mul_of_parity {p} hx one_ne_zero (by simp [hxpos.not_gt])
      (by
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        rw [padicValRat.one]
        exact zmod2_cast_eq (by simpa using he))
      (fun ℓ hℓ hS => ⟨hev ℓ hℓ hS, by rw [padicValRat.one]; exact ⟨0, by simp⟩⟩)
    simpa using this
  · right
    have := isSquare_mul_of_parity {p} hx hp0.ne' (by simp [hxpos.not_gt, hp0.not_gt])
      (by
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        rw [hvpp]
        exact zmod2_cast_eq (by simpa using ho))
      (fun ℓ hℓ hS => ⟨hev ℓ hℓ hS, by
        rw [padicValRat_natCast_prime_ne hℓ hp (by simpa using hS)]; exact ⟨0, by simp⟩⟩)
    rwa [mul_comm] at this

/-! ### The class $-2$: the quartic $Y^2 = 2pX^4 - 2$ has no rational point -/

/-- The argument of `hasse_core` (Milne, Remark 8.4, pdf p. 154) with $-2$ in place of $2$: if $p \equiv 1 \bmod 8$
and coprime integers $r, t$ and an integer $s$ satisfy $-2s^2 = t^4 - pr^4$, then $-2$ is a fourth power modulo $p$.
The odd part $s'$ of $s$ has $(p/s') = 1$, so $s'$, and then $s$, is a square modulo $p$; and
$-2 = (t^2/s)^2$. -/
theorem hasse_core_neg_two (p : ℕ) [hpf : Fact p.Prime] (h8 : p % 8 = 1) (r t s : ℤ) (hcop : IsCoprime r t)
    (h : -2 * s ^ 2 = t ^ 4 - p * r ^ 4) : ∃ x : ZMod p, x ^ 4 = -2 := by
  have hp : p.Prime := hpf.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h' : 2 * s ^ 2 = p * r ^ 4 - t ^ 4 := by linarith
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro hd
    have h1 : p ∣ 2 := by exact_mod_cast hd
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 := hp.two_le
    omega
  have hpt : ¬ (p : ℤ) ∣ t := by
    intro hd
    have h1 : (p : ℤ) ∣ 2 * s ^ 2 := by
      rw [h']; exact dvd_sub (dvd_mul_right _ _) (dvd_pow hd (by norm_num))
    have h2 : (p : ℤ) ∣ s := by
      rcases hpZ.dvd_or_dvd h1 with h | h
      · exact absurd h hp2
      · exact hpZ.dvd_of_dvd_pow h
    obtain ⟨a, ha⟩ := h2
    obtain ⟨b, hb⟩ := hd
    have h3 : (p : ℤ) * r ^ 4 = (p : ℤ) * ((p : ℤ) * (2 * a ^ 2 + (p : ℤ) ^ 2 * b ^ 4)) := by
      rw [ha, hb] at h'
      linear_combination -h'
    have h4 : r ^ 4 = (p : ℤ) * (2 * a ^ 2 + (p : ℤ) ^ 2 * b ^ 4) :=
      mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero) h3
    have h5 : (p : ℤ) ∣ r := hpZ.dvd_of_dvd_pow (⟨_, h4⟩ : (p : ℤ) ∣ r ^ 4)
    exact hpZ.not_isUnit (hcop.isUnit_of_dvd' h5 ⟨b, hb⟩)
  have hps : ¬ (p : ℤ) ∣ s := by
    intro hd
    apply hpt
    have h1 : (p : ℤ) ∣ t ^ 4 := by
      have e : t ^ 4 = p * r ^ 4 - 2 * s ^ 2 := by linarith
      rw [e]
      exact dvd_sub (dvd_mul_right _ _) (Dvd.dvd.mul_left (dvd_pow hd (by norm_num)) _)
    exact hpZ.dvd_of_dvd_pow h1
  have hrs : IsCoprime r s := by
    have h1 : IsCoprime r (-(2 * s ^ 2) + r * (p * r ^ 3)) := by
      have e : -(2 * s ^ 2) + r * (p * r ^ 3) = t ^ 4 := by linear_combination -h'
      rw [e]; exact hcop.pow_right
    have h2 : IsCoprime r (-(2 * s ^ 2)) := IsCoprime.add_mul_left_right_iff.mp h1
    have h3 : IsCoprime r (2 * s ^ 2) := IsCoprime.neg_right_iff _ _ |>.mp h2
    exact (IsCoprime.pow_right_iff (by norm_num)).mp (IsCoprime.of_mul_right_right h3)
  have htp : IsCoprime t (p : ℤ) :=
    ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hpt).symm
  have hts : IsCoprime t s := by
    have h1 : IsCoprime t ((p : ℤ) * r ^ 4) := htp.mul_right hcop.symm.pow_right
    have e : (p : ℤ) * r ^ 4 = 2 * s ^ 2 + t * t ^ 3 := by linear_combination -h'
    rw [e] at h1
    have h3 : IsCoprime t (2 * s ^ 2) := IsCoprime.add_mul_left_right_iff.mp h1
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
      rw [← h]; exact Dvd.dvd.mul_left (dvd_pow hs'dvd two_ne_zero) (-2)
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
  have hmod : (-2 : ZMod p) * ((s : ℤ) : ZMod p) ^ 2 = ((t : ℤ) : ZMod p) ^ 4 := by
    have := congrArg (Int.cast : ℤ → ZMod p) h
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this
  refine ⟨((t : ℤ) : ZMod p) / v, ?_⟩
  rw [div_pow, div_eq_iff (pow_ne_zero 4 hv0)]
  rw [hv] at hmod
  linear_combination -hmod

/-- For $p \equiv 1 \bmod 8$: if $-2$ is a fourth power modulo $p$, so is $2$ (since $(-1)^{(p-1)/4} = 1$). -/
theorem fourth_power_two_of_neg_two (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 1) (h : ∃ x : ZMod p, x ^ 4 = -2) :
    ∃ x : ZMod p, x ^ 4 = 2 := by
  rw [gauss_fourth_pow_iff p h8]
  obtain ⟨x, hx⟩ := h
  have hp2 : p ≠ 2 := by omega
  have h20 : (-2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) = 0 := by linear_combination -h0
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply h20
    rw [← hx]; ring
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 8 * k := ⟨p / 8, by omega⟩
  have hk4 : (p - 1) / 4 = 2 * k := by omega
  have h1 : (-2 : ZMod p) ^ (2 * k) = 1 := by
    rw [← hx, ← pow_mul, show 4 * (2 * k) = p - 1 by omega, ZMod.pow_card_sub_one_eq_one hx0]
  rw [hk4]
  have : (-2 : ZMod p) ^ (2 * k) = (2 : ZMod p) ^ (2 * k) := by
    rw [pow_mul, pow_mul]; ring
  rw [← this, h1]

/-- **The quartic $Y^2 = 2pX^4 - 2$ has no rational point** when $p \equiv 1 \bmod 8$ and $2$ is not a fourth power
modulo $p$ (the class $-2$ of the Selmer group $S^{(\hat\varphi)}(E'/\mathbb Q)$ is not in the image of $E'(\mathbb Q)$). -/
theorem no_rat_point_neg_two_quartic (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 1) (h2 : ∀ x : ZMod p, x ^ 4 ≠ 2)
    (x y : ℚ) : y ^ 2 ≠ 2 * p * x ^ 4 - 2 := by
  intro hxy
  have hx : x * (x.den : ℚ) = x.num := Rat.mul_den_eq_num x
  have hN : ((2 * p * x.num ^ 4 - 2 * (x.den : ℤ) ^ 4 : ℤ) : ℚ) = (y * (x.den : ℚ) ^ 2) ^ 2 := by
    push_cast
    rw [← hx]
    have e : (y * (x.den : ℚ) ^ 2) ^ 2 = y ^ 2 * (x.den : ℚ) ^ 4 := by ring
    rw [e, hxy]; ring
  have hsq : IsSquare (2 * p * x.num ^ 4 - 2 * (x.den : ℤ) ^ 4) := by
    rw [← Rat.isSquare_intCast_iff, hN]; exact ⟨y * (x.den : ℚ) ^ 2, sq _⟩
  obtain ⟨m, hm⟩ := hsq
  have hev : Even (m * m) := ⟨p * x.num ^ 4 - (x.den : ℤ) ^ 4, by linarith⟩
  have hmeven : Even m := (Int.even_mul.mp hev).elim id id
  obtain ⟨s, hs⟩ := hmeven
  have key : -2 * s ^ 2 = (x.den : ℤ) ^ 4 - p * x.num ^ 4 := by
    subst hs; linarith
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using x.reduced
  obtain ⟨z, hz⟩ := fourth_power_two_of_neg_two p h8 (hasse_core_neg_two p h8 x.num x.den s hcop key)
  exact h2 z hz

/-! ### The class $p$: the quartic $Y^2 = pX^4 - 4$ has no rational point -/

theorem dvd8_of_zmod {a : ℤ} (h : (a : ZMod 8) = 0) : (8 : ℤ) ∣ a := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd a 8).1 h
  exact_mod_cast this

/-- Fourth powers of Gaussian integers of odd norm are $\equiv 1 \bmod 8$: for $c^2 + e^2$ odd,
$\mathrm{Re}((c + ei)^4) \equiv 1$ and $\mathrm{Im}((c + ei)^4) \equiv 0 \pmod 8$. -/
theorem fourth_pow_mod_eight {c e : ℤ} (h : Odd (c ^ 2 + e ^ 2)) :
    8 ∣ (c ^ 2 - e ^ 2) ^ 2 - 4 * c ^ 2 * e ^ 2 - 1 ∧ 8 ∣ 4 * c * e * (c ^ 2 - e ^ 2) := by
  have key : ∀ c1 e1 : ZMod 8,
      ((2 * c1) ^ 2 - (2 * e1 + 1) ^ 2) ^ 2 - 4 * (2 * c1) ^ 2 * (2 * e1 + 1) ^ 2 - 1 = 0 ∧
        4 * (2 * c1) * (2 * e1 + 1) * ((2 * c1) ^ 2 - (2 * e1 + 1) ^ 2) = 0 := by decide
  have key' : ∀ c1 e1 : ZMod 8,
      ((2 * c1 + 1) ^ 2 - (2 * e1) ^ 2) ^ 2 - 4 * (2 * c1 + 1) ^ 2 * (2 * e1) ^ 2 - 1 = 0 ∧
        4 * (2 * c1 + 1) * (2 * e1) * ((2 * c1 + 1) ^ 2 - (2 * e1) ^ 2) = 0 := by decide
  have hpar : (Even c ∧ Odd e) ∨ (Odd c ∧ Even e) := by
    rcases Int.even_or_odd c with hc | hc <;> rcases Int.even_or_odd e with he | he
    · exfalso
      have : Even (c ^ 2 + e ^ 2) :=
        Even.add ((Int.even_pow' two_ne_zero).2 hc) ((Int.even_pow' two_ne_zero).2 he)
      exact (Int.not_even_iff_odd.2 h) this
    · exact Or.inl ⟨hc, he⟩
    · exact Or.inr ⟨hc, he⟩
    · exfalso
      have : Even (c ^ 2 + e ^ 2) := Odd.add_odd (Odd.pow hc) (Odd.pow he)
      exact (Int.not_even_iff_odd.2 h) this
  rcases hpar with ⟨⟨c1, rfl⟩, ⟨e1, rfl⟩⟩ | ⟨⟨c1, rfl⟩, ⟨e1, rfl⟩⟩
  · obtain ⟨k1, k2⟩ := key c1 e1
    constructor
    · exact dvd8_of_zmod (by push_cast; rw [← two_mul]; exact k1)
    · exact dvd8_of_zmod (by push_cast; rw [← two_mul]; exact k2)
  · obtain ⟨k1, k2⟩ := key' c1 e1
    constructor
    · exact dvd8_of_zmod (by push_cast; rw [← two_mul]; exact k1)
    · exact dvd8_of_zmod (by push_cast; rw [← two_mul]; exact k2)

/-- A Gaussian integer of prime norm is irreducible. -/
theorem irreducible_of_norm_prime {π : GaussianInt} {p : ℕ} (hp : p.Prime) (hπ : π.norm = p) :
    Irreducible π := by
  refine irreducible_iff.2 ⟨fun hu => ?_, fun x y hxy => ?_⟩
  · have := (Zsqrtd.norm_eq_one_iff.2 hu)
    rw [hπ] at this
    simp at this
    exact hp.one_lt.ne' this
  · have hn : (x.norm.natAbs) * (y.norm.natAbs) = p := by
      have := congrArg (fun z : GaussianInt => z.norm.natAbs) hxy
      simp only [Zsqrtd.norm_mul, Int.natAbs_mul, hπ, Int.natAbs_natCast] at this
      exact this.symm
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ ⟨_, hn.symm⟩) with h1 | h1
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.1 h1)
    · right
      apply Zsqrtd.norm_eq_one_iff.1
      rw [h1] at hn
      have := hp.pos
      nlinarith [hn]

/-- **The Gaussian-integer step** for the class $p$: if $N^2 + 4t^4 = pr^4$ with $N$, $r$ odd and
$\gcd(N, 2t^2) = 1$, and $p = a^2 + b^2$ with $a$ odd, then $2t^2 \equiv \pm b \pmod 8$.  Proof: in $\mathbb Z[i]$,
$z = N + 2t^2 i$ and $\bar z$ are coprime with $z\bar z = pr^4$; a prime $\rho \in \{a \pm bi\}$ divides $z$, and
$z = \rho\,u\,\delta^4$ with $u$ a unit; $\delta^4 \equiv 1 \bmod 8$, and $u = \pm 1$ since $N$ is odd. -/
theorem gaussian_step {p : ℕ} (hp : p.Prime) {a b N t r : ℤ} (hpab : (p : ℤ) = a ^ 2 + b ^ 2) (hb : Even b)
    (hN : Odd N) (hr : Odd r) (hcop : IsCoprime N (2 * t ^ 2)) (h : N ^ 2 + 4 * t ^ 4 = p * r ^ 4) :
    8 ∣ 2 * t ^ 2 - b ∨ 8 ∣ 2 * t ^ 2 + b := by
  set z : GaussianInt := ⟨N, 2 * t ^ 2⟩ with hz
  set π : GaussianInt := ⟨a, b⟩ with hπ
  have hzz : z * star z = (((p : ℤ) * r ^ 4 : ℤ) : GaussianInt) := by
    ext
    · simp only [hz, Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.re_intCast]
      linear_combination h
    · simp only [hz, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.im_intCast]
      ring
  have hππ : π * star π = (((p : ℤ) : ℤ) : GaussianInt) := by
    ext
    · simp only [hπ, Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.re_intCast]
      linear_combination -hpab
    · simp only [hπ, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.im_intCast]
      ring
  have hπnorm : π.norm = p := by rw [Zsqrtd.norm_def, hpab]; simp [hπ]; ring
  have hπprime : Prime π := (irreducible_of_norm_prime hp hπnorm).prime
  have hdvd : π ∣ z * star z := ⟨star π * (r : GaussianInt) ^ 4, by
    rw [hzz, ← mul_assoc, hππ]; push_cast; ring⟩
  -- a prime of norm $p$ dividing $z$
  obtain ⟨ρ, hρz, hρρ, hρre, hρim⟩ : ∃ ρ : GaussianInt, ρ ∣ z ∧ ρ * star ρ = ((p : ℤ) : GaussianInt) ∧
      ρ.re = a ∧ (ρ.im = b ∨ ρ.im = -b) := by
    rcases hπprime.dvd_or_dvd hdvd with h1 | h1
    · exact ⟨π, h1, hππ, rfl, Or.inl rfl⟩
    · refine ⟨star π, ?_, by rw [star_star, mul_comm, hππ], by simp [hπ], Or.inr (by simp [hπ])⟩
      obtain ⟨k, hk⟩ := h1
      exact ⟨star k, by rw [← star_star z, hk, star_mul']⟩
  obtain ⟨w, hw⟩ := hρz
  have hp0 : ((p : ℤ) : GaussianInt) ≠ 0 := by
    intro h0
    have := congrArg Zsqrtd.re h0
    simp at this
    exact hp.ne_zero this
  have hww : w * star w = (r : GaussianInt) ^ 4 := by
    have e1 : z * star z = ((p : ℤ) : GaussianInt) * (w * star w) := by
      rw [hw, star_mul', ← hρρ]; ring
    have e2 : ((p : ℤ) : GaussianInt) * (r : GaussianInt) ^ 4 = ((p : ℤ) : GaussianInt) * (w * star w) := by
      rw [← e1, hzz]; push_cast; ring
    exact (mul_left_cancel₀ hp0 e2).symm
  -- coprimality of $z$ and $\bar z$
  obtain ⟨A, B, hAB⟩ := hcop
  obtain ⟨k, hk⟩ : Odd ((p : ℤ) * r ^ 4) := by rw [← h]; exact (hN.pow).add_even (by
    exact ⟨2 * t ^ 4, by ring⟩)
  have h2 : (2 : GaussianInt) = z * ⟨A, -B⟩ + star z * ⟨A, B⟩ := by
    ext
    · simp [hz]; linear_combination -2 * hAB
    · simp [hz]; ring
  have hcopz : IsCoprime z (star z) := by
    refine ⟨(-k : GaussianInt) * ⟨A, -B⟩ + star z, (-k : GaussianInt) * ⟨A, B⟩, ?_⟩
    have e : ((p : ℤ) * r ^ 4 : ℤ) = 2 * k + 1 := hk
    have e' : z * star z = 2 * (k : GaussianInt) + 1 := by rw [hzz, e]; push_cast; ring
    linear_combination (k : GaussianInt) * h2 + e'
  have hcopw : IsCoprime w (star w) := by
    rw [hw, star_mul'] at hcopz
    exact (hcopz.of_mul_left_right).of_mul_right_right
  obtain ⟨δ, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hcopw hww
  -- norms
  have hunorm : (u : GaussianInt).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num) _).2 u.isUnit
  have hzu : z = ρ * (δ ^ 4 * u) := by rw [hw, ← hu]
  have hδodd : Odd (δ.re ^ 2 + δ.im ^ 2) := by
    have e1 : z.norm = p * δ.norm ^ 4 := by
      have hpow : (δ ^ 4).norm = δ.norm ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, Zsqrtd.norm_mul, Zsqrtd.norm_one]
      rw [hzu, Zsqrtd.norm_mul, Zsqrtd.norm_mul, hpow, hunorm]
      have : ρ.norm = p := by
        have := congrArg Zsqrtd.re hρρ
        rw [Zsqrtd.norm_def]
        simp at this
        linarith
      rw [this]; ring
    have e2 : z.norm = p * r ^ 4 := by rw [Zsqrtd.norm_def, ← h]; simp [hz]; ring
    have e3 : δ.norm ^ 4 = r ^ 4 := by
      have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact mul_left_cancel₀ hp' (e1.symm.trans e2)
    have e4 : Odd (δ.norm ^ 4) := by rw [e3]; exact hr.pow
    have e5 : Odd δ.norm := (Int.odd_pow' (by norm_num)).1 e4
    rw [Zsqrtd.norm_def] at e5
    convert e5 using 1
    ring
  obtain ⟨d1, d2⟩ := fourth_pow_mod_eight hδodd
  have hD : (δ ^ 4).re = (δ.re ^ 2 - δ.im ^ 2) ^ 2 - 4 * δ.re ^ 2 * δ.im ^ 2 ∧
      (δ ^ 4).im = 4 * δ.re * δ.im * (δ.re ^ 2 - δ.im ^ 2) := by
    constructor <;> simp [pow_succ] <;> ring
  -- the unit
  have hu2 : (u : GaussianInt).re ^ 2 + (u : GaussianInt).im ^ 2 = 1 := by
    rw [Zsqrtd.norm_def] at hunorm; linear_combination hunorm
  have hucases : ((u : GaussianInt).re = 1 ∨ (u : GaussianInt).re = -1) ∧ (u : GaussianInt).im = 0 ∨
      (u : GaussianInt).re = 0 ∧ ((u : GaussianInt).im = 1 ∨ (u : GaussianInt).im = -1) := by
    have key : ∀ x y : ℤ, x ^ 2 + y ^ 2 = 1 →
        ((x = 1 ∨ x = -1) ∧ y = 0) ∨ (x = 0 ∧ (y = 1 ∨ y = -1)) := by
      intro x y hxy
      have hx' : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith [sq_nonneg y]
      have hy' : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith [sq_nonneg x]
      obtain ⟨hx1, hx2⟩ := hx'
      obtain ⟨hy1, hy2⟩ := hy'
      interval_cases x <;> interval_cases y <;> simp_all
    exact key _ _ hu2
  -- components of $z = (\rho\delta^4) u$
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = (ρ * δ ^ 4).re := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = (ρ * δ ^ 4).im := ⟨_, rfl⟩
  have hXa : 8 ∣ X - a := by
    have : X - a = a * ((δ ^ 4).re - 1) - ρ.im * (δ ^ 4).im := by
      rw [hX, Zsqrtd.re_mul, hρre]; ring
    rw [this, hD.1, hD.2]
    exact dvd_sub (Dvd.dvd.mul_left d1 _) (Dvd.dvd.mul_left d2 _)
  have hYb : 8 ∣ Y - ρ.im := by
    have : Y - ρ.im = a * (δ ^ 4).im + ρ.im * ((δ ^ 4).re - 1) := by
      rw [hY, Zsqrtd.im_mul, hρre]; ring
    rw [this, hD.1, hD.2]
    exact dvd_add (Dvd.dvd.mul_left d2 _) (Dvd.dvd.mul_left d1 _)
  have hzre : N = X * (u : GaussianInt).re - Y * (u : GaussianInt).im := by
    have := congrArg Zsqrtd.re hzu
    rw [← mul_assoc, Zsqrtd.re_mul (ρ * δ ^ 4) (u : GaussianInt), ← hX, ← hY] at this
    simp only [hz] at this
    linear_combination this
  have hzim : 2 * t ^ 2 = X * (u : GaussianInt).im + Y * (u : GaussianInt).re := by
    have := congrArg Zsqrtd.im hzu
    rw [← mul_assoc, Zsqrtd.im_mul (ρ * δ ^ 4) (u : GaussianInt), ← hX, ← hY] at this
    simp only [hz] at this
    linear_combination this
  obtain ⟨N1, hN1⟩ := hN
  obtain ⟨b1, hb1⟩ := hb
  generalize 2 * t ^ 2 = T at hzim ⊢
  rcases hucases with ⟨hre | hre, him⟩ | ⟨hre, him | him⟩ <;> rw [hre, him] at hzre hzim <;>
    rcases hρim with h' | h' <;> rw [h'] at hYb <;> omega

theorem sq_emod_four (a : ℤ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  have : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

theorem sq_emod_eight_of_odd {a : ℤ} (ha : Odd a) : a ^ 2 % 8 = 1 := by
  have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    obtain ⟨k, rfl⟩ := ha; omega
  rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

/-- For $p \equiv 1 \bmod 8$ such that $2$ is not a fourth power modulo $p$, write $p = a^2 + b^2$ with $a$ odd; then
$b \equiv 4 \pmod 8$ (Gauss's criterion, `gaussQuarticCriterion_holds`). -/
theorem exists_sq_add_sq_b_mod_eight (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 1) (h2 : ∀ x : ZMod p, x ^ 4 ≠ 2) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧ Odd a ∧ b % 8 = 4 := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have hpodd : Odd (p : ℤ) := ⟨p / 2, by omega⟩
  -- one of $a, b$ is odd
  obtain ⟨A, B, hAB, hA⟩ : ∃ A B : ℤ, (p : ℤ) = A ^ 2 + B ^ 2 ∧ Odd A := by
    rcases Int.even_or_odd (a : ℤ) with ha | ha
    · refine ⟨b, a, by rw [← hab]; push_cast; ring, ?_⟩
      rcases Int.even_or_odd (b : ℤ) with hb | hb
      · exfalso
        have : Even ((p : ℤ)) := by rw [← hab]; push_cast; exact ((Int.even_pow' two_ne_zero).2 ha).add ((Int.even_pow' two_ne_zero).2 hb)
        exact (Int.not_even_iff_odd.2 hpodd) this
      · exact hb
    · exact ⟨a, b, by rw [← hab]; push_cast; ring, ha⟩
  have hB : ¬ (8 : ℤ) ∣ A * B := fun hd => by
    obtain ⟨z, hz⟩ := (gaussQuarticCriterion_holds.iff p A B h8 hAB).2 hd
    exact h2 z hz
  have hA8 := sq_emod_eight_of_odd hA
  have hBeven : Even B := by
    rcases Int.even_or_odd B with hb | hb
    · exact hb
    · exfalso
      have := sq_emod_eight_of_odd hb
      omega
  obtain ⟨B1, rfl⟩ := hBeven
  have hB1 : Even B1 := by
    rcases Int.even_or_odd B1 with hb | hb
    · exact hb
    · exfalso
      have := sq_emod_eight_of_odd hb
      have e : (B1 + B1) ^ 2 = 4 * B1 ^ 2 := by ring
      omega
  obtain ⟨B2, rfl⟩ := hB1
  refine ⟨A, B2 + B2 + (B2 + B2), hAB, hA, ?_⟩
  have : ¬ (8 : ℤ) ∣ B2 + B2 + (B2 + B2) := fun hd => hB (Dvd.dvd.mul_left hd A)
  omega

/-- **No integer point on $N^2 = pr^4 - 4t^4$** with $r, t$ coprime, when $p \equiv 1 \bmod 8$ and $2$ is not a
fourth power modulo $p$. -/
theorem no_int_point_p_quartic (p : ℕ) [hpf : Fact p.Prime] (h8 : p % 8 = 1) (h2 : ∀ x : ZMod p, x ^ 4 ≠ 2)
    (N r t : ℤ) (hcop : IsCoprime r t) (h : N ^ 2 = p * r ^ 4 - 4 * t ^ 4) : False := by
  have hp : p.Prime := hpf.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpodd : Odd (p : ℤ) := ⟨p / 2, by omega⟩
  have h2unit : ¬ IsUnit (2 : ℤ) := by rw [Int.isUnit_iff]; omega
  -- $r$ is odd
  have hr : Odd r := by
    rcases Int.even_or_odd r with ⟨r1, rfl⟩ | hr
    · exfalso
      have ht : Odd t := by
        rcases Int.even_or_odd t with ⟨t1, rfl⟩ | ht
        · exact absurd (hcop.isUnit_of_dvd' ⟨r1, by ring⟩ ⟨t1, by ring⟩) h2unit
        · exact ht
      have hNe : Even N := by
        have : Even (N ^ 2) := ⟨8 * p * r1 ^ 4 - 2 * t ^ 4, by rw [h]; ring⟩
        exact (Int.even_pow' (by norm_num)).1 this
      obtain ⟨N1, rfl⟩ := hNe
      have e : N1 ^ 2 = 4 * (p * r1 ^ 4) - (t ^ 2) ^ 2 := by
        have h' := h
        ring_nf at h' ⊢
        linarith
      have h1 := sq_emod_four N1
      have h3 : (t ^ 2) ^ 2 % 4 = 1 := by
        have := sq_emod_eight_of_odd (ht.pow (n := 2)); omega
      omega
    · exact hr
  -- $N$ is odd
  have hN : Odd N := by
    have : Odd (N ^ 2) := by
      rw [h]; exact (hpodd.mul hr.pow).sub_even ⟨2 * t ^ 4, by ring⟩
    exact (Int.odd_pow' (by norm_num)).1 this
  -- $p \nmid t$
  have hpt : ¬ (p : ℤ) ∣ t := by
    rintro ⟨t2, rfl⟩
    have hpN : (p : ℤ) ∣ N := hpZ.dvd_of_dvd_pow (n := 2)
      ⟨r ^ 4 - 4 * p ^ 3 * t2 ^ 4, by rw [h]; ring⟩
    obtain ⟨N2, rfl⟩ := hpN
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have e : r ^ 4 = p * (N2 ^ 2 + 4 * p ^ 2 * t2 ^ 4) := by
      have : (p : ℤ) * r ^ 4 = p * (p * (N2 ^ 2 + 4 * p ^ 2 * t2 ^ 4)) := by linear_combination -h
      exact mul_left_cancel₀ hp0 this
    have hpr : (p : ℤ) ∣ r := hpZ.dvd_of_dvd_pow ⟨_, e⟩
    exact hpZ.not_isUnit (hcop.isUnit_of_dvd' hpr ⟨t2, rfl⟩)
  have htp : IsCoprime t (p : ℤ) :=
    ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hpt).symm
  have htN : IsCoprime t N := by
    have h1 : IsCoprime t ((p : ℤ) * r ^ 4) := htp.mul_right hcop.symm.pow_right
    have e : (p : ℤ) * r ^ 4 = N ^ 2 + t * (4 * t ^ 3) := by linear_combination -h
    rw [e] at h1
    exact (IsCoprime.pow_right_iff (by norm_num)).mp (IsCoprime.add_mul_left_right_iff.mp h1)
  have hN2 : IsCoprime N 2 := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨1, -k, by rw [hk]; ring⟩
  have hcop' : IsCoprime N (2 * t ^ 2) := hN2.mul_right htN.symm.pow_right
  obtain ⟨a, b, hab, ha, hb8⟩ := exists_sq_add_sq_b_mod_eight p h8 h2
  have hbe : Even b := ⟨b / 2, by omega⟩
  have hmain := gaussian_step hp hab hbe hN hr hcop' (by linear_combination h)
  have := sq_emod_four t
  omega

/-- **The quartic $Y^2 = pX^4 - 4$ has no rational point** when $p \equiv 1 \bmod 8$ and $2$ is not a fourth power
modulo $p$ (the class $p$ of $S^{(\hat\varphi)}(E'/\mathbb Q)$ is not in the image of $E'(\mathbb Q)$). -/
theorem no_rat_point_p_quartic (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 1) (h2 : ∀ x : ZMod p, x ^ 4 ≠ 2)
    (x y : ℚ) : y ^ 2 ≠ p * x ^ 4 - 4 := by
  intro hxy
  have hx : x * (x.den : ℚ) = x.num := Rat.mul_den_eq_num x
  have hN : ((p * x.num ^ 4 - 4 * (x.den : ℤ) ^ 4 : ℤ) : ℚ) = (y * (x.den : ℚ) ^ 2) ^ 2 := by
    push_cast
    rw [← hx]
    have e : (y * (x.den : ℚ) ^ 2) ^ 2 = y ^ 2 * (x.den : ℚ) ^ 4 := by ring
    rw [e, hxy]; ring
  have hsq : IsSquare (p * x.num ^ 4 - 4 * (x.den : ℤ) ^ 4) := by
    rw [← Rat.isSquare_intCast_iff, hN]; exact ⟨y * (x.den : ℚ) ^ 2, sq _⟩
  obtain ⟨m, hm⟩ := hsq
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using x.reduced
  exact no_int_point_p_quartic p h8 h2 m x.num x.den hcop (by rw [sq, ← hm])

/-! ### The image of $E'(\mathbb Q)$: the classes $1$ and $-p$ -/

section Dual

variable [hpf : Fact p.Prime]

/-- The class $2$ does not occur: $X = w^2/2$ would give a rational point on $Y^2 = 2 - 2pX^4$. -/
theorem not_class_two (h8 : p % 8 = 1) (h2 : ∀ z : ZMod p, z ^ 4 ≠ 2) {x y w : ℚ} (hx : x ≠ 0)
    (hw : x * 2 = w * w) (hE : y ^ 2 = x ^ 3 - 4 * p * x) : False := by
  have hw0 : w ≠ 0 := by rintro rfl; exact hx (by linarith)
  have hxw : x = w ^ 2 / 2 := by linear_combination hw / 2
  apply (remark_8_4_no_rational_point p h8 h2).1 (2 / w) (4 * y / w ^ 3)
  rw [hxw] at hE
  field_simp
  linear_combination 16 * hE

/-- The class $-2$ does not occur: $X = -w^2/2$ would give a rational point on $Y^2 = 2pX^4 - 2$. -/
theorem not_class_neg_two (h8 : p % 8 = 1) (h2 : ∀ z : ZMod p, z ^ 4 ≠ 2) {x y w : ℚ} (hx : x ≠ 0)
    (hw : x * (-2) = w * w) (hE : y ^ 2 = x ^ 3 - 4 * p * x) : False := by
  have hw0 : w ≠ 0 := by rintro rfl; exact hx (by linarith)
  have hxw : x = -w ^ 2 / 2 := by linear_combination -hw / 2
  apply no_rat_point_neg_two_quartic p h8 h2 (2 / w) (4 * y / w ^ 3)
  rw [hxw] at hE
  field_simp
  linear_combination 16 * hE

/-- The class $p$ does not occur: $X = w^2/p$ would give a rational point on $Y^2 = pX^4 - 4$. -/
theorem not_class_p (h8 : p % 8 = 1) (h2 : ∀ z : ZMod p, z ^ 4 ≠ 2) {x y w : ℚ} (hx : x ≠ 0)
    (hw : x * p = w * w) (hE : y ^ 2 = x ^ 3 - 4 * p * x) : False := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpf.out.ne_zero
  have hw0 : w ≠ 0 := by rintro rfl; exact hx (by simpa [hp0] using hw)
  have hxw : x = w ^ 2 / p := by field_simp; linear_combination hw
  apply no_rat_point_p_quartic p h8 h2 (w / p) (y / w)
  rw [hxw] at hE
  rw [div_pow, hE]
  field_simp

/-- Translation by $T'$ in coordinates: $(X, Y) \mapsto (-4p/X, 4pY/X^2)$ preserves the equation of $E'$. -/
theorem dual_translate_eq {x y : ℚ} (hx : x ≠ 0) (hE : y ^ 2 = x ^ 3 - 4 * p * x) :
    (4 * p * y / x ^ 2) ^ 2 = (-4 * p / x) ^ 3 - 4 * p * (-4 * p / x) := by
  rw [div_pow, mul_pow, hE]
  field_simp
  ring

theorem padicValRat_four_mul_p {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ p) :
    padicValRat ℓ (-4 * p : ℚ) = 0 := by
  have hℓ : ℓ.Prime := Fact.out
  have h2 : padicValRat ℓ (2 : ℚ) = 0 := by
    have := padicValRat_natCast_prime_ne hℓ Nat.prime_two hℓ2; exact_mod_cast this
  have hp : padicValRat ℓ (p : ℚ) = 0 := padicValRat_natCast_prime_ne hℓ hpf.out hℓp
  rw [show (-4 * p : ℚ) = -(2 ^ 2 * p) by ring, padicValRat.neg,
    padicValRat.mul (by norm_num) (by exact_mod_cast hpf.out.ne_zero), padicValRat.pow _, h2, hp]
  simp

/-- The valuation of $\pm 2^{e_2} p^{e_p}$. -/
theorem padicValRat_sign_mul (ℓ : ℕ) [Fact ℓ.Prime] {s : ℚ} (hs : s = 1 ∨ s = -1) (e₂ eₚ : ℕ) :
    padicValRat ℓ (s * 2 ^ e₂ * p ^ eₚ) = e₂ * padicValRat ℓ 2 + eₚ * padicValRat ℓ p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpf.out.ne_zero
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  rw [padicValRat.mul (mul_ne_zero hs0 (by positivity)) (pow_ne_zero _ hp0),
    padicValRat.mul hs0 (by positivity), padicValRat.pow _, padicValRat.pow _]
  have : padicValRat ℓ s = 0 := by rcases hs with rfl | rfl <;> simp [padicValRat.neg]
  rw [this]; ring

/-- Every nonzero rational whose valuations are even away from $2$ and $p$ is $\pm 2^{e_2} p^{e_p}$ times a
square, $e_2, e_p \in \{0, 1\}$. -/
theorem exists_class (hp2 : p ≠ 2) {x : ℚ} (hx : x ≠ 0)
    (hev : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p → Even (padicValRat ℓ x)) :
    ∃ (s : ℚ) (e₂ eₚ : ℕ), (s = 1 ∨ s = -1) ∧ e₂ < 2 ∧ eₚ < 2 ∧ IsSquare (x * (s * 2 ^ e₂ * p ^ eₚ)) := by
  have hp : p.Prime := hpf.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set s : ℚ := if x < 0 then -1 else 1 with hsdef
  have hs : s = 1 ∨ s = -1 := by rw [hsdef]; split_ifs <;> simp
  set e₂ := (padicValRat 2 x % 2).toNat with he₂
  set eₚ := (padicValRat p x % 2).toNat with heₚ
  have he₂' : (e₂ : ℤ) = padicValRat 2 x % 2 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have heₚ' : (eₚ : ℤ) = padicValRat p x % 2 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  refine ⟨s, e₂, eₚ, hs, by omega, by omega, ?_⟩
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hd0 : s * 2 ^ e₂ * (p : ℚ) ^ eₚ ≠ 0 := by positivity
  have h22 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have h2p : padicValRat 2 (p : ℚ) = 0 := padicValRat_natCast_prime_ne Nat.prime_two hp (Ne.symm hp2)
  have hp2' : padicValRat p (2 : ℚ) = 0 := by
    have := padicValRat_natCast_prime_ne hp Nat.prime_two hp2; exact_mod_cast this
  have hpp : padicValRat p (p : ℚ) = 1 := padicValRat.self hp.one_lt
  refine isSquare_mul_of_parity {2, p} hx hd0 ?_ ?_ ?_
  · have hpos : (0 : ℚ) < 2 ^ e₂ * (p : ℚ) ^ eₚ := by positivity
    rw [mul_assoc]
    rw [hsdef]
    split_ifs with hneg
    · simp only [hneg, true_iff]; nlinarith
    · simp only [hneg, false_iff, not_lt]; nlinarith
  · intro q hq
    rw [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | hqp
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [padicValRat_sign_mul 2 hs, h22, h2p]
      exact zmod2_cast_eq (by push_cast; omega)
    · rw [hqp, padicValRat_sign_mul p hs, hp2', hpp]
      exact zmod2_cast_eq (by push_cast; omega)
  · intro ℓ hℓ hS
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hS
    have : Fact ℓ.Prime := ⟨hℓ⟩
    refine ⟨hev ℓ hℓ hS.1 hS.2, ?_⟩
    rw [padicValRat_sign_mul ℓ hs, padicValRat_natCast_prime_ne hℓ hp hS.2]
    have : padicValRat ℓ (2 : ℚ) = 0 := by
      have := padicValRat_natCast_prime_ne hℓ Nat.prime_two hS.1; exact_mod_cast this
    rw [this]; simp

/-- **The image of $E'(\mathbb Q)$ in $\mathbb Q^\times/\mathbb Q^{\times 2}$** (the connecting map of $\hat\varphi$):
for $p \equiv 1 \bmod 8$ such that $2$ is not a fourth power modulo $p$, and $(x, y) \in E'(\mathbb Q)$,
$E' : Y^2 = X^3 - 4pX$, with $x \ne 0$, the class of $x$ is $1$ or $-p$.  The classes $2, -2, p$ are excluded
globally (`not_class_two`, `not_class_neg_two`, `not_class_p`) and $-2p, 2p, -1$ are their translates by $T'$. -/
theorem curvePDual_class (h8 : p % 8 = 1) (h2 : ∀ z : ZMod p, z ^ 4 ≠ 2) {x y : ℚ} (hx : x ≠ 0)
    (hE : y ^ 2 = x ^ 3 - 4 * p * x) : IsSquare x ∨ IsSquare (-p * x) := by
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hev : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p → Even (padicValRat ℓ x) := by
    intro ℓ hℓ h2ℓ hpℓ
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact even_padicValRat_of_eq ℓ (c := -4 * p) (y := y) (by simpa using hp0) (padicValRat_four_mul_p h2ℓ hpℓ) hx
      (by linear_combination hE)
  have hx' : -4 * (p : ℚ) / x ≠ 0 := div_ne_zero (by simpa using hp0) hx
  have hE' := dual_translate_eq hx hE
  obtain ⟨s, e₂, eₚ, hs, he₂, heₚ, w, hw⟩ := exists_class hp2 hx hev
  interval_cases e₂ <;> interval_cases eₚ <;> rcases hs with rfl | rfl
  · left; exact ⟨w, by linear_combination hw⟩
  · -- class $-1$: the translate has class $p$
    exfalso
    have hw0 : w ≠ 0 := by rintro rfl; exact hx (by linear_combination -hw)
    have hxw : x = -(w * w) := by linear_combination -hw
    exact not_class_p h8 h2 hx' (w := 2 * p / w) (by rw [hxw]; field_simp; ring) hE'
  · exfalso; exact not_class_p h8 h2 hx (w := w) (by linear_combination hw) hE
  · right; exact ⟨w, by linear_combination hw⟩
  · exfalso; exact not_class_two h8 h2 hx (w := w) (by linear_combination hw) hE
  · exfalso; exact not_class_neg_two h8 h2 hx (w := w) (by linear_combination hw) hE
  · -- class $2p$: the translate has class $-2$
    exfalso
    have hw0 : w ≠ 0 := by rintro rfl; exact hx (by simpa [hp0] using hw)
    have hxw : x = (w * w) / (2 * p) := by field_simp; linear_combination hw
    exact not_class_neg_two h8 h2 hx' (w := 4 * p / w) (by rw [hxw]; field_simp; ring) hE'
  · -- class $-2p$: the translate has class $2$
    exfalso
    have hw0 : w ≠ 0 := by rintro rfl; exact hx (by simpa [hp0] using hw)
    have hxw : x = -(w * w) / (2 * p) := by field_simp; linear_combination -hw
    exact not_class_two h8 h2 hx' (w := 4 * p / w) (by rw [hxw]; field_simp; ring) hE'

end Dual

/-! ### $E(\mathbb Q) = 2E(\mathbb Q) \cup (T + 2E(\mathbb Q))$ -/

section Main

variable [hpf : Fact p.Prime]

/-- If $(x, y) \in E(\mathbb Q)$ and $x$ is a nonzero square, then $(x, y) \in 2E(\mathbb Q)$. -/
theorem mem_multiples_of_isSquare (h8 : p % 8 = 1) (h2 : ∀ z : ZMod p, z ^ 4 ≠ 2) {x y : ℚ}
    (h : (curveP p).toAffine.Nonsingular x y) (hx : x ≠ 0) (hsq : IsSquare x) :
    Point.some x y h ∈ multiples (curveP p).toAffine.Point 2 := by
  have hp : p.Prime := hpf.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp0' : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by rintro rfl; exact hx (by simpa using hs)
  have hE := curveP_equation_iff.1 h.1
  obtain ⟨X, hXd⟩ : ∃ X : ℚ, X = 2 * (s ^ 3 - y) / s := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : ℚ, Y = 4 * (s ^ 3 - y) := ⟨_, rfl⟩
  obtain ⟨hX0, hE', hxX, hyX⟩ := lift_dual hp0 hs0 (by rw [hs]; ring) hE hXd hYd
  rcases curvePDual_class h8 h2 hX0 hE' with ⟨t, ht⟩ | ⟨w, hw⟩
  · have ht0 : t ≠ 0 := by rintro rfl; exact hX0 (by simpa using ht)
    have h' : (curveP p).toAffine.Nonsingular (Y ^ 2 / (4 * X ^ 2)) (Y * (-4 * p - X ^ 2) / (8 * X ^ 2)) := by
      rw [← hxX, ← hyX]; exact h
    obtain ⟨R, hR⟩ := exists_two_zsmul_eq_of_dual hp0 ht0 (by rw [ht]; ring) hE' h'
    exact ⟨R, hR.trans (some_eq_some hxX.symm hyX.symm)⟩
  · have hw0 : w ≠ 0 := by rintro rfl; exact hX0 (by simpa [hp0'] using hw)
    set X' := -4 * p / X
    set Y' := 4 * p * Y / X ^ 2
    have hE'' : Y' ^ 2 = X' ^ 3 - 4 * p * X' := dual_translate_eq hX0 hE'
    have hX' : X' = (2 * p / w) ^ 2 := by
      have hXw : X = -(w * w) / p := by field_simp; linear_combination -hw
      simp only [X', hXw]
      field_simp
      ring
    obtain ⟨e1, e2⟩ := dual_translate hp0 (Y := Y) hX0
    have h' : (curveP p).toAffine.Nonsingular (Y' ^ 2 / (4 * X' ^ 2)) (Y' * (-4 * p - X' ^ 2) / (8 * X' ^ 2)) := by
      rw [e1, e2, ← hxX, ← hyX]; exact h
    have hpw : 2 * (p : ℚ) / w ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hp0') hw0
    obtain ⟨R, hR⟩ := exists_two_zsmul_eq_of_dual hp0 hpw hX' hE'' h'
    exact ⟨R, hR.trans (some_eq_some (by rw [e1, hxX]) (by rw [e2, hyX]))⟩

/-- The $2$-torsion point $T = (0, 0)$ of $E$. -/
noncomputable def pointT (p : ℕ) [Fact p.Prime] : (curveP p).toAffine.Point :=
  Point.some 0 0 (curveP_nonsingular (Fact.out : p.Prime).ne_zero (by ring))

theorem pointT_add_self : pointT p + pointT p = 0 := by
  unfold pointT
  exact Point.add_self_of_Y_eq (by rw [curveP_negY]; ring)

theorem pointT_ne_zero : pointT p ≠ 0 := by
  unfold pointT; intro h; cases h

/-- **$E(\mathbb Q) = 2E(\mathbb Q) \cup (T + 2E(\mathbb Q))$** for $E : Y^2 = X^3 + pX$, $p \equiv 1 \bmod 8$, $2$ not a
fourth power modulo $p$. -/
theorem curveP_mem_multiples_or (h8 : p % 8 = 1) (h2 : ∀ z : ZMod p, z ^ 4 ≠ 2)
    (P : (curveP p).toAffine.Point) :
    P ∈ multiples (curveP p).toAffine.Point 2 ∨ P + pointT p ∈ multiples (curveP p).toAffine.Point 2 := by
  have hp : p.Prime := hpf.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp0' : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  cases P with
  | zero => exact Or.inl (zero_mem _)
  | some x y h =>
    have hE := curveP_equation_iff.1 h.1
    by_cases hx : x = 0
    · subst hx
      have hy : y = 0 := by simpa using hE
      subst hy
      right
      rw [show (Point.some 0 0 h : (curveP p).toAffine.Point) = pointT p from rfl, pointT_add_self]
      exact zero_mem _
    rcases curveP_class hp hx hE with hsq | ⟨w, hw⟩
    · exact Or.inl (mem_multiples_of_isSquare h8 h2 h hx hsq)
    · right
      unfold pointT
      rw [curveP_add_T hp0 h hx]
      refine mem_multiples_of_isSquare h8 h2 _ (div_ne_zero hp0' hx) ⟨w / x, ?_⟩
      rw [div_mul_div_comm, ← hw]
      field_simp

/-- $\#E(\mathbb Q)/2E(\mathbb Q) \le 2$. -/
theorem card_quot_two_curveP_le (h8 : p % 8 = 1) (h2 : ∀ z : ZMod p, z ^ 4 ≠ 2) :
    Nat.card ((curveP p).toAffine.Point ⧸ multiples (curveP p).toAffine.Point 2) ≤ 2 := by
  classical
  set M := multiples (curveP p).toAffine.Point 2
  have hg : ∀ P Q : (curveP p).toAffine.Point, decide (P ∈ M) = decide (Q ∈ M) → P - Q ∈ M := by
    intro P Q hPQ
    by_cases hP : P ∈ M <;> by_cases hQ : Q ∈ M
    · exact sub_mem hP hQ
    · simp [hP, hQ] at hPQ
    · simp [hP, hQ] at hPQ
    · have hP' := (curveP_mem_multiples_or h8 h2 P).resolve_left hP
      have hQ' := (curveP_mem_multiples_or h8 h2 Q).resolve_left hQ
      have := sub_mem hP' hQ'
      rwa [add_sub_add_right_eq_sub] at this
  have := card_quot_two_le (fun P => decide (P ∈ M)) hg
  simpa using this

/-- The finite basis theorem for $E$, by this descent: $E(\mathbb Q)$ is finitely generated. -/
theorem fg_curveP (h8 : p % 8 = 1) (h2 : ∀ z : ZMod p, z ^ 4 ≠ 2) :
    AddGroup.FG (curveP p).toAffine.Point := by
  classical
  have := curveP_isElliptic (Fact.out : p.Prime).ne_zero
  set M := multiples (curveP p).toAffine.Point 2
  have hg : ∀ P Q : (curveP p).toAffine.Point, decide (P ∈ M) = decide (Q ∈ M) → P - Q ∈ M := by
    intro P Q hPQ
    by_cases hP : P ∈ M <;> by_cases hQ : Q ∈ M
    · exact sub_mem hP hQ
    · simp [hP, hQ] at hPQ
    · simp [hP, hQ] at hPQ
    · have hP' := (curveP_mem_multiples_or h8 h2 P).resolve_left hP
      have hQ' := (curveP_mem_multiples_or h8 h2 Q).resolve_left hQ
      have := sub_mem hP' hQ'
      rwa [add_sub_add_right_eq_sub] at this
  exact fg_of_finite_quotient_two (curveP p).toAffine (finite_quot_two_of (fun P => decide (P ∈ M)) hg)

end Main

/-- If a finitely generated abelian group $M$ has $k$ distinct elements killed by $2$, then
$\#(M/2M) \ge 2^r k$, where $r$ is the rank of $M$ (the argument of `two_pow_le_card_quot_two`, for any $k$). -/
theorem two_pow_mul_le_card_quot_two {M : Type*} [AddCommGroup M] [AddGroup.FG M] {k : ℕ}
    (f : Fin k → M) (hf : Function.Injective f) (h2 : ∀ i, (2 : ℤ) • f i = 0) :
    2 ^ Module.finrank ℤ M * k ≤ Nat.card (M ⧸ multiples M 2) := by
  obtain ⟨e⟩ := addEquiv_torsion_prod_free M
  have hTfin := finite_torsion_of_fg M
  have hMfin := finite_quotient_multiples_of_fg (M := M) (two_ne_zero)
  set T := AddCommGroup.torsion M with hT
  set r := Module.finrank ℤ M with hr
  let σ : M →+ (T ⧸ multiples T 2) × (Fin r → ZMod 2) :=
    ((((QuotientAddGroup.mk' (multiples T 2)).comp (AddMonoidHom.fst T (Fin r → ℤ))).prod
      ((AddMonoidHom.compLeft (Int.castAddHom (ZMod 2)) (Fin r)).comp (AddMonoidHom.snd T (Fin r → ℤ)))).comp
      e.toAddMonoidHom)
  have hσsurj : Function.Surjective σ := by
    rintro ⟨q, g⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨e.symm (t, fun i => ((g i).val : ℤ)), ?_⟩
    simp only [σ, AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.apply_symm_apply]
    refine Prod.ext rfl ?_
    funext i
    simp
  have hσ2 : ∀ x : M, σ ((2 : ℤ) • x) = 0 := by
    intro x
    rw [map_zsmul]
    generalize σ x = y
    obtain ⟨q, g⟩ := y
    refine Prod.ext ?_ ?_
    · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
      show (2 : ℤ) • (QuotientAddGroup.mk t : T ⧸ multiples T 2) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨t, rfl⟩
    · funext i
      show (2 : ℤ) • g i = 0
      have : (2 : ZMod 2) = 0 := rfl
      rw [zsmul_eq_mul]
      simp [this]
  have hlift : Function.Surjective (QuotientAddGroup.lift (multiples M 2) σ (by
      rintro _ ⟨x, rfl⟩
      exact hσ2 x)) := by
    intro y
    obtain ⟨x, rfl⟩ := hσsurj y
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  have hcard := Nat.card_le_card_of_surjective _ hlift
  have hTk : k ≤ Nat.card (T ⧸ multiples T 2) := by
    rw [card_quot_two_eq]
    let g : Fin k → (zsmulAddGroupHom (α := T) 2).ker := fun i =>
      ⟨(e (f i)).1, by
        show (2 : ℤ) • (e (f i)).1 = 0
        have h := congrArg Prod.fst (show (2 : ℤ) • e (f i) = 0 by rw [← map_zsmul, h2, map_zero])
        simpa using h⟩
    have hginj : Function.Injective g := by
      intro i j hij
      have h1 : (e (f i)).1 = (e (f j)).1 := congrArg Subtype.val hij
      have hs : ∀ l, (e (f l)).2 = 0 := by
        intro l
        have h := congrArg Prod.snd (show (2 : ℤ) • e (f l) = 0 by rw [← map_zsmul, h2, map_zero])
        funext m
        have := congrFun h m
        simp at this
        simpa using this
      apply hf
      apply e.injective
      exact Prod.ext h1 (by rw [hs i, hs j])
    have := Nat.card_le_card_of_injective g hginj
    simpa using this
  have hprod : Nat.card ((T ⧸ multiples T 2) × (Fin r → ZMod 2)) =
      Nat.card (T ⧸ multiples T 2) * 2 ^ r := by
    rw [Nat.card_prod]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
    simp
  calc 2 ^ r * k ≤ 2 ^ r * Nat.card (T ⧸ multiples T 2) := Nat.mul_le_mul_left _ hTk
    _ = Nat.card ((T ⧸ multiples T 2) × (Fin r → ZMod 2)) := by rw [hprod, mul_comm]
    _ ≤ _ := hcard

end IsogenyDescent

open IsogenyDescent

/-- **Proposition 8.2, the rank** (Milne, *EC*, IV, Proposition 8.2, pdf p. 152; Silverman 1986, X.6.2(b)): for a
prime $p \equiv 1 \bmod 8$ such that $2$ is not a fourth power modulo $p$, the curve $E : Y^2 = X^3 + pX$ has
$\operatorname{rank} E(\mathbb Q) = 0$.  Proved by the descent by the $2$-isogeny $E \to E' : Y^2 = X^3 - 4pX$
(module docstring); the finite generation of $E(\mathbb Q)$ comes out of the same descent (`fg_curveP`). -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.2 (the rank), pdf p. 152"]
theorem prop_8_2_rank : ∀ p : ℕ, p.Prime → p % 8 = 1 → (¬ ∃ x : ZMod p, x ^ 4 = 2) → rank (curveP p) = 0 := by
  intro p hp h8 h2
  have := Fact.mk hp
  have h2' : ∀ z : ZMod p, z ^ 4 ≠ 2 := fun z hz => h2 ⟨z, hz⟩
  have := fg_curveP h8 h2'
  have hinj : Function.Injective ![(0 : (curveP p).toAffine.Point), pointT p] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact pointT_ne_zero hij.symm
    · exact pointT_ne_zero hij
  have hlow := two_pow_mul_le_card_quot_two ![(0 : (curveP p).toAffine.Point), pointT p] hinj (by
    intro i
    fin_cases i
    · show (2 : ℤ) • (0 : (curveP p).toAffine.Point) = 0
      exact zsmul_zero 2
    · show (2 : ℤ) • pointT p = 0
      rw [two_zsmul, pointT_add_self])
  have hup := card_quot_two_curveP_le h8 h2'
  have h1 : 2 ^ rank (curveP p) ≤ 1 := by
    unfold rank
    omega
  by_contra hr
  have := Nat.one_lt_two_pow hr
  omega

/-- For $p$ as in Proposition 8.2, $E(\mathbb Q)$ is finite ($Y^2 = X^3 + pX$ has rank $0$). -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.2 (the rank), pdf p. 152"]
theorem finite_curveP (p : ℕ) (hp : p.Prime) (h8 : p % 8 = 1) (h2 : ¬ ∃ x : ZMod p, x ^ 4 = 2) :
    Finite (curveP p).toAffine.Point := by
  have := Fact.mk hp
  have := fg_curveP h8 (fun z hz => h2 ⟨z, hz⟩)
  have h0 := prop_8_2_rank p hp h8 h2
  obtain ⟨e⟩ := rank_spec (curveP p)
  have := finite_torsion_of_fg (curveP p).toAffine.Point
  have : Finite (Fin (rank (curveP p)) → ℤ) := by
    rw [h0]
    infer_instance
  exact Finite.of_equiv _ e.symm.toEquiv

end NumberFieldKB.MilneEC
