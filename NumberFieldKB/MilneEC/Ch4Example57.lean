import NumberFieldKB.MilneEC.Ch4TwoDescent
import NumberFieldKB.MilneEC.Ch2Reduction
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import NumberFieldKB.MilneEC.Ch1Rational
import Mathlib.NumberTheory.Real.Irrational

/-!
# Milne, *Elliptic Curves*, Chapter IV, Example 5.7: $E(\mathbb Q) \cong (\mathbb Z/2)^2$ for $Y^2 = X^3 - X$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Example 5.7 (pdf p. 138).
Locators give the pdf page of the text `ectext6` (printed page = pdf page − 8).

Proposition 5.6 (proved unconditionally in `Ch4TwoDescent.lean`) gives rank $0$, so $E(\mathbb Q)$ is finite
(`example_5_7_rank_unconditional`).  The torsion is computed by Chapter II: reduction modulo $3$ is injective on
$E(\mathbb Q)_{\mathrm{tors}}$ (Corollary II.5.7, `II.corollary_5_7_unconditional`; $3 \nmid 4a^3 + 27b^2 = -4$), and
every point of $\bar E(\mathbb F_3)$, $\bar E : Y^2 = X^3 - X$, is $(0 : 1 : 0)$ or $(\bar x : 0 : 1)$, since
$x^3 = x$ on $\mathbb F_3$.  So every rational point has the reduction of one of $O, (0, 0), (1, 0), (-1, 0)$, and equals
it.  Hence $E(\mathbb Q) = \{O, (0,0), (1,0), (-1,0)\} \cong (\mathbb Z/2)^2$ (`example_5_7_unconditional`).

With the definition of congruent numbers, this is the statement that $1$ is not a congruent number: a right triangle
with rational sides and area $1$ would give a point of $Y^2 = X^3 - X$ with $Y \ne 0$
(`no_point_with_y_ne_zero`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

set_option backward.isDefEq.respectTransparency false

namespace NumberFieldKB.MilneEC

namespace Example57

/-- $Y^2 = (X + 1)X(X - 1)$ is Chapter II's short curve $Y^2 = X^3 - X$. -/
theorem cubicCurve_eq_curveQ : cubicCurve (-1) 0 1 = II.curveQ (-1) 0 := by
  simp only [cubicCurve, II.curveQ, II.shortCurve]
  norm_num

/-- Abbreviation for the curve $Y^2 = X^3 - X$ in Chapter II's form. -/
noncomputable abbrev E : WeierstrassCurve ℚ := II.curveQ (-1) 0

theorem equation_iff {x y : ℚ} : E.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [Affine.equation_iff]
  simp only [E, II.curveQ, II.shortCurve]
  constructor <;> intro h <;> push_cast at h ⊢ <;> linear_combination h

instance : E.IsElliptic := by
  rw [show E = cubicCurve (-1) 0 1 from cubicCurve_eq_curveQ.symm]
  exact cubicCurve_isElliptic_of_ne (by norm_num) (by norm_num) (by norm_num)

theorem nonsingular_root (c : ℚ) (hc : c ^ 3 - c = 0) : E.toAffine.Nonsingular c 0 :=
  (Affine.equation_iff_nonsingular).1 (equation_iff.2 (by rw [hc]; norm_num))

/-- The 2-torsion point $(c, 0)$, $c \in \{0, 1, -1\}$. -/
noncomputable def T (c : ℚ) (hc : c ^ 3 - c = 0) : E.toAffine.Point := Point.some c 0 (nonsingular_root c hc)

theorem two_nsmul_T (c : ℚ) (hc : c ^ 3 - c = 0) : 2 • T c hc = 0 := by
  rw [two_nsmul]
  exact Point.add_self_of_Y_eq (by simp [Affine.negY, E, II.curveQ, II.shortCurve])

theorem h0 : (0 : ℚ) ^ 3 - 0 = 0 := by norm_num
theorem h1 : (1 : ℚ) ^ 3 - 1 = 0 := by norm_num
theorem hm1 : (-1 : ℚ) ^ 3 - -1 = 0 := by norm_num

/-- The residue modulo $3$ of an integer. -/
theorem residue_intCast (n : ℤ) : II.residue ((n : ℚ) : ℚ_[3]) = (n : ZMod 3) := by
  have e : ((n : ℚ) : ℚ_[3]) = ((n : ℤ_[3]) : ℚ_[3]) := by push_cast; rfl
  rw [e, II.residue_coe, map_intCast]

/-- The reduction modulo $3$ of the 2-torsion point $(c, 0)$, $c \in \mathbb Z$. -/
theorem reduce_T (c : ℤ) (hc : (c : ℚ) ^ 3 - c = 0) :
    II.reducePoint (II.toQp 3 (-1) 0 (T c hc)) = ![(c : ZMod 3), 0, 1] := by
  have hn : ‖((c : ℚ) : ℚ_[3])‖ ≤ 1 := by
    have : ((c : ℚ) : ℚ_[3]) = ((c : ℤ_[3]) : ℚ_[3]) := by push_cast; rfl
    rw [this]; exact PadicInt.norm_le_one _
  show (if ‖((c : ℚ) : ℚ_[3])‖ ≤ 1 then ![II.residue ((c : ℚ) : ℚ_[3]), II.residue ((0 : ℚ) : ℚ_[3]), 1]
    else ![0, 1, 0]) = _
  rw [if_pos hn, residue_intCast, show ((0 : ℚ) : ℚ_[3]) = (((0 : ℤ) : ℚ) : ℚ_[3]) by simp, residue_intCast]
  simp

/-- **Every point of $\bar E(\mathbb F_3)$ is $(0 : 1 : 0)$ or $(\bar x : 0 : 1)$**: the reduction of a rational point
modulo $3$ is that of $O$, $(0, 0)$, $(1, 0)$ or $(-1, 0)$. -/
theorem reduce_mem (P : E.toAffine.Point) :
    II.reducePoint (II.toQp 3 (-1) 0 P) = II.reducePoint (II.toQp 3 (-1) 0 0) ∨
      II.reducePoint (II.toQp 3 (-1) 0 P) = ![(0 : ZMod 3), 0, 1] ∨
      II.reducePoint (II.toQp 3 (-1) 0 P) = ![(1 : ZMod 3), 0, 1] ∨
      II.reducePoint (II.toQp 3 (-1) 0 P) = ![(-1 : ZMod 3), 0, 1] := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    have hred : II.reducePoint (II.toQp 3 (-1) 0 (Point.some x y h)) =
        if ‖(x : ℚ_[3])‖ ≤ 1 then ![II.residue (x : ℚ_[3]), II.residue (y : ℚ_[3]), 1] else ![0, 1, 0] := rfl
    rw [hred]
    split_ifs with hx
    · right
      have hxy := equation_iff.1 h.1
      have e : (y : ℚ_[3]) ^ 2 = (x : ℚ_[3]) ^ 3 + ((-1 : ℤ) : ℚ_[3]) * x + ((0 : ℤ) : ℚ_[3]) := by
        have := congrArg (fun q : ℚ => (q : ℚ_[3])) hxy
        push_cast at this ⊢
        linear_combination this
      have hy : ‖(y : ℚ_[3])‖ ≤ 1 :=
        II.norm_y_le_one (II.norm_coe_le_one ((-1 : ℤ) : ℤ_[3])) (II.norm_coe_le_one ((0 : ℤ) : ℤ_[3])) hx
          (by push_cast at e ⊢; exact e)
      set X : ℤ_[3] := ⟨x, hx⟩
      set Y : ℤ_[3] := ⟨y, hy⟩
      have hXY : Y ^ 2 = X ^ 3 - X := by
        apply Subtype.ext
        simp only [X, Y, PadicInt.coe_pow, PadicInt.coe_sub]
        push_cast at e
        linear_combination e
      have hmod := congrArg PadicInt.toZMod hXY
      rw [map_pow, map_sub, map_pow] at hmod
      have hcube : ∀ a : ZMod 3, a ^ 3 - a = 0 := by decide
      have hsq : ∀ b : ZMod 3, b ^ 2 = 0 → b = 0 := by decide
      have hY0 : PadicInt.toZMod Y = 0 := hsq _ (by rw [hmod, hcube])
      have ry : II.residue (y : ℚ_[3]) = 0 := by
        rw [show (y : ℚ_[3]) = ((Y : ℤ_[3]) : ℚ_[3]) from rfl, II.residue_coe, hY0]
      rw [ry]
      generalize II.residue (x : ℚ_[3]) = u
      fin_cases u
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (by decide))
    · exact Or.inl rfl

/-- Every rational point of $Y^2 = X^3 - X$ is one of $O, (0, 0), (1, 0), (-1, 0)$ (from the finiteness of
$E(\mathbb Q)$ and reduction modulo $3$). -/
theorem eq_of_finite [Finite E.toAffine.Point] (P : E.toAffine.Point) :
    P = 0 ∨ P = T 0 h0 ∨ P = T 1 h1 ∨ P = T (-1) hm1 := by
  have hinj := II.corollary_5_7_unconditional 3 (a := -1) (b := 0) (by norm_num) (by norm_num) (by decide)
  have htors : ∀ Q : E.toAffine.Point, IsOfFinAddOrder Q := fun Q => isOfFinAddOrder_of_finite Q
  have key : ∀ Q : E.toAffine.Point, II.reducePoint (II.toQp 3 (-1) 0 P) = II.reducePoint (II.toQp 3 (-1) 0 Q) →
      P = Q := fun Q hPQ => hinj (htors P) (htors Q) hPQ
  have r0 := reduce_T 0 (by norm_num)
  have r1 := reduce_T 1 (by norm_num)
  have rm := reduce_T (-1) (by norm_num)
  push_cast at r0 r1 rm
  rcases reduce_mem P with h | h | h | h
  · exact Or.inl (key 0 h)
  · exact Or.inr (Or.inl (key _ (h.trans r0.symm)))
  · exact Or.inr (Or.inr (Or.inl (key _ (h.trans r1.symm))))
  · exact Or.inr (Or.inr (Or.inr (key _ (h.trans rm.symm))))

/-- The four points are distinct. -/
theorem four_injective : Function.Injective ![(0 : E.toAffine.Point), T 0 h0, T 1 h1, T (-1) hm1] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [T] at hij ⊢ <;> norm_num at hij

theorem isAddKleinFour [Finite E.toAffine.Point] : IsAddKleinFour E.toAffine.Point where
  card_four := by
    have hbij : Function.Bijective ![(0 : E.toAffine.Point), T 0 h0, T 1 h1, T (-1) hm1] := by
      refine ⟨four_injective, fun P => ?_⟩
      rcases eq_of_finite P with h | h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
      · exact ⟨3, h.symm⟩
    rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]
  exponent_two := by
    have h2 : ∀ P : E.toAffine.Point, 2 • P = 0 := by
      intro P
      rcases eq_of_finite P with h | h | h | h <;> subst h
      · simp
      all_goals exact two_nsmul_T _ _
    rcases (Nat.dvd_prime Nat.prime_two).1 (AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero h2) with h | h
    · exfalso
      have := AddMonoid.exp_eq_one_iff.1 h
      exact absurd (Subsingleton.elim (T 0 h0) 0) (by simp [T])
    · exact h

/-- $Y^2 = X^3 - X$ has no rational point with $Y \ne 0$. -/
theorem no_point_with_y_ne_zero [Finite E.toAffine.Point] {x y : ℚ} (h : E.toAffine.Nonsingular x y) : y = 0 := by
  rcases eq_of_finite (Point.some x y h) with h' | h' | h' | h' <;> simp [T] at h' <;> exact h'.2

end Example57

/-- **Example 5.7** (pdf p. 138), unconditional: for $E : Y^2 = X^3 - X$, $E(\mathbb Q) \cong (\mathbb Z/2)^2$.
The rank is $0$ by Proposition 5.6 (`example_5_7_rank_unconditional`), and reduction modulo $3$
(Corollary II.5.7) shows $E(\mathbb Q) = \{O, (0,0), (1,0), (-1,0)\}$.  Headline 3 of the 0.3.0 plan, with
`example_5_7_no_point_with_y_ne_zero`: $1$ is not a congruent number. -/
@[kb "milne2006ec" "Ch. IV, Example 5.7, pdf p. 138"]
theorem example_5_7_unconditional :
    rank (cubicCurve (-1) 0 1) = 0 ∧ Nonempty ((cubicCurve (-1) 0 1).toAffine.Point ≃+ ZMod 2 × ZMod 2) := by
  obtain ⟨hr, hfin⟩ := example_5_7_rank_unconditional
  refine ⟨hr, ?_⟩
  rw [Example57.cubicCurve_eq_curveQ] at hfin ⊢
  have := Example57.isAddKleinFour
  exact IsAddKleinFour.nonempty_addEquiv

/-- The rational points of $Y^2 = X^3 - X$ all have $Y = 0$ (so $x \in \{-1, 0, 1\}$): there is no right triangle
with rational sides and area $1$. -/
@[kb "milne2006ec" "Ch. IV, Example 5.7, pdf p. 138 (1 is not a congruent number)"]
theorem example_5_7_no_point_with_y_ne_zero {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) : y = 0 := by
  have hfin := example_5_7_rank_unconditional.2
  rw [Example57.cubicCurve_eq_curveQ] at hfin
  exact Example57.no_point_with_y_ne_zero
    ((Affine.equation_iff_nonsingular).1 (Example57.equation_iff.2 h))

/-- **$1$ is not a congruent number** (Milne, Introduction, pdf p. 10, with Example 5.7, pdf p. 138): no right
triangle with rational sides has area $1$.  A triangle $x^2 + y^2 = z^2$, $xy = 2$ gives the point
$(z^2/4, z(x^2 - y^2)/8)$ of $Y^2 = X^3 - X$; Example 5.7 forces $x = y$, so $x^2 = 2$, impossible over
$\mathbb Q$. -/
@[kb "milne2006ec" "Introduction, congruent numbers (1 is not congruent), pdf p. 10; Ch. IV, Example 5.7, pdf p. 138"]
theorem not_isCongruentNumber_one : ¬ IsCongruentNumber 1 := by
  rintro ⟨x, y, z, hx, hy, hz, hpy, harea⟩
  have hxy : x * y = 2 := by push_cast at harea; linarith
  have hY := example_5_7_no_point_with_y_ne_zero (x := z ^ 2 / 4) (y := z * (x ^ 2 - y ^ 2) / 8)
    (by linear_combination (z ^ 2 / 64 * (x ^ 2 + y ^ 2 + z ^ 2)) * hpy - (z ^ 2 / 16 * (x * y + 2)) * hxy)
  have hsq : x ^ 2 = y ^ 2 := by
    have : z * (x ^ 2 - y ^ 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hz.ne'
    · linarith
  have hxy' : x = y := by nlinarith
  subst hxy'
  have h2 : ((x : ℝ)) ^ 2 = 2 := by exact_mod_cast (by nlinarith : x ^ 2 = 2)
  apply irrational_sqrt_two
  refine ⟨x, ?_⟩
  rw [← h2, Real.sqrt_sq (by exact_mod_cast hx.le)]

end NumberFieldKB.MilneEC
