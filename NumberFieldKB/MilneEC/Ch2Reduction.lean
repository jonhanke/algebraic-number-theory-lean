import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Padic
import NumberFieldKB.MilneEC.Ch2Torsion

/-!
# Milne, *Elliptic Curves*, Chapter II, Theorem 4.1 (b): the reduction homomorphism

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8). Definitions in `Ch2PadicDefs.lean`.

$E^0(\mathbb Q_p)$ is a subgroup (p. 69: a line through two points with nonsingular reduction meets the cubic again
in such a point), $P \mapsto \bar P$ is a homomorphism $E^0(\mathbb Q_p) \to \bar E^{ns}(\mathbb F_p)$, surjective
by Hensel's lemma, with kernel $E^1(\mathbb Q_p)$.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

/-- Chord-and-tangent formula on $y^2 = x^3 + ax + b$ for a slope $\ell$ given by two linear relations. -/
lemma add_some_eq {k : Type*} [Field k] [DecidableEq k] {a b x1 y1 x2 y2 ℓ : k}
    (h1 : (shortCurve a b).toAffine.Nonsingular x1 y1) (h2 : (shortCurve a b).toAffine.Nonsingular x2 y2)
    (hne : ¬(x1 = x2 ∧ y1 = -y2)) (H1 : ℓ * (x1 - x2) = y1 - y2)
    (H2 : ℓ * (y1 + y2) = x1 ^ 2 + x1 * x2 + x2 ^ 2 + a) :
    ∃ h3, Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2 =
      Affine.Point.some (ℓ ^ 2 - x1 - x2) (-(ℓ * ((ℓ ^ 2 - x1 - x2) - x1) + y1)) h3 := by
  have hne' : ¬(x1 = x2 ∧ y1 = (shortCurve a b).toAffine.negY x2 y2) := by
    simpa [Affine.negY] using hne
  have e1 := shortCurve_equation h1.1
  have e2 := shortCurve_equation h2.1
  have hs : (shortCurve a b).toAffine.slope x1 x2 y1 y2 = ℓ := by
    by_cases hx : x1 = x2
    · subst hx
      have hy : y1 ≠ -y2 := fun h => hne ⟨rfl, h⟩
      have hyy : y1 = y2 := by
        have : (y1 - y2) * (y1 + y2) = 0 := by linear_combination e1 - e2
        rcases mul_eq_zero.1 this with h | h
        · exact sub_eq_zero.1 h
        · exact absurd (eq_neg_of_add_eq_zero_left h) hy
      subst hyy
      have h2y : y1 + y1 ≠ 0 := fun h => hy (by linear_combination h)
      rw [Affine.slope_of_Y_ne rfl (by simpa [Affine.negY] using hy)]
      simp only [Affine.negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄]
      rw [div_eq_iff (by simpa using h2y)]
      linear_combination (-1 : k) * H2
    · rw [Affine.slope_of_X_ne hx]
      field_simp [sub_ne_zero.2 hx]
      linear_combination (-1 : k) * H1
  have key := Affine.Point.add_some hne' (h₁ := h1) (h₂ := h2)
  have hn := Affine.nonsingular_add h1 h2 hne'
  simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hs, shortCurve_a₁, shortCurve_a₂,
    shortCurve_a₃, zero_mul, add_zero, sub_zero] at key hn
  exact ⟨hn, key⟩

/-- Nonsingular points of $y^2 = x^3 + ax + b$: the equation and $3x^2 + a \neq 0$ or $2y \neq 0$. -/
lemma shortCurve_nonsingular_iff {k : Type*} [Field k] {a b x y : k} :
    (shortCurve a b).toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + a * x + b ∧ (3 * x ^ 2 + a ≠ 0 ∨ 2 * y ≠ 0) := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, shortCurve_a₆]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linear_combination h1, ?_⟩
    rcases h2 with h | h
    · left; intro h'; apply h; linear_combination -h'
    · right; intro h'; apply h; linear_combination h'
  · rintro ⟨h1, h2⟩
    refine ⟨by linear_combination h1, ?_⟩
    rcases h2 with h | h
    · left; intro h'; apply h; linear_combination -h'
    · right; intro h'; apply h; linear_combination h'

/-- The chord or tangent slope of two points that are not negatives of each other. -/
lemma exists_slope {k : Type*} [Field k] {a b x1 y1 x2 y2 : k}
    (e1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b) (e2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) (hne : ¬(x1 = x2 ∧ y1 = -y2)) :
    ∃ ℓ, ℓ * (x1 - x2) = y1 - y2 ∧ ℓ * (y1 + y2) = x1 ^ 2 + x1 * x2 + x2 ^ 2 + a := by
  by_cases hx : x1 = x2
  · subst hx
    have hy : y1 + y2 ≠ 0 := fun h => hne ⟨rfl, by linear_combination h⟩
    have hyy : y1 = y2 := by
      have : (y1 - y2) * (y1 + y2) = 0 := by linear_combination e1 - e2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hy)
    subst hyy
    refine ⟨(x1 ^ 2 + x1 * x1 + x1 ^ 2 + a) / (y1 + y1), by ring, div_mul_cancel₀ _ hy⟩
  · have hd : x1 - x2 ≠ 0 := sub_ne_zero.2 hx
    refine ⟨(y1 - y2) / (x1 - x2), by field_simp, ?_⟩
    field_simp
    linear_combination e1 - e2

/-- The residue of $w \in \mathbb Z_p$ vanishes iff $\|w\| < 1$. -/
lemma toZMod_eq_zero_iff (w : ℤ_[p]) : PadicInt.toZMod w = 0 ↔ ‖w‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

/-- An element of $\mathbb Z_p$ with nonzero residue is a unit. -/
lemma isUnit_of_toZMod_ne {w : ℤ_[p]} (h : PadicInt.toZMod w ≠ 0) : IsUnit w := by
  rw [PadicInt.isUnit_iff]
  have := (not_congr (toZMod_eq_zero_iff w)).1 h
  exact le_antisymm w.norm_le_one (not_lt.1 this)

/-- Projective coordinates of a point of $\bar E^{ns}(\mathbb F_p)$ are nonsingular. -/
lemma nonsingular_toProjCoords {W : WeierstrassCurve (ZMod p)} (A : W.toAffine.Point) :
    W.toProjective.Nonsingular (toProjCoords A) := by
  cases A with
  | zero => exact Projective.nonsingular_zero
  | some x y h => exact (Projective.nonsingular_some x y).2 h

/-- The reduction of $O$ is $(0 : 1 : 0)$. -/
lemma reducePoint_zero {a b : ℤ_[p]} : reducePoint (0 : (curveQp a b).toAffine.Point) = ![0, 1, 0] := rfl

/-- The reduction of an integral point $(x, y)$ is $(\bar x : \bar y : 1)$. -/
lemma reducePoint_some_of_le {a b : ℤ_[p]} {x y : ℚ_[p]} {h : (curveQp a b).toAffine.Nonsingular x y}
    (hx : ‖x‖ ≤ 1) : reducePoint (Affine.Point.some x y h) = ![residue x, residue y, 1] := by
  simp [reducePoint, hx]

/-- The reduction of a point with $\|x\| > 1$ is $(0 : 1 : 0)$. -/
lemma reducePoint_some_of_gt {a b : ℤ_[p]} {x y : ℚ_[p]} {h : (curveQp a b).toAffine.Nonsingular x y}
    (hx : 1 < ‖x‖) : reducePoint (Affine.Point.some x y h) = ![0, 1, 0] := by
  simp [reducePoint, not_le.2 hx]

/-- Projective coordinates of $O$. -/
lemma toProjCoords_zero {W : WeierstrassCurve (ZMod p)} : toProjCoords (0 : W.toAffine.Point) = ![0, 1, 0] := rfl

/-- A point with projective coordinates $(0 : 1 : 0)$ is $O$. -/
lemma eq_zero_of_toProjCoords {W : WeierstrassCurve (ZMod p)} {A : W.toAffine.Point}
    (h : toProjCoords A = ![0, 1, 0]) : A = 0 := by
  apply toProjCoords_injective
  rw [h]; rfl

/-- $P \in E^0(\mathbb Q_p)$ iff its reduction is the coordinate vector of a point of $\bar E^{ns}(\mathbb F_p)$. -/
lemma mem_E0_iff_exists {a b : ℤ_[p]} (P : (curveQp a b).toAffine.Point) :
    P ∈ E0 a b ↔ ∃ A : (curveFp a b).toAffine.Point, toProjCoords A = reducePoint P := by
  constructor
  · intro hP
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x y h =>
      by_cases hx : ‖x‖ ≤ 1
      · have hP' : (curveFp a b).toProjective.Nonsingular ![residue x, residue y, 1] := by
          have := hP
          simp only [E0, Set.mem_ofPred_eq] at this
          rwa [reducePoint_some_of_le hx] at this
        exact ⟨Affine.Point.some _ _ ((Projective.nonsingular_some _ _).1 hP'), by
          rw [reducePoint_some_of_le hx]; rfl⟩
      · exact ⟨0, by rw [reducePoint_some_of_gt (not_le.1 hx)]; rfl⟩
  · rintro ⟨A, hA⟩
    show (curveFp a b).toProjective.Nonsingular (reducePoint P)
    rw [← hA]
    exact nonsingular_toProjCoords A

/-- An integral point of $E(\mathbb Q_p)$ has coordinates in $\mathbb Z_p$ satisfying the equation. -/
lemma int_lift {a b : ℤ_[p]} {x y : ℚ_[p]} (h : (curveQp a b).toAffine.Nonsingular x y) (hx : ‖x‖ ≤ 1) :
    ∃ X Y : ℤ_[p], (X : ℚ_[p]) = x ∧ (Y : ℚ_[p]) = y ∧ Y ^ 2 = X ^ 3 + a * X + b := by
  have e := shortCurve_equation h.1
  have hy := norm_y_le_one (norm_coe_le_one a) (norm_coe_le_one b) hx e
  obtain ⟨X, hX⟩ : ∃ X : ℤ_[p], (X : ℚ_[p]) = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ_[p], (Y : ℚ_[p]) = y := ⟨⟨y, hy⟩, rfl⟩
  refine ⟨X, Y, hX, hY, ?_⟩
  apply PadicInt.ext
  push_cast
  rw [hX, hY]
  simpa using e

/-- A point of $\bar E^{ns}(\mathbb F_p)$ with coordinates $(u : v : 1)$ is the affine point $(u, v)$. -/
lemma proj_some_eq {a b : ℤ_[p]} {A : (curveFp a b).toAffine.Point} {u v : ZMod p}
    (hA : toProjCoords A = ![u, v, 1]) : ∃ h, A = Affine.Point.some u v h := by
  cases A with
  | zero => have := congrFun hA 2; simp [toProjCoords] at this
  | some x y h =>
    have h0 := congrFun hA 0
    have h1 := congrFun hA 1
    simp [toProjCoords] at h0 h1
    subst h0 h1
    exact ⟨h, rfl⟩

/-- If the reductions of two integral points are negatives of each other, the slope has norm $> 1$. -/
lemma one_lt_norm_slope {a X1 Y1 X2 Y2 : ℤ_[p]} {ℓ : ℚ_[p]}
    (hu : PadicInt.toZMod X1 = PadicInt.toZMod X2) (hv : PadicInt.toZMod Y1 = -PadicInt.toZMod Y2)
    (hns : 3 * PadicInt.toZMod X1 ^ 2 + PadicInt.toZMod a ≠ 0 ∨ 2 * PadicInt.toZMod Y1 ≠ 0)
    (H1 : ℓ * ((X1 : ℚ_[p]) - X2) = Y1 - Y2)
    (H2 : ℓ * ((Y1 : ℚ_[p]) + Y2) = (X1 : ℚ_[p]) ^ 2 + X1 * X2 + X2 ^ 2 + a) : 1 < ‖ℓ‖ := by
  by_contra hl
  push Not at hl
  rcases hns with h | h
  · have hS : IsUnit (X1 ^ 2 + X1 * X2 + X2 ^ 2 + a) := by
      apply isUnit_of_toZMod_ne
      simp only [map_add, map_mul, map_pow]
      rw [← hu]; intro h'; apply h; linear_combination h'
    have hS1 : ‖(X1 ^ 2 + X1 * X2 + X2 ^ 2 + a : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.1 hS
    have hY : ‖Y1 + Y2‖ < 1 := (toZMod_eq_zero_iff _).1 (by simp [map_add, hv])
    have e : ‖ℓ * ((Y1 : ℚ_[p]) + Y2)‖ = 1 := by
      rw [H2, ← hS1, PadicInt.norm_def]; push_cast; rfl
    rw [norm_mul] at e
    have h3 : ‖((Y1 : ℚ_[p]) + Y2)‖ < 1 := by
      have := hY; rw [PadicInt.norm_def] at this; push_cast at this; exact this
    nlinarith [mul_nonneg (sub_nonneg.2 hl) (norm_nonneg ((Y1 : ℚ_[p]) + Y2))]
  · have hU : IsUnit (Y1 - Y2) := by
      apply isUnit_of_toZMod_ne
      rw [map_sub, hv]; intro h'; apply h; rw [hv]; linear_combination h'
    have hU1 : ‖(Y1 - Y2 : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.1 hU
    have hX : ‖X1 - X2‖ < 1 := (toZMod_eq_zero_iff _).1 (by simp [map_sub, hu])
    have e : ‖ℓ * ((X1 : ℚ_[p]) - X2)‖ = 1 := by
      rw [H1, ← hU1, PadicInt.norm_def]; push_cast; rfl
    rw [norm_mul] at e
    have h3 : ‖((X1 : ℚ_[p]) - X2)‖ < 1 := by
      have := hX; rw [PadicInt.norm_def] at this; push_cast at this; exact this
    nlinarith [mul_nonneg (sub_nonneg.2 hl) (norm_nonneg ((X1 : ℚ_[p]) - X2))]

/-- Otherwise the slope through two integral points with nonsingular reduction is integral. -/
lemma norm_slope_le_one {a X1 Y1 X2 Y2 : ℤ_[p]} {ℓ : ℚ_[p]}
    (hn : ¬(PadicInt.toZMod X1 = PadicInt.toZMod X2 ∧ PadicInt.toZMod Y1 = -PadicInt.toZMod Y2))
    (H1 : ℓ * ((X1 : ℚ_[p]) - X2) = Y1 - Y2)
    (H2 : ℓ * ((Y1 : ℚ_[p]) + Y2) = (X1 : ℚ_[p]) ^ 2 + X1 * X2 + X2 ^ 2 + a) : ‖ℓ‖ ≤ 1 := by
  by_cases hu : PadicInt.toZMod X1 = PadicInt.toZMod X2
  · have hv : PadicInt.toZMod Y1 + PadicInt.toZMod Y2 ≠ 0 := fun h => hn ⟨hu, by linear_combination h⟩
    have hU : IsUnit (Y1 + Y2) := isUnit_of_toZMod_ne (by simpa using hv)
    have hU1 : ‖(Y1 + Y2 : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.1 hU
    have h3 : ‖((Y1 : ℚ_[p]) + Y2)‖ = 1 := by
      have := hU1; rw [PadicInt.norm_def] at this; push_cast at this; exact this
    have hS : ‖(X1 : ℚ_[p]) ^ 2 + X1 * X2 + X2 ^ 2 + a‖ ≤ 1 := by
      have := (X1 ^ 2 + X1 * X2 + X2 ^ 2 + a : ℤ_[p]).norm_le_one
      rw [PadicInt.norm_def] at this; push_cast at this; exact this
    have e := congrArg norm H2
    rw [norm_mul, h3, mul_one] at e
    linarith
  · have hU : IsUnit (X1 - X2) := isUnit_of_toZMod_ne (by rw [map_sub]; exact sub_ne_zero.2 hu)
    have hU1 : ‖(X1 - X2 : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.1 hU
    have h3 : ‖((X1 : ℚ_[p]) - X2)‖ = 1 := by
      have := hU1; rw [PadicInt.norm_def] at this; push_cast at this; exact this
    have hS : ‖(Y1 : ℚ_[p]) - Y2‖ ≤ 1 := by
      have := (Y1 - Y2 : ℤ_[p]).norm_le_one
      rw [PadicInt.norm_def] at this; push_cast at this; exact this
    have e := congrArg norm H1
    rw [norm_mul, h3, mul_one] at e
    linarith

/-- Reduction is additive on two integral points. -/
lemma red_add_int {a b : ℤ_[p]} {X1 Y1 X2 Y2 : ℤ_[p]}
    (h1 : (curveQp a b).toAffine.Nonsingular (X1 : ℚ_[p]) (Y1 : ℚ_[p]))
    (h2 : (curveQp a b).toAffine.Nonsingular (X2 : ℚ_[p]) (Y2 : ℚ_[p]))
    {A B : (curveFp a b).toAffine.Point}
    (hA : toProjCoords A = ![PadicInt.toZMod X1, PadicInt.toZMod Y1, 1])
    (hB : toProjCoords B = ![PadicInt.toZMod X2, PadicInt.toZMod Y2, 1]) :
    toProjCoords (A + B) = reducePoint (Affine.Point.some _ _ h1 + Affine.Point.some _ _ h2) := by
  obtain ⟨hA', rfl⟩ := proj_some_eq hA
  obtain ⟨hB', rfl⟩ := proj_some_eq hB
  have e1 := shortCurve_equation h1.1
  have e2 := shortCurve_equation h2.1
  have hns := (shortCurve_nonsingular_iff.1 hA').2
  by_cases hdeg : PadicInt.toZMod X1 = PadicInt.toZMod X2 ∧ PadicInt.toZMod Y1 = -PadicInt.toZMod Y2
  · have hAB : Affine.Point.some _ _ hA' + Affine.Point.some _ _ hB' = 0 :=
      Affine.Point.add_of_Y_eq hdeg.1 (by simp [Affine.negY, hdeg.2])
    rw [hAB]
    show ![0, 1, 0] = _
    by_cases hQ : (X1 : ℚ_[p]) = X2 ∧ (Y1 : ℚ_[p]) = -Y2
    · rw [Affine.Point.add_of_Y_eq hQ.1 (by simp [Affine.negY, hQ.2])]; rfl
    · obtain ⟨ℓ, H1, H2⟩ := exists_slope e1 e2 hQ
      obtain ⟨h3, hsum⟩ := add_some_eq h1 h2 hQ H1 H2
      rw [hsum, reducePoint_some_of_gt]
      · have hl := one_lt_norm_slope (a := a) hdeg.1 hdeg.2 hns H1 H2
        by_contra hle
        push Not at hle
        have e : ℓ ^ 2 = (ℓ ^ 2 - X1 - X2) + (X1 : ℚ_[p]) + X2 := by ring
        have h5 : ‖ℓ ^ 2‖ ≤ 1 := by
          rw [e]
          exact (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans
            (max_le hle (norm_coe_le_one X1))) (norm_coe_le_one X2))
        rw [norm_pow] at h5
        nlinarith
  · have hQ : ¬((X1 : ℚ_[p]) = X2 ∧ (Y1 : ℚ_[p]) = -Y2) := by
      rintro ⟨h, h'⟩
      apply hdeg
      have hx : X1 = X2 := PadicInt.ext h
      have hy : Y1 = -Y2 := PadicInt.ext (by push_cast; exact h')
      rw [hx, hy]; simp
    obtain ⟨ℓ, H1, H2⟩ := exists_slope e1 e2 hQ
    have hl := norm_slope_le_one (a := a) hdeg H1 H2
    obtain ⟨L, hLq⟩ : ∃ L : ℤ_[p], (L : ℚ_[p]) = ℓ := ⟨⟨ℓ, hl⟩, rfl⟩
    subst hLq
    have H1' : L * (X1 - X2) = Y1 - Y2 := PadicInt.ext (by push_cast; exact H1)
    have H2' : L * (Y1 + Y2) = X1 ^ 2 + X1 * X2 + X2 ^ 2 + a := PadicInt.ext (by push_cast; exact H2)
    have H1z : PadicInt.toZMod L * (PadicInt.toZMod X1 - PadicInt.toZMod X2) =
        PadicInt.toZMod Y1 - PadicInt.toZMod Y2 := by simpa using congrArg PadicInt.toZMod H1'
    have H2z : PadicInt.toZMod L * (PadicInt.toZMod Y1 + PadicInt.toZMod Y2) =
        PadicInt.toZMod X1 ^ 2 + PadicInt.toZMod X1 * PadicInt.toZMod X2 + PadicInt.toZMod X2 ^ 2 +
          PadicInt.toZMod a := by simpa using congrArg PadicInt.toZMod H2'
    obtain ⟨h3, hsum⟩ := add_some_eq h1 h2 hQ H1 H2
    obtain ⟨h3z, hsumz⟩ := add_some_eq hA' hB' hdeg H1z H2z
    rw [hsum, hsumz]
    have hx3 : ((L : ℚ_[p]) ^ 2 - X1 - X2) = ((L ^ 2 - X1 - X2 : ℤ_[p]) : ℚ_[p]) := by push_cast; rfl
    have hy3 : -((L : ℚ_[p]) * (((L : ℚ_[p]) ^ 2 - X1 - X2) - X1) + Y1) =
        ((-(L * ((L ^ 2 - X1 - X2) - X1) + Y1) : ℤ_[p]) : ℚ_[p]) := by push_cast; rfl
    rw [reducePoint_some_of_le (by rw [hx3]; exact norm_coe_le_one _), hy3, hx3, residue_coe, residue_coe]
    simp [toProjCoords]

/-- The tangent slope at a point where the chord degenerates. -/
lemma tangent_of_double_root {k : Type*} [Field k] {a b x1 y1 x2 y2 ℓ : k} (hx : x1 ≠ x2)
    (e1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b) (e2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b)
    (H1 : ℓ * (x1 - x2) = y1 - y2) (hl : ℓ ^ 2 = x1 + 2 * x2) : 2 * ℓ * y2 = 3 * x2 ^ 2 + a := by
  have hc : ℓ * x1 + (y2 - ℓ * x2) = y1 := by linear_combination H1
  have hf1 : x1 ^ 3 + a * x1 + b - (ℓ * x1 + (y2 - ℓ * x2)) ^ 2 = 0 := by
    rw [hc]; linear_combination -e1
  have hf2 : x2 ^ 3 + a * x2 + b - (ℓ * x2 + (y2 - ℓ * x2)) ^ 2 = 0 := by
    have : ℓ * x2 + (y2 - ℓ * x2) = y2 := by ring
    rw [this]; linear_combination -e2
  have hS : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2 - ℓ ^ 2 * (x1 + x2) + a - 2 * ℓ * (y2 - ℓ * x2)) = 0 := by
    linear_combination hf1 - hf2
  have hS' := (mul_eq_zero.1 hS).resolve_left (sub_ne_zero.2 hx)
  linear_combination (-1 : k) * hS' - (x1 - x2) * hl

/-- Ultrametric: $\|x - y\| = \|x\|$ when $\|y\| < \|x\|$. -/
lemma norm_sub_eq_of_lt' {u v : ℚ_[p]} (h : ‖v‖ < ‖u‖) : ‖u - v‖ = ‖u‖ := by
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (by rw [norm_neg]; exact h.ne'), norm_neg, max_eq_left h.le]

/-- $E^1(\mathbb Q_p)$ is closed under addition. -/
lemma add_mem_E1 {a b : ℤ_[p]} {P Q : (curveQp a b).toAffine.Point} (hP : P ∈ E1 a b) (hQ : Q ∈ E1 a b) :
    P + Q ∈ E1 a b := by
  rw [← En_one] at *
  exact add_mem_En le_rfl hP hQ

/-- An integral point is not in $E^1(\mathbb Q_p)$. -/
lemma not_mem_E1_of_le {a b : ℤ_[p]} {x y : ℚ_[p]} {h : (curveQp a b).toAffine.Nonsingular x y}
    (hx : ‖x‖ ≤ 1) : Affine.Point.some x y h ∉ E1 a b := by
  intro hm
  rcases (mem_E1_iff _).1 hm with h0 | ⟨x', y', h', he, hx'⟩
  · exact Affine.Point.some_ne_zero h h0
  · simp only [Affine.Point.some.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact absurd hx (not_le.2 hx')

/-- Reduction is additive when one point lies in $E^1(\mathbb Q_p)$ and the other is integral. -/
lemma red_add_big {a b : ℤ_[p]} {x1 y1 : ℚ_[p]} {X2 Y2 : ℤ_[p]}
    (h1 : (curveQp a b).toAffine.Nonsingular x1 y1) (hx1 : 1 < ‖x1‖)
    (h2 : (curveQp a b).toAffine.Nonsingular (X2 : ℚ_[p]) (Y2 : ℚ_[p]))
    {B : (curveFp a b).toAffine.Point}
    (hB : toProjCoords B = ![PadicInt.toZMod X2, PadicInt.toZMod Y2, 1]) :
    toProjCoords B = reducePoint (Affine.Point.some _ _ h1 + Affine.Point.some _ _ h2) := by
  have e1 := shortCurve_equation h1.1
  have e2 := shortCurve_equation h2.1
  have hX2 : ‖(X2 : ℚ_[p])‖ ≤ 1 := norm_coe_le_one X2
  have hY2 : ‖(Y2 : ℚ_[p])‖ ≤ 1 := norm_coe_le_one Y2
  have hxne : x1 ≠ X2 := by
    rintro h; rw [h] at hx1; linarith
  have hQ : ¬(x1 = (X2 : ℚ_[p]) ∧ y1 = -(Y2 : ℚ_[p])) := fun h => hxne h.1
  obtain ⟨ℓ, H1, H2⟩ := exists_slope e1 e2 hQ
  obtain ⟨h3, hsum⟩ := add_some_eq h1 h2 hQ H1 H2
  have hy1 : ‖y1‖ ^ 2 = ‖x1‖ ^ 3 :=
    norm_sq_eq_of_one_lt (norm_coe_le_one a) (norm_coe_le_one b) hx1 e1
  have hy1' : 1 < ‖y1‖ := by
    by_contra hh; push Not at hh
    have : ‖y1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y1]
    nlinarith [one_lt_pow₀ hx1 (by norm_num : 3 ≠ 0)]
  have hℓ : 1 < ‖ℓ‖ := by
    by_contra hh; push Not at hh
    have e := congrArg norm H1
    rw [norm_mul, norm_sub_eq_of_lt' (hX2.trans_lt hx1), norm_sub_eq_of_lt' (hY2.trans_lt hy1')] at e
    have h5 : ‖y1‖ ≤ ‖x1‖ := by
      rw [← e]; nlinarith [norm_nonneg x1, norm_nonneg ℓ]
    have h6 : ‖y1‖ ^ 2 ≤ ‖x1‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h5 2
    nlinarith [mul_pos (by linarith : (0 : ℝ) < ‖x1‖) (by linarith : (0 : ℝ) < ‖x1‖), pow_pos (by linarith : (0 : ℝ) < ‖x1‖) 2]
  generalize hx3d : ℓ ^ 2 - x1 - (X2 : ℚ_[p]) = x3 at h3 hsum
  generalize hy3d : -(ℓ * (x3 - x1) + y1) = y3 at h3 hsum
  rw [hsum]
  have hx3 : ‖x3‖ ≤ 1 := by
    by_contra hh; push Not at hh
    have hR : Affine.Point.some x3 y3 h3 ∈ E1 a b := (mem_E1_iff _).2 (Or.inr ⟨x3, y3, h3, rfl, hh⟩)
    have hP : Affine.Point.some x1 y1 h1 ∈ E1 a b := (mem_E1_iff _).2 (Or.inr ⟨x1, y1, h1, rfl, hx1⟩)
    have : Affine.Point.some (X2 : ℚ_[p]) (Y2 : ℚ_[p]) h2 ∈ E1 a b := by
      have e : Affine.Point.some (X2 : ℚ_[p]) (Y2 : ℚ_[p]) h2 =
          Affine.Point.some x3 y3 h3 + -Affine.Point.some x1 y1 h1 := by
        rw [← hsum]; abel
      rw [e]; exact add_mem_E1 hR (neg_mem_E1 hP)
    exact not_mem_E1_of_le hX2 this
  have e3 := shortCurve_equation h3.1
  have hy3 : ‖y3‖ ≤ 1 := norm_y_le_one (norm_coe_le_one a) (norm_coe_le_one b) hx3 e3
  obtain ⟨X3, Y3, hX3, hY3, -⟩ := int_lift h3 hx3
  subst hX3 hY3
  have H3 : (Y3 : ℚ_[p]) + Y2 = -ℓ * ((X3 : ℚ_[p]) - X2) := by
    rw [← hy3d]; linear_combination H1
  have hxn : ‖(X3 : ℚ_[p]) - X2‖ < 1 := by
    by_contra hh; push Not at hh
    have e := congrArg norm H3
    rw [norm_mul, norm_neg] at e
    have : ‖(Y3 : ℚ_[p]) + Y2‖ ≤ 1 :=
      (Padic.nonarchimedean _ _).trans (max_le (norm_coe_le_one Y3) hY2)
    nlinarith
  have hyn : ‖(Y3 : ℚ_[p]) - Y2‖ < 1 := by
    by_cases hxx : (X3 : ℚ_[p]) = X2
    · have hsum0 : (Y3 : ℚ_[p]) + Y2 = 0 := by rw [H3, hxx]; ring
      have hl2 : ℓ ^ 2 = x1 + 2 * X2 := by
        have := hx3d; rw [← hxx] at this; linear_combination this + 2 * hxx
      have hT := tangent_of_double_root hxne e1 e2 H1 hl2
      have hT' : ‖2 * ℓ * (Y2 : ℚ_[p])‖ ≤ 1 := by
        rw [hT]
        have := (3 * X2 ^ 2 + a : ℤ_[p]).norm_le_one
        rw [PadicInt.norm_def] at this; push_cast at this; exact this
      have e : (Y3 : ℚ_[p]) - Y2 = -(2 * Y2) := by linear_combination hsum0
      rw [e, norm_neg]
      by_contra hh; push Not at hh
      have : ‖2 * ℓ * (Y2 : ℚ_[p])‖ = ‖ℓ‖ * ‖2 * (Y2 : ℚ_[p])‖ := by
        rw [mul_comm 2 ℓ, mul_assoc, norm_mul]
      nlinarith [norm_nonneg ℓ]
    · have hd : (X3 : ℚ_[p]) - X2 ≠ 0 := sub_ne_zero.2 hxx
      have key : ℓ * ((Y3 : ℚ_[p]) - Y2) = -((X3 : ℚ_[p]) ^ 2 + X3 * X2 + X2 ^ 2 + a) := by
        apply mul_left_cancel₀ hd
        linear_combination ((Y3 : ℚ_[p]) - Y2) * H3 - e3 + e2
      have hS : ‖(X3 : ℚ_[p]) ^ 2 + X3 * X2 + X2 ^ 2 + a‖ ≤ 1 := by
        have := (X3 ^ 2 + X3 * X2 + X2 ^ 2 + a : ℤ_[p]).norm_le_one
        rw [PadicInt.norm_def] at this; push_cast at this; exact this
      have e := congrArg norm key
      rw [norm_mul, norm_neg] at e
      by_contra hh; push Not at hh
      nlinarith [norm_nonneg ℓ]
  have hxz : PadicInt.toZMod X3 = PadicInt.toZMod X2 := by
    rw [← sub_eq_zero, ← map_sub, toZMod_eq_zero_iff, PadicInt.norm_def]; push_cast; exact hxn
  have hyz : PadicInt.toZMod Y3 = PadicInt.toZMod Y2 := by
    rw [← sub_eq_zero, ← map_sub, toZMod_eq_zero_iff, PadicInt.norm_def]; push_cast; exact hyn
  rw [reducePoint_some_of_le (norm_coe_le_one _), residue_coe, residue_coe, hxz, hyz, hB]

/-- Reduction is additive on $E^0(\mathbb Q_p)$. -/
lemma red_add {a b : ℤ_[p]} {P Q : (curveQp a b).toAffine.Point} {A B : (curveFp a b).toAffine.Point}
    (hA : toProjCoords A = reducePoint P) (hB : toProjCoords B = reducePoint Q) :
    toProjCoords (A + B) = reducePoint (P + Q) := by
  cases P with
  | zero =>
    have := eq_zero_of_toProjCoords hA
    subst this
    have h0 : (Affine.Point.zero : (curveQp a b).toAffine.Point) = 0 := rfl
    rw [h0, zero_add, zero_add]; exact hB
  | some x1 y1 h1 =>
    cases Q with
    | zero =>
      have := eq_zero_of_toProjCoords hB
      subst this
      have h0 : (Affine.Point.zero : (curveQp a b).toAffine.Point) = 0 := rfl
      rw [h0, add_zero, add_zero]; exact hA
    | some x2 y2 h2 =>
      by_cases hx1 : ‖x1‖ ≤ 1
      · by_cases hx2 : ‖x2‖ ≤ 1
        · obtain ⟨X1, Y1, hX1, hY1, -⟩ := int_lift h1 hx1
          obtain ⟨X2, Y2, hX2, hY2, -⟩ := int_lift h2 hx2
          subst hX1 hY1 hX2 hY2
          rw [reducePoint_some_of_le hx1, residue_coe, residue_coe] at hA
          rw [reducePoint_some_of_le hx2, residue_coe, residue_coe] at hB
          exact red_add_int h1 h2 hA hB
        · obtain ⟨X1, Y1, hX1, hY1, -⟩ := int_lift h1 hx1
          subst hX1 hY1
          rw [reducePoint_some_of_le hx1, residue_coe, residue_coe] at hA
          rw [reducePoint_some_of_gt (not_le.1 hx2)] at hB
          have := eq_zero_of_toProjCoords hB
          subst this
          rw [add_comm (Affine.Point.some _ _ h1), add_zero]
          exact red_add_big h2 (not_le.1 hx2) h1 hA
      · by_cases hx2 : ‖x2‖ ≤ 1
        · obtain ⟨X2, Y2, hX2, hY2, -⟩ := int_lift h2 hx2
          subst hX2 hY2
          rw [reducePoint_some_of_le hx2, residue_coe, residue_coe] at hB
          rw [reducePoint_some_of_gt (not_le.1 hx1)] at hA
          have := eq_zero_of_toProjCoords hA
          subst this
          rw [zero_add]
          exact red_add_big h1 (not_le.1 hx1) h2 hB
        · rw [reducePoint_some_of_gt (not_le.1 hx1)] at hA
          rw [reducePoint_some_of_gt (not_le.1 hx2)] at hB
          have := eq_zero_of_toProjCoords hA
          have := eq_zero_of_toProjCoords hB
          subst_vars
          have hE : Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2 ∈ E1 a b :=
            add_mem_E1 ((mem_E1_iff _).2 (Or.inr ⟨x1, y1, h1, rfl, not_le.1 hx1⟩))
              ((mem_E1_iff _).2 (Or.inr ⟨x2, y2, h2, rfl, not_le.1 hx2⟩))
          rw [zero_add]
          exact hE.symm

/-- Reduction commutes with negation. -/
lemma red_neg {a b : ℤ_[p]} {P : (curveQp a b).toAffine.Point} {A : (curveFp a b).toAffine.Point}
    (hA : toProjCoords A = reducePoint P) : toProjCoords (-A) = reducePoint (-P) := by
  cases P with
  | zero =>
    have := eq_zero_of_toProjCoords hA
    subst this
    rfl
  | some x y h =>
    by_cases hx : ‖x‖ ≤ 1
    · obtain ⟨X, Y, hX, hY, -⟩ := int_lift h hx
      subst hX hY
      rw [reducePoint_some_of_le hx, residue_coe, residue_coe] at hA
      obtain ⟨hA', rfl⟩ := proj_some_eq hA
      have hneg : (curveQp a b).toAffine.negY (X : ℚ_[p]) (Y : ℚ_[p]) = ((-Y : ℤ_[p]) : ℚ_[p]) := by
        simp [Affine.negY]
      rw [Affine.Point.neg_some, Affine.Point.neg_some, reducePoint_some_of_le hx, hneg, residue_coe, residue_coe]
      simp [toProjCoords, Affine.negY]
    · rw [reducePoint_some_of_gt (not_le.1 hx)] at hA
      have := eq_zero_of_toProjCoords hA
      subst this
      have hm : -Affine.Point.some x y h ∈ E1 a b :=
        neg_mem_E1 ((mem_E1_iff _).2 (Or.inr ⟨x, y, h, rfl, not_le.1 hx⟩))
      exact hm.symm ▸ rfl

/-- Hensel's lemma in the form used for lifting points. -/
lemma exists_hensel_root {F : Polynomial ℤ_[p]} {x0 : ℤ_[p]} (h0 : PadicInt.toZMod (F.aeval x0) = 0)
    (h1 : PadicInt.toZMod (F.derivative.aeval x0) ≠ 0) :
    ∃ z : ℤ_[p], F.aeval z = 0 ∧ PadicInt.toZMod z = PadicInt.toZMod x0 := by
  have hu : ‖F.derivative.aeval x0‖ = 1 := PadicInt.isUnit_iff.1 (isUnit_of_toZMod_ne h1)
  have hn : ‖F.aeval x0‖ < ‖F.derivative.aeval x0‖ ^ 2 := by
    rw [hu, one_pow]; exact (toZMod_eq_zero_iff _).1 h0
  obtain ⟨z, hz, hzd, -, -⟩ := hensels_lemma hn
  refine ⟨z, hz, ?_⟩
  rw [hu] at hzd
  rw [← sub_eq_zero, ← map_sub, toZMod_eq_zero_iff]
  exact hzd

/-- Every point of $\bar E^{ns}(\mathbb F_p)$ lifts to $E^0(\mathbb Q_p)$ (Hensel). -/
lemma exists_lift {a b : ℤ_[p]} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (A : (curveFp a b).toAffine.Point) :
    ∃ P : (curveQp a b).toAffine.Point, toProjCoords A = reducePoint P := by
  cases A with
  | zero => exact ⟨0, rfl⟩
  | some u v hA =>
    obtain ⟨heqA, hns⟩ := shortCurve_nonsingular_iff.1 hA
    obtain ⟨X0, hX0⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) u
    obtain ⟨Y0, hY0⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) v
    have hΔq : 4 * (a : ℚ_[p]) ^ 3 + 27 * (b : ℚ_[p]) ^ 2 ≠ 0 := by
      intro h
      apply hΔ
      have h' : ((4 * a ^ 3 + 27 * b ^ 2 : ℤ_[p]) : ℚ_[p]) = 0 := by push_cast; exact h
      exact PadicInt.coe_eq_zero.1 h'
    have : (curveQp a b).IsElliptic := (isElliptic_shortCurve_iff _ _).2 hΔq
    -- a solution in `ℤ_[p]` of the equation reducing to `(u, v)`
    obtain ⟨X, Y, hXY, hXu, hYv⟩ : ∃ X Y : ℤ_[p], Y ^ 2 = X ^ 3 + a * X + b ∧
        PadicInt.toZMod X = u ∧ PadicInt.toZMod Y = v := by
      rcases hns with h | h
      · -- solve for `X` with `Y = Y0`
        let F : Polynomial ℤ_[p] := Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X +
          Polynomial.C (b - Y0 ^ 2)
        have hF : ∀ z : ℤ_[p], F.aeval z = z ^ 3 + a * z + b - Y0 ^ 2 := by
          intro z; simp [F]; ring
        have hF' : ∀ z : ℤ_[p], F.derivative.aeval z = 3 * z ^ 2 + a := by
          intro z; simp [F, Polynomial.derivative_pow]
        obtain ⟨z, hz, hzx⟩ := exists_hensel_root (F := F) (x0 := X0)
          (by rw [hF]; simp only [map_sub, map_add, map_mul, map_pow]; rw [hX0, hY0]; linear_combination heqA.symm)
          (by rw [hF']; simp only [map_add, map_mul, map_pow, map_ofNat]; rw [hX0]; exact h)
        refine ⟨z, Y0, ?_, by rw [hzx, hX0], hY0⟩
        rw [hF] at hz
        linear_combination -hz
      · -- solve for `Y` with `X = X0`
        let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C (X0 ^ 3 + a * X0 + b)
        have hF : ∀ z : ℤ_[p], F.aeval z = z ^ 2 - (X0 ^ 3 + a * X0 + b) := by
          intro z; simp [F]
        have hF' : ∀ z : ℤ_[p], F.derivative.aeval z = 2 * z := by
          intro z; simp [F, Polynomial.derivative_pow]
        obtain ⟨z, hz, hzy⟩ := exists_hensel_root (F := F) (x0 := Y0)
          (by rw [hF]; simp only [map_sub, map_add, map_mul, map_pow]; rw [hX0, hY0]; linear_combination heqA)
          (by rw [hF']; simp only [map_mul, map_ofNat]; rw [hY0]; exact h)
        refine ⟨X0, z, ?_, hX0, by rw [hzy, hY0]⟩
        rw [hF] at hz
        linear_combination hz
    have heq : (curveQp a b).toAffine.Equation (X : ℚ_[p]) (Y : ℚ_[p]) := by
      rw [Affine.equation_iff]
      simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, shortCurve_a₆]
      have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hXY
      simp only [PadicInt.coe_pow, PadicInt.coe_add, PadicInt.coe_mul] at this
      linear_combination this
    have hns' := (Affine.equation_iff_nonsingular).1 heq
    refine ⟨Affine.Point.some _ _ hns', ?_⟩
    rw [reducePoint_some_of_le (norm_coe_le_one _), residue_coe, residue_coe, hXu, hYv]
    rfl

/-- **Theorem 4.1 (b)** (pdf p. 70), proved: the named statement `Theorem4_1b` holds. -/
@[kb "milne2006ec" "Ch. II, Theorem 4.1 (b), pdf p. 70"]
theorem theorem_4_1_b : Theorem4_1b := by
  refine ⟨fun p _ a b hΔ => ?_⟩
  let G : AddSubgroup (curveQp a b).toAffine.Point :=
    { carrier := E0 a b
      zero_mem' := (mem_E0_iff_exists _).2 ⟨0, rfl⟩
      add_mem' := fun {P Q} hP hQ => by
        obtain ⟨A, hA⟩ := (mem_E0_iff_exists _).1 hP
        obtain ⟨B, hB⟩ := (mem_E0_iff_exists _).1 hQ
        exact (mem_E0_iff_exists _).2 ⟨A + B, red_add hA hB⟩
      neg_mem' := fun {P} hP => by
        obtain ⟨A, hA⟩ := (mem_E0_iff_exists _).1 hP
        exact (mem_E0_iff_exists _).2 ⟨-A, red_neg hA⟩ }
  refine ⟨G, rfl, ?_⟩
  choose ρ0 hρ0 using fun P : G => (mem_E0_iff_exists P.1).1 P.2
  have h0 : ρ0 0 = 0 := by
    apply toProjCoords_injective
    rw [hρ0]; rfl
  have hadd : ∀ P Q : G, ρ0 (P + Q) = ρ0 P + ρ0 Q := fun P Q => by
    apply toProjCoords_injective
    rw [hρ0]
    exact (red_add (hρ0 P) (hρ0 Q)).symm
  refine ⟨{ toFun := ρ0, map_zero' := h0, map_add' := hadd }, hρ0, ?_, ?_⟩
  · intro A
    obtain ⟨P, hP⟩ := exists_lift hΔ A
    have hPG : P ∈ G := (mem_E0_iff_exists P).2 ⟨A, hP⟩
    refine ⟨⟨P, hPG⟩, ?_⟩
    apply toProjCoords_injective
    show toProjCoords (ρ0 ⟨P, hPG⟩) = _
    rw [hρ0]; exact hP.symm
  · intro P
    show ρ0 P = 0 ↔ _
    constructor
    · intro h
      have := hρ0 P
      rw [h] at this
      exact this.symm
    · intro h
      apply eq_zero_of_toProjCoords
      rw [hρ0]; exact h

/-- **Corollary 5.7** (pdf p. 74), unconditional: if $E$ has good reduction at $p$ ($p \neq 2$ and
$p \nmid 4a^3 + 27b^2$), reduction is injective on $E(\mathbb Q)_{\mathrm{tors}}$ (`corollary_5_7` with
Theorem 4.1 (b) proved). -/
@[kb "milne2006ec" "Ch. II, Corollary 5.7, pdf p. 74"]
theorem corollary_5_7_unconditional (p : ℕ) [Fact p.Prime] {a b : ℤ} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (hp2 : p ≠ 2) (hgood : ¬(p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) :
    Set.InjOn (fun P => reducePoint (toQp p a b P)) {P : (curveQ a b).toAffine.Point | IsOfFinAddOrder P} :=
  corollary_5_7 p theorem_4_1_b hΔ hp2 hgood

end NumberFieldKB.MilneEC.II
