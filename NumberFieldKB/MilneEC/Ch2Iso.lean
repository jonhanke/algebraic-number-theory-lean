import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Short
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Milne, *Elliptic Curves*, Chapter II §2: Weierstrass equations over an arbitrary field (Theorem 2.4)

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

**Isomorphisms.** Mathlib has no regular maps of curves. An isomorphism $\varphi : (E', O') \to (E, O)$ of elliptic
curves in Weierstrass form restricts to an isomorphism $E' \smallsetminus \{O'\} \to E \smallsetminus \{O\}$ of
affine curves, i.e. (by the anti-equivalence between affine varieties and their coordinate rings, Milne I §4) to its
comorphism, a $k$-algebra isomorphism $k[E] \to k[E']$ of affine coordinate rings; conversely such an isomorphism
of nonsingular affine curves extends uniquely to the projective closures and sends $O'$ to $O$ (Milne I 4.18). So
Theorem 2.4 (b) is stated for $k$-algebra isomorphisms of Mathlib's `CoordinateRing`s.

Mathlib's `VariableChange` $(u, r, s, t)$ acts by `C • W = W'` where $x = u^2x' + r$, $y = u^3y' + su^2x' + t$:
exactly Milne's convention in Theorem 2.4 (b) (`variableChange_eq_iff` gives Milne's five equations).

Contents.
* Theorem 2.4 (a) (nonsingular iff $\Delta \neq 0$; the existence of a Weierstrass equation is Proposition 1.2 and
  the named statements of `Ch2Cubic.lean`), (b), (c).
* The map on points $(x', y') \mapsto (u^2x' + r, u^3y' + su^2x' + t)$ is an isomorphism of groups
  (`variableChangePointEquiv`), and the comorphism on coordinate rings (`variableChangeAlgEquiv`).
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve Polynomial

variable {k : Type*} [Field k]

/-- **Theorem 2.4 (b)**, Milne's equations (pdf p. 61): `C • W = W'` iff
$ua_1' = a_1 + 2s$, $u^2a_2' = a_2 - sa_1 + 3r - s^2$, $u^3a_3' = a_3 + ra_1 + 2t$,
$u^4a_4' = a_4 - sa_3 + 2ra_2 - (t + rs)a_1 + 3r^2 - 2st$,
$u^6a_6' = a_6 + ra_4 + r^2a_2 + r^3 - ta_3 - t^2 - rta_1$. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.4 (b), pdf p. 61"]
theorem variableChange_eq_iff {R : Type*} [CommRing R] (W W' : WeierstrassCurve R) (C : VariableChange R) :
    C • W = W' ↔
      (C.u : R) * W'.a₁ = W.a₁ + 2 * C.s ∧
      (C.u : R) ^ 2 * W'.a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 ∧
      (C.u : R) ^ 3 * W'.a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t ∧
      (C.u : R) ^ 4 * W'.a₄ = W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 -
        2 * C.s * C.t ∧
      (C.u : R) ^ 6 * W'.a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2 -
        C.r * C.t * W.a₁ := by
  have hu : (C.u : R) * (C.u⁻¹ : Rˣ) = 1 := C.u.mul_inv
  have hp := fun n : ℕ => pow_mul_pow_eq_one n hu
  constructor
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [variableChange_a₁]; linear_combination (W.a₁ + 2 * C.s) * hp 1
    · rw [variableChange_a₂]; linear_combination (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * hp 2
    · rw [variableChange_a₃]; linear_combination (W.a₃ + C.r * W.a₁ + 2 * C.t) * hp 3
    · rw [variableChange_a₄]
      linear_combination (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 -
        2 * C.s * C.t) * hp 4
    · rw [variableChange_a₆]
      linear_combination (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2 -
        C.r * C.t * W.a₁) * hp 6
  · rintro ⟨h1, h2, h3, h4, h6⟩
    ext
    · rw [variableChange_a₁]; linear_combination -(((C.u⁻¹ : Rˣ) : R) * h1) + W'.a₁ * hu
    · rw [variableChange_a₂]; linear_combination -(((C.u⁻¹ : Rˣ) : R) ^ 2 * h2) + W'.a₂ * hp 2
    · rw [variableChange_a₃]; linear_combination -(((C.u⁻¹ : Rˣ) : R) ^ 3 * h3) + W'.a₃ * hp 3
    · rw [variableChange_a₄]; linear_combination -(((C.u⁻¹ : Rˣ) : R) ^ 4 * h4) + W'.a₄ * hp 4
    · rw [variableChange_a₆]; linear_combination -(((C.u⁻¹ : Rˣ) : R) ^ 6 * h6) + W'.a₆ * hp 6

/-- The coefficients of `W` in terms of those of `C • W` (the equations of `variableChange_eq_iff`, solved). -/
theorem variableChange_coeffs {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R) :
    W.a₁ = (C.u : R) * (C • W).a₁ - 2 * C.s ∧
    W.a₂ = (C.u : R) ^ 2 * (C • W).a₂ + C.s * W.a₁ - 3 * C.r + C.s ^ 2 ∧
    W.a₃ = (C.u : R) ^ 3 * (C • W).a₃ - C.r * W.a₁ - 2 * C.t ∧
    W.a₄ = (C.u : R) ^ 4 * (C • W).a₄ + C.s * W.a₃ - 2 * C.r * W.a₂ + (C.t + C.r * C.s) * W.a₁ -
      3 * C.r ^ 2 + 2 * C.s * C.t ∧
    W.a₆ = (C.u : R) ^ 6 * (C • W).a₆ - C.r * W.a₄ - C.r ^ 2 * W.a₂ - C.r ^ 3 + C.t * W.a₃ + C.t ^ 2 +
      C.r * C.t * W.a₁ := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := (variableChange_eq_iff W (C • W) C).mp rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -h1
  · linear_combination -h2
  · linear_combination -h3
  · linear_combination -h4
  · linear_combination -h6

/-- The Weierstrass equation and its partial derivatives transform under a change of variables: with
$X = u^2x + r$, $Y = u^3y + su^2x + t$ one has $F(X, Y) = u^6F'(x, y)$, $F_Y(X, Y) = u^3F'_y(x, y)$ and
$F_X(X, Y) + sF_Y(X, Y) = u^4F'_x(x, y)$. -/
theorem variableChange_identities (W : WeierstrassCurve k) (C : VariableChange k) (x y : k) :
    let u := (C.u : k)
    let X := u ^ 2 * x + C.r
    let Y := u ^ 3 * y + C.s * u ^ 2 * x + C.t
    (Y ^ 2 + W.a₁ * X * Y + W.a₃ * Y - (X ^ 3 + W.a₂ * X ^ 2 + W.a₄ * X + W.a₆) =
      u ^ 6 * (y ^ 2 + (C • W).a₁ * x * y + (C • W).a₃ * y -
        (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆))) ∧
    (2 * Y + W.a₁ * X + W.a₃ = u ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃)) ∧
    ((W.a₁ * Y - (3 * X ^ 2 + 2 * W.a₂ * X + W.a₄)) + C.s * (2 * Y + W.a₁ * X + W.a₃) =
      u ^ 4 * ((C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄))) := by
  obtain ⟨e1, e2, e3, e4, e6⟩ := variableChange_coeffs W C
  intro u X Y
  simp only [X, Y, u]
  simp only [e6, e4, e3, e2, e1]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- A point is a nonsingular point of `C • W` iff its image $(u^2x + r, u^3y + su^2x + t)$ is a nonsingular
point of `W`. -/
theorem variableChange_nonsingular_iff (W : WeierstrassCurve k) (C : VariableChange k) (x y : k) :
    (C • W).toAffine.Nonsingular x y ↔
      W.toAffine.Nonsingular ((C.u : k) ^ 2 * x + C.r) ((C.u : k) ^ 3 * y + C.s * (C.u : k) ^ 2 * x + C.t) := by
  obtain ⟨hE, hY, hX⟩ := variableChange_identities W C x y
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  simp only [Affine.nonsingular_iff', Affine.equation_iff']
  rw [hE]
  have hX' : W.a₁ * ((C.u : k) ^ 3 * y + C.s * (C.u : k) ^ 2 * x + C.t) -
      (3 * ((C.u : k) ^ 2 * x + C.r) ^ 2 + 2 * W.a₂ * ((C.u : k) ^ 2 * x + C.r) + W.a₄) =
      (C.u : k) ^ 4 * ((C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄)) -
        C.s * ((C.u : k) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃)) := by
    rw [← hY, ← hX]; ring
  have h6 : (C.u : k) ^ 6 ≠ 0 := pow_ne_zero _ hu
  have h4 : (C.u : k) ^ 4 ≠ 0 := pow_ne_zero _ hu
  have h3 : (C.u : k) ^ 3 ≠ 0 := pow_ne_zero _ hu
  have key : ∀ F A B : k, (F = 0 ∧ (A ≠ 0 ∨ B ≠ 0)) ↔
      ((C.u : k) ^ 6 * F = 0 ∧ ((C.u : k) ^ 4 * A - C.s * ((C.u : k) ^ 3 * B) ≠ 0 ∨ (C.u : k) ^ 3 * B ≠ 0)) := by
    intro F A B
    simp only [mul_eq_zero, h6, h3, false_or, ne_eq]
    constructor
    · rintro ⟨hF, hAB⟩
      refine ⟨hF, ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      rcases hAB with hA | hB
      · apply hA
        have : B = 0 := h2
        rw [this, mul_zero, mul_zero, sub_zero] at h1
        simpa [h4] using h1
      · exact hB h2
    · rintro ⟨hF, hAB⟩
      refine ⟨hF, ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      apply hAB.elim
      · intro h; apply h
        rw [h1, h2]; ring
      · exact fun h => h (by rw [h2])
  rw [hX', hY]
  exact key _ _ _

/-- The map on points of Theorem 2.4 (b): $(x', y') \mapsto (u^2x' + r, u^3y' + su^2x' + t)$ sends nonsingular
points of `C • W` to nonsingular points of `W`. -/
theorem variableChange_nonsingular (W : WeierstrassCurve k) (C : VariableChange k) {x y : k}
    (h : (C • W).toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular ((C.u : k) ^ 2 * x + C.r) ((C.u : k) ^ 3 * y + C.s * (C.u : k) ^ 2 * x + C.t) :=
  (variableChange_nonsingular_iff W C x y).mp h

/-- The negation formula is compatible with the change of variables. -/
theorem variableChange_negY (W : WeierstrassCurve k) (C : VariableChange k) (x y : k) :
    W.toAffine.negY ((C.u : k) ^ 2 * x + C.r) ((C.u : k) ^ 3 * y + C.s * (C.u : k) ^ 2 * x + C.t) =
      (C.u : k) ^ 3 * (C • W).toAffine.negY x y + C.s * (C.u : k) ^ 2 * x + C.t := by
  obtain ⟨e1, e2, e3, e4, e6⟩ := variableChange_coeffs W C
  simp only [Affine.negY]
  rw [e3, e1]
  ring

/-- The slope of the secant or tangent line transforms as $\ell = u\ell' + s$. -/
theorem variableChange_slope [DecidableEq k] (W : WeierstrassCurve k) (C : VariableChange k) {x₁ x₂ y₁ y₂ : k}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : k) ^ 2 * x₁ + C.r) ((C.u : k) ^ 2 * x₂ + C.r)
        ((C.u : k) ^ 3 * y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t) ((C.u : k) ^ 3 * y₂ + C.s * (C.u : k) ^ 2 * x₂ + C.t) =
      (C.u : k) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  obtain ⟨e1, e2, e3, e4, e6⟩ := variableChange_coeffs W C
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hy2 : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hy2
    have hD : y₁ - (C • W).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hy' : (C.u : k) ^ 3 * y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t ≠
        W.toAffine.negY ((C.u : k) ^ 2 * x₁ + C.r) ((C.u : k) ^ 3 * y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t) := by
      rw [variableChange_negY]
      intro h
      apply hy
      have : (C.u : k) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (pow_ne_zero _ hu)
      · exact absurd h0 hD
    rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy, variableChange_negY]
    have hnum : 3 * ((C.u : k) ^ 2 * x₁ + C.r) ^ 2 + 2 * W.toAffine.a₂ * ((C.u : k) ^ 2 * x₁ + C.r) +
        W.toAffine.a₄ - W.toAffine.a₁ * ((C.u : k) ^ 3 * y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t) =
        (C.u : k) ^ 4 * (3 * x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * x₁ + (C • W).toAffine.a₄ -
          (C • W).toAffine.a₁ * y₁) + C.s * ((C.u : k) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁)) := by
      simp only [Affine.negY]
      rw [e4, e3, e2, e1]
      ring
    have hden : (C.u : k) ^ 3 * y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t -
        ((C.u : k) ^ 3 * (C • W).toAffine.negY x₁ y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t) =
        (C.u : k) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁) := by ring
    rw [hnum, hden]
    have h3 : (C.u : k) ^ 3 ≠ 0 := pow_ne_zero _ hu
    field_simp
  · rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne]
    · have : (C.u : k) ^ 2 * (x₁ - x₂) ≠ 0 := mul_ne_zero (pow_ne_zero _ hu) (sub_ne_zero.mpr hx)
      have hx' : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hden : (C.u : k) ^ 2 * x₁ + C.r - ((C.u : k) ^ 2 * x₂ + C.r) = (C.u : k) ^ 2 * (x₁ - x₂) := by ring
      rw [hden]
      field_simp
      ring
    · intro h
      apply hx
      have : (C.u : k) ^ 2 * (x₁ - x₂) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (pow_ne_zero _ hu)
      · exact sub_eq_zero.mp h0

/-- The $x$-coordinate of the addition formula is compatible with the change of variables. -/
theorem variableChange_addX (W : WeierstrassCurve k) (C : VariableChange k) (x₁ x₂ ℓ : k) :
    W.toAffine.addX ((C.u : k) ^ 2 * x₁ + C.r) ((C.u : k) ^ 2 * x₂ + C.r) ((C.u : k) * ℓ + C.s) =
      (C.u : k) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  obtain ⟨e1, e2, e3, e4, e6⟩ := variableChange_coeffs W C
  simp only [Affine.addX]
  rw [e2, e1]
  ring

/-- The $y$-coordinate of the addition formula is compatible with the change of variables. -/
theorem variableChange_addY (W : WeierstrassCurve k) (C : VariableChange k) (x₁ x₂ y₁ ℓ : k) :
    W.toAffine.addY ((C.u : k) ^ 2 * x₁ + C.r) ((C.u : k) ^ 2 * x₂ + C.r)
        ((C.u : k) ^ 3 * y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t) ((C.u : k) * ℓ + C.s) =
      (C.u : k) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ +
        C.s * (C.u : k) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  have hn : W.toAffine.negAddY ((C.u : k) ^ 2 * x₁ + C.r) ((C.u : k) ^ 2 * x₂ + C.r)
        ((C.u : k) ^ 3 * y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t) ((C.u : k) * ℓ + C.s) =
      (C.u : k) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ +
        C.s * (C.u : k) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
    simp only [Affine.negAddY]
    rw [variableChange_addX]
    ring
  simp only [Affine.addY]
  rw [variableChange_addX, hn, variableChange_negY]

/-- Two points with equal coordinates are equal. -/
theorem point_some_congr {W : Affine k} {a b c d : k} {h : W.Nonsingular a b} {h' : W.Nonsingular c d}
    (hac : a = c) (hbd : b = d) : Affine.Point.some a b h = Affine.Point.some c d h' := by
  subst hac; subst hbd; rfl

/-- The inverse of the change of variables on nonsingular points. -/
theorem variableChange_nonsingular_inv (W : WeierstrassCurve k) (C : VariableChange k) {x y : k}
    (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (((C.u : k)⁻¹) ^ 2 * (x - C.r))
      (((C.u : k)⁻¹) ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  rw [variableChange_nonsingular_iff]
  have hx : (C.u : k) ^ 2 * (((C.u : k)⁻¹) ^ 2 * (x - C.r)) + C.r = x := by field_simp; ring
  have hy : (C.u : k) ^ 3 * (((C.u : k)⁻¹) ^ 3 * (y - C.s * (x - C.r) - C.t)) +
      C.s * (C.u : k) ^ 2 * (((C.u : k)⁻¹) ^ 2 * (x - C.r)) + C.t = y := by field_simp; ring
  rw [hx, hy]
  exact h

/-- The map on points underlying `variableChangePointEquiv`. -/
noncomputable def variableChangePointFwd (W : WeierstrassCurve k) (C : VariableChange k) :
    (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some _ _ h => .some _ _ (variableChange_nonsingular W C h)

/-- The inverse map on points underlying `variableChangePointEquiv`. -/
noncomputable def variableChangePointBwd (W : WeierstrassCurve k) (C : VariableChange k) :
    W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some _ _ h => .some _ _ (variableChange_nonsingular_inv W C h)

/-- **Theorem 2.4 (b)**, converse (pdf p. 61): the change of variables
$(x : y : z) \mapsto (u^2x + rz : u^3y + su^2x + tz : z)$ is an isomorphism from `C • W` onto `W` sending $O$
to $O$; on points it is an isomorphism of groups. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.4 (b), converse, pdf p. 61"]
noncomputable def variableChangePointEquiv [DecidableEq k] (W : WeierstrassCurve k) (C : VariableChange k) :
    (C • W).toAffine.Point ≃+ W.toAffine.Point where
  toFun := variableChangePointFwd W C
  invFun := variableChangePointBwd W C
  left_inv := by
    have hu : (C.u : k) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · apply point_some_congr
      · field_simp; ring
      · field_simp; ring
  right_inv := by
    have hu : (C.u : k) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · apply point_some_congr
      · field_simp; ring
      · field_simp; ring
  map_add' := by
    have hu : (C.u : k) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    · rfl
    · rfl
    · rfl
    · by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
      · obtain ⟨hx, hy⟩ := hxy
        subst hx
        rw [Affine.Point.add_of_Y_eq rfl hy]
        change (0 : W.toAffine.Point) = _
        symm
        apply Affine.Point.add_of_Y_eq rfl
        rw [variableChange_negY, hy]
      · have hxy' : ¬((C.u : k) ^ 2 * x₁ + C.r = (C.u : k) ^ 2 * x₂ + C.r ∧
            (C.u : k) ^ 3 * y₁ + C.s * (C.u : k) ^ 2 * x₁ + C.t =
              W.toAffine.negY ((C.u : k) ^ 2 * x₂ + C.r) ((C.u : k) ^ 3 * y₂ + C.s * (C.u : k) ^ 2 * x₂ + C.t)) := by
          rintro ⟨hx, hy⟩
          apply hxy
          have hx2 : x₁ = x₂ := by
            have : (C.u : k) ^ 2 * (x₁ - x₂) = 0 := by linear_combination hx
            rcases mul_eq_zero.mp this with h0 | h0
            · exact absurd h0 (pow_ne_zero _ hu)
            · exact sub_eq_zero.mp h0
          subst hx2
          refine ⟨rfl, ?_⟩
          rw [variableChange_negY] at hy
          have : (C.u : k) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₂) = 0 := by linear_combination hy
          rcases mul_eq_zero.mp this with h0 | h0
          · exact absurd h0 (pow_ne_zero _ hu)
          · exact sub_eq_zero.mp h0
        change variableChangePointFwd W C (_ + _) = variableChangePointFwd W C _ + variableChangePointFwd W C _
        rw [Affine.Point.add_some hxy]
        simp only [variableChangePointFwd]
        rw [Affine.Point.add_some hxy']
        apply point_some_congr
        · rw [variableChange_slope W C h₁.1 h₂.1 hxy, variableChange_addX]
        · rw [variableChange_slope W C h₁.1 h₂.1 hxy, variableChange_addY]

/-- The formula for `variableChangePointEquiv`. -/
theorem variableChangePointEquiv_some [DecidableEq k] (W : WeierstrassCurve k) (C : VariableChange k) {x y : k}
    (h : (C • W).toAffine.Nonsingular x y) :
    variableChangePointEquiv W C (.some x y h) =
      .some _ _ (variableChange_nonsingular W C h) := rfl

/-- The Weierstrass polynomial of `W` evaluated at $(\xi, \eta)$ in a commutative `k`-algebra. -/
def wpoly {T : Type*} [CommRing T] [Algebra k T] (W : WeierstrassCurve k) (ξ η : T) : T :=
  η ^ 2 + algebraMap k T W.a₁ * ξ * η + algebraMap k T W.a₃ * η -
    (ξ ^ 3 + algebraMap k T W.a₂ * ξ ^ 2 + algebraMap k T W.a₄ * ξ + algebraMap k T W.a₆)

/-- Evaluating the Weierstrass polynomial of `W` (a polynomial in `Y` over `k[X]`) at $X = \xi$, $Y = \eta$. -/
theorem eval₂_polynomial_aeval {T : Type*} [CommRing T] [Algebra k T] (W : WeierstrassCurve k) (ξ η : T) :
    W.toAffine.polynomial.eval₂ ((Polynomial.aeval ξ : k[X] →ₐ[k] T) : k[X] →+* T) η = wpoly W ξ η := by
  simp [Affine.polynomial, wpoly, Polynomial.eval₂_pow]
  ring

/-- The change-of-variables identity of `variableChange_identities`, in a commutative `k`-algebra. -/
theorem variableChange_wpoly {T : Type*} [CommRing T] [Algebra k T] (W : WeierstrassCurve k)
    (C : VariableChange k) (x y : T) :
    wpoly W (algebraMap k T ((C.u : k) ^ 2) * x + algebraMap k T C.r)
        (algebraMap k T ((C.u : k) ^ 3) * y + algebraMap k T (C.s * (C.u : k) ^ 2) * x + algebraMap k T C.t) =
      algebraMap k T ((C.u : k) ^ 6) * wpoly (C • W) x y := by
  obtain ⟨e1, e2, e3, e4, e6⟩ := variableChange_coeffs W C
  have f1 := congrArg (algebraMap k T) e1
  have f2 := congrArg (algebraMap k T) e2
  have f3 := congrArg (algebraMap k T) e3
  have f4 := congrArg (algebraMap k T) e4
  have f6 := congrArg (algebraMap k T) e6
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at f1 f2 f3 f4 f6 ⊢
  unfold wpoly
  rw [f6, f4, f3, f2, f1]
  ring

/-- The coordinate functions $x, y$ satisfy the Weierstrass equation in the coordinate ring. -/
theorem wpoly_root (W : WeierstrassCurve k) :
    wpoly W (Affine.CoordinateRing.mk W (Polynomial.C X)) (Affine.CoordinateRing.mk W X) = 0 := by
  rw [← eval₂_polynomial_aeval]
  have : ((Polynomial.aeval (Affine.CoordinateRing.mk W (Polynomial.C X)) :
      k[X] →ₐ[k] W.toAffine.CoordinateRing) : k[X] →+* W.toAffine.CoordinateRing) =
      AdjoinRoot.of W.toAffine.polynomial := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [Polynomial.coe_aeval_eq_eval, AlgHom.coe_toRingHom, Polynomial.aeval_C]
      rw [IsScalarTower.algebraMap_apply k k[X] W.toAffine.CoordinateRing a, AdjoinRoot.algebraMap_eq]
      rfl
    · simp
  rw [this]
  exact AdjoinRoot.eval₂_root _

/-- The comorphism of a change of variables $W_2 = C \bullet W_1$ on affine coordinate rings, as a
`k`-algebra homomorphism $k[W_1] \to k[W_2]$ (general form of `variableChangeAlgEquiv`). -/
noncomputable def variableChangeAlgHom (W₁ W₂ : WeierstrassCurve k) (C : VariableChange k)
    (hC : W₂ = C • W₁) : W₁.toAffine.CoordinateRing →ₐ[k] W₂.toAffine.CoordinateRing :=
  AdjoinRoot.liftAlgHom W₁.toAffine.polynomial
    (Polynomial.aeval (algebraMap k _ ((C.u : k) ^ 2) * Affine.CoordinateRing.mk W₂ (Polynomial.C X) +
      algebraMap k _ C.r))
    (algebraMap k _ ((C.u : k) ^ 3) * Affine.CoordinateRing.mk W₂ X +
      algebraMap k _ (C.s * (C.u : k) ^ 2) * Affine.CoordinateRing.mk W₂ (Polynomial.C X) + algebraMap k _ C.t)
    (by
      rw [eval₂_polynomial_aeval, variableChange_wpoly, ← hC, wpoly_root, mul_zero])

/-- `variableChangeAlgHom` on the coordinate function $x$. -/
theorem variableChangeAlgHom_x (W₁ W₂ : WeierstrassCurve k) (C : VariableChange k) (hC : W₂ = C • W₁) :
    variableChangeAlgHom W₁ W₂ C hC (Affine.CoordinateRing.mk W₁ (Polynomial.C X)) =
      algebraMap k _ ((C.u : k) ^ 2) * Affine.CoordinateRing.mk W₂ (Polynomial.C X) + algebraMap k _ C.r := by
  simp [variableChangeAlgHom]

/-- `variableChangeAlgHom` on the coordinate function $y$. -/
theorem variableChangeAlgHom_y (W₁ W₂ : WeierstrassCurve k) (C : VariableChange k) (hC : W₂ = C • W₁) :
    variableChangeAlgHom W₁ W₂ C hC (Affine.CoordinateRing.mk W₁ X) =
      algebraMap k _ ((C.u : k) ^ 3) * Affine.CoordinateRing.mk W₂ X +
        algebraMap k _ (C.s * (C.u : k) ^ 2) * Affine.CoordinateRing.mk W₂ (Polynomial.C X) +
          algebraMap k _ C.t := by
  simp [variableChangeAlgHom]

/-- Two `k`-algebra homomorphisms out of the coordinate ring agree if they agree on the coordinate
functions $x$ and $y$. -/
theorem coordinateRing_algHom_ext (W : WeierstrassCurve k) {A : Type*} [CommRing A] [Algebra k A]
    {f g : W.toAffine.CoordinateRing →ₐ[k] A}
    (hx : f (Affine.CoordinateRing.mk W (Polynomial.C X)) = g (Affine.CoordinateRing.mk W (Polynomial.C X)))
    (hy : f (Affine.CoordinateRing.mk W X) = g (Affine.CoordinateRing.mk W X)) : f = g := by
  apply AlgHom.toRingHom_injective
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      have : (AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C a) =
          algebraMap k W.toAffine.CoordinateRing a := by
        rw [IsScalarTower.algebraMap_apply k k[X] W.toAffine.CoordinateRing a, AdjoinRoot.algebraMap_eq]
        rfl
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this, AlgHom.commutes]
    · exact hx
  · exact hy

/-- The unit $u$ and its inverse multiply to one in any `k`-algebra. -/
theorem algebraMap_inv_mul {A : Type*} [CommRing A] [Algebra k A] (C : VariableChange k) :
    algebraMap k A (C.u : k) * algebraMap k A ((C.u⁻¹ : kˣ) : k) = 1 := by
  rw [← map_mul, C.u.mul_inv, map_one]

/-- The comorphism of the change of variables on affine coordinate rings: $x \mapsto u^2x' + r$,
$y \mapsto u^3y' + su^2x' + t$, an isomorphism $k[W] \cong k[C \bullet W]$ of $k$-algebras. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.4 (b), converse, pdf p. 61"]
noncomputable def variableChangeAlgEquiv (W : WeierstrassCurve k) (C : VariableChange k) :
    W.toAffine.CoordinateRing ≃ₐ[k] (C • W).toAffine.CoordinateRing :=
  AlgEquiv.ofAlgHom (variableChangeAlgHom W (C • W) C rfl)
    (variableChangeAlgHom (C • W) W C⁻¹ (by rw [smul_smul, inv_mul_cancel, one_smul]))
    (by
      apply coordinateRing_algHom_ext
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, variableChangeAlgHom_x, map_add, map_mul,
          AlgHom.commutes, VariableChange.inv_def, map_pow, map_neg, map_sub]
        have hab := algebraMap_inv_mul (k := k) (A := (C • W).toAffine.CoordinateRing) C
        generalize algebraMap k (C • W).toAffine.CoordinateRing (C.u : k) = a at hab ⊢
        generalize algebraMap k (C • W).toAffine.CoordinateRing ((C.u⁻¹ : kˣ) : k) = b at hab ⊢
        linear_combination (Affine.CoordinateRing.mk (C • W) (Polynomial.C X) * (a * b + 1)) * hab
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, variableChangeAlgHom_x, variableChangeAlgHom_y,
          map_add, map_mul, AlgHom.commutes, VariableChange.inv_def, map_pow, map_neg, map_sub]
        have hab := algebraMap_inv_mul (k := k) (A := (C • W).toAffine.CoordinateRing) C
        generalize algebraMap k (C • W).toAffine.CoordinateRing (C.u : k) = a at hab ⊢
        generalize algebraMap k (C • W).toAffine.CoordinateRing ((C.u⁻¹ : kˣ) : k) = b at hab ⊢
        generalize algebraMap k (C • W).toAffine.CoordinateRing C.s = s
        generalize algebraMap k (C • W).toAffine.CoordinateRing C.r = r
        generalize algebraMap k (C • W).toAffine.CoordinateRing C.t = t
        linear_combination (Affine.CoordinateRing.mk (C • W) X * (a ^ 2 * b ^ 2 + a * b + 1)) * hab)
    (by
      apply coordinateRing_algHom_ext
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, variableChangeAlgHom_x, map_add, map_mul,
          AlgHom.commutes, VariableChange.inv_def, map_pow, map_neg]
        have hab := algebraMap_inv_mul (k := k) (A := W.toAffine.CoordinateRing) C
        generalize algebraMap k W.toAffine.CoordinateRing (C.u : k) = a at hab ⊢
        generalize algebraMap k W.toAffine.CoordinateRing ((C.u⁻¹ : kˣ) : k) = b at hab ⊢
        generalize algebraMap k W.toAffine.CoordinateRing C.r = r
        linear_combination ((Affine.CoordinateRing.mk W (Polynomial.C X) - r) * (a * b + 1)) * hab
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, variableChangeAlgHom_x, variableChangeAlgHom_y,
          map_add, map_mul, AlgHom.commutes, VariableChange.inv_def, map_pow, map_neg, map_sub]
        have hab := algebraMap_inv_mul (k := k) (A := W.toAffine.CoordinateRing) C
        generalize algebraMap k W.toAffine.CoordinateRing (C.u : k) = a at hab ⊢
        generalize algebraMap k W.toAffine.CoordinateRing ((C.u⁻¹ : kˣ) : k) = b at hab ⊢
        generalize algebraMap k W.toAffine.CoordinateRing C.s = s
        generalize algebraMap k W.toAffine.CoordinateRing C.r = r
        generalize algebraMap k W.toAffine.CoordinateRing C.t = t
        linear_combination (Affine.CoordinateRing.mk W X * (a ^ 2 * b ^ 2 + a * b + 1) -
          s * a ^ 2 * b ^ 2 * Affine.CoordinateRing.mk W (Polynomial.C X) +
          (r * s - t) * (a ^ 2 * b ^ 2 + a * b + 1) - r * s * (a * b + 1)) * hab)

/-- The formula for `variableChangeAlgEquiv` on the coordinate functions $x$ and $y$. -/
theorem variableChangeAlgEquiv_apply (W : WeierstrassCurve k) (C : VariableChange k) :
    variableChangeAlgEquiv W C (Affine.CoordinateRing.mk W (Polynomial.C X)) =
        algebraMap k _ ((C.u : k) ^ 2) * Affine.CoordinateRing.mk (C • W) (Polynomial.C X) + algebraMap k _ C.r ∧
      variableChangeAlgEquiv W C (Affine.CoordinateRing.mk W X) =
        algebraMap k _ ((C.u : k) ^ 3) * Affine.CoordinateRing.mk (C • W) X +
          algebraMap k _ (C.s * (C.u : k) ^ 2) * Affine.CoordinateRing.mk (C • W) (Polynomial.C X) + algebraMap k _ C.t :=
  ⟨variableChangeAlgHom_x W (C • W) C rfl, variableChangeAlgHom_y W (C • W) C rfl⟩

/-- Characteristic different from two: a vanishing discriminant gives a repeated root of the
two-torsion polynomial, which is the $x$-coordinate of a singular point. -/
theorem exists_singular_of_Δ_eq_zero_of_ne_two {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) (h2 : (2 : K) ≠ 0) (hΔ : W.Δ = 0) :
    ∃ x y : K, y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 ∧
      W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 ∧ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := h4
  obtain ⟨x, y, z, h3⟩ := (Cubic.splits_iff_roots_eq_three (φ := RingHom.id K) ha).mp
    (IsAlgClosed.splits_domain _)
  have hb := Cubic.b_eq_three_roots ha h3
  have hc := Cubic.c_eq_three_roots ha h3
  have hd := Cubic.d_eq_three_roots ha h3
  have hdisc := Cubic.discr_eq_prod_three_roots ha h3
  rw [twoTorsionPolynomial_discr, hΔ, mul_zero] at hdisc
  simp only [twoTorsionPolynomial, RingHom.id_apply, map_zero] at hb hc hd hdisc
  have key : ∀ x0 : K, 4 * x0 ^ 3 + W.b₂ * x0 ^ 2 + 2 * W.b₄ * x0 + W.b₆ = 0 →
      12 * x0 ^ 2 + 2 * W.b₂ * x0 + 2 * W.b₄ = 0 →
      ∃ x y : K, y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 ∧
        W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 ∧ 2 * y + W.a₁ * x + W.a₃ = 0 := by
    intro x0 hf hf'
    obtain ⟨y0, hy2⟩ : ∃ y0 : K, 2 * y0 + W.a₁ * x0 + W.a₃ = 0 :=
      ⟨-(W.a₁ * x0 + W.a₃) / 2, by field_simp; ring⟩
    simp only [b₂, b₄, b₆] at hf hf'
    refine ⟨x0, y0, ?_, ?_, hy2⟩
    · apply mul_left_cancel₀ h4
      linear_combination (2 * y0 + W.a₁ * x0 + W.a₃) * hy2 - hf
    · apply mul_left_cancel₀ h4
      linear_combination 2 * W.a₁ * hy2 - hf'
  have hz : (4 : K) * 4 * (x - y) * (x - z) * (y - z) = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 hdisc.symm
    simpa using this
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (mul_ne_zero h4 h4)
      · have := sub_eq_zero.mp h
        subst this
        exact key x (by linear_combination x ^ 2 * hb + x * hc + hd)
          (by linear_combination 2 * x * hb + hc)
    · have := sub_eq_zero.mp h
      subst this
      exact key x (by linear_combination x ^ 2 * hb + x * hc + hd)
        (by linear_combination 2 * x * hb + hc)
  · have := sub_eq_zero.mp h
    subst this
    exact key y (by linear_combination y ^ 2 * hb + y * hc + hd)
      (by linear_combination 2 * y * hb + hc)

/-- Characteristic two: a vanishing discriminant gives a singular point. -/
theorem exists_singular_of_Δ_eq_zero_of_two {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2]
    (W : WeierstrassCurve K) (hΔ : W.Δ = 0) :
    ∃ x y : K, y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 ∧
      W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 ∧ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  simp only [Δ, b₂, b₄, b₆, b₈] at hΔ
  by_cases h1 : W.a₁ = 0
  · have h3 : W.a₃ ^ 4 = 0 := by
      rw [h1] at hΔ
      grind
    have h3 : W.a₃ = 0 := pow_eq_zero_iff (by norm_num) |>.1 h3
    obtain ⟨x0, hx0⟩ := IsAlgClosed.exists_pow_nat_eq W.a₄ (n := 2) (by norm_num)
    obtain ⟨y0, hy0⟩ := IsAlgClosed.exists_pow_nat_eq
      (x0 ^ 3 + W.a₂ * x0 ^ 2 + W.a₄ * x0 + W.a₆) (n := 2) (by norm_num)
    refine ⟨x0, y0, ?_, ?_, ?_⟩
    · rw [h1, h3]; linear_combination hy0
    · rw [h1]; grind
    · rw [h1, h3]; grind
  · refine ⟨W.a₃ / W.a₁, ((W.a₃ / W.a₁) ^ 2 + W.a₄) / W.a₁, ?_, ?_, ?_⟩
    · field_simp
      grind
    · field_simp
      grind
    · field_simp
      grind

/-- **Theorem 2.4 (a)**, second statement (pdf p. 61): the curve $E(a_1, \dots, a_6)$ is nonsingular iff
$\Delta \neq 0$. (The first statement, that every elliptic curve has a Weierstrass equation, is
`proposition_1_2` for curves as in Definition 1.1 (b), and the named statement `NagellReduction` for curves as in
Definition 1.1 (a), both in `Ch2Cubic.lean`; form (d), a genus 1 curve, is not formalized here: Mathlib has no
genus of a curve.) -/
@[kb "milne2006ec" "Ch. II, Theorem 2.4 (a), pdf p. 61"]
theorem theorem_2_4_a_nonsingular (W : WeierstrassCurve k) : IsNonsingularCurve W ↔ W.Δ ≠ 0 := by
  unfold IsNonsingularCurve
  have hΔK : (W.baseChange (AlgebraicClosure k)).Δ = algebraMap k (AlgebraicClosure k) W.Δ :=
    WeierstrassCurve.map_Δ W (algebraMap k (AlgebraicClosure k))
  have hinj : algebraMap k (AlgebraicClosure k) W.Δ = 0 ↔ W.Δ = 0 :=
    map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective
  constructor
  · intro H h0
    have hΔ0 : (W.baseChange (AlgebraicClosure k)).Δ = 0 := by rw [hΔK, hinj]; exact h0
    obtain ⟨x0, y0, hF, hFx, hFy⟩ : ∃ x y : AlgebraicClosure k,
        y ^ 2 + (W.baseChange (AlgebraicClosure k)).a₁ * x * y + (W.baseChange (AlgebraicClosure k)).a₃ * y -
          (x ^ 3 + (W.baseChange (AlgebraicClosure k)).a₂ * x ^ 2 +
            (W.baseChange (AlgebraicClosure k)).a₄ * x + (W.baseChange (AlgebraicClosure k)).a₆) = 0 ∧
        (W.baseChange (AlgebraicClosure k)).a₁ * y -
          (3 * x ^ 2 + 2 * (W.baseChange (AlgebraicClosure k)).a₂ * x +
            (W.baseChange (AlgebraicClosure k)).a₄) = 0 ∧
        2 * y + (W.baseChange (AlgebraicClosure k)).a₁ * x + (W.baseChange (AlgebraicClosure k)).a₃ = 0 := by
      by_cases h2 : (2 : AlgebraicClosure k) = 0
      · haveI : CharP (AlgebraicClosure k) 2 := by
          have := CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact_mod_cast h2)
          rw [← this]; exact ringChar.charP _
        exact exists_singular_of_Δ_eq_zero_of_two _ hΔ0
      · exact exists_singular_of_Δ_eq_zero_of_ne_two _ h2 hΔ0
    have hP : (![x0, y0, 1] : Fin 3 → AlgebraicClosure k) ≠ 0 := by
      intro h
      have := congrFun h 2
      simp at this
    have hEq : (W.baseChange (AlgebraicClosure k)).toProjective.Equation ![x0, y0, 1] := by
      rw [Projective.equation_some, Affine.equation_iff']
      exact hF
    have hS := (Projective.nonsingular_some _ _).mp (H _ hP hEq)
    rw [Affine.nonsingular_iff'] at hS
    rcases hS.2 with h | h
    · exact h hFx
    · exact h hFy
  · intro h P hP hEq
    have hE : (W.baseChange (AlgebraicClosure k)).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr (by rw [hΔK]; exact fun h' => h (hinj.mp h'))⟩
    by_cases hz : P 2 ≠ 0
    · rw [Projective.nonsingular_of_Z_ne_zero hz]
      exact (Affine.equation_iff_nonsingular).1 ((Projective.equation_of_Z_ne_zero hz).1 hEq)
    · push Not at hz
      rw [Projective.nonsingular_of_Z_eq_zero hz]
      refine ⟨hEq, Or.inr ?_⟩
      have hx : P 0 = 0 := Projective.X_eq_zero_of_Z_eq_zero hEq hz
      have hy : P 1 ≠ 0 := by
        intro hy
        apply hP
        ext i
        fin_cases i <;> simp [hx, hy, hz]
      simp [hx, hy]

/-- **Theorem 2.4 (c)** (pdf p. 61): $j = c_4^3/\Delta$ depends only on $(E, O)$, and two elliptic curves become
isomorphic over an algebraic closure of $k$ iff they have the same $j$. (Same statement as Theorem 2.1 (c),
which was proved for every field.) -/
@[kb "milne2006ec" "Ch. II, Theorem 2.4 (c), pdf p. 61"]
theorem theorem_2_4_c (E E' : WeierstrassCurve k) [E.IsElliptic] [E'.IsElliptic] :
    (∀ C : VariableChange k, (C • E).j = E.j) ∧
      ((∃ C : VariableChange (AlgebraicClosure k),
        C • E.baseChange (AlgebraicClosure k) = E'.baseChange (AlgebraicClosure k)) ↔ E.j = E'.j) :=
  ⟨fun C => variableChange_j E C, theorem_2_1_c E E'⟩

end NumberFieldKB.MilneEC.II
