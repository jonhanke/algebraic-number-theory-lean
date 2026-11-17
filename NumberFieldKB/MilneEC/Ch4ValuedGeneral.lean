import NumberFieldKB.MilneEC.Ch4ValuedGeneralField
import NumberFieldKB.MilneEC.Ch4ValuedShort

/-!
# Reduction of a general Weierstrass model over a valuation ring: the homomorphism

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter II §4 (Theorem 4.1 (b), pdf pp. 69-70) and
Chapter IV, Lemma 3.2 (pdf p. 119).

This is the port of `Ch4ValuedShort.lean` from short models $Y^2 = X^3 + aX + b$ (with $2$ a unit) to an
arbitrary Weierstrass equation $W$ over a valuation ring $R$ (domain, fraction field $K$, residue field $k$)
with $\Delta$ a unit of $R$.  The curve over $K$ is `curveK K W = W.map (algebraMap R K)`, the reduced curve is
`curveRes W = W.map (IsLocalRing.residue R)`.

* `isInt_y`: if $x \in R$ and $(x, y) \in W(K)$ then $y \in R$ ($y$ is a root of a monic quadratic over $R$).
* `nonsingular_res`: the reduction of an integral point is a nonsingular point (the reduced curve is elliptic,
  since $\bar\Delta$ is a unit).
* `redPt`: $O \mapsto O$, $(x,y) \mapsto (\bar x, \bar y)$ if $x \in R$, and $O$ otherwise.
* `redPt_add`: it is a homomorphism (`redHom`).  The proof follows Milne: integral points
  (`red_add_int`: the chord slope is integral unless the reductions are opposite, in which case it is not),
  one integral and one point with $x \notin R$ (`red_add_big`, via `isInt_x3_big`), and two such points
  (`red_add_bb`).
-/

namespace NumberFieldKB.MilneEC.II.ValuedGen

open WeierstrassCurve Polynomial IsLocalRing
open NumberFieldKB.MilneEC.II.Valued (IsInt liftInt ι_inj ι_eq isInt_zero isInt_add isInt_mul isInt_neg
  isInt_sub isInt_pow exists_small liftInt_algebraMap isInt_algebraMap isInt_of_mul_unit isInt_of_root)

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve R)

local notation "ι" => algebraMap R K

variable (K) in
/-- The curve $W$ over the fraction field $K$. -/
abbrev curveK : WeierstrassCurve K := W.map (algebraMap R K)

/-- The reduced curve $\bar W$ over the residue field. -/
abbrev curveRes : WeierstrassCurve (ResidueField R) := W.map (IsLocalRing.residue R)

lemma curveRes_Δ_ne_zero (hΔ : IsUnit W.Δ) : (curveRes W).Δ ≠ 0 := by
  show (W.map (IsLocalRing.residue R)).Δ ≠ 0
  rw [map_Δ]
  exact (hΔ.map (IsLocalRing.residue R)).ne_zero

lemma curveK_Δ_ne_zero (hΔ : IsUnit W.Δ) : (curveK K W).Δ ≠ 0 := by
  show (W.map (algebraMap R K)).Δ ≠ 0
  rw [map_Δ]
  exact (map_ne_zero_iff (algebraMap R K) (ι_inj (K := K))).2 hΔ.ne_zero

lemma equationK {x y : K} : (curveK K W).toAffine.Equation x y ↔
    y ^ 2 + ι W.a₁ * x * y + ι W.a₃ * y = x ^ 3 + ι W.a₂ * x ^ 2 + ι W.a₄ * x + ι W.a₆ :=
  Affine.equation_iff _ _

lemma negY_K (x y : K) : (curveK K W).toAffine.negY x y = -y - ι W.a₁ * x - ι W.a₃ := rfl

lemma negY_res (x y : ResidueField R) :
    (curveRes W).toAffine.negY x y = -y - IsLocalRing.residue R W.a₁ * x - IsLocalRing.residue R W.a₃ := rfl

lemma addX_K (x1 x2 ℓ : K) :
    (curveK K W).toAffine.addX x1 x2 ℓ = ℓ ^ 2 + ι W.a₁ * ℓ - ι W.a₂ - x1 - x2 := rfl

lemma addX_res (x1 x2 ℓ : ResidueField R) :
    (curveRes W).toAffine.addX x1 x2 ℓ = ℓ ^ 2 + IsLocalRing.residue R W.a₁ * ℓ - IsLocalRing.residue R W.a₂ - x1 - x2 := rfl

lemma addY_K (x1 x2 y1 ℓ : K) :
    (curveK K W).toAffine.addY x1 x2 y1 ℓ =
      -(ℓ * (ℓ ^ 2 + ι W.a₁ * ℓ - ι W.a₂ - x1 - x2 - x1) + y1) -
        ι W.a₁ * (ℓ ^ 2 + ι W.a₁ * ℓ - ι W.a₂ - x1 - x2) - ι W.a₃ := rfl

lemma addY_res (x1 x2 y1 ℓ : ResidueField R) :
    (curveRes W).toAffine.addY x1 x2 y1 ℓ =
      -(ℓ * (ℓ ^ 2 + IsLocalRing.residue R W.a₁ * ℓ - IsLocalRing.residue R W.a₂ - x1 - x2 - x1) + y1) -
        IsLocalRing.residue R W.a₁ * (ℓ ^ 2 + IsLocalRing.residue R W.a₁ * ℓ - IsLocalRing.residue R W.a₂ - x1 - x2) -
          IsLocalRing.residue R W.a₃ := rfl

/-- Roots in `K` of monic quadratics over `R` are integral. -/
lemma isInt_of_quad {z : K} {b c : R} (h : z ^ 2 + ι b * z + ι c = 0) : IsInt R z := by
  refine isInt_of_root (K := K) (C 1 * X ^ 2 + C b * X + C c) ?_ ?_
  · rw [leadingCoeff_quadratic one_ne_zero]; exact isUnit_one
  · simp
    linear_combination h

/-- If $x$ is integral and $(x, y)$ lies on $W$, then $y$ is integral. -/
theorem isInt_y {x y : K} (hxy : (curveK K W).toAffine.Equation x y) (hx : IsInt R x) : IsInt R y := by
  rw [equationK] at hxy
  obtain ⟨X, rfl⟩ := hx
  refine isInt_of_quad (b := W.a₁ * X + W.a₃) (c := -(X ^ 3 + W.a₂ * X ^ 2 + W.a₄ * X + W.a₆)) ?_
  simp only [map_add, map_mul, map_neg, map_pow]
  linear_combination hxy

/-- The reduction of an integral point is a nonsingular point of the reduced curve. -/
theorem nonsingular_res (hΔ : IsUnit W.Δ) {x y : K} (hxy : (curveK K W).toAffine.Nonsingular x y)
    (hx : IsInt R x) :
    (curveRes W).toAffine.Nonsingular (IsLocalRing.residue R (liftInt R x)) (IsLocalRing.residue R (liftInt R y)) := by
  obtain ⟨Y, hY⟩ := isInt_y W hxy.1 hx
  obtain ⟨X, hX⟩ := hx
  have hX' : liftInt R x = X := by rw [← hX]; exact liftInt_algebraMap X
  have hY' : liftInt R y = Y := by rw [← hY]; exact liftInt_algebraMap Y
  have eK := hxy.1
  rw [← hX, ← hY] at eK
  have eR : W.toAffine.Equation X Y := (Affine.map_equation W.toAffine (ι_inj (K := K)) X Y).1 eK
  rw [hX', hY']
  exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero (curveRes_Δ_ne_zero W hΔ)).1 (eR.map (IsLocalRing.residue R))

/-- The reduction map $E(K) \to \bar E(k)$ (Milne, Chapter II §4, pdf p. 69). -/
noncomputable def redPt (hΔ : IsUnit W.Δ) :
    (curveK K W).toAffine.Point → (curveRes W).toAffine.Point
  | 0 => 0
  | .some x y hxy => if hx : IsInt R x then .some _ _ (nonsingular_res W hΔ hxy hx) else 0

variable {W}

lemma redPt_zero (hΔ : IsUnit W.Δ) : redPt W hΔ (0 : (curveK K W).toAffine.Point) = 0 := rfl

lemma redPt_some_of_isInt (hΔ : IsUnit W.Δ) {x y : K} (hxy : (curveK K W).toAffine.Nonsingular x y)
    (hx : IsInt R x) : redPt W hΔ (.some x y hxy) = .some _ _ (nonsingular_res W hΔ hxy hx) := by
  simp [redPt, hx]

lemma redPt_some_of_not_isInt (hΔ : IsUnit W.Δ) {x y : K}
    (hxy : (curveK K W).toAffine.Nonsingular x y) (hx : ¬ IsInt R x) :
    redPt W hΔ (.some x y hxy) = 0 := by
  simp [redPt, hx]

/-- The kernel of reduction is $E^1(K)$: the points $O$ and $(x, y)$ with $x \notin R$. -/
theorem redPt_eq_zero_iff (hΔ : IsUnit W.Δ) (P : (curveK K W).toAffine.Point) :
    redPt W hΔ P = 0 ↔ ∀ (x y : K) (hxy : (curveK K W).toAffine.Nonsingular x y),
      P = .some x y hxy → ¬ IsInt R x := by
  cases P with
  | zero => exact ⟨fun _ x y hxy hP => (by cases hP), fun _ => rfl⟩
  | some x0 y0 h0 =>
    constructor
    · intro hP x y hxy hxeq
      simp only [Affine.Point.some.injEq] at hxeq
      obtain ⟨rfl, rfl⟩ := hxeq
      intro hx
      rw [redPt_some_of_isInt hΔ h0 hx] at hP
      exact Affine.Point.some_ne_zero _ hP
    · intro H
      exact redPt_some_of_not_isInt hΔ h0 (H x0 y0 h0 rfl)

lemma redPt_some_of_alg (hΔ : IsUnit W.Δ) {x y : K} (hxy : (curveK K W).toAffine.Nonsingular x y)
    {X Y : R} (hX : algebraMap R K X = x) (hY : algebraMap R K Y = y) :
    ∃ hA, redPt W hΔ (.some x y hxy) = .some (IsLocalRing.residue R X) (IsLocalRing.residue R Y) hA := by
  have hx : IsInt R x := ⟨X, hX⟩
  have e1 : liftInt R x = X := by rw [← hX]; exact liftInt_algebraMap X
  have e2 : liftInt R y = Y := by rw [← hY]; exact liftInt_algebraMap Y
  have hA := nonsingular_res W hΔ hxy hx
  rw [e1, e2] at hA
  refine ⟨hA, ?_⟩
  rw [redPt_some_of_isInt hΔ hxy hx]
  simp only [Affine.Point.some.injEq]
  exact ⟨by rw [e1], by rw [e2]⟩

/-- The slope of a chord between integral points is integral unless the reductions are opposite. -/
lemma isInt_slope_of_nondeg {X1 Y1 X2 Y2 : R} {ℓ : K}
    (hnd : ¬(IsLocalRing.residue R X1 = IsLocalRing.residue R X2 ∧ IsLocalRing.residue R (Y1 + Y2 + W.a₁ * X2 + W.a₃) = 0))
    (H1 : ℓ * (ι X1 - ι X2) = ι Y1 - ι Y2)
    (H2 : ℓ * (ι Y1 + ι Y2 + ι W.a₁ * ι X2 + ι W.a₃) =
      ι X1 ^ 2 + ι X1 * ι X2 + ι X2 ^ 2 + ι W.a₂ * (ι X1 + ι X2) + ι W.a₄ - ι W.a₁ * ι Y1) :
    IsInt R ℓ := by
  by_cases hu : IsLocalRing.residue R X1 = IsLocalRing.residue R X2
  · have hv : IsUnit (Y1 + Y2 + W.a₁ * X2 + W.a₃) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      intro h0
      exact hnd ⟨hu, h0⟩
    exact isInt_of_mul_unit hv
      (V := X1 ^ 2 + X1 * X2 + X2 ^ 2 + W.a₂ * (X1 + X2) + W.a₄ - W.a₁ * Y1)
      (by simp only [map_add, map_mul, map_pow, map_sub]; exact H2)
  · have hv : IsUnit (X1 - X2) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub]
      exact sub_ne_zero.2 hu
    exact isInt_of_mul_unit hv (V := Y1 - Y2) (by simp only [map_sub]; exact H1)

/-- If the reductions are opposite and the reduced point is nonsingular, the slope is not integral. -/
lemma not_isInt_slope_of_deg {X1 Y1 X2 Y2 : R} {ℓ : K}
    (hdeg : IsLocalRing.residue R X1 = IsLocalRing.residue R X2 ∧ IsLocalRing.residue R (Y1 + Y2 + W.a₁ * X2 + W.a₃) = 0)
    (hns : IsLocalRing.residue R W.a₁ * IsLocalRing.residue R Y1 -
        (3 * IsLocalRing.residue R X1 ^ 2 + 2 * IsLocalRing.residue R W.a₂ * IsLocalRing.residue R X1 + IsLocalRing.residue R W.a₄) ≠ 0 ∨
      2 * IsLocalRing.residue R Y1 + IsLocalRing.residue R W.a₁ * IsLocalRing.residue R X1 + IsLocalRing.residue R W.a₃ ≠ 0)
    (H1 : ℓ * (ι X1 - ι X2) = ι Y1 - ι Y2)
    (H2 : ℓ * (ι Y1 + ι Y2 + ι W.a₁ * ι X2 + ι W.a₃) =
      ι X1 ^ 2 + ι X1 * ι X2 + ι X2 ^ 2 + ι W.a₂ * (ι X1 + ι X2) + ι W.a₄ - ι W.a₁ * ι Y1) :
    ¬ IsInt R ℓ := by
  rintro ⟨L, rfl⟩
  have H1' : L * (X1 - X2) = Y1 - Y2 := ι_eq (K := K) (by simp only [map_mul, map_sub]; exact H1)
  have H2' : L * (Y1 + Y2 + W.a₁ * X2 + W.a₃) =
      X1 ^ 2 + X1 * X2 + X2 ^ 2 + W.a₂ * (X1 + X2) + W.a₄ - W.a₁ * Y1 :=
    ι_eq (K := K) (by simp only [map_add, map_mul, map_pow, map_sub]; exact H2)
  have r1 := congrArg (IsLocalRing.residue R) H1'
  have r2 := congrArg (IsLocalRing.residue R) H2'
  obtain ⟨hx, hv⟩ := hdeg
  simp only [map_add, map_mul, map_pow, map_sub] at r1 r2 hv
  rw [hx] at r1 r2 hns
  have hy : IsLocalRing.residue R Y1 = IsLocalRing.residue R Y2 := by linear_combination (-1 : ResidueField R) * r1
  rcases hns with n | n
  · exact n (by linear_combination r2 - IsLocalRing.residue R L * hv)
  · exact n (by linear_combination hv + hy)

lemma isInt_x3_iff {ℓ : K} {X1 X2 : R} :
    IsInt R (ℓ ^ 2 + ι W.a₁ * ℓ - ι W.a₂ - ι X1 - ι X2) ↔ IsInt R ℓ := by
  constructor
  · rintro ⟨Z, hZ⟩
    refine isInt_of_quad (b := W.a₁) (c := -(W.a₂ + X1 + X2 + Z)) ?_
    simp only [map_add, map_neg]
    linear_combination -hZ
  · intro hh
    exact isInt_sub (isInt_sub (isInt_sub (isInt_add (isInt_pow hh 2)
      (isInt_mul (isInt_algebraMap _) hh)) (isInt_algebraMap _)) (isInt_algebraMap _)) (isInt_algebraMap _)

/-- Reduction is additive on two integral points. -/
lemma red_add_int (hΔ : IsUnit W.Δ) {X1 Y1 X2 Y2 : R}
    (h1 : (curveK K W).toAffine.Nonsingular (ι X1) (ι Y1))
    (h2 : (curveK K W).toAffine.Nonsingular (ι X2) (ι Y2)) :
    redPt W hΔ (Affine.Point.some _ _ h1 + Affine.Point.some _ _ h2) =
      redPt W hΔ (Affine.Point.some _ _ h1) + redPt W hΔ (Affine.Point.some _ _ h2) := by
  obtain ⟨hA1, e1⟩ := redPt_some_of_alg hΔ h1 rfl rfl
  obtain ⟨hA2, e2⟩ := redPt_some_of_alg hΔ h2 rfl rfl
  rw [e1, e2]
  have n1 := ((Affine.nonsingular_iff' _ _).1 hA1).2
  by_cases hQ : ι X1 = ι X2 ∧ ι Y1 = (curveK K W).toAffine.negY (ι X2) (ι Y2)
  · have hz : Affine.Point.some _ _ h1 + Affine.Point.some _ _ h2 = 0 :=
      Affine.Point.add_of_Y_eq hQ.1 hQ.2
    have hX : X1 = X2 := ι_eq (K := K) hQ.1
    have hY : Y1 = -Y2 - W.a₁ * X2 - W.a₃ :=
      ι_eq (K := K) (by rw [hQ.2]; simp only [map_sub, map_neg, map_mul]; try rfl)
    rw [hz, redPt_zero]
    symm
    refine Affine.Point.add_of_Y_eq (by rw [hX]) ?_
    rw [hY, negY_res]
    simp only [map_sub, map_neg, map_mul]
  · obtain ⟨ℓ, H1, H2⟩ := exists_slope_gen (curveK K W) h1.1 h2.1 hQ
    obtain ⟨h3, hsum⟩ := add_some_eq_gen (curveK K W) h1 h2 hQ H1 H2
    rw [hsum]
    by_cases hdeg : IsLocalRing.residue R X1 = IsLocalRing.residue R X2 ∧ IsLocalRing.residue R (Y1 + Y2 + W.a₁ * X2 + W.a₃) = 0
    · have hv := hdeg.2
      simp only [map_add, map_mul] at hv
      have hz : (Affine.Point.some _ _ hA1 + Affine.Point.some _ _ hA2 :
          (curveRes W).toAffine.Point) = 0 :=
        Affine.Point.add_of_Y_eq hdeg.1 (by rw [negY_res]; linear_combination hv)
      rw [hz]
      apply redPt_some_of_not_isInt
      intro hint
      have hint' : IsInt R (ℓ ^ 2 + ι W.a₁ * ℓ - ι W.a₂ - ι X1 - ι X2) := hint
      exact not_isInt_slope_of_deg hdeg n1 H1 H2 ((isInt_x3_iff).1 hint')
    · obtain ⟨L, rfl⟩ := isInt_slope_of_nondeg hdeg H1 H2
      have H1' : L * (X1 - X2) = Y1 - Y2 := ι_eq (K := K) (by simp only [map_mul, map_sub]; exact H1)
      have H2' : L * (Y1 + Y2 + W.a₁ * X2 + W.a₃) =
          X1 ^ 2 + X1 * X2 + X2 ^ 2 + W.a₂ * (X1 + X2) + W.a₄ - W.a₁ * Y1 :=
        ι_eq (K := K) (by simp only [map_add, map_mul, map_pow, map_sub]; exact H2)
      have H1z := congrArg (IsLocalRing.residue R) H1'
      have H2z := congrArg (IsLocalRing.residue R) H2'
      simp only [map_add, map_mul, map_pow, map_sub] at H1z H2z
      have hdeg' : ¬(IsLocalRing.residue R X1 = IsLocalRing.residue R X2 ∧
          IsLocalRing.residue R Y1 = (curveRes W).toAffine.negY (IsLocalRing.residue R X2) (IsLocalRing.residue R Y2)) := by
        rintro ⟨ha, hb⟩
        apply hdeg
        refine ⟨ha, ?_⟩
        rw [negY_res] at hb
        simp only [map_add, map_mul]
        linear_combination hb
      obtain ⟨h3z, hsumz⟩ := add_some_eq_gen (curveRes W) hA1 hA2 hdeg' H1z H2z
      rw [hsumz]
      obtain ⟨hA3, e3⟩ := redPt_some_of_alg hΔ h3
        (X := L ^ 2 + W.a₁ * L - W.a₂ - X1 - X2)
        (Y := -(L * (L ^ 2 + W.a₁ * L - W.a₂ - X1 - X2 - X1) + Y1) -
          W.a₁ * (L ^ 2 + W.a₁ * L - W.a₂ - X1 - X2) - W.a₃)
        (by simp only [addX_K, map_sub, map_add, map_mul, map_pow])
        (by simp only [addY_K, map_neg, map_sub, map_add, map_mul, map_pow])
      rw [e3]
      simp only [Affine.Point.some.injEq]
      constructor <;>
        simp only [addX_res, addY_res, map_neg, map_sub, map_add, map_mul, map_pow]

/-- If `x₁` is not integral and `P₂` is integral, then `x(P₁ + P₂)` is integral. -/
lemma isInt_x3_big {x1 y1 ℓ x3 : K} (hx1 : ¬ IsInt R x1) {X2 Y2 : R}
    (e1 : y1 ^ 2 + ι W.a₁ * x1 * y1 + ι W.a₃ * y1 =
      x1 ^ 3 + ι W.a₂ * x1 ^ 2 + ι W.a₄ * x1 + ι W.a₆)
    (H1 : ℓ * (x1 - ι X2) = y1 - ι Y2)
    (hx3 : ℓ ^ 2 + ι W.a₁ * ℓ - ι W.a₂ - x1 - ι X2 = x3) : IsInt R x3 := by
  obtain ⟨S, hS, hSx⟩ := exists_small hx1
  have hx0 : x1 ≠ 0 := fun h0 => hx1 (h0 ▸ isInt_zero)
  have hC : IsInt R (y1 * ι S ^ 2) := by
    refine isInt_of_quad (b := W.a₁ * S + W.a₃ * S ^ 2)
      (c := -(S + W.a₂ * S ^ 2 + W.a₄ * S ^ 3 + W.a₆ * S ^ 4)) ?_
    simp only [map_add, map_mul, map_pow, map_neg]
    linear_combination (ι S) ^ 4 * e1 + (-(ι W.a₁ * y1 * (ι S) ^ 3) +
      ι S * ((ι S * x1) ^ 2 + ι S * x1 + 1) + ι W.a₂ * (ι S) ^ 2 * (ι S * x1 + 1) +
      ι W.a₄ * (ι S) ^ 3) * hSx
  obtain ⟨C, hC⟩ := hC
  have hN : x3 * (x1 - ι X2) ^ 2 = -y1 * (ι W.a₃ + 2 * ι Y2 + ι W.a₁ * ι X2) + ι X2 * x1 ^ 2 +
      (ι W.a₄ - ι W.a₁ * ι Y2 + 2 * ι W.a₂ * ι X2 + ι X2 ^ 2) * x1 +
      (ι W.a₆ + ι Y2 ^ 2 + ι W.a₁ * ι X2 * ι Y2 - ι W.a₂ * ι X2 ^ 2 - ι X2 ^ 3) := by
    rw [← hx3]
    linear_combination (ℓ * (x1 - ι X2) + (y1 - ι Y2) + ι W.a₁ * (x1 - ι X2)) * H1 + e1
  have ht : ι S = x1⁻¹ := eq_inv_of_mul_eq_one_left hSx
  have hW : x3 * ι ((1 - X2 * S) ^ 2) = ι (-(W.a₃ + 2 * Y2 + W.a₁ * X2) * C + X2 +
      (W.a₄ - W.a₁ * Y2 + 2 * W.a₂ * X2 + X2 ^ 2) * S +
      (W.a₆ + Y2 ^ 2 + W.a₁ * X2 * Y2 - W.a₂ * X2 ^ 2 - X2 ^ 3) * S ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_sub, map_one, map_neg, map_ofNat, hC, ht]
    field_simp
    linear_combination hN
  have hD : IsUnit (1 - X2 * S) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have : IsLocalRing.residue R S = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hS
    simp [this]
  exact isInt_of_mul_unit (hD.pow 2) hW

/-- Reduction is additive when one point has non-integral `x` and the other is integral. -/
lemma red_add_big (hΔ : IsUnit W.Δ) {x1 y1 : K} (h1 : (curveK K W).toAffine.Nonsingular x1 y1)
    (hx1 : ¬ IsInt R x1) {X2 Y2 : R}
    (h2 : (curveK K W).toAffine.Nonsingular (ι X2) (ι Y2)) :
    redPt W hΔ (Affine.Point.some x1 y1 h1 + Affine.Point.some _ _ h2) =
      redPt W hΔ (Affine.Point.some _ _ h2) := by
  have hQ : ¬(x1 = ι X2 ∧ y1 = (curveK K W).toAffine.negY (ι X2) (ι Y2)) :=
    fun hh => hx1 (hh.1 ▸ isInt_algebraMap X2)
  obtain ⟨ℓ, H1, H2⟩ := exists_slope_gen (curveK K W) h1.1 h2.1 hQ
  obtain ⟨h3, hsum⟩ := add_some_eq_gen (curveK K W) h1 h2 hQ H1 H2
  have hx3int := isInt_x3_big hx1 ((equationK W).1 h1.1) H1
    (x3 := (curveK K W).toAffine.addX x1 (ι X2) ℓ) rfl
  generalize hx3d : (curveK K W).toAffine.addX x1 (ι X2) ℓ = x3 at h3 hsum hx3int
  generalize hy3d : (curveK K W).toAffine.addY x1 (ι X2) y1 ℓ = y3 at h3 hsum
  rw [hsum]
  obtain ⟨X3, hX3⟩ := hx3int
  obtain ⟨Y3, hY3⟩ := isInt_y W h3.1 ⟨X3, hX3⟩
  obtain ⟨hA3, e3⟩ := redPt_some_of_alg hΔ h3 hX3 hY3
  obtain ⟨hA2, e2⟩ := redPt_some_of_alg hΔ h2 rfl rfl
  rw [e3, e2]
  simp only [Affine.Point.some.injEq]
  obtain ⟨h2', hneg⟩ : ∃ h', -Affine.Point.some (ι X2) (ι Y2) h2 =
      Affine.Point.some (ι X2) ((curveK K W).toAffine.negY (ι X2) (ι Y2)) h' :=
    ⟨_, Affine.Point.neg_some h2⟩
  have hne : ¬(x3 = ι X2 ∧ y3 = (curveK K W).toAffine.negY (ι X2)
      ((curveK K W).toAffine.negY (ι X2) (ι Y2))) := by
    rintro ⟨hh1, hh2⟩
    have hh : Affine.Point.some x1 y1 h1 + Affine.Point.some _ _ h2 = Affine.Point.some _ _ h2 := by
      rw [hsum]
      simp only [Affine.Point.some.injEq]
      exact ⟨hh1, by rw [hh2, Affine.negY_negY]⟩
    exact Affine.Point.some_ne_zero _ (add_right_cancel (hh.trans (zero_add _).symm))
  obtain ⟨ℓ', H1', H2'⟩ := exists_slope_gen (curveK K W) h3.1 h2'.1 hne
  obtain ⟨h4, hsum4⟩ := add_some_eq_gen (curveK K W) h3 h2' hne H1' H2'
  have hPeq : Affine.Point.some x3 y3 h3 + Affine.Point.some _ _ h2' =
      Affine.Point.some x1 y1 h1 := by
    rw [← hneg, ← hsum]; abel
  rw [hPeq] at hsum4
  simp only [Affine.Point.some.injEq] at hsum4
  obtain ⟨hxx, -⟩ := hsum4
  subst hX3 hY3
  by_contra hnd
  have hnd' : ¬(IsLocalRing.residue R X3 = IsLocalRing.residue R X2 ∧
      IsLocalRing.residue R (Y3 + (-Y2 - W.a₁ * X2 - W.a₃) + W.a₁ * X2 + W.a₃) = 0) := by
    rintro ⟨ha, hb⟩
    apply hnd
    refine ⟨ha, ?_⟩
    simp only [map_add, map_sub, map_neg, map_mul] at hb
    linear_combination hb
  have hℓ := isInt_slope_of_nondeg (W := W) (ℓ := ℓ') (X1 := X3) (Y1 := Y3) (X2 := X2)
    (Y2 := -Y2 - W.a₁ * X2 - W.a₃) hnd'
    (by simp only [map_sub, map_neg, map_mul]; exact H1')
    (by simp only [map_sub, map_neg, map_mul]; exact H2')
  apply hx1
  rw [hxx]
  exact (isInt_x3_iff (X1 := X3) (X2 := X2)).2 hℓ

/-- The sum of two points with non-integral `x` has reduction `0`. -/
lemma red_add_bb (hΔ : IsUnit W.Δ) {x1 y1 x2 y2 : K} (h1 : (curveK K W).toAffine.Nonsingular x1 y1)
    (h2 : (curveK K W).toAffine.Nonsingular x2 y2) (hx1 : ¬ IsInt R x1) (hx2 : ¬ IsInt R x2) :
    redPt W hΔ (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) = 0 := by
  rcases hT : (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) with _ | ⟨x3, y3, h3⟩
  · rfl
  · by_cases hx3 : IsInt R x3
    · exfalso
      obtain ⟨X3, rfl⟩ := hx3
      obtain ⟨Y3, rfl⟩ := isInt_y W h3.1 ⟨X3, rfl⟩
      obtain ⟨h2', hneg⟩ : ∃ h', -Affine.Point.some x2 y2 h2 =
          Affine.Point.some x2 ((curveK K W).toAffine.negY x2 y2) h' := ⟨_, Affine.Point.neg_some h2⟩
      have hP : Affine.Point.some x2 ((curveK K W).toAffine.negY x2 y2) h2' + Affine.Point.some _ _ h3 =
          Affine.Point.some x1 y1 h1 := by
        rw [← hneg, ← hT]; abel
      have key := red_add_big hΔ h2' hx2 h3
      rw [hP, redPt_some_of_not_isInt hΔ h1 hx1] at key
      obtain ⟨hA, e⟩ := redPt_some_of_alg hΔ h3 rfl rfl
      rw [e] at key
      exact Affine.Point.some_ne_zero _ key.symm
    · exact redPt_some_of_not_isInt hΔ h3 hx3

/-- **Theorem 4.1 (b)** over $R$ (Milne, pdf p. 70): reduction is a homomorphism. -/
theorem redPt_add (hΔ : IsUnit W.Δ) (P Q : (curveK K W).toAffine.Point) :
    redPt W hΔ (P + Q) = redPt W hΔ P + redPt W hΔ Q := by
  have h0 : (Affine.Point.zero : (curveK K W).toAffine.Point) = 0 := rfl
  cases P with
  | zero => rw [h0, zero_add, redPt_zero, zero_add]
  | some x1 y1 h1 =>
    cases Q with
    | zero => rw [h0, add_zero, redPt_zero, add_zero]
    | some x2 y2 h2 =>
      by_cases hx1 : IsInt R x1
      · by_cases hx2 : IsInt R x2
        · obtain ⟨X1, rfl⟩ := hx1
          obtain ⟨Y1, rfl⟩ := isInt_y W h1.1 ⟨X1, rfl⟩
          obtain ⟨X2, rfl⟩ := hx2
          obtain ⟨Y2, rfl⟩ := isInt_y W h2.1 ⟨X2, rfl⟩
          exact red_add_int hΔ h1 h2
        · obtain ⟨X1, rfl⟩ := hx1
          obtain ⟨Y1, rfl⟩ := isInt_y W h1.1 ⟨X1, rfl⟩
          rw [redPt_some_of_not_isInt hΔ h2 hx2, add_zero, add_comm]
          exact red_add_big hΔ h2 hx2 h1
      · by_cases hx2 : IsInt R x2
        · obtain ⟨X2, rfl⟩ := hx2
          obtain ⟨Y2, rfl⟩ := isInt_y W h2.1 ⟨X2, rfl⟩
          rw [redPt_some_of_not_isInt hΔ h1 hx1, zero_add]
          exact red_add_big hΔ h1 hx1 h2
        · rw [redPt_some_of_not_isInt hΔ h1 hx1, redPt_some_of_not_isInt hΔ h2 hx2, add_zero]
          exact red_add_bb hΔ h1 h2 hx1 hx2

variable (W) in
/-- Reduction as a homomorphism of groups. -/
noncomputable def redHom (hΔ : IsUnit W.Δ) :
    (curveK K W).toAffine.Point →+ (curveRes W).toAffine.Point :=
  AddMonoidHom.mk' (redPt W hΔ) (redPt_add hΔ)

@[simp] lemma redHom_apply (hΔ : IsUnit W.Δ) (P : (curveK K W).toAffine.Point) :
    redHom W hΔ P = redPt W hΔ P := rfl

end NumberFieldKB.MilneEC.II.ValuedGen
