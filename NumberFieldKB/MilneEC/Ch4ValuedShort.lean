import NumberFieldKB.MilneEC.Ch2Corollary42
import NumberFieldKB.MilneEC.Ch2Reduction
import NumberFieldKB.TauCetiPort.RingTheory.Henselian.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.Integral

/-!
# Reduction of a short Weierstrass model over a Henselian valuation ring

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter II §4 (Theorem 4.1 (b), Corollary 4.2, pdf
pp. 69–71) and Chapter IV, Lemma 3.2 (pdf p. 119).  Milne works over $\mathbb Q_p$; the proof of Lemma 3.5
(pdf p. 120) applies Lemma 3.2 over a finite unramified extension $K$ of $\mathbb Q_p$ ("the same argument"),
which this file makes precise.

**Setting.** $R$ is a valuation ring with fraction field $K$ and residue field $k$; the model is
$E : Y^2 = X^3 + aX + b$ with $a, b \in R$, and *good reduction* means that $2$ and $4a^3 + 27b^2$ are units
of $R$ (`Good`).  For $R = \mathbb Z_p$, $p$ odd, this is the setting of `Ch2Reduction.lean` and
`Ch2Corollary42.lean`; for $R = \mathcal O_K$ with $K/\mathbb Q_p$ finite unramified it is the one Lemma 3.5
needs.

* `redPt`: the reduction $E(K) \to \bar E(k)$: $O \mapsto O$, $(x, y) \mapsto (\bar x, \bar y)$ if $x \in R$
  (then $y \in R$, `isInt_y`), and $(x, y) \mapsto O$ otherwise (then $(x : y : 1) = (x/y : 1 : 1/y)$ reduces
  to $(0 : 1 : 0)$).
* `redPt_add`: it is a homomorphism (Theorem 4.1 (b) over $R$; the proof is that of `Ch2Reduction.lean`, with
  the valuation of $R$ in place of the $p$-adic norm).
* `redPt_surjective`: it is surjective when $R$ is Henselian.
* `exists_zsmul_eq_of_redPt_eq_zero`: for $n$ a unit of $R$, multiplication by $n$ maps the kernel
  $E^1(K)$ onto itself (Corollary 4.2 over $R$; Hensel's lemma on the division polynomials, as in
  `Ch2Corollary42.lean`).
* `lemma_3_2_valued`: Lemma 3.2 over $R$.
-/

namespace NumberFieldKB.MilneEC.II.Valued

open WeierstrassCurve Polynomial IsLocalRing

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- An element of $K$ is *integral* if it lies in (the image of) $R$. -/
def IsInt (x : K) : Prop := ∃ X : R, algebraMap R K X = x

/-- A preimage in $R$ of an integral element of $K$ (and $0$ otherwise). -/
noncomputable def liftInt (x : K) : R := if h : IsInt R x then h.choose else 0

variable {R}

lemma ι_inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

lemma ι_eq {x y : R} (h : algebraMap R K x = algebraMap R K y) : x = y := IsFractionRing.injective R K h

lemma isInt_zero : IsInt R (0 : K) := ⟨0, map_zero _⟩

lemma isInt_add {x y : K} (hx : IsInt R x) (hy : IsInt R y) : IsInt R (x + y) := by
  obtain ⟨X, rfl⟩ := hx; obtain ⟨Y, rfl⟩ := hy; exact ⟨X + Y, map_add _ _ _⟩

lemma isInt_mul {x y : K} (hx : IsInt R x) (hy : IsInt R y) : IsInt R (x * y) := by
  obtain ⟨X, rfl⟩ := hx; obtain ⟨Y, rfl⟩ := hy; exact ⟨X * Y, map_mul _ _ _⟩

lemma isInt_neg {x : K} (hx : IsInt R x) : IsInt R (-x) := by
  obtain ⟨X, rfl⟩ := hx; exact ⟨-X, map_neg _ _⟩

lemma isInt_sub {x y : K} (hx : IsInt R x) (hy : IsInt R y) : IsInt R (x - y) := by
  rw [sub_eq_add_neg]; exact isInt_add hx (isInt_neg hy)

lemma isInt_pow {x : K} (hx : IsInt R x) (n : ℕ) : IsInt R (x ^ n) := by
  obtain ⟨X, rfl⟩ := hx; exact ⟨X ^ n, map_pow _ _ _⟩

/-- A non-integral element of `K` is the inverse of a nonzero element of the maximal ideal. -/
lemma exists_small {x : K} (hx : ¬ IsInt R x) :
    ∃ S : R, S ∈ maximalIdeal R ∧ algebraMap R K S * x = 1 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isInt_zero)
  rcases ValuationRing.isInteger_or_isInteger R x with h | ⟨S, hS⟩
  · exact absurd h hx
  · refine ⟨S, ?_, by rw [hS]; exact inv_mul_cancel₀ hx0⟩
    by_contra hnm
    apply hx
    have hu : IsUnit S := by
      by_contra hu
      exact hnm ((IsLocalRing.mem_maximalIdeal _).2 hu)
    obtain ⟨u, rfl⟩ := hu
    refine ⟨↑u⁻¹, ?_⟩
    rw [map_units_inv, hS, inv_inv]

/-- Square roots of integral elements are integral (a valuation ring is integrally closed). -/
lemma isInt_of_sq {z : K} {r : R} (h : z ^ 2 = algebraMap R K r) : IsInt R z := by
  by_contra hz
  obtain ⟨S, hS, hSz⟩ := exists_small hz
  have h1 : algebraMap R K (S ^ 2 * r) = algebraMap R K 1 := by
    rw [map_mul, map_pow, ← h, ← mul_pow, hSz, one_pow, map_one]
  have h2 : S * (S * r) = 1 := by
    have := ι_eq (K := K) h1; linear_combination this
  exact ((IsLocalRing.mem_maximalIdeal _).1 hS) (IsUnit.of_mul_eq_one _ h2)

/-- Roots of monic cubics `z^3 + a z + b` with integral coefficients are integral. -/
lemma isInt_of_cubic {z : K} {a b : R}
    (h : z ^ 3 + algebraMap R K a * z + algebraMap R K b = 0) : IsInt R z := by
  by_contra hz
  obtain ⟨S, hS, hSz⟩ := exists_small hz
  have h1 : algebraMap R K (1 + a * S ^ 2 + b * S ^ 3) = 0 := by
    simp only [map_add, map_mul, map_pow, map_one]
    linear_combination (algebraMap R K S) ^ 3 * h - (1 + algebraMap R K S * z + (algebraMap R K S * z) ^ 2
      + algebraMap R K a * (algebraMap R K S) ^ 2) * hSz
  have h2 : 1 + a * S ^ 2 + b * S ^ 3 = 0 := by
    exact ι_eq (K := K) (by rw [h1, map_zero])
  have h3 : (1 : R) ∈ maximalIdeal R := by
    have e : (1 : R) = -(a * S ^ 2 + b * S ^ 3) := by linear_combination h2
    rw [e]
    exact neg_mem (add_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hS _ (by norm_num)))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hS _ (by norm_num))))
  exact ((IsLocalRing.mem_maximalIdeal _).1 h3) isUnit_one

lemma algebraMap_liftInt {x : K} (hx : IsInt R x) : algebraMap R K (liftInt R x) = x := by
  unfold liftInt; simp only [hx, ↓reduceDIte]; exact hx.choose_spec

lemma liftInt_algebraMap (X : R) : liftInt R (algebraMap R K X) = X :=
  ι_eq (K := K) (algebraMap_liftInt ⟨X, rfl⟩)

variable (K) in
/-- The short model $Y^2 = X^3 + aX + b$ over the fraction field $K$. -/
noncomputable abbrev curveK (a b : R) : WeierstrassCurve K := shortCurve (algebraMap R K a) (algebraMap R K b)

/-- The reduced model $Y^2 = X^3 + \bar aX + \bar b$ over the residue field. -/
noncomputable abbrev curveRes (a b : R) : WeierstrassCurve (ResidueField R) :=
  shortCurve (IsLocalRing.residue R a) (IsLocalRing.residue R b)

/-- Good reduction for a short model: $2$ and $4a^3 + 27b^2$ are units of $R$. -/
structure Good (a b : R) : Prop where
  two : IsUnit (2 : R)
  disc : IsUnit (4 * a ^ 3 + 27 * b ^ 2)

variable {a b : R}

/-- If $x$ is integral and $(x, y)$ lies on $E$, then $y$ is integral ($R$ is integrally closed). -/
theorem isInt_y {x y : K} (hxy : (curveK K a b).toAffine.Equation x y) (hx : IsInt R x) : IsInt R y := by
  have e := shortCurve_equation hxy
  obtain ⟨X, rfl⟩ := hx
  refine isInt_of_sq (r := X ^ 3 + a * X + b) ?_
  rw [e]; simp only [map_add, map_mul, map_pow]

/-- The reduction of an integral point is a nonsingular point of the reduced curve. -/
theorem nonsingular_res (h : Good a b) {x y : K} (hxy : (curveK K a b).toAffine.Nonsingular x y)
    (hx : IsInt R x) :
    (curveRes a b).toAffine.Nonsingular (IsLocalRing.residue R (liftInt R x)) (IsLocalRing.residue R (liftInt R y)) := by
  obtain ⟨Y, hY⟩ := isInt_y hxy.1 hx
  obtain ⟨X, hX⟩ := hx
  have hX' : liftInt R x = X := by rw [← hX]; exact liftInt_algebraMap X
  have hY' : liftInt R y = Y := by rw [← hY]; exact liftInt_algebraMap Y
  have eK := shortCurve_equation hxy.1
  rw [← hX, ← hY] at eK
  have eR : Y ^ 2 = X ^ 3 + a * X + b := by
    apply ι_inj (K := K)
    simp only [map_add, map_mul, map_pow]
    exact eK
  rw [hX', hY', shortCurve_nonsingular_iff]
  have e2 : IsLocalRing.residue R Y ^ 2 = IsLocalRing.residue R X ^ 3 + IsLocalRing.residue R a * IsLocalRing.residue R X + IsLocalRing.residue R b := by
    have := congrArg (IsLocalRing.residue R) eR
    simpa only [map_add, map_mul, map_pow] using this
  refine ⟨e2, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have h2' : (2 : ResidueField R) ≠ 0 := by
    have := (h.two.map (IsLocalRing.residue R)).ne_zero
    rwa [map_ofNat] at this
  have hy0 : IsLocalRing.residue R Y = 0 := (mul_eq_zero.1 h2).resolve_left h2'
  have hD : IsLocalRing.residue R (4 * a ^ 3 + 27 * b ^ 2) = 0 := by
    rw [hy0] at e2
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination (4 * (IsLocalRing.residue R a) ^ 2 + 15 * (IsLocalRing.residue R X) ^ 2 * IsLocalRing.residue R a +
      9 * (IsLocalRing.residue R X) ^ 4) * h1 - 27 * (IsLocalRing.residue R b - (IsLocalRing.residue R X) ^ 3 -
      IsLocalRing.residue R a * IsLocalRing.residue R X) * e2
  exact (h.disc.map (IsLocalRing.residue R)).ne_zero hD

/-- The reduction map $E(K) \to \bar E(k)$ (Milne, Chapter II §4, pdf p. 69). -/
noncomputable def redPt (h : Good a b) : (curveK K a b).toAffine.Point → (curveRes a b).toAffine.Point
  | 0 => 0
  | .some x y hxy =>
    if hx : IsInt R x then .some _ _ (nonsingular_res h hxy hx) else 0

lemma redPt_zero (h : Good a b) : redPt h (0 : (curveK K a b).toAffine.Point) = 0 := rfl

lemma redPt_some_of_isInt (h : Good a b) {x y : K} (hxy : (curveK K a b).toAffine.Nonsingular x y)
    (hx : IsInt R x) : redPt h (.some x y hxy) = .some _ _ (nonsingular_res h hxy hx) := by
  simp [redPt, hx]

lemma redPt_some_of_not_isInt (h : Good a b) {x y : K} (hxy : (curveK K a b).toAffine.Nonsingular x y)
    (hx : ¬ IsInt R x) : redPt h (.some x y hxy) = 0 := by
  simp [redPt, hx]

/-- The kernel of reduction is $E^1(K)$: the points $O$ and $(x, y)$ with $x \notin R$. -/
theorem redPt_eq_zero_iff (h : Good a b) (P : (curveK K a b).toAffine.Point) :
    redPt h P = 0 ↔ ∀ (x y : K) (hxy : (curveK K a b).toAffine.Nonsingular x y), P = .some x y hxy →
      ¬ IsInt R x := by
  cases P with
  | zero => exact ⟨fun _ x y hxy hP => (by cases hP), fun _ => rfl⟩
  | some x0 y0 h0 =>
    constructor
    · intro hP x y hxy hxeq
      simp only [Affine.Point.some.injEq] at hxeq
      obtain ⟨rfl, rfl⟩ := hxeq
      intro hx
      rw [redPt_some_of_isInt h h0 hx] at hP
      exact Affine.Point.some_ne_zero _ hP
    · intro H
      exact redPt_some_of_not_isInt h h0 (H x0 y0 h0 rfl)

lemma redPt_some_of_alg (h : Good a b) {x y : K} (hxy : (curveK K a b).toAffine.Nonsingular x y) {X Y : R}
    (hX : algebraMap R K X = x) (hY : algebraMap R K Y = y) :
    ∃ hA, redPt h (.some x y hxy) =
      .some (IsLocalRing.residue R X) (IsLocalRing.residue R Y) hA := by
  have hx : IsInt R x := ⟨X, hX⟩
  have e1 : liftInt R x = X := by rw [← hX]; exact liftInt_algebraMap X
  have e2 : liftInt R y = Y := by rw [← hY]; exact liftInt_algebraMap Y
  have hA := nonsingular_res h hxy hx
  rw [e1, e2] at hA
  refine ⟨hA, ?_⟩
  rw [redPt_some_of_isInt h hxy hx]
  simp only [Affine.Point.some.injEq]
  exact ⟨by rw [e1], by rw [e2]⟩

lemma isInt_algebraMap (X : R) : IsInt R (algebraMap R K X) := ⟨X, rfl⟩

lemma isInt_of_mul_unit {ℓ : K} {U V : R} (hU : IsUnit U) (h : ℓ * algebraMap R K U = algebraMap R K V) :
    IsInt R ℓ := by
  obtain ⟨u, rfl⟩ := hU
  refine ⟨V * ↑u⁻¹, ?_⟩
  rw [map_mul, ← h, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

lemma isInt_slope_of_nondeg {X1 Y1 X2 Y2 : R} {ℓ : K}
    (hnd : ¬(IsLocalRing.residue R X1 = IsLocalRing.residue R X2 ∧
      IsLocalRing.residue R Y1 = -IsLocalRing.residue R Y2))
    (H1 : ℓ * (algebraMap R K X1 - algebraMap R K X2) = algebraMap R K Y1 - algebraMap R K Y2)
    (H2 : ℓ * (algebraMap R K Y1 + algebraMap R K Y2) = algebraMap R K X1 ^ 2 +
      algebraMap R K X1 * algebraMap R K X2 + algebraMap R K X2 ^ 2 + algebraMap R K a) :
    IsInt R ℓ := by
  by_cases hu : IsLocalRing.residue R X1 = IsLocalRing.residue R X2
  · have hv : IsUnit (Y1 + Y2) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      intro h0
      apply hnd
      refine ⟨hu, ?_⟩
      rw [map_add] at h0
      linear_combination h0
    exact isInt_of_mul_unit hv (V := X1 ^ 2 + X1 * X2 + X2 ^ 2 + a)
      (by simp only [map_add, map_mul, map_pow]; exact H2)
  · have hv : IsUnit (X1 - X2) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub]
      exact sub_ne_zero.2 hu
    exact isInt_of_mul_unit hv (V := Y1 - Y2) (by simp only [map_sub]; exact H1)

lemma not_isInt_slope_of_deg {X1 Y1 X2 Y2 : R} {ℓ : K}
    (hdeg : IsLocalRing.residue R X1 = IsLocalRing.residue R X2 ∧
      IsLocalRing.residue R Y1 = -IsLocalRing.residue R Y2)
    (hns : 3 * IsLocalRing.residue R X1 ^ 2 + IsLocalRing.residue R a ≠ 0 ∨
      2 * IsLocalRing.residue R Y1 ≠ 0)
    (H1 : ℓ * (algebraMap R K X1 - algebraMap R K X2) = algebraMap R K Y1 - algebraMap R K Y2)
    (H2 : ℓ * (algebraMap R K Y1 + algebraMap R K Y2) = algebraMap R K X1 ^ 2 +
      algebraMap R K X1 * algebraMap R K X2 + algebraMap R K X2 ^ 2 + algebraMap R K a) :
    ¬ IsInt R ℓ := by
  rintro ⟨L, rfl⟩
  have H1' : L * (X1 - X2) = Y1 - Y2 := ι_eq (K := K) (by simp only [map_mul, map_sub]; exact H1)
  have H2' : L * (Y1 + Y2) = X1 ^ 2 + X1 * X2 + X2 ^ 2 + a :=
    ι_eq (K := K) (by simp only [map_add, map_mul, map_pow]; exact H2)
  have r1 := congrArg (IsLocalRing.residue R) H1'
  have r2 := congrArg (IsLocalRing.residue R) H2'
  simp only [map_add, map_mul, map_pow, map_sub] at r1 r2
  obtain ⟨hx, hy⟩ := hdeg
  simp only [hx, hy] at r1 r2 hns
  rcases hns with n | n
  · exact n (by linear_combination (-1 : ResidueField R) * r2)
  · exact n (by linear_combination (-1 : ResidueField R) * r1)

lemma isInt_x3_iff {ℓ : K} {X1 X2 : R} :
    IsInt R (ℓ ^ 2 - algebraMap R K X1 - algebraMap R K X2) ↔ IsInt R ℓ := by
  constructor
  · intro hh
    have h2 : IsInt R (ℓ ^ 2) := by
      have := isInt_add (isInt_add hh (isInt_algebraMap (K := K) X1)) (isInt_algebraMap (K := K) X2)
      convert this using 1; ring
    obtain ⟨r, hr⟩ := h2
    exact isInt_of_sq hr.symm
  · intro hh
    exact isInt_sub (isInt_sub (isInt_pow hh 2) (isInt_algebraMap X1)) (isInt_algebraMap X2)

lemma neg_some_eq {x y : K} (hxy : (curveK K a b).toAffine.Nonsingular x y) :
    ∃ h' : (curveK K a b).toAffine.Nonsingular x (-y),
      -Affine.Point.some x y hxy = Affine.Point.some x (-y) h' := by
  have e : (curveK K a b).toAffine.negY x y = -y := by simp [Affine.negY]
  have h' := (Affine.nonsingular_neg x y).2 hxy
  rw [e] at h'
  refine ⟨h', ?_⟩
  simp only [Affine.Point.neg_some, e]


/-- Reduction is additive on two integral points. -/
lemma red_add_int (h : Good a b) {X1 Y1 X2 Y2 : R}
    (h1 : (curveK K a b).toAffine.Nonsingular (algebraMap R K X1) (algebraMap R K Y1))
    (h2 : (curveK K a b).toAffine.Nonsingular (algebraMap R K X2) (algebraMap R K Y2)) :
    redPt h (Affine.Point.some _ _ h1 + Affine.Point.some _ _ h2) =
      redPt h (Affine.Point.some _ _ h1) + redPt h (Affine.Point.some _ _ h2) := by
  obtain ⟨hA1, e1⟩ := redPt_some_of_alg h h1 rfl rfl
  obtain ⟨hA2, e2⟩ := redPt_some_of_alg h h2 rfl rfl
  rw [e1, e2]
  have n1 := (shortCurve_nonsingular_iff.1 hA1).2
  have ek1 := shortCurve_equation h1.1
  have ek2 := shortCurve_equation h2.1
  by_cases hQ : algebraMap R K X1 = algebraMap R K X2 ∧ algebraMap R K Y1 = -algebraMap R K Y2
  · have hz : Affine.Point.some _ _ h1 + Affine.Point.some _ _ h2 = 0 :=
      Affine.Point.add_of_Y_eq hQ.1 (by simp [Affine.negY, hQ.2])
    have hX : X1 = X2 := ι_eq (K := K) hQ.1
    have hY : Y1 = -Y2 := ι_eq (K := K) (by rw [map_neg]; exact hQ.2)
    rw [hz, redPt_zero]
    symm
    refine Affine.Point.add_of_Y_eq (by rw [hX]) ?_
    simp [Affine.negY, hY]
  · obtain ⟨ℓ, H1, H2⟩ := exists_slope ek1 ek2 hQ
    obtain ⟨h3, hsum⟩ := add_some_eq h1 h2 hQ H1 H2
    rw [hsum]
    by_cases hdeg : IsLocalRing.residue R X1 = IsLocalRing.residue R X2 ∧
        IsLocalRing.residue R Y1 = -IsLocalRing.residue R Y2
    · rw [Affine.Point.add_of_Y_eq hdeg.1 (by simp [Affine.negY, hdeg.2])]
      apply redPt_some_of_not_isInt
      intro hint
      exact not_isInt_slope_of_deg hdeg n1 H1 H2 (isInt_x3_iff.1 hint)
    · obtain ⟨L, rfl⟩ := isInt_slope_of_nondeg hdeg H1 H2
      have H1' : L * (X1 - X2) = Y1 - Y2 := ι_eq (K := K) (by simp only [map_mul, map_sub]; exact H1)
      have H2' : L * (Y1 + Y2) = X1 ^ 2 + X1 * X2 + X2 ^ 2 + a :=
        ι_eq (K := K) (by simp only [map_add, map_mul, map_pow]; exact H2)
      have H1z := congrArg (IsLocalRing.residue R) H1'
      have H2z := congrArg (IsLocalRing.residue R) H2'
      simp only [map_add, map_mul, map_pow, map_sub] at H1z H2z
      obtain ⟨h3z, hsumz⟩ := add_some_eq hA1 hA2 hdeg H1z H2z
      rw [hsumz]
      obtain ⟨hA3, e3⟩ := redPt_some_of_alg h h3 (X := L ^ 2 - X1 - X2)
        (Y := -(L * ((L ^ 2 - X1 - X2) - X1) + Y1)) (by simp only [map_sub, map_pow])
        (by simp only [map_neg, map_add, map_mul, map_sub, map_pow])
      rw [e3]
      simp only [map_neg, map_add, map_mul, map_sub, map_pow]


/-- If `x₁` is not integral, and `x₃ = ℓ² - x₁ - X₂` comes from the chord through `(x₁, y₁)` and an integral
point, then `x₃` is integral. -/
lemma isInt_x3_big {x1 y1 ℓ x3 : K} (hx1 : ¬ IsInt R x1) {X2 Y2 : R}
    (e1 : y1 ^ 2 = x1 ^ 3 + algebraMap R K a * x1 + algebraMap R K b)
    (H1 : ℓ * (x1 - algebraMap R K X2) = y1 - algebraMap R K Y2)
    (hx3 : ℓ ^ 2 - x1 - algebraMap R K X2 = x3) : IsInt R x3 := by
  obtain ⟨S, hS, hSx⟩ := exists_small hx1
  have hx0 : x1 ≠ 0 := fun h0 => hx1 (h0 ▸ isInt_zero)
  have hc2 : (y1 * algebraMap R K S ^ 2) ^ 2 = algebraMap R K (S + a * S ^ 3 + b * S ^ 4) := by
    simp only [map_add, map_mul, map_pow]
    linear_combination (algebraMap R K S) ^ 4 * e1 + (algebraMap R K S * ((algebraMap R K S * x1) ^ 2 +
      algebraMap R K S * x1 + 1) + algebraMap R K a * (algebraMap R K S) ^ 3) * hSx
  obtain ⟨C, hC⟩ := isInt_of_sq hc2
  have hN : x3 * (x1 - algebraMap R K X2) ^ 2 = x1 ^ 2 * algebraMap R K X2 +
      x1 * algebraMap R K X2 ^ 2 - algebraMap R K X2 ^ 3 + algebraMap R K a * x1 + algebraMap R K b +
      algebraMap R K Y2 ^ 2 - 2 * y1 * algebraMap R K Y2 := by
    rw [← hx3]
    linear_combination (ℓ * (x1 - algebraMap R K X2) + (y1 - algebraMap R K Y2)) * H1 + e1
  have ht : algebraMap R K S = x1⁻¹ := eq_inv_of_mul_eq_one_left hSx
  have hW : x3 * algebraMap R K ((1 - X2 * S) ^ 2) = algebraMap R K
      (X2 + S * (X2 ^ 2 + a) - S ^ 2 * (X2 ^ 3 - b - Y2 ^ 2) - 2 * C * Y2) := by
    simp only [map_add, map_mul, map_pow, map_sub, map_one, map_ofNat, hC, ht]
    field_simp
    linear_combination hN
  have hD : IsUnit (1 - X2 * S) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have : IsLocalRing.residue R S = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hS
    simp [this]
  exact isInt_of_mul_unit (hD.pow 2) hW


/-- Reduction is additive when one point has non-integral `x` and the other is integral. -/
lemma red_add_big (h : Good a b) {x1 y1 : K} (h1 : (curveK K a b).toAffine.Nonsingular x1 y1)
    (hx1 : ¬ IsInt R x1) {X2 Y2 : R}
    (h2 : (curveK K a b).toAffine.Nonsingular (algebraMap R K X2) (algebraMap R K Y2)) :
    redPt h (Affine.Point.some x1 y1 h1 + Affine.Point.some _ _ h2) =
      redPt h (Affine.Point.some _ _ h2) := by
  have hQ : ¬(x1 = algebraMap R K X2 ∧ y1 = -algebraMap R K Y2) :=
    fun hh => hx1 (hh.1 ▸ isInt_algebraMap X2)
  have ek1 := shortCurve_equation h1.1
  have ek2 := shortCurve_equation h2.1
  obtain ⟨ℓ, H1, H2⟩ := exists_slope ek1 ek2 hQ
  obtain ⟨h3, hsum⟩ := add_some_eq h1 h2 hQ H1 H2
  have hx3int := isInt_x3_big hx1 ek1 H1 rfl
  generalize hx3d : ℓ ^ 2 - x1 - algebraMap R K X2 = x3 at h3 hsum hx3int
  generalize hy3d : -(ℓ * (x3 - x1) + y1) = y3 at h3 hsum
  rw [hsum]
  obtain ⟨X3, hX3⟩ := hx3int
  obtain ⟨Y3, hY3⟩ := isInt_y h3.1 ⟨X3, hX3⟩
  obtain ⟨hA3, e3⟩ := redPt_some_of_alg h h3 hX3 hY3
  obtain ⟨hA2, e2⟩ := redPt_some_of_alg h h2 rfl rfl
  rw [e3, e2]
  simp only [Affine.Point.some.injEq]
  obtain ⟨h2', hneg⟩ := neg_some_eq h2
  have hne : ¬(x3 = algebraMap R K X2 ∧ y3 = -(-algebraMap R K Y2)) := by
    rintro ⟨hh1, hh2⟩
    have hh : Affine.Point.some x1 y1 h1 + Affine.Point.some _ _ h2 = Affine.Point.some _ _ h2 := by
      rw [hsum]; simp only [Affine.Point.some.injEq]; exact ⟨hh1, by rw [hh2, neg_neg]⟩
    exact Affine.Point.some_ne_zero _ (add_right_cancel (hh.trans (zero_add _).symm))
  have e3' := shortCurve_equation h3.1
  have ek2' : (-algebraMap R K Y2) ^ 2 = algebraMap R K X2 ^ 3 + algebraMap R K a * algebraMap R K X2 +
      algebraMap R K b := by rw [neg_sq]; exact ek2
  obtain ⟨ℓ', H1', H2'⟩ := exists_slope e3' ek2' hne
  obtain ⟨h4, hsum4⟩ := add_some_eq h3 h2' hne H1' H2'
  have hPeq : Affine.Point.some x3 y3 h3 + Affine.Point.some _ _ h2' = Affine.Point.some x1 y1 h1 := by
    rw [← hneg, ← hsum]; abel
  rw [hPeq] at hsum4
  simp only [Affine.Point.some.injEq] at hsum4
  obtain ⟨hxx, -⟩ := hsum4
  have hdeg : IsLocalRing.residue R X3 = IsLocalRing.residue R X2 ∧
      IsLocalRing.residue R Y3 = -IsLocalRing.residue R (-Y2) := by
    by_contra hnd
    have hℓ := isInt_slope_of_nondeg (a := a) (ℓ := ℓ') (X1 := X3) (Y1 := Y3) (X2 := X2) (Y2 := -Y2) hnd
      (by rw [map_neg, hX3, hY3]; exact H1') (by rw [map_neg, hX3, hY3]; exact H2')
    apply hx1
    rw [hxx, ← hX3]
    exact isInt_x3_iff.2 hℓ
  obtain ⟨hdx, hdy⟩ := hdeg
  refine ⟨hdx, ?_⟩
  rw [hdy, map_neg, neg_neg]

/-- The sum of two points with non-integral `x` has reduction `0`. -/
lemma red_add_bb (h : Good a b) {x1 y1 x2 y2 : K} (h1 : (curveK K a b).toAffine.Nonsingular x1 y1)
    (h2 : (curveK K a b).toAffine.Nonsingular x2 y2) (hx1 : ¬ IsInt R x1) (hx2 : ¬ IsInt R x2) :
    redPt h (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) = 0 := by
  rcases hT : (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) with _ | ⟨x3, y3, h3⟩
  · rfl
  · by_cases hx3 : IsInt R x3
    · exfalso
      obtain ⟨X3, rfl⟩ := hx3
      obtain ⟨Y3, rfl⟩ := isInt_y h3.1 ⟨X3, rfl⟩
      obtain ⟨h2', hneg⟩ := neg_some_eq h2
      have hP : Affine.Point.some x2 (-y2) h2' + Affine.Point.some _ _ h3 =
          Affine.Point.some x1 y1 h1 := by
        rw [← hneg, ← hT]; abel
      have key := red_add_big h h2' hx2 h3
      rw [hP, redPt_some_of_not_isInt h h1 hx1] at key
      obtain ⟨hA, e⟩ := redPt_some_of_alg h h3 rfl rfl
      rw [e] at key
      exact Affine.Point.some_ne_zero _ key.symm
    · exact redPt_some_of_not_isInt h h3 hx3


/-- **Theorem 4.1 (b)** over $R$ (Milne, pdf p. 70): reduction is a homomorphism. -/
theorem redPt_add (h : Good a b) (P Q : (curveK K a b).toAffine.Point) :
    redPt h (P + Q) = redPt h P + redPt h Q := by
  have h0 : (Affine.Point.zero : (curveK K a b).toAffine.Point) = 0 := rfl
  cases P with
  | zero => rw [h0, zero_add, redPt_zero, zero_add]
  | some x1 y1 h1 =>
    cases Q with
    | zero => rw [h0, add_zero, redPt_zero, add_zero]
    | some x2 y2 h2 =>
      by_cases hx1 : IsInt R x1
      · by_cases hx2 : IsInt R x2
        · obtain ⟨X1, rfl⟩ := hx1
          obtain ⟨Y1, rfl⟩ := isInt_y h1.1 ⟨X1, rfl⟩
          obtain ⟨X2, rfl⟩ := hx2
          obtain ⟨Y2, rfl⟩ := isInt_y h2.1 ⟨X2, rfl⟩
          exact red_add_int h h1 h2
        · obtain ⟨X1, rfl⟩ := hx1
          obtain ⟨Y1, rfl⟩ := isInt_y h1.1 ⟨X1, rfl⟩
          rw [redPt_some_of_not_isInt h h2 hx2, add_zero, add_comm]
          exact red_add_big h h2 hx2 h1
      · by_cases hx2 : IsInt R x2
        · obtain ⟨X2, rfl⟩ := hx2
          obtain ⟨Y2, rfl⟩ := isInt_y h2.1 ⟨X2, rfl⟩
          rw [redPt_some_of_not_isInt h h1 hx1, zero_add]
          exact red_add_big h h1 hx1 h2
        · rw [redPt_some_of_not_isInt h h1 hx1, redPt_some_of_not_isInt h h2 hx2, add_zero]
          exact red_add_bb h h1 h2 hx1 hx2

/-- Reduction as a homomorphism of groups. -/
noncomputable def redHom (h : Good a b) : (curveK K a b).toAffine.Point →+ (curveRes a b).toAffine.Point :=
  AddMonoidHom.mk' (redPt h) (redPt_add h)

@[simp] lemma redHom_apply (h : Good a b) (P : (curveK K a b).toAffine.Point) : redHom h P = redPt h P := rfl

/-- **Theorem 4.1 (b)** over $R$, surjectivity (Hensel's lemma): every point of $\bar E(k)$ lifts. -/
theorem redPt_surjective [HenselianLocalRing R] (h : Good a b) :
    Function.Surjective (redPt (K := K) h) := by
  intro A
  cases A with
  | zero => exact ⟨0, rfl⟩
  | some u v hA =>
    obtain ⟨heqA, hns⟩ := shortCurve_nonsingular_iff.1 hA
    obtain ⟨X0, rfl⟩ := IsLocalRing.residue_surjective u
    obtain ⟨Y0, rfl⟩ := IsLocalRing.residue_surjective v
    obtain ⟨X, Y, hXY, hXu, hYv⟩ : ∃ X Y : R, Y ^ 2 = X ^ 3 + a * X + b ∧
        IsLocalRing.residue R X = IsLocalRing.residue R X0 ∧
        IsLocalRing.residue R Y = IsLocalRing.residue R Y0 := by
      by_cases hc : IsUnit (3 * X0 ^ 2 + a)
      · let F : R[X] := Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C (b - Y0 ^ 2)
        have hF : F.Monic := by
          unfold F; monicity!
        have hFe : ∀ z : R, F.eval z = z ^ 3 + a * z + (b - Y0 ^ 2) := by
          intro z; simp [F]
        have hFd : ∀ z : R, F.derivative.eval z = 3 * z ^ 2 + a := by
          intro z; simp [F, derivative_pow]
        obtain ⟨z, hz, hzx⟩ := HenselianLocalRing.is_henselian F hF X0
          (by
            rw [hFe, ← IsLocalRing.residue_eq_zero_iff]
            simp only [map_add, map_mul, map_pow, map_sub]
            linear_combination -heqA)
          (by rw [hFd]; exact hc)
        refine ⟨z, Y0, ?_, ?_, rfl⟩
        · have := hz.eq_zero; rw [hFe] at this; linear_combination -this
        · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hzx
      · have hc' : IsUnit (2 * Y0) := by
          rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
          rcases hns with n | n
          · exfalso; apply hc; rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
            simpa only [map_add, map_mul, map_pow, map_ofNat] using n
          · simpa only [map_mul, map_ofNat] using n
        let F : R[X] := Polynomial.X ^ 2 - Polynomial.C (X0 ^ 3 + a * X0 + b)
        have hF : F.Monic := monic_X_pow_sub_C _ (by norm_num)
        have hFe : ∀ z : R, F.eval z = z ^ 2 - (X0 ^ 3 + a * X0 + b) := by
          intro z; simp [F]
        have hFd : ∀ z : R, F.derivative.eval z = 2 * z := by
          intro z; simp [F, derivative_pow]
        obtain ⟨z, hz, hzy⟩ := HenselianLocalRing.is_henselian F hF Y0
          (by
            rw [hFe, ← IsLocalRing.residue_eq_zero_iff]
            simp only [map_add, map_mul, map_pow, map_sub]
            linear_combination heqA)
          (by rw [hFd]; exact hc')
        refine ⟨X0, z, ?_, rfl, ?_⟩
        · have := hz.eq_zero; rw [hFe] at this; linear_combination this
        · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hzy
    have hnsK : (curveK K a b).toAffine.Nonsingular (algebraMap R K X) (algebraMap R K Y) := by
      rw [shortCurve_nonsingular_iff]
      refine ⟨?_, ?_⟩
      · simp only [← map_pow, ← map_mul, ← map_add, hXY]
      · by_contra hc
        push Not at hc
        obtain ⟨c1, c2⟩ := hc
        have c1' : 3 * X ^ 2 + a = 0 := ι_eq (K := K) (by
          simp only [map_add, map_mul, map_pow, map_ofNat, map_zero]; exact c1)
        have c2' : 2 * Y = 0 := ι_eq (K := K) (by
          simp only [map_mul, map_ofNat, map_zero]; exact c2)
        have r1 := congrArg (IsLocalRing.residue R) c1'
        have r2 := congrArg (IsLocalRing.residue R) c2'
        simp only [map_add, map_mul, map_pow, map_ofNat, map_zero, hXu, hYv] at r1 r2
        rcases hns with n | n
        · exact n r1
        · exact n r2
    obtain ⟨hA', e⟩ := redPt_some_of_alg h hnsK rfl rfl
    refine ⟨_, e.trans ?_⟩
    simp only [Affine.Point.some.injEq]
    exact ⟨hXu, hYv⟩

/-- The short model $Y^2 = X^3 + aX + b$ over $R$ itself. -/
def shortR (a b : R) : WeierstrassCurve R := ⟨0, 0, 0, a, b⟩

lemma curveK_eq_map (a b : R) :
    curveK K a b = (shortR a b).map (algebraMap R K) := by
  ext <;> simp [shortR, shortCurve]

lemma curveK_Δ_ne_zero (h : Good a b) : (curveK K a b).Δ ≠ 0 := by
  show (shortCurve (algebraMap R K a) (algebraMap R K b)).Δ ≠ 0
  rw [Δ_shortCurve]
  have h16 : IsUnit (16 : R) := by
    have := h.two.pow 4
    norm_num at this
    exact this
  have hu : IsUnit (-16 * (4 * a ^ 3 + 27 * b ^ 2) : R) := h16.neg.mul h.disc
  have hne := (map_ne_zero_iff (algebraMap R K) ι_inj).2 hu.ne_zero
  simp only [map_mul, map_neg, map_add, map_pow, map_ofNat] at hne
  exact hne

lemma two_ne_zero_K (h : Good a b) : (2 : K) ≠ 0 := by
  have := (map_ne_zero_iff (algebraMap R K) ι_inj).2 h.two.ne_zero
  rwa [map_ofNat] at this

/-- A point with non-integral `x` is not 2-torsion. -/
lemma two_nsmul_ne_zero (h : Good a b) {x y : K} (hxy : (curveK K a b).toAffine.Nonsingular x y)
    (hx : ¬ IsInt R x) : (2 : ℕ) • Affine.Point.some x y hxy ≠ 0 := by
  intro h0
  rw [two_nsmul] at h0
  by_cases hy : y = (curveK K a b).toAffine.negY x y
  · have hy' : y = -y := by simpa [Affine.negY] using hy
    have hy0 : y = 0 := by
      have : (2 : K) * y = 0 := by linear_combination hy'
      exact (mul_eq_zero.1 this).resolve_left (two_ne_zero_K h)
    have e := shortCurve_equation hxy.1
    rw [hy0] at e
    exact hx (isInt_of_cubic (a := a) (b := b) (by linear_combination -e))
  · have := Affine.Point.add_of_Y_ne (h₁ := hxy) (h₂ := hxy) hy
    rw [this] at h0
    exact Affine.Point.some_ne_zero _ h0

/-- Step 1 (Hensel): for `xP` not integral and `n` a unit there is `x₁` not integral with
`Φₙ(x₁) = xP Ψₙ²(x₁)`. -/
theorem exists_x_of_hensel_valued [HenselianLocalRing R] (a b : R) {n : ℤ} (hn : IsUnit (n : R)) {xP : K}
    (hx : ¬ IsInt R xP) :
    ∃ x₁ : K, ¬ IsInt R x₁ ∧
      ((curveK K a b).Φ n).eval x₁ = xP * ((curveK K a b).ΨSq n).eval x₁ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨S, hS, hSx⟩ := exists_small hx
  have hxP0 : xP ≠ 0 := fun h0 => hx (h0 ▸ isInt_zero)
  have hS0 : S ≠ 0 := by
    rintro rfl; rw [map_zero, zero_mul] at hSx; exact zero_ne_one hSx
  set W₀ := shortR a b with hW₀
  set N := n.natAbs ^ 2 with hN
  have hNpos : 1 ≤ N := Nat.one_le_pow _ _ (Int.natAbs_pos.2 hn0)
  set Φ₀ := W₀.Φ n
  set Ψ₀ := W₀.ΨSq n
  set hh : R[X] := C S * reflect N Φ₀ - reflect N Ψ₀ with hhdef
  have hΦN : Φ₀.coeff N = 1 := W₀.coeff_Φ n
  have hΨdeg : Ψ₀.natDegree ≤ N - 1 := W₀.natDegree_ΨSq_le n
  have hΨN : Ψ₀.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hΨ1 : Ψ₀.coeff (N - 1) = (n : R) ^ 2 := W₀.coeff_ΨSq n
  have hΦdeg : Φ₀.natDegree ≤ N := W₀.natDegree_Φ_le n
  have h0 : hh.coeff 0 = S := by
    simp [hhdef, coeff_reflect, hΦN, hΨN]
  have h1 : hh.coeff 1 = S * Φ₀.coeff (N - 1) - (n : R) ^ 2 := by
    simp [hhdef, coeff_reflect, revAt_le hNpos, hΨ1]
  have hunit : IsUnit (hh.derivative.eval 0) := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simp only [Nat.cast_zero, zero_add, mul_one, h1]
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have : IsLocalRing.residue R S = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hS
    have hn' : IsLocalRing.residue R (n : R) ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hn
    simp only [map_sub, map_mul, map_pow, this, zero_mul, zero_sub, ne_eq, neg_eq_zero]
    exact pow_ne_zero 2 hn'
  have hev : hh.eval 0 ∈ maximalIdeal R := by
    rw [← coeff_zero_eq_eval_zero, h0]; exact hS
  obtain ⟨z, hz, hzm⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R) hh (a₀ := 0) hev
    (hunit.map (Ideal.Quotient.mk (maximalIdeal R)))
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hS0
    rw [← h0, coeff_zero_eq_eval_zero]
    exact hz.eq_zero
  have hzq : algebraMap R K z ≠ 0 := by
    intro h0'; exact hz0 (ι_eq (K := K) (by rw [h0', map_zero]))
  have hzm' : z ∈ maximalIdeal R := by simpa using hzm
  refine ⟨(algebraMap R K z)⁻¹, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    have : t * z = 1 := ι_eq (K := K) (by rw [map_mul, ht, map_one]; exact inv_mul_cancel₀ hzq)
    exact ((IsLocalRing.mem_maximalIdeal _).1 hzm') (IsUnit.of_mul_eq_one t (by rw [mul_comm]; exact this))
  · have hz' : eval₂ (algebraMap R K) (algebraMap R K z) hh = 0 := by
      rw [eval₂_at_apply, hz.eq_zero, map_zero]
    rw [hhdef, eval₂_sub, eval₂_mul, eval₂_C] at hz'
    let _ : Invertible ((algebraMap R K z)⁻¹) := invertibleOfNonzero (inv_ne_zero hzq)
    have hinv : ⅟((algebraMap R K z)⁻¹) = algebraMap R K z := by
      rw [invOf_eq_inv, inv_inv]
    have k1 := eval₂_reflect_mul_pow (algebraMap R K) ((algebraMap R K z)⁻¹) N Φ₀ hΦdeg
    have k2 := eval₂_reflect_mul_pow (algebraMap R K) ((algebraMap R K z)⁻¹) N Ψ₀ (by omega)
    rw [hinv] at k1 k2
    rw [curveK_eq_map, map_Φ, map_ΨSq, eval_map, eval_map, ← k1, ← k2]
    have hsq : algebraMap R K S = xP⁻¹ := eq_inv_of_mul_eq_one_left hSx
    rw [hsq] at hz'
    generalize eval₂ (algebraMap R K) (algebraMap R K z) (reflect N Φ₀) = A at hz' ⊢
    generalize eval₂ (algebraMap R K) (algebraMap R K z) (reflect N Ψ₀) = B at hz' ⊢
    have hB : B = xP⁻¹ * A := by linear_combination (-1 : K) * hz'
    rw [hB]
    field_simp

/-- Helper for `exists_zsmul_eq_of_redPt_eq_zero`. -/
theorem exists_zsmul_eq_of_redPt_eq_zero' [HenselianLocalRing R] (h : Good a b) {n : ℤ}
    (hn : IsUnit (n : R)) {P : (curveK K a b).toAffine.Point} (hP : redPt h P = 0) :
    ∃ Q, redPt h Q = 0 ∧ n • Q = P := by
  cases P with
  | zero => exact ⟨0, rfl, zsmul_zero n⟩
  | some xP yP hPns =>
    have hx := (redPt_eq_zero_iff h _).1 hP xP yP hPns rfl
    obtain ⟨x₁, hx₁, h₁⟩ := exists_x_of_hensel_valued (K := K) a b hn hx
    have hΔ := curveK_Δ_ne_zero (K := K) h
    obtain ⟨y₁, hy₁⟩ := exists_y_aux (algebraMap R K a) (algebraMap R K b) hΔ hPns
      (two_nsmul_ne_zero h hPns hx) h₁
    have hQ : (curveK K a b).toAffine.Nonsingular x₁ y₁ :=
      (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 hy₁
    rcases smul_eq_of_eval (curveK K a b) hΔ hPns hQ h₁ with e | e
    · exact ⟨_, redPt_some_of_not_isInt h hQ hx₁, e⟩
    · obtain ⟨h', hneg⟩ := neg_some_eq hQ
      rw [hneg] at e
      exact ⟨_, redPt_some_of_not_isInt h h' hx₁, e⟩


/-- **Corollary 4.2** over $R$ (Milne, pdf p. 71), surjectivity: for $n$ a unit of $R$, every point of
$E^1(K)$ is $n$ times a point of $E^1(K)$. -/
theorem exists_zsmul_eq_of_redPt_eq_zero [HenselianLocalRing R] (h : Good a b) {n : ℤ}
    (hn : IsUnit (n : R)) {P : (curveK K a b).toAffine.Point} (hP : redPt h P = 0) :
    ∃ Q, redPt h Q = 0 ∧ n • Q = P :=
  exists_zsmul_eq_of_redPt_eq_zero' h hn hP

lemma isInt_of_isIntegral {z : K} (hz : IsIntegral R z) : IsInt R z := by
  have : IsIntegrallyClosed R := Valuation.Integers.isIntegrallyClosed (ValuationRing.integers R K)
  exact IsIntegrallyClosed.isIntegral_iff.1 hz

/-- A root in `K` of a polynomial over `R` with unit leading coefficient is integral. -/
lemma isInt_of_root {z : K} (p : R[X]) (hp : IsUnit p.leadingCoeff)
    (hz : (p.map (algebraMap R K)).eval z = 0) : IsInt R z := by
  obtain ⟨u, hu⟩ := hp
  apply isInt_of_isIntegral
  refine ⟨C (↑u⁻¹) * p, monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu]; simp), ?_⟩
  rw [eval₂_mul, eval₂_C, eval₂_eq_eval_map, hz, mul_zero]

/-- **Corollary 4.2** over $R$, injectivity: for $n$ a unit of $R$, the kernel of reduction has no
$n$-torsion. -/
theorem eq_zero_of_zsmul_eq_zero (h : Good a b) {n : ℤ} (hn : IsUnit (n : R))
    {P : (curveK K a b).toAffine.Point} (hP : redPt h P = 0) (hnP : n • P = 0) : P = 0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
    exfalso
    have hx := (redPt_eq_zero_iff h _).1 hP x y hxy rfl
    have hψ : ((curveK K a b).ψ n).evalEval x y = 0 := by
      by_contra hψ
      obtain ⟨h', heq⟩ := zsmul_some_eq_of_evalEval_ψ_ne_zero (curveK K a b) hxy n hψ
      rw [hnP] at heq
      exact Affine.Point.some_ne_zero _ heq.symm
    have hΨ : ((curveK K a b).ΨSq n).eval x = 0 := by
      rw [← evalEval_Ψ_sq_eq_eval_ΨSq _ hxy.1 n, ← evalEval_ψ_eq_evalEval_Ψ _ hxy.1 n, hψ]; ring
    apply hx
    refine isInt_of_root ((shortR a b).ΨSq n) ?_ ?_
    · rw [(shortR a b).leadingCoeff_ΨSq hn.ne_zero]; exact hn.pow 2
    · rw [← map_ΨSq, ← curveK_eq_map]; exact hΨ


/-- **Lemma 3.2** over a Henselian valuation ring (Milne, pdf p. 119): for good reduction and $n$ a unit of
$R$, a point $P \in E(K)$ is in $nE(K)$ if and only if its reduction is in $n\bar E(k)$. -/
theorem lemma_3_2_valued [HenselianLocalRing R] (h : Good a b) {n : ℤ} (hn : IsUnit (n : R))
    (P : (curveK K a b).toAffine.Point) :
    (∃ Q, n • Q = P) ↔ ∃ Q', n • Q' = redPt h P := by
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨redPt h Q, by rw [← redHom_apply, ← redHom_apply, map_zsmul]⟩
  · rintro ⟨Q', hQ'⟩
    obtain ⟨R₀, hR₀⟩ := redPt_surjective (K := K) h Q'
    have hD : redPt h (P - n • R₀) = 0 := by
      rw [← redHom_apply, map_sub, map_zsmul, redHom_apply, redHom_apply, hR₀, hQ', sub_self]
    obtain ⟨S, -, hS⟩ := exists_zsmul_eq_of_redPt_eq_zero h hn hD
    exact ⟨R₀ + S, by rw [zsmul_add, hS]; abel⟩

end NumberFieldKB.MilneEC.II.Valued
