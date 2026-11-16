import NumberFieldKB.MilneEC.Ch4Rank
import NumberFieldKB.MilneEC.Ch4Lemma21

/-!
# Milne, *Elliptic Curves*, Chapter IV: explicit 2-descent when the 2-torsion is rational

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Remark 3.7 (pdf p. 121) and the
proof of Proposition 5.6 (pdf pp. 137–138).  Locators give the pdf page of the text `ectext6` (printed page = pdf
page − 8).

For $E : Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$ with distinct integers $\alpha, \beta, \gamma$, Milne's maps
$\varphi_\alpha, \varphi_\beta : E(\mathbb Q) \to \mathbb Q^\times/\mathbb Q^{\times 2}$ (`phiAlpha`, `phiBeta`,
Chapter IV, Remark 3.7) are proved to be homomorphisms with kernel $2E(\mathbb Q)$, taking values represented by
$\pm$ products of primes dividing $2\Delta$.  This proves the named statement `Remark3_7` (`remark_3_7`), which Milne
leaves to the reader with a reference to Cassels (1991), Chapter 15.  The local statements (a)–(c) of the proof of
Proposition 5.6 are proved as well (`prop_5_6_local : Prop5_6Local`).

The arguments are the classical ones:
* **homomorphism**: if a line meets $E$ in $P_1, P_2, P_3$, then $(x_1 - r)(x_2 - r)(x_3 - r) = \ell(r)^2$ for each root
  $r$, where $Y = \ell(X)$ is the line (`chord_identity`, from Mathlib's `addPolynomial_slope`); translation by the
  2-torsion point $T_r = (r, 0)$ sends $x - r$ to $(r - s)(r - t)/(x - r)$ (`descentRep_add_root`);
* **kernel**: if $x_0 - \alpha$, $x_0 - \beta$, $x_0 - \gamma$ are the squares $u^2, v^2, w^2$, then the tangent line
  $Y = lX + m$ with $l = u + v + w$, $m = -x_0 l - uvw$ touches $E$ at the point with abscissa
  $\xi = x_0 + uv + vw + wu$, and doubles it to $\pm(x_0, y_0)$ (`exists_two_zsmul_eq_of_sq`).  This is the
  tangent-line criterion of Tau Ceti's `WeierstrassCurve.exists_eq_two_smul_iff`
  (`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`, Apache-2.0), specialized to a split cubic with
  the explicit solution $(\xi, l, m)$;
* **valuations**: $v_p(x - r) + v_p(x - s) + v_p(x - t) = 2v_p(y)$, and the ultrametric inequality
  (`even_padicValRat_core`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

set_option backward.isDefEq.respectTransparency false

namespace NumberFieldKB.MilneEC

section TwoDescent

variable {α β γ : ℤ}

/-! ### The curve $Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$ -/

theorem cubicCurve_equation_iff {x y : ℚ} :
    (cubicCurve α β γ).toAffine.Equation x y ↔ y ^ 2 = (x - α) * (x - β) * (x - γ) := by
  rw [Affine.equation_iff]
  simp only [cubicCurve]
  constructor <;> intro h <;> linear_combination h

theorem cubicCurve_negY (x y : ℚ) : (cubicCurve α β γ).toAffine.negY x y = -y := by
  simp only [Affine.negY, cubicCurve]
  ring

/-- $r, s, t$ are $\alpha, \beta, \gamma$ in some order: their elementary symmetric functions agree. -/
structure IsRootTriple (α β γ : ℤ) (r s t : ℚ) : Prop where
  e1 : (α : ℚ) + β + γ = r + s + t
  e2 : (α : ℚ) * β + β * γ + γ * α = r * s + s * t + t * r
  e3 : (α : ℚ) * β * γ = r * s * t

theorem IsRootTriple.cubic {r s t : ℚ} (h : IsRootTriple α β γ r s t) (x : ℚ) :
    (x - α) * (x - β) * (x - γ) = (x - r) * (x - s) * (x - t) := by
  linear_combination (-x ^ 2) * h.e1 + x * h.e2 - h.e3

theorem isRootTriple_alpha : IsRootTriple α β γ α β γ := ⟨rfl, rfl, rfl⟩

theorem isRootTriple_beta : IsRootTriple α β γ β α γ := ⟨by ring, by ring, by ring⟩

theorem isRootTriple_gamma : IsRootTriple α β γ γ α β := ⟨by ring, by ring, by ring⟩

variable {r s t : ℚ}

theorem IsRootTriple.equation_iff (h : IsRootTriple α β γ r s t) {x y : ℚ} :
    (cubicCurve α β γ).toAffine.Equation x y ↔ y ^ 2 = (x - r) * (x - s) * (x - t) := by
  rw [cubicCurve_equation_iff, h.cubic]

/-- A point with abscissa a root has ordinate $0$. -/
theorem IsRootTriple.y_eq_zero (h : IsRootTriple α β γ r s t) {y : ℚ}
    (hy : (cubicCurve α β γ).toAffine.Equation r y) : y = 0 := by
  rw [h.equation_iff] at hy
  simpa using hy

/-- A point with ordinate $0$ has abscissa a root. -/
theorem IsRootTriple.root_of_y_eq_zero (h : IsRootTriple α β γ r s t) {x : ℚ}
    (hy : (cubicCurve α β γ).toAffine.Equation x 0) : x = r ∨ x = s ∨ x = t := by
  rw [h.equation_iff] at hy
  have : (x - r) * (x - s) * (x - t) = 0 := by linear_combination -hy
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.1 h2)
    · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h1))

/-- A point with abscissa a root is the 2-torsion point $(r, 0)$. -/
theorem IsRootTriple.some_eq_root (h : IsRootTriple α β γ r s t) {x y : ℚ}
    (hP : (cubicCurve α β γ).toAffine.Nonsingular x y) (hx : x = r) :
    ∃ hT : (cubicCurve α β γ).toAffine.Nonsingular r 0, Point.some x y hP = Point.some r 0 hT := by
  subst hx
  have hy : y = 0 := h.y_eq_zero hP.1
  subst hy
  exact ⟨hP, rfl⟩

theorem cubicCurve_isElliptic_of_ne (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) : (cubicCurve α β γ).IsElliptic :=
  (cubicCurve_isElliptic_iff α β γ).2 ⟨hαβ, hβγ, hγα⟩

/-! ### The representatives `descentRep` -/

@[simp]
theorem descentRep_zero (r c : ℚ) : descentRep (α := α) (β := β) (γ := γ) r c 0 = 1 := rfl

theorem descentRep_some (r c x y : ℚ) (h : (cubicCurve α β γ).toAffine.Nonsingular x y) :
    descentRep r c (Point.some x y h : (cubicCurve α β γ).toAffine.Point) = if x = r then c else x - r := rfl

@[simp]
theorem descentRep_neg (r c : ℚ) (P : (cubicCurve α β γ).toAffine.Point) :
    descentRep r c (-P) = descentRep r c P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

/-! ### The chord identity and translation by a 2-torsion point -/

/-- **The chord identity** (Cassels 1991, Chapter 15): if the line through $(x_1, y_1)$ and $(x_2, y_2)$ (the
tangent if they coincide) has slope $\ell$ and meets $E$ again at abscissa $x_3$, then
$(x_1 - r)(x_2 - r)(x_3 - r) = (\ell(r - x_1) + y_1)^2$ for each root $r$. -/
theorem chord_identity (hr : IsRootTriple α β γ r s t) {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : (cubicCurve α β γ).toAffine.Equation x₁ y₁) (h₂ : (cubicCurve α β γ).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (cubicCurve α β γ).toAffine.negY x₂ y₂)) :
    (x₁ - r) * (x₂ - r) *
        ((cubicCurve α β γ).toAffine.addX x₁ x₂ ((cubicCurve α β γ).toAffine.slope x₁ x₂ y₁ y₂) - r) =
      ((cubicCurve α β γ).toAffine.slope x₁ x₂ y₁ y₂ * (r - x₁) + y₁) ^ 2 := by
  have H := congrArg (Polynomial.eval r) (Affine.addPolynomial_slope h₁ h₂ hxy)
  rw [Affine.addPolynomial_eq] at H
  simp only [Cubic.toPoly, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub] at H
  have hf : (r - α) * (r - β) * (r - γ) = 0 := by rw [hr.cubic]; ring
  simp only [cubicCurve] at H ⊢
  linear_combination -H - hf

/-- **Translation by $T_r = (r, 0)$**: for a point $(x, y)$ with $x \ne r$, the abscissa of $(x, y) + T_r$ is
$r + (r - s)(r - t)/(x - r)$; so the representative of $\varphi_r$ at $(x, y) + T_r$ is $(r - s)(r - t)/(x - r)$. -/
theorem descentRep_add_root (hr : IsRootTriple α β γ r s t) (hc : (r - s) * (r - t) ≠ 0) {x y : ℚ}
    (h : (cubicCurve α β γ).toAffine.Nonsingular x y) (hT : (cubicCurve α β γ).toAffine.Nonsingular r 0)
    (hx : x ≠ r) :
    descentRep r ((r - s) * (r - t)) (Point.some x y h + Point.some r 0 hT) = (r - s) * (r - t) / (x - r) := by
  have hxr : x - r ≠ 0 := sub_ne_zero.2 hx
  have hy2 : y ^ 2 = (x - r) * (x - s) * (x - t) := hr.equation_iff.1 h.1
  have key : (cubicCurve α β γ).toAffine.addX x r ((cubicCurve α β γ).toAffine.slope x r y 0) - r =
      (r - s) * (r - t) / (x - r) := by
    rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, cubicCurve]
    rw [eq_div_iff hxr, sub_zero, div_pow]
    field_simp
    linear_combination hy2 + (x - r) ^ 2 * hr.e1
  rw [Point.add_of_X_ne hx, descentRep_some, if_neg, key]
  intro h3
  rw [h3, sub_self] at key
  exact div_ne_zero hc hxr key.symm

/-- For the 2-torsion point $T_r$ and any point $Q$, $c \cdot \operatorname{rep}(Q) \cdot \operatorname{rep}(T_r + Q)$
is a square, $c = (r - s)(r - t)$. -/
theorem isSquare_mul_descentRep_root_add (hr : IsRootTriple α β γ r s t) (hc : (r - s) * (r - t) ≠ 0)
    (hT : (cubicCurve α β γ).toAffine.Nonsingular r 0) (Q : (cubicCurve α β γ).toAffine.Point) :
    IsSquare ((r - s) * (r - t) * descentRep r ((r - s) * (r - t)) Q *
      descentRep r ((r - s) * (r - t)) (Point.some r 0 hT + Q)) := by
  cases Q with
  | zero =>
    rw [← Point.zero_def, add_zero, descentRep_some, if_pos rfl, descentRep_zero]
    exact ⟨(r - s) * (r - t), by ring⟩
  | some x y h =>
    by_cases hx : x = r
    · subst x
      have hy : y = 0 := hr.y_eq_zero h.1
      subst hy
      rw [Point.add_of_Y_eq rfl (by rw [cubicCurve_negY, neg_zero]), descentRep_some, if_pos rfl, descentRep_zero]
      exact ⟨(r - s) * (r - t), by ring⟩
    · rw [add_comm, descentRep_add_root hr hc h hT hx, descentRep_some, if_neg hx]
      refine ⟨(r - s) * (r - t), ?_⟩
      field_simp [sub_ne_zero.2 hx]

/-- **The product of the representatives at $P$, $Q$, $P + Q$ is a square** (Cassels 1991, Chapter 15). -/
theorem isSquare_mul_descentRep_add (hr : IsRootTriple α β γ r s t) (hc : (r - s) * (r - t) ≠ 0)
    (P Q : (cubicCurve α β γ).toAffine.Point) :
    IsSquare (descentRep r ((r - s) * (r - t)) P * descentRep r ((r - s) * (r - t)) Q *
      descentRep r ((r - s) * (r - t)) (P + Q)) := by
  cases P with
  | zero => rw [← Point.zero_def, zero_add, descentRep_zero, one_mul]; exact ⟨_, rfl⟩
  | some x₁ y₁ h₁ =>
  cases Q with
  | zero => rw [← Point.zero_def, add_zero, descentRep_zero, mul_one]; exact ⟨_, rfl⟩
  | some x₂ y₂ h₂ =>
    by_cases hx₁ : x₁ = r
    · subst x₁
      have hy : y₁ = 0 := hr.y_eq_zero h₁.1
      subst hy
      rw [descentRep_some r _ r, if_pos rfl]
      exact isSquare_mul_descentRep_root_add hr hc h₁ _
    by_cases hx₂ : x₂ = r
    · subst x₂
      have hy : y₂ = 0 := hr.y_eq_zero h₂.1
      subst hy
      rw [add_comm, descentRep_some r _ r, if_pos rfl, mul_comm (descentRep r _ _) ((r - s) * (r - t))]
      exact isSquare_mul_descentRep_root_add hr hc h₂ _
    by_cases hxy : x₁ = x₂ ∧ y₁ = (cubicCurve α β γ).toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2, descentRep_zero, mul_one, descentRep_some, descentRep_some, hxy.1]
      exact ⟨_, rfl⟩
    have hsum := Point.add_some hxy (h₁ := h₁) (h₂ := h₂)
    by_cases hx₃ : (cubicCurve α β γ).toAffine.addX x₁ x₂ ((cubicCurve α β γ).toAffine.slope x₁ x₂ y₁ y₂) = r
    · -- $P + Q = T_r$, so $Q = T_r + (-P)$.
      obtain ⟨hT, hTe⟩ := hr.some_eq_root (Affine.nonsingular_add h₁ h₂ hxy) hx₃
      rw [hTe] at hsum
      have hQ : Point.some x₂ y₂ h₂ = Point.some r 0 hT + -Point.some x₁ y₁ h₁ := by
        rw [← hsum]; abel
      have key := isSquare_mul_descentRep_root_add hr hc hT (-Point.some x₁ y₁ h₁)
      rw [← hQ, descentRep_neg] at key
      rw [hsum, descentRep_some r _ r, if_pos rfl]
      convert key using 1
      ring
    · rw [hsum, descentRep_some, descentRep_some, descentRep_some, if_neg hx₁, if_neg hx₂, if_neg hx₃,
        chord_identity hr h₁.1 h₂.1 hxy]
      exact ⟨_, sq _⟩

/-! ### The maps $\varphi_r$ are homomorphisms -/

/-- The group $\mathbb Q^\times/\mathbb Q^{\times 2}$ has exponent $2$. -/
theorem ratModSquares_mul_self (z : RatModSquares) : z * z = 1 := by
  induction z using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact ⟨u, by simp [pow_two]⟩

/-- The class of a nonzero rational in $\mathbb Q^\times/\mathbb Q^{\times 2}$ is trivial iff it is a square. -/
theorem descentMap_eq_one_iff (r c : ℚ) (P : (cubicCurve α β γ).toAffine.Point) (hP : descentRep r c P ≠ 0) :
    descentMap r c P = 1 ↔ IsSquare (descentRep r c P) := by
  unfold descentMap
  rw [dif_neg hP, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨v, hv⟩
    have := congrArg Units.val hv
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0] at this
    exact ⟨v, by rw [← this, pow_two]⟩
  · rintro ⟨q, hq⟩
    have hq0 : q ≠ 0 := by rintro rfl; exact hP (by simpa using hq)
    exact ⟨Units.mk0 q hq0, Units.ext (by simp [hq, pow_two])⟩

/-- Three nonzero rationals whose product is a square: the class of the third is the product of the first two. -/
theorem descentMap_add_of_isSquare (r c : ℚ) (P Q : (cubicCurve α β γ).toAffine.Point)
    (hP : descentRep r c P ≠ 0) (hQ : descentRep r c Q ≠ 0) (hPQ : descentRep r c (P + Q) ≠ 0)
    (hsq : IsSquare (descentRep r c P * descentRep r c Q * descentRep r c (P + Q))) :
    descentMap r c (P + Q) = descentMap r c P * descentMap r c Q := by
  unfold descentMap
  rw [dif_neg hP, dif_neg hQ, dif_neg hPQ, ← QuotientGroup.mk_mul]
  obtain ⟨q, hq⟩ := hsq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (mul_ne_zero hP hQ) hPQ (by simpa using hq)
  apply QuotientGroup.eq.2
  refine ⟨Units.mk0 (q / descentRep r c (P + Q)) (div_ne_zero hq0 hPQ), ?_⟩
  apply Units.ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp
  linear_combination -hq

/-- $\varphi_r$ is a homomorphism (Remark 3.7). -/
theorem descentMap_add (hr : IsRootTriple α β γ r s t) (hc : (r - s) * (r - t) ≠ 0)
    (P Q : (cubicCurve α β γ).toAffine.Point) :
    descentMap r ((r - s) * (r - t)) (P + Q) =
      descentMap r ((r - s) * (r - t)) P * descentMap r ((r - s) * (r - t)) Q :=
  descentMap_add_of_isSquare r _ P Q (descentRep_ne_zero _ _ hc P) (descentRep_ne_zero _ _ hc Q)
    (descentRep_ne_zero _ _ hc (P + Q)) (isSquare_mul_descentRep_add hr hc P Q)

/-! ### Halving: the kernel is $2E(\mathbb Q)$ -/

/-- **Halving** (the tangent-line criterion; compare Tau Ceti's `WeierstrassCurve.exists_eq_two_smul_iff`): if
$x_0 - \alpha = u^2$, $x_0 - \beta = v^2$, $x_0 - \gamma = w^2$, then $(x_0, y_0) \in 2E(\mathbb Q)$.  The point
$Q = (\xi, l\xi + m)$ with $\xi = x_0 + uv + vw + wu$, $l = u + v + w$, $m = -x_0 l - uvw$ satisfies $2Q = \pm(x_0, y_0)$. -/
theorem exists_two_zsmul_eq_of_sq (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) {x₀ y₀ : ℚ}
    (h : (cubicCurve α β γ).toAffine.Nonsingular x₀ y₀) {u v w : ℚ}
    (hu : x₀ - α = u ^ 2) (hv : x₀ - β = v ^ 2) (hw : x₀ - γ = w ^ 2) :
    ∃ Q : (cubicCurve α β γ).toAffine.Point, (2 : ℤ) • Q = Point.some x₀ y₀ h := by
  have := cubicCurve_isElliptic_of_ne hαβ hβγ hγα
  have hα : (α : ℚ) = x₀ - u ^ 2 := by linarith
  have hβ : (β : ℚ) = x₀ - v ^ 2 := by linarith
  have hγ : (γ : ℚ) = x₀ - w ^ 2 := by linarith
  have hαβ' : (α : ℚ) ≠ β := by exact_mod_cast hαβ
  have hβγ' : (β : ℚ) ≠ γ := by exact_mod_cast hβγ
  have hγα' : (γ : ℚ) ≠ α := by exact_mod_cast hγα
  set ξ := x₀ + u * v + v * w + w * u with hξ
  set η := (u + v + w) * ξ + (-x₀ * (u + v + w) - u * v * w) with hη
  have hηf : η = (u + v) * (v + w) * (w + u) := by rw [hη, hξ]; ring
  have heq : (cubicCurve α β γ).toAffine.Equation ξ η := by
    rw [cubicCurve_equation_iff, hα, hβ, hγ, hηf, hξ]
    ring
  have hη0 : η ≠ 0 := by
    rw [hηf]
    intro h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact hαβ' (by rw [hα, hβ, show u = -v by linarith]; ring)
      · exact hβγ' (by rw [hβ, hγ, show v = -w by linarith]; ring)
    · exact hγα' (by rw [hγ, hα, show w = -u by linarith]; ring)
  have hy : η ≠ (cubicCurve α β γ).toAffine.negY ξ η := by
    rw [cubicCurve_negY]
    intro h'
    exact hη0 (by linarith)
  have hsl : (cubicCurve α β γ).toAffine.slope ξ ξ η η = u + v + w := by
    rw [Affine.slope_of_Y_ne rfl hy, cubicCurve_negY]
    simp only [cubicCurve]
    rw [div_eq_iff (by intro h'; exact hη0 (by linarith))]
    rw [hα, hβ, hγ, hη, hξ]
    ring
  have hns := (Affine.equation_iff_nonsingular).1 heq
  have hx : (cubicCurve α β γ).toAffine.addX ξ ξ ((cubicCurve α β γ).toAffine.slope ξ ξ η η) = x₀ := by
    rw [hsl]
    simp only [Affine.addX, cubicCurve]
    rw [hα, hβ, hγ, hξ]
    ring
  have h2 : (2 : ℤ) • (Point.some ξ η hns : (cubicCurve α β γ).toAffine.Point) =
      Point.some _ _ (Affine.nonsingular_add hns hns fun hxy => hy hxy.2) := by
    rw [two_zsmul, Point.add_self_of_Y_ne hy]
  rcases (Point.X_eq_iff (h₁ := Affine.nonsingular_add hns hns fun hxy => hy hxy.2) (h₂ := h)).1 hx with
    h3 | h3
  · exact ⟨_, h2.trans h3⟩
  · refine ⟨-Point.some ξ η hns, ?_⟩
    rw [zsmul_neg, h2, h3, neg_neg]

/-- $\varphi_r$ kills $2E(\mathbb Q)$. -/
theorem descentMap_two_zsmul (hr : IsRootTriple α β γ r s t) (hc : (r - s) * (r - t) ≠ 0)
    (Q : (cubicCurve α β γ).toAffine.Point) : descentMap r ((r - s) * (r - t)) ((2 : ℤ) • Q) = 1 := by
  rw [two_zsmul, descentMap_add hr hc, ratModSquares_mul_self]

/-- **The kernel of $(\varphi_\alpha, \varphi_\beta)$ is contained in $2E(\mathbb Q)$**: if $\varphi_\alpha(P)$ and
$\varphi_\beta(P)$ are trivial, then $x - \alpha$, $x - \beta$, $x - \gamma$ are squares and `exists_two_zsmul_eq_of_sq`
halves $P$. -/
theorem mem_multiples_of_phi_eq_one (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α)
    (P : (cubicCurve α β γ).toAffine.Point) (hA : phiAlpha α β γ P = 1) (hB : phiBeta α β γ P = 1) :
    P ∈ multiples (cubicCurve α β γ).toAffine.Point 2 := by
  have hαβ' : (α : ℚ) ≠ β := by exact_mod_cast hαβ
  have hβγ' : (β : ℚ) ≠ γ := by exact_mod_cast hβγ
  have hγα' : (γ : ℚ) ≠ α := by exact_mod_cast hγα
  have hcA : ((α : ℚ) - β) * (α - γ) ≠ 0 := mul_ne_zero (sub_ne_zero.2 hαβ') (sub_ne_zero.2 hγα'.symm)
  have hcB : ((β : ℚ) - α) * (β - γ) ≠ 0 := mul_ne_zero (sub_ne_zero.2 hαβ'.symm) (sub_ne_zero.2 hβγ')
  have sA := (descentMap_eq_one_iff _ _ P (descentRep_ne_zero _ _ hcA P)).1 hA
  have sB := (descentMap_eq_one_iff _ _ P (descentRep_ne_zero _ _ hcB P)).1 hB
  cases P with
  | zero => exact zero_mem _
  | some x y h =>
    rw [descentRep_some] at sA sB
    suffices ∃ u v w : ℚ, x - α = u ^ 2 ∧ x - β = v ^ 2 ∧ x - γ = w ^ 2 by
      obtain ⟨u, v, w, hu, hv, hw⟩ := this
      obtain ⟨Q, hQ⟩ := exists_two_zsmul_eq_of_sq hαβ hβγ hγα h hu hv hw
      exact ⟨Q, hQ⟩
    have hy2 := cubicCurve_equation_iff.1 h.1
    by_cases hxa : x = α
    · subst x
      rw [if_pos rfl] at sA
      rw [if_neg hαβ'] at sB
      obtain ⟨a, ha⟩ := sA
      obtain ⟨b, hb⟩ := sB
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact hαβ' (by linarith)
      refine ⟨0, b, a / b, by ring, by rw [hb]; ring, ?_⟩
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hb0), pow_two b, ← hb]
      linear_combination ha
    by_cases hxb : x = β
    · subst x
      rw [if_neg hαβ'.symm] at sA
      rw [if_pos rfl] at sB
      obtain ⟨a, ha⟩ := sA
      obtain ⟨b, hb⟩ := sB
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hαβ' (by linarith)
      refine ⟨a, 0, b / a, by rw [ha]; ring, by ring, ?_⟩
      rw [div_pow, eq_div_iff (pow_ne_zero 2 ha0), pow_two a, ← ha]
      linear_combination hb
    rw [if_neg hxa] at sA
    rw [if_neg hxb] at sB
    obtain ⟨a, ha⟩ := sA
    obtain ⟨b, hb⟩ := sB
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hxa (by linarith)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hxb (by linarith)
    refine ⟨a, b, y / (a * b), by rw [ha]; ring, by rw [hb]; ring, ?_⟩
    rw [div_pow, eq_div_iff (pow_ne_zero 2 (mul_ne_zero ha0 hb0)), hy2, ha, hb]
    ring

/-! ### Valuations -/

/-- The $p$-adic valuation of a difference of integers not divisible by $p$ is $0$. -/
theorem padicValRat_intCast_sub_eq_zero (p : ℕ) {a b : ℤ} (h : ¬ (p : ℤ) ∣ a - b) :
    padicValRat p ((a : ℚ) - b) = 0 := by
  rw [← Int.cast_sub, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h, Nat.cast_zero]

theorem not_dvd_sub_comm {p a b : ℤ} (h : ¬ p ∣ a - b) : ¬ p ∣ b - a := by
  intro h'
  apply h
  rw [← neg_sub]
  exact dvd_neg.2 h'

/-- A prime not dividing $\Delta$ divides none of the differences of the roots. -/
theorem not_dvd_sub_of_not_dvd_cubicDisc {p : ℤ} (h : ¬ p ∣ cubicDisc α β γ) :
    ¬ p ∣ α - β ∧ ¬ p ∣ β - γ ∧ ¬ p ∣ γ - α := by
  unfold cubicDisc at h
  refine ⟨fun h' => h ?_, fun h' => h ?_, fun h' => h ?_⟩
  · exact Dvd.dvd.pow (Dvd.dvd.mul_right (Dvd.dvd.mul_right h' _) _) two_ne_zero
  · exact Dvd.dvd.pow (Dvd.dvd.mul_right (Dvd.dvd.mul_left h' _) _) two_ne_zero
  · exact Dvd.dvd.pow (Dvd.dvd.mul_left h' _) two_ne_zero

/-- **The valuation argument**: if $y^2 = (x - r)(x - s)(x - t)$ with $y \ne 0$ and $v_p(r - s) = v_p(r - t) = 0$,
then $v_p(x - r)$ and $v_p(x - s) + v_p(x - t)$ are even.  (If $v_p(x - r) < 0$ the three valuations agree; if
$v_p(x - r) > 0$ the other two vanish.) -/
theorem even_padicValRat_core (p : ℕ) [Fact p.Prime] {x y r s t : ℚ} (hy2 : y ^ 2 = (x - r) * (x - s) * (x - t))
    (hy : y ≠ 0) (hrs : r - s ≠ 0) (hrt : r - t ≠ 0) (hvs : padicValRat p (r - s) = 0)
    (hvt : padicValRat p (r - t) = 0) :
    Even (padicValRat p (x - r)) ∧ Even (padicValRat p (x - s) + padicValRat p (x - t)) := by
  have hprod : (x - r) * (x - s) * (x - t) ≠ 0 := by rw [← hy2]; exact pow_ne_zero 2 hy
  have h1 : x - r ≠ 0 := fun h => hprod (by rw [h]; ring)
  have h2 : x - s ≠ 0 := fun h => hprod (by rw [h]; ring)
  have h3 : x - t ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hsum : padicValRat p (x - r) + padicValRat p (x - s) + padicValRat p (x - t) = 2 * padicValRat p y := by
    have := congrArg (padicValRat p) hy2
    rw [padicValRat.pow, padicValRat.mul (mul_ne_zero h1 h2) h3, padicValRat.mul h1 h2] at this
    push_cast at this
    linarith
  have es : x - s = (x - r) + (r - s) := by ring
  have et : x - t = (x - r) + (r - t) := by ring
  rw [Int.even_iff, Int.even_iff]
  rcases lt_trichotomy (padicValRat p (x - r)) 0 with ha | ha | ha
  · have hs : padicValRat p (x - s) = padicValRat p (x - r) := by
      rw [es]
      exact padicValRat.add_eq_of_lt (by rw [← es]; exact h2) h1 hrs (by rw [hvs]; exact ha)
    have ht : padicValRat p (x - t) = padicValRat p (x - r) := by
      rw [et]
      exact padicValRat.add_eq_of_lt (by rw [← et]; exact h3) h1 hrt (by rw [hvt]; exact ha)
    omega
  · omega
  · have hs : padicValRat p (x - s) = 0 := by
      rw [es, add_comm, ← hvs]
      exact padicValRat.add_eq_of_lt (by rw [add_comm, ← es]; exact h2) hrs h1 (by rw [hvs]; exact ha)
    have ht : padicValRat p (x - t) = 0 := by
      rw [et, add_comm, ← hvt]
      exact padicValRat.add_eq_of_lt (by rw [add_comm, ← et]; exact h3) hrt h1 (by rw [hvt]; exact ha)
    omega

/-- The representative of $\varphi_r$ has even valuation at a prime not dividing $(r - s)(r - t)$. -/
theorem even_padicValRat_descentRep (hr : IsRootTriple α β γ r s t) (p : ℕ) [Fact p.Prime]
    (hrs : r - s ≠ 0) (hrt : r - t ≠ 0) (hvs : padicValRat p (r - s) = 0) (hvt : padicValRat p (r - t) = 0)
    (P : (cubicCurve α β γ).toAffine.Point) : Even (padicValRat p (descentRep r ((r - s) * (r - t)) P)) := by
  cases P with
  | zero => rw [← Point.zero_def, descentRep_zero, padicValRat.one]; exact ⟨0, rfl⟩
  | some x y h =>
    rw [descentRep_some]
    split_ifs with hx
    · rw [padicValRat.mul hrs hrt, hvs, hvt]
      exact ⟨0, rfl⟩
    · by_cases hy : y = 0
      · subst hy
        rcases hr.root_of_y_eq_zero h.1 with h' | h' | h'
        · exact absurd h' hx
        · rw [h', show s - r = -(r - s) by ring, padicValRat.neg, hvs]
          exact ⟨0, rfl⟩
        · rw [h', show t - r = -(r - t) by ring, padicValRat.neg, hvt]
          exact ⟨0, rfl⟩
      · exact (even_padicValRat_core p (hr.equation_iff.1 h.1) hy hrs hrt hvs hvt).1

/-- The representatives of $\varphi_\alpha$ and $\varphi_\beta$ have even valuation at a prime dividing none of the
differences of the roots. -/
theorem even_padicValRat_phi (p : ℕ) [Fact p.Prime] (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α)
    (h : ¬ (p : ℤ) ∣ cubicDisc α β γ) (P : (cubicCurve α β γ).toAffine.Point) :
    Even (padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) P)) ∧
      Even (padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) P)) := by
  obtain ⟨h1, h2, h3⟩ := not_dvd_sub_of_not_dvd_cubicDisc h
  have hαβ' : (α : ℚ) ≠ β := by exact_mod_cast hαβ
  have hβγ' : (β : ℚ) ≠ γ := by exact_mod_cast hβγ
  have hγα' : (γ : ℚ) ≠ α := by exact_mod_cast hγα
  exact ⟨even_padicValRat_descentRep isRootTriple_alpha p (sub_ne_zero.2 hαβ') (sub_ne_zero.2 hγα'.symm)
      (padicValRat_intCast_sub_eq_zero p h1) (padicValRat_intCast_sub_eq_zero p (not_dvd_sub_comm h3)) P,
    even_padicValRat_descentRep isRootTriple_beta p (sub_ne_zero.2 hαβ'.symm) (sub_ne_zero.2 hβγ')
      (padicValRat_intCast_sub_eq_zero p (not_dvd_sub_comm h1)) (padicValRat_intCast_sub_eq_zero p h2) P⟩

/-- **Remark 3.7** (pdf p. 121), proved: the named statement `Remark3_7` holds.  For distinct integers
$\alpha, \beta, \gamma$, $\varphi_\alpha$ and $\varphi_\beta$ are homomorphisms, the kernel of
$(\varphi_\alpha, \varphi_\beta)$ is $2E(\mathbb Q)$, and the representatives have even valuation outside $2\Delta$. -/
@[kb "milne2006ec" "Ch. IV, Remark 3.7, pdf p. 121"]
theorem remark_3_7 : Remark3_7 where
  hom_alpha α β γ hαβ _ hγα P Q :=
    descentMap_add isRootTriple_alpha
      (mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hαβ)) (sub_ne_zero.2 (by exact_mod_cast hγα.symm))) P Q
  hom_beta α β γ hαβ hβγ _ P Q :=
    descentMap_add isRootTriple_beta
      (mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hαβ.symm)) (sub_ne_zero.2 (by exact_mod_cast hβγ))) P Q
  ker α β γ hαβ hβγ hγα P := by
    refine ⟨fun h => mem_multiples_of_phi_eq_one hαβ hβγ hγα P h.1 h.2, ?_⟩
    rintro ⟨Q, rfl⟩
    exact ⟨descentMap_two_zsmul isRootTriple_alpha
        (mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hαβ)) (sub_ne_zero.2 (by exact_mod_cast hγα.symm))) Q,
      descentMap_two_zsmul isRootTriple_beta
        (mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hαβ.symm)) (sub_ne_zero.2 (by exact_mod_cast hβγ))) Q⟩
  support α β γ hαβ hβγ hγα P p hp h2Δ := by
    have := Fact.mk hp
    exact even_padicValRat_phi p hαβ hβγ hγα (fun h => h2Δ (Dvd.dvd.mul_left h 2)) P

/-! ### The local statements of Proposition 5.6 -/

/-- Nodal case (b) with $\alpha \equiv \beta$: if $v_p(\gamma - \alpha) = v_p(\gamma - \beta) = 0$, the valuations of
the two representatives have even sum. -/
theorem even_add_padicValRat_phi (p : ℕ) [Fact p.Prime] (hαβ : (α : ℚ) ≠ β) (hβγ : (β : ℚ) ≠ γ)
    (hγα : (γ : ℚ) ≠ α) (hvαγ : padicValRat p ((γ : ℚ) - α) = 0) (hvβγ : padicValRat p ((γ : ℚ) - β) = 0)
    (P : (cubicCurve α β γ).toAffine.Point) :
    Even (padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) P) +
      padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) P)) := by
  have hvαγ' : padicValRat p ((α : ℚ) - γ) = 0 := by
    rw [show (α : ℚ) - γ = -(γ - α) by ring, padicValRat.neg, hvαγ]
  have hvβγ' : padicValRat p ((β : ℚ) - γ) = 0 := by
    rw [show (β : ℚ) - γ = -(γ - β) by ring, padicValRat.neg, hvβγ]
  cases P with
  | zero => rw [← Point.zero_def]; simp only [descentRep_zero, padicValRat.one]; exact ⟨0, rfl⟩
  | some x y h =>
    rw [descentRep_some, descentRep_some]
    by_cases hxa : x = α
    · subst x
      rw [if_pos rfl, if_neg hαβ, padicValRat.mul (sub_ne_zero.2 hαβ) (sub_ne_zero.2 hγα.symm), hvαγ']
      exact ⟨padicValRat p ((α : ℚ) - β), by ring⟩
    by_cases hxb : x = β
    · subst x
      rw [if_neg hαβ.symm, if_pos rfl, padicValRat.mul (sub_ne_zero.2 hαβ.symm) (sub_ne_zero.2 hβγ), hvβγ']
      exact ⟨padicValRat p ((β : ℚ) - α), by ring⟩
    rw [if_neg hxa, if_neg hxb]
    by_cases hy : y = 0
    · subst hy
      rcases isRootTriple_alpha.root_of_y_eq_zero h.1 with h' | h' | h'
      · exact absurd h' hxa
      · exact absurd h' hxb
      · rw [h', hvαγ, hvβγ]
        exact ⟨0, rfl⟩
    · exact (even_padicValRat_core p (isRootTriple_gamma.equation_iff.1 h.1) hy (sub_ne_zero.2 hγα)
        (sub_ne_zero.2 hβγ.symm) hvαγ hvβγ).2

/-- Sign (c) of the proof of Proposition 5.6: for $\alpha < \beta < \gamma$ the representative of $\varphi_\alpha$ is
positive (a point has $x \ge \alpha$, since the cubic is negative for $x < \alpha$). -/
theorem descentRep_alpha_pos (hαβ : α < β) (hβγ : β < γ) (P : (cubicCurve α β γ).toAffine.Point) :
    0 < descentRep (α : ℚ) ((α - β) * (α - γ)) P := by
  have h1 : (α : ℚ) < β := by exact_mod_cast hαβ
  have h2 : (β : ℚ) < γ := by exact_mod_cast hβγ
  cases P with
  | zero => rw [← Point.zero_def, descentRep_zero]; exact one_pos
  | some x y h =>
    rw [descentRep_some]
    split_ifs with hx
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · by_contra hneg
      have hlt : x < α := lt_of_le_of_ne (by linarith) hx
      have hy2 := cubicCurve_equation_iff.1 h.1
      have h3 : 0 < (x - α) * (x - β) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have h4 : (x - α) * (x - β) * (x - γ) < 0 := mul_neg_of_pos_of_neg h3 (by linarith)
      nlinarith [sq_nonneg y]

/-- The local statements (a)–(c) of the proof of **Proposition 5.6** (pdf pp. 137–138), proved: the named
statement `Prop5_6Local` holds. -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.6, statements (a), (b), (c) of the proof, pdf pp. 137-138"]
theorem prop_5_6_local : Prop5_6Local where
  away α β γ hαβ hβγ P p hp hΔ := by
    have := Fact.mk hp
    exact even_padicValRat_phi p hαβ.ne hβγ.ne (lt_trans hαβ hβγ).ne' hΔ P
  nodal α β γ hαβ hβγ P p hmem := by
    have hαβ' : (α : ℚ) ≠ β := by exact_mod_cast hαβ.ne
    have hβγ' : (β : ℚ) ≠ γ := by exact_mod_cast hβγ.ne
    have hγα' : (γ : ℚ) ≠ α := by exact_mod_cast (lt_trans hαβ hβγ).ne'
    obtain ⟨hpS, hnot⟩ := Finset.mem_filter.1 hmem
    have := Fact.mk (Nat.prime_of_mem_primeFactors hpS)
    intro a b
    refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
    · have n2 : ¬ (p : ℤ) ∣ β - γ := fun h' => hnot ⟨h1, h'⟩
      have n3 : ¬ (p : ℤ) ∣ γ - α := fun h' => n2 (by
        rw [show β - γ = -(α - β) - (γ - α) by ring]; exact dvd_sub (dvd_neg.2 h1) h')
      exact even_add_padicValRat_phi p hαβ' hβγ' hγα' (padicValRat_intCast_sub_eq_zero p n3)
        (padicValRat_intCast_sub_eq_zero p (not_dvd_sub_comm n2)) P
    · have n1 : ¬ (p : ℤ) ∣ α - β := fun h' => hnot ⟨h', by
        rw [show β - γ = -(α - β) - (γ - α) by ring]; exact dvd_sub (dvd_neg.2 h') h2⟩
      have n2 : ¬ (p : ℤ) ∣ β - γ := fun h' => hnot ⟨by
        rw [show α - β = -(β - γ) - (γ - α) by ring]; exact dvd_sub (dvd_neg.2 h') h2, h'⟩
      exact even_padicValRat_descentRep isRootTriple_beta p (sub_ne_zero.2 hαβ'.symm) (sub_ne_zero.2 hβγ')
        (padicValRat_intCast_sub_eq_zero p (not_dvd_sub_comm n1)) (padicValRat_intCast_sub_eq_zero p n2) P
    · have n1 : ¬ (p : ℤ) ∣ α - β := fun h' => hnot ⟨h', h3⟩
      have n3 : ¬ (p : ℤ) ∣ γ - α := fun h' => n1 (by
        rw [show α - β = -(β - γ) - (γ - α) by ring]; exact dvd_sub (dvd_neg.2 h3) h')
      exact even_padicValRat_descentRep isRootTriple_alpha p (sub_ne_zero.2 hαβ') (sub_ne_zero.2 hγα'.symm)
        (padicValRat_intCast_sub_eq_zero p n1) (padicValRat_intCast_sub_eq_zero p (not_dvd_sub_comm n3)) P
  sign α β γ hαβ hβγ P := descentRep_alpha_pos hαβ hβγ P

/-! ### Unconditional forms of Propositions 5.5, 5.6 and Example 5.7 -/

/-- **The finite basis theorem for $Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$** (distinct integer roots), by
Milne's explicit descent: Remark 3.7 makes $E(\mathbb Q)/2E(\mathbb Q)$ finite (`finite_quot_two_cubic`), and the
descent theorem with the canonical height (`fg_of_finite_quotient_two`, Chapter IV §4) gives finite generation.
No Selmer group is needed. -/
@[kb "milne2006ec" "Ch. IV, Remark 3.7 with the descent argument of the introduction, pdf pp. 110, 121"]
theorem fg_cubicCurve (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) :
    AddGroup.FG (cubicCurve α β γ).toAffine.Point := by
  have := cubicCurve_isElliptic_of_ne hαβ hβγ hγα
  exact fg_of_finite_quotient_two (cubicCurve α β γ).toAffine (finite_quot_two_cubic remark_3_7 hαβ hβγ hγα)

/-- **Proposition 5.5** (pdf p. 137), unconditional: for distinct integers $\alpha, \beta, \gamma$ the rank of
$E(\mathbb Q)$, $E : Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$, is at most $2\cdot\#\{p \mid 2\Delta\}$. -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.5, pdf p. 137"]
theorem prop_5_5_rank_unconditional (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) :
    rank (cubicCurve α β γ) ≤ 2 * (2 * cubicDisc α β γ).natAbs.primeFactors.card := by
  have := fg_cubicCurve hαβ hβγ hγα
  exact prop_5_5_rank_of_fg remark_3_7 hαβ hβγ hγα

/-- **Proposition 5.6** (pdf p. 137), unconditional: for integers $\alpha < \beta < \gamma$ the rank $r$ of
$E(\mathbb Q)$ satisfies $r \le t_1 + 2t_2 - 1$ ($t_1$, $t_2$ the numbers of primes of nodal and cuspidal reduction),
stated as $r + 1 \le t_1 + 2t_2$. -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.6, pdf p. 137"]
theorem prop_5_6_unconditional (hαβ : α < β) (hβγ : β < γ) :
    rank (cubicCurve α β γ) + 1 ≤ (nodalPrimes α β γ).card + 2 * (cuspidalPrimes α β γ).card := by
  have := fg_cubicCurve hαβ.ne hβγ.ne (lt_trans hαβ hβγ).ne'
  exact prop_5_6_of_fg remark_3_7 prop_5_6_local hαβ hβγ

/-- **Example 5.7** (pdf p. 138), the rank, unconditional: $E : Y^2 = X^3 - X$ has rank $0$ and $E(\mathbb Q)$ is
finite.  (The group itself, $(\mathbb Z/2)^2$, is `example_5_7_unconditional`.) -/
@[kb "milne2006ec" "Ch. IV, Example 5.7, pdf p. 138"]
theorem example_5_7_rank_unconditional :
    rank (cubicCurve (-1) 0 1) = 0 ∧ Finite (cubicCurve (-1) 0 1).toAffine.Point := by
  have := fg_cubicCurve (α := -1) (β := 0) (γ := 1) (by norm_num) (by norm_num) (by norm_num)
  exact example_5_7_of_fg remark_3_7 prop_5_6_local

end TwoDescent

/-! ### Proposition 5.1 with Lemma 2.1 proved -/

/-- **Proposition 5.1** (pdf p. 135), corrected, with Lemma 2.1 proved (`lemma2_1`): (a) the image
of $E(K)/2E(K)$ in $S^{(2)}(E/K)$ lies in every $S^{(2,n)}(E/K)$; (b) it equals $\bigcap_n S^{(2,n)}(E/K)$ iff no
nonzero element of $Ш(E/K)$ of 2-power order is divisible in $Ш(E/K)$ by all powers of 2. -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.1, pdf p. 135"]
theorem prop_5_1_unconditional {K : Type} [Field K] [DecidableEq K] [NumberField K] (W : WeierstrassCurve K)
    [W.IsElliptic] :
    (∀ m : ℕ, (kummerMap W lemma2_1 2 two_ne_zero).range ≤ selmerImage W m) ∧
      ((⨅ m : ℕ, selmerImage W m) = (kummerMap W lemma2_1 2 two_ne_zero).range ↔
        ∀ z ∈ tateShafarevich K W, (∃ k : ℕ, (2 : ℤ) ^ k • z = 0) →
          (∀ n : ℕ, ∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ n • y = z) → z = 0) :=
  prop_5_1 W lemma2_1


end NumberFieldKB.MilneEC
