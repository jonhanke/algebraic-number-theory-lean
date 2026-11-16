import Mathlib.NumberTheory.Padics.ProperSpace
import NumberFieldKB.MilneEC.Ch2Reduction

/-!
# Milne, *Elliptic Curves*, Chapter II, Theorem 4.1 (a): $E^0(\mathbb Q_p)$ has finite index

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`,
Chapter II, Theorem 4.1 (a), pdf p. 70.

Milne's proof: $E(\mathbb Q_p)$ is compact and $E^0(\mathbb Q_p)$ is an open subgroup. Here the same argument is made
explicit in coordinates, without a topology on $E(\mathbb Q_p)$:

* every point outside $E^1(\mathbb Q_p)$ is $(x, y)$ with $x, y \in \mathbb Z_p$, and these pairs form a compact
  subset $K$ of $\mathbb Q_p^2$ (closed and bounded; `ProperSpace ℚ_[p]`);
* "$E^1(\mathbb Q_p)$ is open" becomes the slope estimate `mem_E1_neg_add`: if $P = (x_1, y_1)$ and
  $Q = (x_2, y_2)$ are integral and $|x_2 - x_1|, |y_2 - y_1| < c(P) = \max(|2y_1|, |3x_1^2 + a|)$, then
  $-P + Q \in E^1(\mathbb Q_p)$, since the chord through $-P$ and $Q$ has slope of norm $> 1$. Here $c(P) > 0$
  because the curve is nonsingular (`c_pos`);
* finitely many such balls cover $K$, so finitely many cosets of $E^1(\mathbb Q_p)$, hence of
  $E^0(\mathbb Q_p) \supseteq E^1(\mathbb Q_p)$, cover $E(\mathbb Q_p)$.

The proof gives the stronger statement that $E^1(\mathbb Q_p)$ has finite index (`finite_cosets_E1`), and works for
every prime $p$, including $p = 2$ and $p = 3$, for the short models $Y^2 = X^3 + aX + b$ with $a, b \in \mathbb Z_p$
of the named statement `Theorem4_1a`.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve Metric

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

/-- Ultrametric inequality in the form used below: if $u = v + w$ then $|u| \le \max(|v|, |w|)$. -/
private lemma norm_le_max_of_eq {u v w : ℚ_[p]} (h : u = v + w) : ‖u‖ ≤ max ‖v‖ ‖w‖ :=
  h ▸ Padic.nonarchimedean v w

/-- If $|\ell| > 1$ and $|x_1|, |x_2| \le 1$ then $|\ell^2 - x_1 - x_2| > 1$. -/
private lemma one_lt_norm_addX {ℓ x₁ x₂ : ℚ_[p]} (hℓ : 1 < ‖ℓ‖) (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1) :
    1 < ‖ℓ ^ 2 - x₁ - x₂‖ := by
  have hs : ‖x₁ + x₂‖ ≤ 1 := (Padic.nonarchimedean _ _).trans (max_le hx₁ hx₂)
  have hℓ2 : 1 < ‖ℓ ^ 2‖ := by rw [norm_pow]; exact one_lt_pow₀ hℓ two_ne_zero
  have := norm_le_max_of_eq (show ℓ ^ 2 = (ℓ ^ 2 - x₁ - x₂) + (x₁ + x₂) by ring)
  rcases le_max_iff.1 this with h | h
  · exact hℓ2.trans_le h
  · exact absurd (h.trans hs) (not_le.2 hℓ2)

/-- The radius $c(P) = \max(|2y|, |3x^2 + a|)$ of the ball around an integral point $P = (x, y)$. -/
noncomputable def radius (a x y : ℚ_[p]) : ℝ := max ‖2 * y‖ ‖3 * x ^ 2 + a‖

/-- $c(P) > 0$ on a nonsingular curve: $2y = 0$ and $3x^2 + a = 0$ would make $x$ a double root of
$X^3 + aX + b$, so $4a^3 + 27b^2 = 0$. -/
lemma c_pos {a b x y : ℚ_[p]} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (e : y ^ 2 = x ^ 3 + a * x + b) :
    0 < radius a x y := by
  unfold radius
  by_contra h
  push Not at h
  have h1 : 2 * y = 0 := norm_eq_zero.1 (le_antisymm ((le_max_left _ _).trans h) (norm_nonneg _))
  have h2 : 3 * x ^ 2 + a = 0 :=
    norm_eq_zero.1 (le_antisymm ((le_max_right _ _).trans h) (norm_nonneg _))
  have hy : y = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h two_ne_zero
    · exact h
  subst hy
  have ha : a = -3 * x ^ 2 := by linear_combination h2
  subst ha
  have hb : b = 2 * x ^ 3 := by linear_combination -e
  subst hb
  exact hΔ (by ring)

/-- The slope estimate: on the chord through $-P = (x_1, -y_1)$ and $Q = (x_2, y_2)$ (integral points, $Q \ne P$)
the slope has norm $> 1$ when $|x_2 - x_1|, |y_2 - y_1| < c(P)$. -/
lemma one_lt_norm_slope_neg_add {a b x₁ y₁ x₂ y₂ : ℚ_[p]} (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (e₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (e₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b)
    (hne : ¬(x₁ = x₂ ∧ -y₁ = -y₂))
    (hdx : ‖x₂ - x₁‖ < radius a x₁ y₁) (hdy : ‖y₂ - y₁‖ < radius a x₁ y₁) :
    1 < ‖(shortCurve a b).toAffine.slope x₁ x₂ (-y₁) y₂‖ := by
  -- the key relations: `ℓ (x₁ - x₂) = -(y₁ + y₂)` and `ℓ (y₂ - y₁) = g` with `g ≈ 3x₁² + a`
  set c := radius a x₁ y₁ with hc
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₂ = -y₁ := by
      have : (y₂ - y₁) * (y₂ + y₁) = 0 := by linear_combination e₂ - e₁
      rcases mul_eq_zero.1 this with h | h
      · exact absurd ⟨rfl, by linear_combination h⟩ hne
      · linear_combination h
    subst hy
    have hy0 : -y₁ ≠ (shortCurve a b).toAffine.negY x₁ (-y₁) := by
      simp only [Affine.negY, shortCurve_a₁, shortCurve_a₃, zero_mul, sub_zero, neg_neg]
      intro h
      exact hne ⟨rfl, by simpa using h⟩
    rw [Affine.slope_of_Y_ne rfl hy0]
    simp only [Affine.negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, zero_mul, mul_zero,
      sub_zero, add_zero, neg_neg]
    have h2 : ‖2 * y₁‖ < c := by
      have : -y₁ - y₁ = -(2 * y₁) := by ring
      rw [this, norm_neg] at hdy; exact hdy
    have hc' : c = ‖3 * x₁ ^ 2 + a‖ := by
      by_cases hh : ‖2 * y₁‖ ≤ ‖3 * x₁ ^ 2 + a‖
      · rw [hc, radius, max_eq_right hh]
      · push Not at hh
        have : c = ‖2 * y₁‖ := by rw [hc, radius, max_eq_left hh.le]
        linarith
    rw [show -y₁ - y₁ = -(2 * y₁) by ring, norm_div, norm_neg, ← hc']
    have hy1 : 0 < ‖2 * y₁‖ := by
      refine norm_pos_iff.2 (mul_ne_zero two_ne_zero fun h0 => hne ⟨rfl, ?_⟩)
      simp [h0]
    rw [one_lt_div hy1]
    exact h2
  · rw [Affine.slope_of_X_ne hx]
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    set ℓ := (-y₁ - y₂) / (x₁ - x₂) with hℓ
    have r1 : ℓ * (x₁ - x₂) = -y₁ - y₂ := by rw [hℓ]; field_simp
    have r2 : ℓ * (y₂ - y₁) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a := by
      apply mul_left_cancel₀ hd
      linear_combination (y₂ - y₁) * r1 + (e₁ - e₂)
    -- now compare with `c`
    by_contra hℓ1
    push Not at hℓ1
    rcases le_max_iff.1 (le_refl c) with h | h
    · -- `c = |2y₁| ≤ |y₁ + y₂| = |ℓ| |x₁ - x₂| ≤ |x₁ - x₂| < c`
      have h1 : ‖2 * y₁‖ ≤ ‖-y₁ - y₂‖ := by
        have := norm_le_max_of_eq (show 2 * y₁ = -(-y₁ - y₂) + (y₁ - y₂) by ring)
        rw [norm_neg] at this
        rcases le_max_iff.1 this with h' | h'
        · exact h'
        · have : ‖y₁ - y₂‖ < ‖2 * y₁‖ := by rw [norm_sub_rev]; exact hdy.trans_le h
          exact absurd h' (not_le.2 this)
      have : ‖-y₁ - y₂‖ ≤ ‖x₁ - x₂‖ := by
        rw [← r1, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hℓ1
      rw [norm_sub_rev x₁ x₂] at this
      linarith [h.trans (h1.trans this)]
    · -- `c = |3x₁² + a| ≤ |g| = |ℓ| |y₂ - y₁| ≤ |y₂ - y₁| < c`
      have h1 : ‖3 * x₁ ^ 2 + a‖ ≤ ‖x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a‖ := by
        have := norm_le_max_of_eq (show 3 * x₁ ^ 2 + a =
          (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a) + (x₁ - x₂) * (x₂ + 2 * x₁) by ring)
        rcases le_max_iff.1 this with h' | h'
        · exact h'
        · have hs : ‖x₂ + 2 * x₁‖ ≤ 1 := by
            refine (Padic.nonarchimedean _ _).trans (max_le hx₂ ?_)
            rw [norm_mul]
            have : ‖(2 : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) 2
            exact (mul_le_mul this hx₁ (norm_nonneg _) zero_le_one).trans (by norm_num)
          have : ‖(x₁ - x₂) * (x₂ + 2 * x₁)‖ < ‖3 * x₁ ^ 2 + a‖ := by
            rw [norm_mul, norm_sub_rev]
            exact (mul_le_of_le_one_right (norm_nonneg _) hs).trans_lt (hdx.trans_le h)
          exact absurd h' (not_le.2 this)
      have : ‖x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a‖ ≤ ‖y₂ - y₁‖ := by
        rw [← r2, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hℓ1
      linarith [h.trans (h1.trans this)]

/-- Integral points: if $|x| \le 1$ on the curve then $|y| \le 1$. -/
private lemma norm_y_le_one' {a b : ℤ_[p]} {x y : ℚ_[p]} (h : (curveQp a b).toAffine.Equation x y)
    (hx : ‖x‖ ≤ 1) : ‖y‖ ≤ 1 :=
  norm_y_le_one (norm_coe_le_one a) (norm_coe_le_one b) hx (shortCurve_equation h)

/-- **"$E^1(\mathbb Q_p)$ is open"**: for integral points $P = (x_1, y_1)$, $Q = (x_2, y_2)$ with
$|x_2 - x_1|, |y_2 - y_1| < c(P)$, the point $-P + Q$ lies in $E^1(\mathbb Q_p)$. -/
lemma mem_E1_neg_add {a b : ℤ_[p]} {x₁ y₁ x₂ y₂ : ℚ_[p]} (h₁ : (curveQp a b).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQp a b).toAffine.Nonsingular x₂ y₂) (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hdx : ‖x₂ - x₁‖ < radius (a : ℚ_[p]) x₁ y₁) (hdy : ‖y₂ - y₁‖ < radius (a : ℚ_[p]) x₁ y₁) :
    -Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂ ∈ E1 a b := by
  have e₁ := shortCurve_equation h₁.1
  have e₂ := shortCurve_equation h₂.1
  by_cases hne : x₁ = x₂ ∧ -y₁ = -y₂
  · obtain ⟨rfl, hy⟩ := hne
    obtain rfl : y₁ = y₂ := neg_injective hy
    rw [neg_add_cancel]
    exact (mem_E1_iff _).2 (Or.inl rfl)
  · have hn : ∀ x y : ℚ_[p], (curveQp a b).toAffine.negY x y = -y := fun x y => by
      simp [Affine.negY]
    have hxy : ¬(x₁ = x₂ ∧ (curveQp a b).toAffine.negY x₁ y₁ = (curveQp a b).toAffine.negY x₂ y₂) := by
      rw [hn, hn]; exact hne
    rw [Affine.Point.neg_some, Affine.Point.add_some hxy]
    refine (mem_E1_iff _).2 (Or.inr ⟨_, _, _, rfl, ?_⟩)
    have hℓ := one_lt_norm_slope_neg_add hx₁ hx₂ e₁ e₂ hne hdx hdy
    rw [hn]
    simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
    exact one_lt_norm_addX hℓ hx₁ hx₂

/-- The integral points of the curve, as a subset of $\mathbb Q_p^2$. -/
def intPoints (a b : ℤ_[p]) : Set (ℚ_[p] × ℚ_[p]) :=
  closedBall (0 : ℚ_[p] × ℚ_[p]) 1 ∩
    {v | v.2 ^ 2 = v.1 ^ 3 + (a : ℚ_[p]) * v.1 + (b : ℚ_[p])}

lemma isCompact_intPoints (a b : ℤ_[p]) : IsCompact (intPoints a b) :=
  (isCompact_closedBall _ _).inter_right
    (isClosed_eq (by fun_prop) (by fun_prop))

/-- **Finitely many cosets of $E^1(\mathbb Q_p)$** cover $E(\mathbb Q_p)$: there is a finite set $F$ of points
with $-f + P \in E^1(\mathbb Q_p)$ for some $f \in F$, for every $P$. -/
theorem finite_cosets_E1 (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    ∃ F : Finset (curveQp a b).toAffine.Point, ∀ P, ∃ f ∈ F, -f + P ∈ E1 a b := by
  have hΔ' : 4 * (a : ℚ_[p]) ^ 3 + 27 * (b : ℚ_[p]) ^ 2 ≠ 0 := by
    intro h
    apply hΔ
    have : ((4 * a ^ 3 + 27 * b ^ 2 : ℤ_[p]) : ℚ_[p]) = 0 := by push_cast; exact h
    exact PadicInt.coe_eq_zero.1 this
  have : (curveQp a b).IsElliptic := (isElliptic_shortCurve_iff _ _).2 hΔ'
  -- the ball around each integral point
  let U : ℚ_[p] × ℚ_[p] → Set (ℚ_[p] × ℚ_[p]) := fun v => ball v (radius (a : ℚ_[p]) v.1 v.2)
  have hU : ∀ v ∈ intPoints a b, U v ∈ nhds v := fun v hv =>
    ball_mem_nhds v (c_pos hΔ' hv.2)
  obtain ⟨t, ht, hcover⟩ := (isCompact_intPoints a b).elim_nhds_subcover U hU
  -- each center is a point of the curve
  have hpt : ∀ v ∈ t, (curveQp a b).toAffine.Nonsingular v.1 v.2 := fun v hv => by
    have e : v.2 ^ 2 = v.1 ^ 3 + (a : ℚ_[p]) * v.1 + (b : ℚ_[p]) := (ht v hv).2
    refine (Affine.equation_iff_nonsingular).1 ?_
    rw [Affine.equation_iff]
    simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, shortCurve_a₆]
    linear_combination e
  let pt : t → (curveQp a b).toAffine.Point := fun v => .some v.1.1 v.1.2 (hpt v.1 v.2)
  refine ⟨insert 0 (Finset.univ.image pt), fun P => ?_⟩
  by_cases hP : P ∈ E1 a b
  · exact ⟨0, Finset.mem_insert_self _ _, by rwa [neg_zero, zero_add]⟩
  · rcases (mem_E1_iff P).not.1 hP |> not_or.1 with ⟨hP0, hPx⟩
    cases P with
    | zero => exact absurd rfl hP0
    | some x y h =>
      have hx : ‖x‖ ≤ 1 := by
        by_contra hx
        exact hPx ⟨x, y, h, rfl, not_le.1 hx⟩
      have hy := norm_y_le_one' h.1 hx
      have hv : (x, y) ∈ intPoints a b := by
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right, Prod.norm_def]
          exact max_le hx hy
        · simpa using shortCurve_equation h.1
      obtain ⟨v, hvt, hmem⟩ := Set.mem_iUnion₂.1 (hcover hv)
      refine ⟨pt ⟨v, hvt⟩, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)), ?_⟩
      have hd : dist (x, y) v < radius (a : ℚ_[p]) v.1 v.2 := hmem
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hd
      have hv1 : ‖v.1‖ ≤ 1 := by
        have := (ht v hvt).1
        rw [mem_closedBall, dist_zero_right, Prod.norm_def] at this
        exact (le_max_left _ _).trans this
      exact mem_E1_neg_add _ h hv1 hx hd.1 hd.2

/-- $E^1(\mathbb Q_p) \subseteq E^0(\mathbb Q_p)$: the point $(0 : 1 : 0)$ is nonsingular on $\bar E$. -/
lemma E1_subset_E0 (a b : ℤ_[p]) : E1 a b ⊆ E0 a b := fun P hP =>
  (mem_E0_iff_exists P).2 ⟨0, by rw [show reducePoint P = ![0, 1, 0] from hP]; rfl⟩

/-- **Theorem 4.1 (a)** (pdf p. 70), proved for the short models $Y^2 = X^3 + aX + b$, $a, b \in \mathbb Z_p$, at
every prime $p$: $E^0(\mathbb Q_p)$ is a subgroup of finite index in $E(\mathbb Q_p)$. -/
@[kb "milne2006ec" "Ch. II, Theorem 4.1 (a), pdf p. 70"]
theorem theorem_4_1_a : Theorem4_1a := by
  refine ⟨fun p _ a b hΔ => ?_⟩
  obtain ⟨G, hG, -⟩ := theorem_4_1_b.iso p a b hΔ
  refine ⟨G, hG, ?_⟩
  obtain ⟨F, hF⟩ := finite_cosets_E1 a b hΔ
  have hsurj : Function.Surjective
      (fun f : F => (QuotientAddGroup.mk f.1 : (curveQp a b).toAffine.Point ⧸ G)) := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H P =>
      obtain ⟨f, hf, hfP⟩ := hF P
      refine ⟨⟨f, hf⟩, ?_⟩
      apply QuotientAddGroup.eq.2
      rw [← SetLike.mem_coe, hG]
      exact E1_subset_E0 a b hfP
  have : Finite ((curveQp a b).toAffine.Point ⧸ G) := Finite.of_surjective _ hsurj
  exact AddSubgroup.finiteIndex_of_finite_quotient

end NumberFieldKB.MilneEC.II
