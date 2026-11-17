import NumberFieldKB.MilneEC.Ch4IsogenyDescent

/-!
# Proposition 8.1: point algebra on $E : y^2 = x^3 + px$ over an extension field

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 8.1 (pdf p. 151),
following Silverman (1986), X.4.9 and X.6.2.  Explicit formulas on `curveP p` over a field `L` containing
$\mathbb Q$ (in practice $\bar{\mathbb Q}$ or $\bar{\mathbb Q}_v$), used to compare the Galois-cohomological
$2$-Selmer group with the quartic torsors of `Ch4SelmerExplicit`.

* The $2$-torsion: $E[2] = \{0, T, T_+, T_-\}$ with $T = (0, 0)$ and $T_\pm = (\pm r, 0)$, $r^2 = -p$
  (`two_torsion_cases`).
* `psi`: the map $E[2] \to \mathbb Z/2$ with kernel $\{0, T\}$ (it is the restriction of the $2$-isogeny
  $\varphi$ to $E[2]$); additive on $E[2]$ (`psi_add`) and invariant under base change (`psi_map`).
* Translation by $T$ and by $T_\pm$ (`add_T`, `add_root`).
* The halving function $t(x, y) = (x^2 - p)/2y$: $t(Q)^2 = x(2Q)$ and $t(Q + e) = \pm t(Q)$ according to
  `psi e` (`halving_t`); the case $2Q = T$ (`halving_T`).
* The function $s(x, y) = y/x$ with $s(Q + T) = -s(Q)$, and $Y = y(p - x^2)/x^2$ with $Y(Q + T) = Y(Q)$;
  $(s^2, Y)$ lies on $E' : Y^2 = X^3 - 4pX$ (`sfun_add_T`).
* `lift_point`: from a point $(X, Y)$ of $E'$ and $s^2 = X$, a point $P$ of $E$ whose $s$-function is $s$ and
  with $P_{-s} = P_s + T$.
-/

open WeierstrassCurve WeierstrassCurve.Affine

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NumberFieldKB.MilneEC.Prop81

/-- The curve $E : y^2 = x^3 + px$ over a field `L` containing $\mathbb Q$. -/
abbrev EC (p : ℕ) (L : Type*) [Field L] [Algebra ℚ L] : Affine L := (curveP p).toAffine⁄L

variable {p : ℕ} [hp : Fact p.Prime]

section Field

variable {L : Type*} [Field L] [CharZero L] [Algebra ℚ L] [DecidableEq L]

omit [Algebra ℚ L] [DecidableEq L] in


theorem p_ne_zero : (p : L) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

theorem equation_iff {x y : L} : (EC p L).Equation x y ↔ y ^ 2 = x ^ 3 + (p : L) * x := by
  rw [Affine.equation_iff]
  simp only [curveP, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero,
    map_natCast]
  constructor <;> intro h <;> linear_combination h

theorem negY_eq (x y : L) : (EC p L).negY x y = -y := by
  simp only [Affine.negY, curveP, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    map_zero]
  ring

theorem nonsingular {x y : L} (h : y ^ 2 = x ^ 3 + (p : L) * x) : (EC p L).Nonsingular x y := by
  have := curveP_isElliptic hp.out.ne_zero
  have : ((curveP p).map (algebraMap ℚ L)).IsElliptic := inferInstance
  exact (Affine.equation_iff_nonsingular (W := (curveP p).map (algebraMap ℚ L))).1 (equation_iff.2 h)

theorem eq_of_nonsingular {x y : L} (h : (EC p L).Nonsingular x y) : y ^ 2 = x ^ 3 + (p : L) * x :=
  equation_iff.1 h.1

theorem some_eq_some' {x y x' y' : L} {h : (EC p L).Nonsingular x y} {h' : (EC p L).Nonsingular x' y'}
    (hx : x = x') (hy : y = y') : Point.some x y h = Point.some x' y' h' := by
  subst hx hy
  rfl

/-- The $2$-torsion point $T = (0, 0)$ over `L`. -/
noncomputable def ptT : (EC p L).Point := Point.some 0 0 (nonsingular (by ring))

theorem ptT_ne_zero : (ptT : (EC p L).Point) ≠ 0 := by
  unfold ptT; intro h; cases h

/-- The $x$-coordinate of a point ($0$ at infinity). -/
def xc : (EC p L).Point → L
  | 0 => 0
  | Point.some x _ _ => x

/-- The map $E[2] \to \mathbb Z/2$ with kernel $\{0, T\}$: $1$ exactly on the points $(r, 0)$, $r \ne 0$. -/
noncomputable def psi : (EC p L).Point → ZMod 2
  | 0 => 0
  | Point.some x _ _ => if x = 0 then 0 else 1

theorem psi_zero : psi (0 : (EC p L).Point) = 0 := rfl

theorem psi_T : psi (ptT : (EC p L).Point) = 0 := by
  simp [ptT, psi]

theorem two_smul_eq_zero_iff (Q : (EC p L).Point) :
    (2 : ℤ) • Q = 0 ↔ Q = 0 ∨ ∃ (x : L) (h : (EC p L).Nonsingular x 0), Q = Point.some x 0 h := by
  rw [two_zsmul]
  cases Q with
  | zero => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | @some x y h =>
    constructor
    · intro h2
      right
      by_cases hy : y = (EC p L).negY x y
      · rw [negY_eq] at hy
        have : y = 0 := by
          have h2y : (2 : L) * y = 0 := by linear_combination hy
          rcases mul_eq_zero.1 h2y with h | h
          · exact absurd h two_ne_zero
          · exact h
        subst this
        exact ⟨x, h, rfl⟩
      · rw [Point.add_self_of_Y_ne hy] at h2
        cases h2
    · rintro (h0 | ⟨x', h', he⟩)
      · cases h0
      · rw [he]
        exact Point.add_self_of_Y_eq (by rw [negY_eq]; ring)

theorem two_torsion_root {x : L} (h : (EC p L).Nonsingular x 0) : x = 0 ∨ x ^ 2 = -(p : L) := by
  have h1 := eq_of_nonsingular h
  have : x * (x ^ 2 + p) = 0 := by linear_combination -h1
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · right; linear_combination h

/-- The $2$-torsion: $0$, $T$, or $(r, 0)$ with $r^2 = -p$. -/
theorem two_torsion_cases (Q : (EC p L).Point) (hQ : (2 : ℤ) • Q = 0) :
    Q = 0 ∨ Q = ptT ∨ ∃ (r : L) (h : (EC p L).Nonsingular r 0), r ^ 2 = -(p : L) ∧ Q = Point.some r 0 h := by
  rcases (two_smul_eq_zero_iff Q).1 hQ with h0 | ⟨x, h, rfl⟩
  · exact Or.inl h0
  · rcases two_torsion_root h with hx | hx
    · subst hx; exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨x, h, hx, rfl⟩)

theorem root_ne_zero {r : L} (hr : r ^ 2 = -(p : L)) : r ≠ 0 := by
  rintro rfl
  have : (p : L) = 0 := by linear_combination hr
  exact p_ne_zero this

theorem psi_root {r : L} (h : (EC p L).Nonsingular r 0) (hr : r ^ 2 = -(p : L)) :
    psi (Point.some r 0 h) = 1 := by
  simp [psi, root_ne_zero hr]

/-- Translation by $T$: $(x, y) + T = (p/x, -py/x^2)$. -/
theorem add_T {x y : L} (h : (EC p L).Nonsingular x y) (hx : x ≠ 0) :
    ∃ h' : (EC p L).Nonsingular (p / x) (-(p * y) / x ^ 2), Point.some x y h + ptT = Point.some _ _ h' := by
  have hy := eq_of_nonsingular h
  have hpx : (p : L) = (y ^ 2 - x ^ 3) / x := by
    rw [eq_div_iff hx]; linear_combination -hy
  refine ⟨nonsingular (by rw [hpx]; field_simp; ring), ?_⟩
  unfold ptT
  rw [Point.add_of_X_ne hx]
  apply some_eq_some'
  · rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, curveP, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      map_zero]
    rw [hpx]; field_simp; ring
  · rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, curveP, Affine.baseChange,
      WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero]
    rw [hpx]; field_simp; ring

/-- Translation by $T_r = (r, 0)$, $r^2 = -p$: $(x, y) + T_r = (r(x + r)/(x - r), -2r^2y/(x - r)^2)$ for $x \ne r$. -/
theorem add_root {r x y : L} (hr : r ^ 2 = -(p : L)) (hr0 : (EC p L).Nonsingular r 0) (h : (EC p L).Nonsingular x y)
    (hxr : x ≠ r) :
    ∃ h' : (EC p L).Nonsingular (r * (x + r) / (x - r)) (-(2 * r ^ 2 * y) / (x - r) ^ 2),
      Point.some x y h + Point.some r 0 hr0 = Point.some _ _ h' := by
  have hy := eq_of_nonsingular h
  have hxr' : x - r ≠ 0 := sub_ne_zero.2 hxr
  have hp' : (p : L) = -r ^ 2 := by linear_combination hr
  rw [hp'] at hy
  refine ⟨nonsingular (by rw [hp', div_pow, neg_sq, mul_pow, hy]; field_simp; ring), ?_⟩
  rw [Point.add_of_X_ne hxr]
  apply some_eq_some'
  · rw [Affine.slope_of_X_ne hxr]
    simp only [Affine.addX, curveP, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      map_zero, sub_zero]
    rw [div_pow, hy]
    field_simp
    ring
  · rw [Affine.slope_of_X_ne hxr]
    simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, curveP, Affine.baseChange,
      WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, sub_zero]
    rw [div_pow, hy]
    field_simp
    ring

theorem ptT_add_self : (ptT : (EC p L).Point) + ptT = 0 := by
  unfold ptT
  exact Point.add_self_of_Y_eq (by rw [negY_eq]; ring)

theorem root_add_self {r : L} (h : (EC p L).Nonsingular r 0) : Point.some r 0 h + Point.some r 0 h = 0 :=
  Point.add_self_of_Y_eq (by rw [negY_eq]; ring)

theorem two_smul_ptT : (2 : ℤ) • (ptT : (EC p L).Point) = 0 := by
  rw [two_zsmul, ptT_add_self]

theorem two_smul_root {r : L} (h : (EC p L).Nonsingular r 0) : (2 : ℤ) • Point.some r 0 h = 0 := by
  rw [two_zsmul, root_add_self]

theorem psi_some {x y : L} (h : (EC p L).Nonsingular x y) :
    psi (Point.some x y h) = if x = 0 then 0 else 1 := rfl

theorem xc_some {x y : L} (h : (EC p L).Nonsingular x y) : xc (Point.some x y h) = x := rfl

/-- $T + T_r = (-r, 0)$. -/
theorem ptT_add_root {r : L} (hr : r ^ 2 = -(p : L)) (h : (EC p L).Nonsingular r 0) :
    ∃ h' : (EC p L).Nonsingular (-r) 0, ptT + Point.some r 0 h = Point.some (-r) 0 h' := by
  obtain ⟨h1, e1⟩ := add_T h (root_ne_zero hr)
  have hr0 := root_ne_zero hr
  have e2 : (p : L) / r = -r := by
    rw [div_eq_iff hr0]; linear_combination hr
  refine ⟨by rw [← e2]; simpa using h1, ?_⟩
  rw [add_comm, e1]
  exact some_eq_some' e2 (by simp)

/-- $T_r + T_{-r} = T$. -/
theorem root_add_neg_root {r : L} (hr : r ^ 2 = -(p : L)) (h : (EC p L).Nonsingular r 0)
    (h' : (EC p L).Nonsingular (-r) 0) : Point.some r 0 h + Point.some (-r) 0 h' = ptT := by
  have hr0 := root_ne_zero hr
  have hne : r ≠ -r := by
    intro e; apply hr0; linear_combination e / 2
  obtain ⟨h1, e1⟩ := add_root (r := -r) (by rw [neg_sq]; exact hr) h' h hne
  rw [e1]
  unfold ptT
  exact some_eq_some' (by simp) (by simp)

/-- `psi` is additive on $E[2]$. -/
theorem psi_add (Q₁ Q₂ : (EC p L).Point) (h₁ : (2 : ℤ) • Q₁ = 0) (h₂ : (2 : ℤ) • Q₂ = 0) :
    psi (Q₁ + Q₂) = psi Q₁ + psi Q₂ := by
  rcases two_torsion_cases Q₁ h₁ with rfl | rfl | ⟨r₁, hr₁, er₁, rfl⟩
  · simp [psi_zero]
  · rcases two_torsion_cases Q₂ h₂ with rfl | rfl | ⟨r₂, hr₂, er₂, rfl⟩
    · simp [psi_zero]
    · rw [ptT_add_self, psi_T, psi_zero]; rfl
    · obtain ⟨h', e⟩ := ptT_add_root er₂ hr₂
      rw [e, psi_T, psi_root hr₂ er₂, psi_root h' (by rw [neg_sq]; exact er₂)]
      ring
  · rcases two_torsion_cases Q₂ h₂ with rfl | rfl | ⟨r₂, hr₂, er₂, rfl⟩
    · simp [psi_zero]
    · obtain ⟨h', e⟩ := ptT_add_root er₁ hr₁
      rw [add_comm, e, psi_T, psi_root hr₁ er₁, psi_root h' (by rw [neg_sq]; exact er₁)]
      ring
    · rw [psi_root hr₁ er₁, psi_root hr₂ er₂]
      by_cases e : r₁ = r₂
      · subst e
        rw [root_add_self, psi_zero]
        decide
      · have e' : r₂ = -r₁ := by
          have : (r₂ - r₁) * (r₂ + r₁) = 0 := by linear_combination er₂ - er₁
          rcases mul_eq_zero.1 this with h | h
          · exact absurd (sub_eq_zero.1 h).symm e
          · linear_combination h
        subst e'
        rw [root_add_neg_root er₁ hr₁ hr₂, psi_T]
        decide

/-! ### Base change -/

section Map

variable {L' : Type*} [Field L'] [CharZero L'] [Algebra ℚ L'] [DecidableEq L'] (f : L →ₐ[ℚ] L')

theorem map_ptT : Point.map (W' := (curveP p).toAffine) f (ptT : (EC p L).Point) = ptT := by
  unfold ptT
  rw [Point.map_some]
  exact some_eq_some' (by simp) (by simp)

theorem psi_map (Q : (EC p L).Point) : psi (Point.map (W' := (curveP p).toAffine) f Q) = psi Q := by
  cases Q with
  | zero => rfl
  | @some x y h =>
    rw [Point.map_some]
    show (if f x = 0 then (0 : ZMod 2) else 1) = if x = 0 then 0 else 1
    simp [map_eq_zero_iff f f.injective]

theorem xc_map (Q : (EC p L).Point) : xc (Point.map (W' := (curveP p).toAffine) f Q) = f (xc Q) := by
  cases Q with
  | zero => simp [xc]; rfl
  | @some x y h => rfl

end Map

/-! ### Halving -/

/-- The halving function $t(x, y) = (x^2 - p)/2y$. -/
noncomputable def tc : (EC p L).Point → L
  | 0 => 0
  | Point.some x y _ => (x ^ 2 - p) / (2 * y)

theorem tc_some {x y : L} (h : (EC p L).Nonsingular x y) : tc (Point.some x y h) = (x ^ 2 - p) / (2 * y) := rfl

/-- The double of $(x, y)$, $y \ne 0$. -/
theorem two_smul_some {x y : L} (h : (EC p L).Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : (EC p L).Nonsingular (((3 * x ^ 2 + p) / (2 * y)) ^ 2 - 2 * x)
      (((3 * x ^ 2 + p) / (2 * y)) * x - y -
        ((3 * x ^ 2 + p) / (2 * y)) * (((3 * x ^ 2 + p) / (2 * y)) ^ 2 - 2 * x)),
      (2 : ℤ) • Point.some x y h = Point.some _ _ h' := by
  have hne : y ≠ (EC p L).negY x y := by
    rw [negY_eq]; intro e; apply hy; linear_combination e / 2
  rw [two_zsmul, Point.add_self_of_Y_ne hne]
  have e1 : (EC p L).slope x x y y = (3 * x ^ 2 + p) / (2 * y) := by
    rw [Affine.slope_of_Y_ne rfl hne, negY_eq]
    simp only [curveP, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero,
      map_natCast]
    congr 1 <;> ring
  have ex : (EC p L).addX x x ((EC p L).slope x x y y) = ((3 * x ^ 2 + p) / (2 * y)) ^ 2 - 2 * x := by
    rw [e1]
    simp only [Affine.addX, curveP, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      map_zero]
    ring
  have ey : (EC p L).addY x x y ((EC p L).slope x x y y) = ((3 * x ^ 2 + p) / (2 * y)) * x - y -
      ((3 * x ^ 2 + p) / (2 * y)) * (((3 * x ^ 2 + p) / (2 * y)) ^ 2 - 2 * x) := by
    simp only [Affine.addY, Affine.negAddY]
    rw [ex, e1]
    simp only [Affine.negY, curveP, Affine.baseChange, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, map_zero]
    ring
  have hns := Affine.nonsingular_add h h (fun hxy => hne hxy.2)
  rw [ey, ex] at hns
  exact ⟨hns, some_eq_some' ex ey⟩

/-- **Halving $T$.** If $2Q = T$ then $Q = (x, y)$ with $x^2 = p$, and for $e \in E[2]$ the point $Q + e$ has
$x$-coordinate $x$ or $-x$ according as `psi e` is $0$ or $1$. -/
theorem halving_T (Q : (EC p L).Point) (hQ : (2 : ℤ) • Q = ptT) :
    ∃ (x y : L) (h : (EC p L).Nonsingular x y), Q = Point.some x y h ∧ x ^ 2 = (p : L) ∧
      ∀ e : (EC p L).Point, (2 : ℤ) • e = 0 → xc (Q + e) = if psi e = 0 then x else -x := by
  cases Q with
  | zero => exact absurd (hQ.symm.trans (smul_zero (2 : ℤ))) ptT_ne_zero
  | @some x y h =>
    have hy : y ≠ 0 := by
      rintro rfl
      have := (two_smul_eq_zero_iff (Point.some x 0 h)).2 (Or.inr ⟨x, h, rfl⟩)
      rw [this] at hQ
      exact ptT_ne_zero hQ.symm
    obtain ⟨h', e'⟩ := two_smul_some h hy
    rw [e'] at hQ
    unfold ptT at hQ
    obtain ⟨hX, hY⟩ := Point.some.inj hQ
    set l := (3 * x ^ 2 + p) / (2 * y) with hl
    have hyl : y = l * x := by rw [hX] at hY; linear_combination -hY
    have hl2 : l ^ 2 = 2 * x := by linear_combination hX
    have heq := eq_of_nonsingular h
    have hx0 : x ≠ 0 := by rintro rfl; apply hy; rw [hyl]; ring
    have hx2 : x ^ 2 = (p : L) := by
      have : x * (x ^ 2 - p) = 0 := by
        have : y ^ 2 = 2 * x ^ 3 := by rw [hyl, mul_pow, hl2]; ring
        linear_combination heq - this
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hx0
      · linear_combination h0
    refine ⟨x, y, h, rfl, hx2, fun e he => ?_⟩
    rcases two_torsion_cases e he with rfl | rfl | ⟨r, hr, er, rfl⟩
    · simp [psi_zero, xc_some]
    · obtain ⟨h1, e1⟩ := add_T h hx0
      rw [e1, xc_some, psi_T, ite_eq_left_iff.2 (fun h => absurd rfl h)]
      rw [div_eq_iff hx0]; first | linear_combination hx2 | linear_combination -hx2
    · have hxr : x ≠ r := by
        rintro rfl
        apply p_ne_zero (L := L) (p := p)
        linear_combination (er - hx2) / 2
      obtain ⟨h1, e1⟩ := add_root er hr h hxr
      rw [e1, xc_some, psi_root hr er]
      simp only [one_ne_zero, ite_false]
      have hxr' : x - r ≠ 0 := sub_ne_zero.2 hxr
      rw [div_eq_iff hxr']
      linear_combination er + hx2

/-- **Halving a point $\ne 0, T$.**  If $2Q = (x_0, y_0)$ with $x_0 \ne 0$, then $t(Q)^2 = x_0$ where
$t = (x^2 - p)/2y$, $t(Q) \ne 0$, and $t(Q + e) = \pm t(Q)$ according to `psi e`. -/
theorem halving_t (Q : (EC p L).Point) {x₀ y₀ : L} (h₀ : (EC p L).Nonsingular x₀ y₀)
    (hQ : (2 : ℤ) • Q = Point.some x₀ y₀ h₀) (hx₀ : x₀ ≠ 0) :
    tc Q ^ 2 = x₀ ∧ tc Q ≠ 0 ∧
      ∀ e : (EC p L).Point, (2 : ℤ) • e = 0 → tc (Q + e) = if psi e = 0 then tc Q else -tc Q := by
  cases Q with
  | zero => exact absurd (hQ.symm.trans (smul_zero (2 : ℤ))) (by intro h; cases h)
  | @some x y h =>
    have hy : y ≠ 0 := by
      rintro rfl
      have := (two_smul_eq_zero_iff (Point.some x 0 h)).2 (Or.inr ⟨x, h, rfl⟩)
      rw [this] at hQ
      cases hQ
    have heq := eq_of_nonsingular h
    obtain ⟨h', e'⟩ := two_smul_some h hy
    rw [e'] at hQ
    obtain ⟨hX, -⟩ := Point.some.inj hQ
    have hx0 : x ≠ 0 := by rintro rfl; apply hy; simpa using heq
    have h2y : (2 : L) * y ≠ 0 := mul_ne_zero two_ne_zero hy
    have ht2 : tc (Point.some x y h) ^ 2 = x₀ := by
      rw [tc_some, ← hX, div_pow, div_pow]
      field_simp
      linear_combination 8 * x * heq
    have ht0 : tc (Point.some x y h) ≠ 0 := by
      intro h0; rw [h0] at ht2; exact hx₀ (by rw [← ht2]; ring)
    refine ⟨ht2, ht0, fun e he => ?_⟩
    rcases two_torsion_cases e he with rfl | rfl | ⟨r, hr, er, rfl⟩
    · simp [psi_zero]
    · obtain ⟨h1, e1⟩ := add_T h hx0
      rw [e1, psi_T, ite_eq_left_iff.2 (fun h => absurd rfl h), tc_some, tc_some]
      have hp0 := p_ne_zero (L := L) (p := p)
      field_simp
      ring
    · have hxr : x ≠ r := by
        rintro rfl
        apply hy
        have : y ^ 2 = 0 := by rw [heq]; linear_combination x * er
        exact pow_eq_zero_iff two_ne_zero |>.1 this
      have hxr' : x - r ≠ 0 := sub_ne_zero.2 hxr
      have hr0 := root_ne_zero er
      obtain ⟨h1, e1⟩ := add_root er hr h hxr
      rw [e1, psi_root hr er, tc_some, tc_some]
      simp only [one_ne_zero, ite_false]
      have hp' : (p : L) = -r ^ 2 := by linear_combination er
      rw [hp']
      field_simp
      ring

/-! ### The function $s = y/x$ and the point of $E'$ -/

/-- $s(x, y) = y/x$. -/
noncomputable def sc : (EC p L).Point → L
  | 0 => 0
  | Point.some x y _ => y / x

/-- $Y(x, y) = y(p - x^2)/x^2$, the $Y$-coordinate of $\varphi(x, y)$. -/
noncomputable def Yc : (EC p L).Point → L
  | 0 => 0
  | Point.some x y _ => y * (p - x ^ 2) / x ^ 2

/-- For $Q = (x, y)$, $x \ne 0$: $s(Q + T) = -s(Q)$, $Y(Q + T) = Y(Q)$, and $(s^2, Y)$ lies on
$E' : Y^2 = X^3 - 4pX$. -/
theorem sfun_add_T {x y : L} (h : (EC p L).Nonsingular x y) (hx : x ≠ 0) :
    sc (Point.some x y h + ptT) = -sc (Point.some x y h) ∧
      Yc (Point.some x y h + ptT) = Yc (Point.some x y h) ∧
      Yc (Point.some x y h) ^ 2 = (sc (Point.some x y h) ^ 2) ^ 3 - 4 * p * sc (Point.some x y h) ^ 2 := by
  have heq := eq_of_nonsingular h
  obtain ⟨h1, e1⟩ := add_T h hx
  have hp0 := p_ne_zero (L := L) (p := p)
  rw [e1]
  refine ⟨?_, ?_, ?_⟩
  · show -(p * y) / x ^ 2 / (p / x) = -(y / x)
    field_simp
  · show -(p * y) / x ^ 2 * (p - (p / x) ^ 2) / (p / x) ^ 2 = y * (p - x ^ 2) / x ^ 2
    field_simp
    ring
  · show (y * (p - x ^ 2) / x ^ 2) ^ 2 = ((y / x) ^ 2) ^ 3 - 4 * p * (y / x) ^ 2
    rw [div_pow, mul_pow, div_pow, heq]
    field_simp
    ring

/-- **Lifting a point of $E'$.**  If $Y^2 = X^3 - 4pX$ and $s^2 = X$, $s \ne 0$, then
$P_s = (x_s, x_s s)$ with $x_s = (X - Y/s)/2$ lies on $E$, and $P_{-s} = P_s + T$. -/
theorem lift_point {X Y s : L} (hE : Y ^ 2 = X ^ 3 - 4 * p * X) (hs : s ^ 2 = X) (hs0 : s ≠ 0) :
    ∃ (h : (EC p L).Nonsingular ((X - Y / s) / 2) ((X - Y / s) / 2 * s))
      (h' : (EC p L).Nonsingular ((X - Y / (-s)) / 2) ((X - Y / (-s)) / 2 * (-s))),
      Point.some _ _ h + ptT = Point.some _ _ h' := by
  have hp0 := p_ne_zero (L := L) (p := p)
  have hprod : ∀ t : L, t ^ 2 = X → t ≠ 0 → (X - Y / t) / 2 * ((X - Y / (-t)) / 2) = p := by
    intro t ht ht0
    rw [div_neg, sub_neg_eq_add]
    have : Y ^ 2 = t ^ 6 - 4 * p * t ^ 2 := by rw [hE, ← ht]; ring
    field_simp
    rw [← ht]
    linear_combination (-1 : L) * this
  have key : ∀ t : L, t ^ 2 = X → t ≠ 0 →
      ((X - Y / t) / 2 * t) ^ 2 = ((X - Y / t) / 2) ^ 3 + p * ((X - Y / t) / 2) := by
    intro t ht ht0
    have hpr := hprod t ht ht0
    have hsum : (X - Y / (-t)) / 2 = X - (X - Y / t) / 2 := by rw [div_neg]; ring
    rw [hsum] at hpr
    rw [mul_pow, ht]
    linear_combination ((X - Y / t) / 2) * hpr
  have hs' : (-s) ^ 2 = X := by rw [neg_sq]; exact hs
  have h := nonsingular (key s hs hs0)
  have h' := nonsingular (key (-s) hs' (neg_ne_zero.2 hs0))
  have hps := hprod s hs hs0
  have hx0 : (X - Y / s) / 2 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hps; exact hp0 hps.symm
  refine ⟨h, h', ?_⟩
  obtain ⟨h1, e1⟩ := add_T h hx0
  rw [e1]
  have hxs : (X - Y / (-s)) / 2 = p / ((X - Y / s) / 2) := by
    rw [eq_div_iff hx0, mul_comm]; exact hps
  apply some_eq_some'
  · exact hxs.symm
  · rw [hxs]
    field_simp

end Field

end NumberFieldKB.MilneEC.Prop81
