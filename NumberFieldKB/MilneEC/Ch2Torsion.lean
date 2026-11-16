import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Padic

/-!
# Milne, *Elliptic Curves*, Chapter II §5: torsion points (Lutz–Nagell)

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

Setting (p. 72): $E : Y^2Z = X^3 + aXZ^2 + bZ^3$ with $a, b \in \mathbb Z$ and $\Delta = 4a^3 + 27b^2 \neq 0$
(`curveQ a b`; in §5 Milne writes $\Delta$ for $4a^3 + 27b^2$, not for the discriminant $-16(4a^3 + 27b^2)$ of
Mathlib's `WeierstrassCurve.Δ`). A point of $E(\mathbb Q)$ gives a point of $E(\mathbb Q_p)$ (`toQp`), where
$E(\mathbb Q_p)$ is `curveQp a b` of `Ch2PadicDefs.lean`.

Contents: Proposition 5.3, Corollaries 5.6 and 5.7, Theorem 5.1 (Lutz–Nagell), Remark 5.11 (Mazur) as a named
statement with its consequence that $|E(\mathbb Q)_{\mathrm{tors}}| \le 16$.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

attribute [local instance] Classical.propDecidable

/-- The curve $E : Y^2Z = X^3 + aXZ^2 + bZ^3$ over $\mathbb Q$ with $a, b \in \mathbb Z$ (Ch. II §5, p. 72). -/
noncomputable abbrev curveQ (a b : ℤ) : WeierstrassCurve ℚ := shortCurve (a : ℚ) (b : ℚ)

variable (p : ℕ) [Fact p.Prime]

/-- The curve over $\mathbb Q_p$ is the image of the curve over $\mathbb Q$ under the inclusion. -/
lemma map_curveQ (a b : ℤ) :
    (curveQ a b).map (Rat.castHom ℚ_[p]) = curveQp (a : ℤ_[p]) (b : ℤ_[p]) := by
  ext <;> simp [shortCurve]

/-- A rational point of $E$ is a $p$-adic point. -/
theorem nonsingular_toQp {a b : ℤ} {x y : ℚ} (h : (curveQ a b).toAffine.Nonsingular x y) :
    (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.Nonsingular (x : ℚ_[p]) (y : ℚ_[p]) := by
  rw [← map_curveQ p a b]
  exact (Affine.map_nonsingular (f := Rat.castHom ℚ_[p]) (curveQ a b) (Rat.castHom ℚ_[p]).injective x y).2 h

/-- The map $E(\mathbb Q) \to E(\mathbb Q_p)$ on points. -/
noncomputable def toQpFun {a b : ℤ} : (curveQ a b).toAffine.Point → (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.Point
  | 0 => 0
  | .some x y h => .some (x : ℚ_[p]) (y : ℚ_[p]) (nonsingular_toQp p h)

/-- The inclusion $E(\mathbb Q) \to E(\mathbb Q_p)$, a group homomorphism. -/
noncomputable def toQp (a b : ℤ) :
    (curveQ a b).toAffine.Point →+ (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.Point where
  toFun := toQpFun p
  map_zero' := rfl
  map_add' := by
    have hm := map_curveQ p a b
    have hneg : ∀ x y : ℚ, (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.negY (x : ℚ_[p]) (y : ℚ_[p]) =
        (((curveQ a b).toAffine.negY x y : ℚ) : ℚ_[p]) := fun x y => by
      rw [← hm]; exact Affine.map_negY (W' := (curveQ a b).toAffine) (Rat.castHom ℚ_[p]) x y
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    · rfl
    · change toQpFun p (0 + Affine.Point.some x₂ y₂ h₂) = toQpFun p 0 + toQpFun p (Affine.Point.some x₂ y₂ h₂)
      rw [zero_add]; exact (zero_add _).symm
    · change toQpFun p (Affine.Point.some x₁ y₁ h₁ + 0) = toQpFun p (Affine.Point.some x₁ y₁ h₁) + toQpFun p 0
      rw [add_zero]; exact (add_zero _).symm
    · by_cases hxy : x₁ = x₂ ∧ y₁ = (curveQ a b).toAffine.negY x₂ y₂
      · obtain ⟨hx, hy⟩ := hxy
        have hy' : (y₁ : ℚ_[p]) = (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.negY (x₂ : ℚ_[p]) (y₂ : ℚ_[p]) := by
          rw [hneg, hy]
        rw [Affine.Point.add_of_Y_eq hx hy]
        show toQpFun p 0 = _
        simp only [toQpFun]
        rw [Affine.Point.add_of_Y_eq (by rw [hx]) hy']
      · have hxy' : ¬((x₁ : ℚ_[p]) = x₂ ∧ (y₁ : ℚ_[p]) = (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.negY (x₂ : ℚ_[p]) (y₂ : ℚ_[p])) := by
          rintro ⟨hx, hy⟩
          apply hxy
          rw [hneg] at hy
          exact ⟨by exact_mod_cast hx, by exact_mod_cast hy⟩
        rw [Affine.Point.add_some hxy]
        show toQpFun p (.some _ _ _) = _
        simp only [toQpFun]
        rw [Affine.Point.add_some hxy']
        have e1 := Affine.map_slope (W := (curveQ a b).toAffine) (Rat.castHom ℚ_[p]) x₁ x₂ y₁ y₂
        have e2 := Affine.map_addX (W' := (curveQ a b).toAffine) (Rat.castHom ℚ_[p]) (x₁ := x₁) (x₂ := x₂)
          (ℓ := Affine.slope (curveQ a b).toAffine x₁ x₂ y₁ y₂)
        have e3 := Affine.map_addY (W' := (curveQ a b).toAffine) (Rat.castHom ℚ_[p]) (x₁ := x₁) (x₂ := x₂)
          (y₁ := y₁) (ℓ := Affine.slope (curveQ a b).toAffine x₁ x₂ y₁ y₂)
        have e1' : (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.slope (x₁ : ℚ_[p]) x₂ y₁ y₂ =
            ((Affine.slope (curveQ a b).toAffine x₁ x₂ y₁ y₂ : ℚ) : ℚ_[p]) := by rw [← hm]; exact e1
        have e2' : (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.addX (x₁ : ℚ_[p]) x₂
            ((Affine.slope (curveQ a b).toAffine x₁ x₂ y₁ y₂ : ℚ) : ℚ_[p]) =
            (((curveQ a b).toAffine.addX x₁ x₂ (Affine.slope (curveQ a b).toAffine x₁ x₂ y₁ y₂) : ℚ) : ℚ_[p]) := by
          rw [← hm]; exact e2
        have e3' : (curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.addY (x₁ : ℚ_[p]) x₂ y₁
            ((Affine.slope (curveQ a b).toAffine x₁ x₂ y₁ y₂ : ℚ) : ℚ_[p]) =
            (((curveQ a b).toAffine.addY x₁ x₂ y₁ (Affine.slope (curveQ a b).toAffine x₁ x₂ y₁ y₂) : ℚ) : ℚ_[p]) := by
          rw [← hm]; exact e3
        simp only [e1', e2', e3']

/-- The inclusion $E(\mathbb Q) \to E(\mathbb Q_p)$ is injective. -/
theorem toQp_injective (a b : ℤ) : Function.Injective (toQp p a b) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · have h' : toQpFun p (a := a) (b := b) 0 = toQpFun p (a := a) (b := b) (.some x₂ y₂ h₂) := h
    simp [toQpFun] at h'
  · have h' : toQpFun p (a := a) (b := b) (.some x₁ y₁ h₁) = toQpFun p (a := a) (b := b) 0 := h
    simp [toQpFun] at h'
  · have h : toQpFun p (a := a) (b := b) (.some x₁ y₁ h₁) = toQpFun p (a := a) (b := b) (.some x₂ y₂ h₂) := h
    simp only [toQpFun, Affine.Point.some.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Affine.Point.some.injEq]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **Proposition 5.3** (pdf p. 73). Let $P = (x_1 : y_1 : 1) \in E(\mathbb Q)$ with $x_1, y_1 \in \mathbb Z$. If $2P$
has integer coordinates (or $2P = O$) then $y_1 = 0$ or $y_1 \mid 4a^3 + 27b^2$. (Milne's standing hypothesis
$4a^3 + 27b^2 \neq 0$ is not needed: the proof uses the resultant identity of footnote 2.) -/
@[kb "milne2006ec" "Ch. II, Proposition 5.3, pdf p. 73"]
theorem proposition_5_3 {a b x₁ y₁ : ℤ} (h₁ : (curveQ a b).toAffine.Nonsingular (x₁ : ℚ) (y₁ : ℚ))
    (h2P : 2 • Affine.Point.some _ _ h₁ = 0 ∨
      ∃ (x₂ y₂ : ℤ) (h₂ : (curveQ a b).toAffine.Nonsingular (x₂ : ℚ) (y₂ : ℚ)),
        2 • Affine.Point.some _ _ h₁ = Affine.Point.some _ _ h₂) :
    y₁ = 0 ∨ y₁ ∣ 4 * a ^ 3 + 27 * b ^ 2 := by
  by_cases hy : y₁ = 0
  · exact Or.inl hy
  right
  have hyQ : (y₁ : ℚ) ≠ 0 := by exact_mod_cast hy
  have e : (y₁ : ℚ) ^ 2 = (x₁ : ℚ) ^ 3 + (a : ℚ) * x₁ + b := shortCurve_equation h₁.1
  have eZ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b := by exact_mod_cast e
  rcases h2P with h0 | ⟨x₂, y₂, h₂, hdbl⟩
  · exfalso
    rw [two_nsmul] at h0
    have hne : (y₁ : ℚ) ≠ (curveQ a b).toAffine.negY (x₁ : ℚ) (y₁ : ℚ) := by
      simp only [Affine.negY, shortCurve_a₁, shortCurve_a₃]
      intro h'
      apply hyQ
      linarith
    rw [Affine.Point.add_self_of_Y_ne hne] at h0
    exact Affine.Point.some_ne_zero _ h0
  · rw [two_nsmul] at hdbl
    obtain ⟨-, hx2, -, -⟩ := duplication_formula h₁ h₂ hdbl
    have hy2 : (4 : ℚ) * (y₁ : ℚ) ^ 2 ≠ 0 := by positivity
    rw [eq_div_iff hy2] at hx2
    have hsq : (3 * x₁ ^ 2 + a) ^ 2 = y₁ ^ 2 * (4 * x₂ + 8 * x₁) := by
      have : (((3 * x₁ ^ 2 + a) ^ 2 : ℤ) : ℚ) = ((y₁ ^ 2 * (4 * x₂ + 8 * x₁) : ℤ) : ℚ) := by
        push_cast
        linear_combination -hx2
      exact_mod_cast this
    have hd1 : y₁ ∣ 3 * x₁ ^ 2 + a :=
      (Int.pow_dvd_pow_iff two_ne_zero).1 ⟨_, hsq⟩
    have hd2 : y₁ ∣ x₁ ^ 3 + a * x₁ + b := ⟨y₁, by rw [← eZ]; ring⟩
    have key : 4 * a ^ 3 + 27 * b ^ 2 = (3 * x₁ ^ 2 + a) * (4 * a ^ 2 + 3 * x₁ * (2 * a * x₁ - 3 * b)) -
        9 * (x₁ ^ 3 + a * x₁ + b) * (2 * a * x₁ - 3 * b) := by ring
    rw [key]
    exact dvd_sub (dvd_mul_of_dvd_left hd1 _) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd2 _) _)

/-- A rational number of $p$-adic norm at most $1$ for every prime $p$ is an integer (its denominator is $1$). -/
lemma den_eq_one_of_norm_le_one (q : ℚ) (h : ∀ (p : ℕ) [Fact p.Prime], ‖(q : ℚ_[p])‖ ≤ 1) : q.den = 1 := by
  by_contra hd
  have hp : q.den.minFac.Prime := Nat.minFac_prime hd
  have : Fact q.den.minFac.Prime := ⟨hp⟩
  have hq : (q : ℚ_[q.den.minFac]) * (q.den : ℚ_[q.den.minFac]) = q.num := by
    exact_mod_cast Rat.mul_den_eq_num q
  have hden : ‖(q.den : ℚ_[q.den.minFac])‖ < 1 :=
    Padic.norm_natCast_lt_one_iff.2 (Nat.minFac_dvd _)
  have hnd : ¬ ((q.den.minFac : ℕ) : ℤ) ∣ q.num := fun h' => by
    have := Nat.dvd_gcd (Int.natCast_dvd.1 h') (Nat.minFac_dvd q.den)
    rw [q.reduced.gcd_eq_one] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hnum : ‖(q.num : ℚ_[q.den.minFac])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _) (not_lt.1 fun hlt => hnd (Padic.norm_intCast_lt_one_iff.1 hlt))
  have h1 := congrArg norm hq
  rw [norm_mul, hnum] at h1
  have h2 := h q.den.minFac
  have h3 : 0 ≤ ‖(q.den : ℚ_[q.den.minFac])‖ := norm_nonneg _
  nlinarith [norm_nonneg (q : ℚ_[q.den.minFac])]

/-- **Corollary 5.6** (pdf p. 74): if $P = (x : y : 1) \in E(\mathbb Q)_{\mathrm{tors}}$ then $x, y \in \mathbb Z$. -/
@[kb "milne2006ec" "Ch. II, Corollary 5.6, pdf p. 74"]
theorem corollary_5_6 {a b : ℤ} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {x y : ℚ}
    {h : (curveQ a b).toAffine.Nonsingular x y} (htors : IsOfFinAddOrder (Affine.Point.some x y h)) :
    ∃ X Y : ℤ, x = X ∧ y = Y := by
  have key : ∀ (p : ℕ) [Fact p.Prime], ‖(x : ℚ_[p])‖ ≤ 1 ∧ ‖(y : ℚ_[p])‖ ≤ 1 := by
    intro p _
    have hΔp : 4 * (a : ℤ_[p]) ^ 3 + 27 * (b : ℤ_[p]) ^ 2 ≠ 0 := by
      intro h0
      apply hΔ
      exact_mod_cast (by exact_mod_cast h0 : ((4 * a ^ 3 + 27 * b ^ 2 : ℤ) : ℤ_[p]) = 0)
    exact corollary_5_5 (a : ℤ_[p]) (b : ℤ_[p]) hΔp (h := nonsingular_toQp p h)
      ((toQp p a b).isOfFinAddOrder htors)
  have hx := den_eq_one_of_norm_le_one x (fun p _ => (key p).1)
  have hy := den_eq_one_of_norm_le_one y (fun p _ => (key p).2)
  exact ⟨x.num, y.num, (Rat.den_eq_one_iff x).1 hx |>.symm, (Rat.den_eq_one_iff y).1 hy |>.symm⟩

/-- **Theorem 5.1** (Lutz–Nagell, pdf p. 72): if $P = (x : y : 1) \in E(\mathbb Q)_{\mathrm{tors}}$ then
$x, y \in \mathbb Z$ and either $y = 0$ or $y \mid 4a^3 + 27b^2$. -/
@[kb "milne2006ec" "Ch. II, Theorem 5.1, pdf p. 72"]
theorem theorem_5_1 {a b : ℤ} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {x y : ℚ}
    {h : (curveQ a b).toAffine.Nonsingular x y} (htors : IsOfFinAddOrder (Affine.Point.some x y h)) :
    ∃ X Y : ℤ, x = X ∧ y = Y ∧ (Y = 0 ∨ Y ∣ 4 * a ^ 3 + 27 * b ^ 2) := by
  obtain ⟨X, Y, rfl, rfl⟩ := corollary_5_6 hΔ htors
  refine ⟨X, Y, rfl, rfl, ?_⟩
  refine proposition_5_3 (h₁ := h) ?_
  have h2tors : IsOfFinAddOrder (2 • Affine.Point.some _ _ h) := htors.nsmul
  rcases hP : 2 • Affine.Point.some _ _ h with _ | ⟨x₂, y₂, h₂⟩
  · exact Or.inl rfl
  · rw [hP] at h2tors
    obtain ⟨X₂, Y₂, hx₂, hy₂⟩ := corollary_5_6 hΔ h2tors
    subst hx₂ hy₂
    exact Or.inr ⟨X₂, Y₂, h₂, rfl⟩

/-- Projective coordinates of points of a Weierstrass curve over $\mathbb F_p$ determine the point. -/
lemma toProjCoords_injective {W : WeierstrassCurve (ZMod p)} :
    Function.Injective (toProjCoords (W := W)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · have := congrFun h 2
    simp [toProjCoords] at this
  · have := congrFun h 2
    simp [toProjCoords] at this
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [toProjCoords] at h0 h1
    subst h0 h1
    rfl

/-- On the curve with good reduction, a torsion point of $E(\mathbb Q)$ has nonsingular reduction at $p$. -/
lemma torsion_mem_E0 {a b : ℤ} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hp2 : p ≠ 2)
    (hgood : ¬(p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {P : (curveQ a b).toAffine.Point} (hP : IsOfFinAddOrder P) :
    toQp p a b P ∈ E0 (a : ℤ_[p]) (b : ℤ_[p]) := by
  have hΔp : 4 * (a : ℤ_[p]) ^ 3 + 27 * (b : ℤ_[p]) ^ 2 ≠ 0 := by
    intro h0
    apply hΔ
    exact_mod_cast (by exact_mod_cast h0 : ((4 * a ^ 3 + 27 * b ^ 2 : ℤ) : ℤ_[p]) = 0)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hΔz : (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2) ≠ 0 := by
    intro h0
    apply hgood
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h0
  cases P with
  | zero =>
    show (curveFp (a : ℤ_[p]) (b : ℤ_[p])).toProjective.Nonsingular (reducePoint (toQp p a b 0))
    rw [map_zero]
    exact Projective.nonsingular_zero
  | some x y h =>
    have hx := corollary_5_5 (a : ℤ_[p]) (b : ℤ_[p]) hΔp (h := nonsingular_toQp p h)
      ((toQp p a b).isOfFinAddOrder hP)
    show (curveFp (a : ℤ_[p]) (b : ℤ_[p])).toProjective.Nonsingular
      (reducePoint (Affine.Point.some (x : ℚ_[p]) (y : ℚ_[p]) (nonsingular_toQp p h)))
    simp only [reducePoint, hx.1, ite_true]
    have rx : residue (x : ℚ_[p]) = PadicInt.toZMod ⟨(x : ℚ_[p]), hx.1⟩ := by simp only [residue, hx.1, dite_true]
    have ry : residue (y : ℚ_[p]) = PadicInt.toZMod ⟨(y : ℚ_[p]), hx.2⟩ := by simp only [residue, hx.2, dite_true]
    rw [rx, ry, Projective.nonsingular_some]
    set x' : ℤ_[p] := ⟨(x : ℚ_[p]), hx.1⟩
    set y' : ℤ_[p] := ⟨(y : ℚ_[p]), hx.2⟩
    have e : (y : ℚ_[p]) ^ 2 = (x : ℚ_[p]) ^ 3 + (a : ℚ) * x + (b : ℚ) := by
      exact_mod_cast shortCurve_equation h.1
    have e' : y' ^ 2 = x' ^ 3 + (a : ℤ_[p]) * x' + (b : ℤ_[p]) := by
      apply PadicInt.ext
      push_cast
      simpa using e
    have ez : (PadicInt.toZMod y') ^ 2 = (PadicInt.toZMod x') ^ 3 + (a : ZMod p) * PadicInt.toZMod x' + (b : ZMod p) := by
      have := congrArg (PadicInt.toZMod (p := p)) e'
      simpa using this
    rw [Affine.nonsingular_iff]
    refine ⟨?_, ?_⟩
    · rw [Affine.equation_iff]
      simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, shortCurve_a₆, map_intCast]
      linear_combination ez
    · by_contra hcon
      push Not at hcon
      obtain ⟨c1, c2⟩ := hcon
      simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, map_intCast] at c1 c2
      have hy0 : PadicInt.toZMod y' = 0 := by
        have : 2 * PadicInt.toZMod y' = 0 := by linear_combination c2
        exact (mul_eq_zero.1 this).resolve_left h2
      apply hΔz
      linear_combination (-(4 * (a : ZMod p) ^ 2 + 3 * PadicInt.toZMod x' * (2 * (a : ZMod p) * PadicInt.toZMod x' - 3 * (b : ZMod p)))) * c1 + 9 * (2 * (a : ZMod p) * PadicInt.toZMod x' - 3 * (b : ZMod p)) * ez + (-9 * (2 * (a : ZMod p) * PadicInt.toZMod x' - 3 * (b : ZMod p)) * (PadicInt.toZMod y' + 0)) * hy0

/-- **Corollary 5.7** (pdf p. 74), conditional on Theorem 4.1 (b) (`Theorem4_1b`, a named statement): if $E$ has
good reduction at $p$ ($p \neq 2$ and $p \nmid 4a^3 + 27b^2$), the reduction map
$E(\mathbb Q)_{\mathrm{tors}} \to \bar E(\mathbb F_p)$, $P \mapsto \bar P$ (`reducePoint`), is injective. -/
@[kb "milne2006ec" "Ch. II, Corollary 5.7, pdf p. 74"]
theorem corollary_5_7 (h41b : Theorem4_1b) {a b : ℤ} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hp2 : p ≠ 2)
    (hgood : ¬(p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) :
    Set.InjOn (fun P => reducePoint (toQp p a b P)) {P : (curveQ a b).toAffine.Point | IsOfFinAddOrder P} := by
  intro P hP Q hQ hPQ
  have hΔp : 4 * (a : ℤ_[p]) ^ 3 + 27 * (b : ℤ_[p]) ^ 2 ≠ 0 := by
    intro h0
    apply hΔ
    exact_mod_cast (by exact_mod_cast h0 : ((4 * a ^ 3 + 27 * b ^ 2 : ℤ) : ℤ_[p]) = 0)
  obtain ⟨G, hG, ρ, hρ, -, hker⟩ := h41b.iso p (a : ℤ_[p]) (b : ℤ_[p]) hΔp
  have memP : toQp p a b P ∈ G := by
    rw [← SetLike.mem_coe, hG]; exact torsion_mem_E0 p hΔ hp2 hgood hP
  have memQ : toQp p a b Q ∈ G := by
    rw [← SetLike.mem_coe, hG]; exact torsion_mem_E0 p hΔ hp2 hgood hQ
  have hρeq : ρ ⟨_, memP⟩ = ρ ⟨_, memQ⟩ :=
    by apply toProjCoords_injective p; rw [hρ, hρ]; exact hPQ
  have hsub : ρ (⟨_, memP⟩ - ⟨_, memQ⟩) = 0 := by rw [map_sub, hρeq, sub_self]
  have hE1 := (hker _).1 hsub
  have e : toQp p a b (P - Q) = toQp p a b P - toQp p a b Q := map_sub _ _ _
  have htors : IsOfFinAddOrder (toQp p a b (P - Q)) := by
    apply (toQp p a b).isOfFinAddOrder
    rw [sub_eq_add_neg]
    exact hP.add hQ.neg
  obtain ⟨m, hm, hmP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 htors
  have h0 : toQp p a b (P - Q) = 0 :=
    proposition_5_4 (a : ℤ_[p]) (b : ℤ_[p]) hΔp (by rw [e]; exact hE1) hm hmP
  have := toQp_injective p a b (h0.trans (map_zero _).symm)
  exact sub_eq_zero.1 this

/-- **Remark 5.11** (Mazur 1977, pdf p. 76), as a named statement: for an elliptic curve $E$ over $\mathbb Q$,
$E(\mathbb Q)_{\mathrm{tors}}$ is isomorphic to $\mathbb Z/m\mathbb Z$ with $1 \le m \le 10$ or $m = 12$, or to
$\mathbb Z/2\mathbb Z \times \mathbb Z/2m\mathbb Z$ with $1 \le m \le 4$. (Milne states it for the curves of §5;
every elliptic curve over $\mathbb Q$ has such an equation, Theorem 2.1, and the statement is given here for every
Weierstrass equation.) -/
@[kb "milne2006ec" "Ch. II, Remark 5.11, pdf p. 76"]
structure MazurTorsion : Prop where
  classification : ∀ (W : WeierstrassCurve ℚ), W.IsElliptic →
    (∃ m : ℕ, (1 ≤ m ∧ m ≤ 10 ∨ m = 12) ∧
        Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ ZMod m)) ∨
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ 4 ∧ Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ ZMod 2 × ZMod (2 * m))

/-- From Mazur's theorem (Remark 5.11): $E(\mathbb Q)_{\mathrm{tors}}$ is finite with at most $16$ elements. -/
@[kb "milne2006ec" "Ch. II, Remark 5.11, pdf p. 76"]
theorem card_torsion_le_sixteen (hM : MazurTorsion) (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    Finite (AddCommGroup.torsion W.toAffine.Point) ∧ Nat.card (AddCommGroup.torsion W.toAffine.Point) ≤ 16 := by
  rcases hM.classification W inferInstance with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm1, hm4, ⟨e⟩⟩
  · have hm0 : NeZero m := ⟨by omega⟩
    refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
    omega
  · have hm0 : NeZero (2 * m) := ⟨by omega⟩
    refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
    omega

end NumberFieldKB.MilneEC.II
