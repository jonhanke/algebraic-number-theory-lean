import Mathlib.Computability.Reduce
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Short

/-!
# Milne, *Elliptic Curves*, Chapter II §§4–5: elliptic curves over $\mathbb Q_p$, definitions

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

Setting (pp. 69–70): $E : Y^2Z = X^3 + aXZ^2 + bZ^3$ with $a, b \in \mathbb Z_p$, $4a^3 + 27b^2 \neq 0$
(`curveQp a b`, Mathlib's Weierstrass curve over $\mathbb Q_p$), and its reduction
$\bar E : Y^2Z = X^3 + \bar aXZ^2 + \bar bZ^3$ over $\mathbb F_p$ (`curveFp a b`, possibly singular; Mathlib's
`Point` type of a singular Weierstrass curve consists of its nonsingular points, with the chord-and-tangent law, so
it is Milne's group $\bar E^{ns}(\mathbb F_p)$).

Definitions (D059, p. 70):
* `reducePoint P`: $\bar P$ in projective coordinates: choose primitive coordinates for $P$ and reduce. For
  $P = (x : y : 1)$ with $x \in \mathbb Z_p$ (then $y \in \mathbb Z_p$) this is $(\bar x : \bar y : 1)$; when
  $x \notin \mathbb Z_p$ it is $(0 : 1 : 0)$ (`reducePoint` is defined by these cases).
* `E0 a b` = $E^0(\mathbb Q_p) = \{P \mid \bar P \text{ nonsingular}\}$; `E1 a b` = $E^1(\mathbb Q_p) =
  \{P \mid \bar P = (0 : 1 : 0)\}$; `En a b n` = $E^n(\mathbb Q_p) = \{P \in E^1(\mathbb Q_p) \mid
  x(P)/y(P) \in p^n\mathbb Z_p\}$ ($n \ge 1$).
* `xPrime P` $= x'(P) = x(P)/y(P)$ (with $x'(O) = 0$), the coordinate of §5 (p. 74).

Results in this file: the description of $E^1(\mathbb Q_p)$ and of the valuations of $x, y$ on
$E^n(\mathbb Q_p) \smallsetminus E^{n+1}(\mathbb Q_p)$. Lemma 5.9 is in `Ch2Lemma59.lean`, Theorem 4.1 and the rest
in `Ch2Padic.lean`.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

/-- The curve $E : Y^2Z = X^3 + aXZ^2 + bZ^3$ over $\mathbb Q_p$ with $a, b \in \mathbb Z_p$ (Ch. II §4). -/
noncomputable abbrev curveQp (a b : ℤ_[p]) : WeierstrassCurve ℚ_[p] := shortCurve (a : ℚ_[p]) (b : ℚ_[p])

/-- The reduction $\bar E : Y^2Z = X^3 + \bar aXZ^2 + \bar bZ^3$ over $\mathbb F_p$ (Ch. II §§3–4). -/
@[kb "milne2006ec" "Ch. II, §3, reduction of an elliptic curve (definition in prose), pdf p. 67"]
noncomputable abbrev curveFp (a b : ℤ_[p]) : WeierstrassCurve (ZMod p) :=
  shortCurve (PadicInt.toZMod a) (PadicInt.toZMod b)

/-- The residue in $\mathbb F_p$ of an element of $\mathbb Q_p$ of norm at most $1$ (and $0$ otherwise). -/
noncomputable def residue (z : ℚ_[p]) : ZMod p :=
  if h : ‖z‖ ≤ 1 then PadicInt.toZMod ⟨z, h⟩ else 0

/-- The coordinate $x'(P) = x(P)/y(P)$ of §5 (p. 74), with $x'(O) = 0$. -/
noncomputable def xPrime {a b : ℤ_[p]} : (curveQp a b).toAffine.Point → ℚ_[p]
  | 0 => 0
  | .some x y _ => x / y

/-- The reduction $\bar P$ of a point of $E(\mathbb Q_p)$, in projective coordinates over $\mathbb F_p$ (p. 70):
reduce primitive coordinates of $P$. For $P = (x : y : 1)$ with $\|x\| \le 1$ this is $(\bar x : \bar y : 1)$; if
$\|x\| > 1$ then $P = (x/y : 1 : 1/y)$ with $x/y, 1/y \in p\mathbb Z_p$, so $\bar P = (0 : 1 : 0)$. -/
@[kb "milne2006ec" "Ch. II, §4, reduction map (definition in prose), pdf p. 69"]
noncomputable def reducePoint {a b : ℤ_[p]} : (curveQp a b).toAffine.Point → Fin 3 → ZMod p
  | 0 => ![0, 1, 0]
  | .some x y _ => if ‖x‖ ≤ 1 then ![residue x, residue y, 1] else ![0, 1, 0]

/-- Projective coordinates of a point of $\bar E^{ns}(\mathbb F_p)$ (Mathlib's affine `Point` type). -/
def toProjCoords {W : WeierstrassCurve (ZMod p)} : W.toAffine.Point → Fin 3 → ZMod p
  | 0 => ![0, 1, 0]
  | .some x y _ => ![x, y, 1]

/-- $E^0(\mathbb Q_p) = \{P \mid \bar P \text{ is nonsingular}\}$ (p. 69). -/
@[kb "milne2006ec" "Ch. II, §4, the subgroups E^n(Q_p) (definition in prose), pdf p. 69"]
def E0 (a b : ℤ_[p]) : Set (curveQp a b).toAffine.Point :=
  {P | (curveFp a b).toProjective.Nonsingular (reducePoint P)}

/-- $E^1(\mathbb Q_p) = \{P \mid \bar P = (0 : 1 : 0)\}$, the kernel of reduction (p. 70). -/
@[kb "milne2006ec" "Ch. II, §4, the subgroups E^n(Q_p) (definition in prose), pdf p. 70"]
def E1 (a b : ℤ_[p]) : Set (curveQp a b).toAffine.Point :=
  {P | reducePoint P = ![0, 1, 0]}

/-- $E^n(\mathbb Q_p) = \{P \in E^1(\mathbb Q_p) \mid x(P)/y(P) \in p^n\mathbb Z_p\}$ (p. 70), for $n \ge 1$
(for $n = 1$ it is $E^1(\mathbb Q_p)$, `En_one`). -/
@[kb "milne2006ec" "Ch. II, §4, the subgroups E^n(Q_p) (definition in prose), pdf p. 70"]
def En (a b : ℤ_[p]) (n : ℕ) : Set (curveQp a b).toAffine.Point :=
  {P | P ∈ E1 a b ∧ ‖xPrime P‖ ≤ (p : ℝ) ^ (-(n : ℤ))}

/-- The norm of an element of $\mathbb Z_p$ viewed in $\mathbb Q_p$ is at most $1$. -/
lemma norm_coe_le_one (a : ℤ_[p]) : ‖(a : ℚ_[p])‖ ≤ 1 := a.norm_le_one

/-- If $y^2 = x^3 + ax + b$ with $\|a\|, \|b\| \le 1$ and $\|x\| \le 1$ then $\|y\| \le 1$. -/
lemma norm_y_le_one {a b x y : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (e : y ^ 2 = x ^ 3 + a * x + b) : ‖y‖ ≤ 1 := by
  have h1 : ‖y ^ 2‖ ≤ 1 := by
    rw [e]
    refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans
      (max_le ?_ ?_)) hb)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    · rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hx
  rw [norm_pow] at h1
  by_contra h
  push_neg at h
  have := one_lt_pow₀ h (two_ne_zero)
  linarith

/-- If $y^2 = x^3 + ax + b$ with $\|a\|, \|b\| \le 1$ and $\|x\| > 1$ then $\|y\|^2 = \|x\|^3$. -/
lemma norm_sq_eq_of_one_lt {a b x y : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hx : 1 < ‖x‖)
    (e : y ^ 2 = x ^ 3 + a * x + b) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have h1 : ‖a * x + b‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    have hx3 : ‖x‖ < ‖x‖ ^ 3 := by
      calc ‖x‖ = ‖x‖ ^ 1 := (pow_one _).symm
        _ < ‖x‖ ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
    refine lt_of_le_of_lt ((Padic.nonarchimedean _ _).trans (max_le ?_ ?_)) hx3
    · rw [norm_mul]; calc ‖a‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
        _ = ‖x‖ := one_mul _
    · exact hb.trans hx.le
  have h2 : ‖x ^ 3 + a * x + b‖ = ‖x ^ 3‖ := by
    rw [add_assoc]
    exact Padic.add_eq_max_of_ne h1.ne' |>.trans (max_eq_left h1.le)
  rw [← norm_pow, e, h2, norm_pow]

/-- For $\|x\| > 1$ on the curve: $\|x\| = p^{2m}$, $\|y\| = p^{3m}$ for some $m \ge 1$. -/
lemma exists_norm_of_one_lt {a b x y : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hx : 1 < ‖x‖)
    (e : y ^ 2 = x ^ 3 + a * x + b) :
    ∃ m : ℕ, 1 ≤ m ∧ ‖x‖ = (p : ℝ) ^ (2 * m : ℤ) ∧ ‖y‖ = (p : ℝ) ^ (3 * m : ℤ) := by
  have key := norm_sq_eq_of_one_lt ha hb hx e
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hx0 : x ≠ 0 := by rintro rfl; exact absurd hx (by simp)
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < ‖x‖ ^ 3 := by positivity
    simp at key; linarith
  have nx := Padic.norm_eq_zpow_neg_valuation hx0
  have ny := Padic.norm_eq_zpow_neg_valuation hy0
  have hv : x.valuation < 0 := by
    by_contra h
    push_neg at h
    exact absurd ((Padic.norm_le_one_iff_val_nonneg x).2 h) (not_le.2 hx)
  rw [nx, ny, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at key
  have := zpow_right_injective₀ (by linarith : (0 : ℝ) < p) (by linarith : (p : ℝ) ≠ 1) key
  refine ⟨(-x.valuation / 2).toNat, ?_, ?_, ?_⟩
  · omega
  · rw [nx]; congr 1; omega
  · rw [ny]; congr 1; omega

/-- $E^1(\mathbb Q_p)$ consists of $O$ and the points $(x : y : 1)$ with $x \notin \mathbb Z_p$ (p. 70). -/
theorem mem_E1_iff {a b : ℤ_[p]} (P : (curveQp a b).toAffine.Point) :
    P ∈ E1 a b ↔ P = 0 ∨ ∃ x y h, P = .some x y h ∧ 1 < ‖x‖ := by
  cases P with
  | zero => simp [E1, reducePoint]; rfl
  | some x y h =>
    simp only [E1, Set.mem_setOf_eq, reducePoint]
    by_cases hx : ‖x‖ ≤ 1
    · simp only [hx, if_true]
      constructor
      · intro hh
        have := congrFun hh 2
        simp at this
      · rintro (h0 | ⟨x', y', h', he, hx'⟩)
        · exact absurd h0 (Affine.Point.some_ne_zero h)
        · simp only [Affine.Point.some.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact absurd hx (not_le.2 hx')
    · simp only [hx, if_false, true_iff]
      exact Or.inr ⟨x, y, h, rfl, not_le.1 hx⟩

/-- The two definitions of $E^1(\mathbb Q_p)$ agree: `En a b 1 = E1 a b` (p. 70). -/
theorem En_one (a b : ℤ_[p]) : En a b 1 = E1 a b := by
  ext P
  refine ⟨fun h => h.1, fun hP => ⟨hP, ?_⟩⟩
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rcases (mem_E1_iff P).1 hP with rfl | ⟨x, y, h, rfl, hx⟩
  · simp [xPrime]
  · have e := shortCurve_equation h.1
    obtain ⟨m, hm, nx, ny⟩ := exists_norm_of_one_lt (norm_coe_le_one a) (norm_coe_le_one b) hx e
    simp only [xPrime, norm_div, nx, ny]
    rw [← zpow_sub₀ (by positivity)]
    apply zpow_le_zpow_right₀ hp.le
    push_cast; omega

/-- p. 70: the points of $E^n(\mathbb Q_p) \smallsetminus E^{n+1}(\mathbb Q_p)$, $n \ge 1$, satisfy
$\operatorname{ord}_p x = -2n$, $\operatorname{ord}_p y = -3n$ (in the chart $z = 1$). -/
@[kb "milne2006ec" "Ch. II, Theorem 4.1, proof of (c), pdf p. 71"]
theorem norm_x_y_of_mem_En {a b : ℤ_[p]} {n : ℕ} (hn : 1 ≤ n) {x y : ℚ_[p]}
    {h : (curveQp a b).toAffine.Nonsingular x y} (hP : Affine.Point.some x y h ∈ En a b n)
    (hP' : Affine.Point.some x y h ∉ En a b (n + 1)) :
    ‖x‖ = (p : ℝ) ^ (2 * n : ℤ) ∧ ‖y‖ = (p : ℝ) ^ (3 * n : ℤ) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨hE1, hle⟩ := hP
  rcases (mem_E1_iff _).1 hE1 with h0 | ⟨x', y', h', he, hx⟩
  · exact absurd h0 (Affine.Point.some_ne_zero h)
  · simp only [Affine.Point.some.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have e := shortCurve_equation h.1
    obtain ⟨m, hm, nx, ny⟩ := exists_norm_of_one_lt (norm_coe_le_one a) (norm_coe_le_one b) hx e
    have hxy : ‖xPrime (Affine.Point.some x y h)‖ = (p : ℝ) ^ (-(m : ℤ)) := by
      simp only [xPrime, norm_div, nx, ny]
      rw [← zpow_sub₀ (by positivity)]
      congr 1; ring
    rw [hxy] at hle
    have h1 := (zpow_le_zpow_iff_right₀ hp).1 hle
    have h2 : ¬ ((p : ℝ) ^ (-(m : ℤ)) ≤ (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) := fun hh =>
      hP' ⟨hE1, by rw [hxy]; exact hh⟩
    rw [zpow_le_zpow_iff_right₀ hp] at h2
    have : m = n := by push_cast at h2; omega
    subst this
    exact ⟨nx, ny⟩

end NumberFieldKB.MilneEC.II
