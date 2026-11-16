import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Normed.Group.Ultra
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Lemma59
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Milne, *Elliptic Curves*, Chapter II §§4–5: the filtration of $E(\mathbb Q_p)$ and torsion

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8). Definitions in `Ch2PadicDefs.lean`, Lemma 5.9 in
`Ch2Lemma59.lean`.

* Theorem 4.1: (a) and (b) are named statements (`Theorem4_1a`, `Theorem4_1b`); (c) and (d) are proved, (c) from
  Lemma 5.9 and Hensel's lemma.
* Corollary 4.2: injectivity proved; the full statement (with surjectivity, whose proof uses the completeness of
  $E^1(\mathbb Q_p)$) is the named statement `Corollary4_2`.
* Proposition 5.4 and Corollary 5.5 (proved).
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

/-- $E^1(\mathbb Q_p)$ is closed under negation. -/
lemma neg_mem_E1 {a b : ℤ_[p]} {P : (curveQp a b).toAffine.Point} (hP : P ∈ E1 a b) : -P ∈ E1 a b := by
  rcases (mem_E1_iff P).1 hP with rfl | ⟨x, y, h, rfl, hx⟩
  · exact (mem_E1_iff _).2 (Or.inl (by simp))
  · exact (mem_E1_iff _).2 (Or.inr ⟨x, _, _, rfl, hx⟩)

/-- $E^n(\mathbb Q_p)$ is closed under addition (Lemma 5.9). -/
lemma add_mem_En {a b : ℤ_[p]} {n : ℕ} (hn : 1 ≤ n) {P Q : (curveQp a b).toAffine.Point}
    (hP : P ∈ En a b n) (hQ : Q ∈ En a b n) : P + Q ∈ En a b n := by
  have := (lemma_5_9 hn (P₃ := -(P + Q)) (by abel) hP hQ).1
  simpa using neg_mem_En this

/-- The key congruence: $x'(P+Q) \equiv x'(P) + x'(Q) \bmod p^{5n}$ on $E^n$. -/
lemma norm_xPrime_add_sub_le {a b : ℤ_[p]} {n : ℕ} (hn : 1 ≤ n) {P Q : (curveQp a b).toAffine.Point}
    (hP : P ∈ En a b n) (hQ : Q ∈ En a b n) :
    ‖xPrime (P + Q) - (xPrime P + xPrime Q)‖ ≤ (p : ℝ) ^ (-(5 * n : ℤ)) := by
  have := (lemma_5_9 hn (P₃ := -(P + Q)) (by abel) hP hQ).2
  rw [xPrime_neg] at this
  rw [← norm_neg]
  convert this using 2; ring

/-- $E^n(\mathbb Q_p)$, $n \ge 1$, is a subgroup (Theorem 4.1 (c), from Lemma 5.9). -/
noncomputable def EnSubgroup (a b : ℤ_[p]) (n : ℕ) (hn : 1 ≤ n) : AddSubgroup (curveQp a b).toAffine.Point where
  carrier := En a b n
  add_mem' := add_mem_En hn
  zero_mem' := zero_mem_En a b n
  neg_mem' := neg_mem_En

/-- For a point $P \ne O$ of $E^1(\mathbb Q_p)$, $\|x'(P)\| = p^{-n}$ for some $n \ge 1$. -/
lemma exists_norm_xPrime {a b : ℤ_[p]} {P : (curveQp a b).toAffine.Point} (hP : P ∈ E1 a b) (h0 : P ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ ‖xPrime P‖ = (p : ℝ) ^ (-(n : ℤ)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rcases (mem_E1_iff P).1 hP with h | ⟨x, y, h, rfl, hx⟩
  · exact absurd h h0
  · have e := shortCurve_equation h.1
    obtain ⟨m, hm, nx, ny⟩ := exists_norm_of_one_lt (norm_coe_le_one a) (norm_coe_le_one b) hx e
    refine ⟨m, hm, ?_⟩
    simp only [xPrime, norm_div, nx, ny]
    rw [← zpow_sub₀ (by positivity)]
    congr 1; ring

/-- If $\|x'(P)\| = p^{-n}$ and $P \in E^1(\mathbb Q_p)$ then $P \in E^n(\mathbb Q_p)$. -/
lemma mem_En_of_norm_xPrime {a b : ℤ_[p]} {n : ℕ} {P : (curveQp a b).toAffine.Point} (hP : P ∈ E1 a b)
    (h : ‖xPrime P‖ = (p : ℝ) ^ (-(n : ℤ))) : P ∈ En a b n :=
  ⟨hP, h.le⟩

/-- Multiples on $E^n(\mathbb Q_p)$: $kP \in E^n(\mathbb Q_p)$ and $x'(kP) \equiv k\,x'(P) \bmod p^{5n}$. -/
lemma nsmul_mem_En_xPrime {a b : ℤ_[p]} {n : ℕ} (hn : 1 ≤ n) {P : (curveQp a b).toAffine.Point}
    (hP : P ∈ En a b n) (k : ℕ) :
    k • P ∈ En a b n ∧ ‖xPrime (k • P) - (k : ℚ_[p]) * xPrime P‖ ≤ (p : ℝ) ^ (-(5 * n : ℤ)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  induction k with
  | zero => exact ⟨by simpa using zero_mem_En a b n, by simp [xPrime]; positivity⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨by rw [succ_nsmul]; exact add_mem_En hn h1 hP, ?_⟩
    have h3 := norm_xPrime_add_sub_le hn h1 hP
    have : xPrime ((k + 1) • P) - ((k + 1 : ℕ) : ℚ_[p]) * xPrime P =
        (xPrime (k • P + P) - (xPrime (k • P) + xPrime P)) + (xPrime (k • P) - (k : ℚ_[p]) * xPrime P) := by
      rw [succ_nsmul]; push_cast; ring
    rw [this]
    exact (Padic.nonarchimedean _ _).trans (max_le h3 h2)

/-- A nonzero point $P$ of $E^1(\mathbb Q_p)$ has $cP \ne O$ for every natural number $c$ with
$p^{-1} \le \|c\|$. -/
lemma nsmul_ne_zero_of_E1 {a b : ℤ_[p]} {P : (curveQp a b).toAffine.Point} (hP : P ∈ E1 a b) (h0 : P ≠ 0)
    {c : ℕ} (hc : (p : ℝ)⁻¹ ≤ ‖(c : ℚ_[p])‖) : c • P ≠ 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn, hx⟩ := exists_norm_xPrime hP h0
  obtain ⟨-, h2⟩ := nsmul_mem_En_xPrime hn (mem_En_of_norm_xPrime hP hx) c
  intro hz
  have e0 : xPrime (0 : (curveQp a b).toAffine.Point) = 0 := rfl
  rw [hz, e0, zero_sub, norm_neg, norm_mul, hx] at h2
  have h4 : (p : ℝ) ^ (-(5 * n : ℤ)) < (p : ℝ) ^ (-(n : ℤ) - 1) :=
    zpow_lt_zpow_right₀ hp (by omega)
  have h5 : (p : ℝ) ^ (-(n : ℤ) - 1) ≤ ‖(c : ℚ_[p])‖ * (p : ℝ) ^ (-(n : ℤ)) := by
    rw [zpow_sub₀ (by positivity), zpow_one, mul_comm, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  linarith

/-- The residue of an element of $\mathbb Z_p$ is its image in $\mathbb F_p$. -/
lemma residue_coe (z : ℤ_[p]) : residue (z : ℚ_[p]) = PadicInt.toZMod z := by
  unfold residue
  split_ifs with h
  · rfl
  · exact absurd z.norm_le_one h

/-- The residue is additive on elements of norm at most $1$. -/
lemma residue_add {z w : ℚ_[p]} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    residue (z + w) = residue z + residue w := by
  have h : ‖z + w‖ ≤ 1 := (Padic.nonarchimedean _ _).trans (max_le hz hw)
  have e : (⟨z + w, h⟩ : ℤ_[p]) = ⟨z, hz⟩ + ⟨w, hw⟩ := rfl
  have r1 : residue z = PadicInt.toZMod ⟨z, hz⟩ := dif_pos hz
  have r2 : residue w = PadicInt.toZMod ⟨w, hw⟩ := dif_pos hw
  have r3 : residue (z + w) = PadicInt.toZMod ⟨z + w, h⟩ := dif_pos h
  rw [r1, r2, r3, e]
  exact map_add _ _ _

/-- For $\|z\| \le 1$, the residue of $z$ vanishes iff $\|z\| < 1$. -/
lemma residue_eq_zero_iff {z : ℚ_[p]} (hz : ‖z‖ ≤ 1) : residue z = 0 ↔ ‖z‖ < 1 := by
  have r1 : residue z = PadicInt.toZMod ⟨z, hz⟩ := dif_pos hz
  have key : ∀ w : ℤ_[p], PadicInt.toZMod w = 0 ↔ ‖w‖ < 1 := by
    intro w
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  rw [r1]
  exact key ⟨z, hz⟩

/-- The residue only depends on the class modulo elements of norm less than $1$. -/
lemma residue_congr {z w : ℚ_[p]} (hz : ‖z‖ ≤ 1) (h : ‖w - z‖ < 1) : residue w = residue z := by
  have e : w = z + (w - z) := by ring
  have h1 : ‖w - z‖ ≤ 1 := h.le
  rw [e, residue_add hz h1, (residue_eq_zero_iff h1).2 h, add_zero]

/-- Scaling by $p^{-n}$ multiplies the norm by $p^n$. -/
lemma norm_scaled_le (n : ℕ) {m : ℤ} {t : ℚ_[p]} (ht : ‖t‖ ≤ (p : ℝ) ^ m) :
    ‖((p : ℚ_[p]) ^ n)⁻¹ * t‖ ≤ (p : ℝ) ^ ((n : ℤ) + m) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_mul, norm_inv, Padic.norm_p_pow, zpow_add₀ hp.ne', ← zpow_neg, neg_neg, zpow_natCast]
  exact mul_le_mul_of_nonneg_left ht (by positivity)

/-- $\|p^{-n} t\| = p^n \|t\|$. -/
lemma norm_scaled_eq (n : ℕ) (t : ℚ_[p]) :
    ‖((p : ℚ_[p]) ^ n)⁻¹ * t‖ = (p : ℝ) ^ n * ‖t‖ := by
  rw [norm_mul, norm_inv, Padic.norm_p_pow, ← zpow_neg, neg_neg, zpow_natCast]

/-- For $P \in E^1(\mathbb Q_p)$: $\|x'(P)\| < p^{-n}$ iff $\|x'(P)\| \le p^{-(n+1)}$. -/
lemma norm_xPrime_lt_iff {a b : ℤ_[p]} {P : (curveQp a b).toAffine.Point} (hP : P ∈ E1 a b) (n : ℕ) :
    ‖xPrime P‖ < (p : ℝ) ^ (-(n : ℤ)) ↔ ‖xPrime P‖ ≤ (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_cases h0 : P = 0
  · subst h0
    have e0 : xPrime (0 : (curveQp a b).toAffine.Point) = 0 := rfl
    rw [e0, norm_zero]
    exact ⟨fun _ => by positivity, fun _ => by positivity⟩
  · obtain ⟨m, hm, hx⟩ := exists_norm_xPrime hP h0
    rw [hx, zpow_lt_zpow_iff_right₀ hp, zpow_le_zpow_iff_right₀ hp]
    push_cast
    omega

/-- The norm of $1 - w$ is $1$ if $\|w\| < 1$ in $\mathbb Z_p$. -/
lemma norm_one_sub_eq_one {w : ℤ_[p]} (hw : ‖w‖ < 1) : ‖1 - w‖ = 1 := by
  have h1 : ‖(1 : ℤ_[p]) - w‖ ≤ 1 := (1 - w).norm_le_one
  refine le_antisymm h1 ?_
  by_contra h
  push Not at h
  have : ‖(1 : ℤ_[p])‖ ≤ max ‖1 - w‖ ‖w‖ := by
    have := IsUltrametricDist.norm_add_le_max (1 - w) w
    simpa using this
  rw [norm_one] at this
  rcases le_max_iff.1 this with h2 | h2 <;> linarith

/-- In $\mathbb Z_p$, $\|z c\| \le \|z\|$. -/
lemma norm_mul_le_left' (z c : ℤ_[p]) : ‖z * c‖ ≤ ‖z‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) c.norm_le_one

/-- Hensel step: for $u \in \mathbb Z_p$ with $0 < \|u\| < 1$ there is $z \in \mathbb Z_p$ with
$z = u^3 + a u z^2 + b z^3$ and $0 < \|z\| < \|u\|$. -/
lemma exists_hensel_z (a b u : ℤ_[p]) (hu0 : u ≠ 0) (hu1 : ‖u‖ < 1) :
    ∃ z : ℤ_[p], z = u ^ 3 + a * u * z ^ 2 + b * z ^ 3 ∧ z ≠ 0 ∧ ‖z‖ < ‖u‖ := by
  have hu : 0 < ‖u‖ := norm_pos_iff.2 hu0
  let F : Polynomial ℤ_[p] :=
    Polynomial.C (-b) * Polynomial.X ^ 3 + Polynomial.C (-(a * u)) * Polynomial.X ^ 2 + Polynomial.X
      - Polynomial.C (u ^ 3)
  have hev : ∀ z : ℤ_[p], F.aeval z = z - (u ^ 3 + a * u * z ^ 2 + b * z ^ 3) := by
    intro z; simp [F]; ring
  have hder : ∀ z : ℤ_[p], F.derivative.aeval z = 1 - (2 * a * u * z + 3 * b * z ^ 2) := by
    intro z; simp [F, Polynomial.derivative_pow, Polynomial.derivative_C]; ring
  have hZ0 : ‖u ^ 3‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hu1 (by norm_num)
  have hlt : ‖u ^ 3‖ ≤ ‖u‖ := by
    rw [norm_pow]; exact pow_le_of_le_one (norm_nonneg _) hu1.le (by norm_num)
  have hd : ‖F.derivative.aeval (u ^ 3)‖ = 1 := by
    rw [hder]
    apply norm_one_sub_eq_one
    have e : 2 * a * u * u ^ 3 + 3 * b * (u ^ 3) ^ 2 = u ^ 3 * (2 * a * u + 3 * b * u ^ 3) := by ring
    rw [e]
    exact lt_of_le_of_lt (norm_mul_le_left' _ _) hZ0
  have hn : ‖F.aeval (u ^ 3)‖ < ‖F.derivative.aeval (u ^ 3)‖ ^ 2 := by
    rw [hd, hev]
    have e : u ^ 3 - (u ^ 3 + a * u * (u ^ 3) ^ 2 + b * (u ^ 3) ^ 3) =
        u ^ 3 * (-(a * u * u ^ 3 + b * u ^ 6)) := by ring
    rw [e, one_pow]
    exact lt_of_le_of_lt (norm_mul_le_left' _ _) hZ0
  obtain ⟨z, hz0, hzd, -, -⟩ := hensels_lemma hn
  rw [hd] at hzd
  rw [hev] at hz0
  have hzeq : z = u ^ 3 + a * u * z ^ 2 + b * z ^ 3 := by linear_combination hz0
  have hz1 : ‖z‖ < 1 := by
    have : z = (z - u ^ 3) + u ^ 3 := by ring
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hzd hZ0)
  have hzne : z ≠ 0 := by
    rintro rfl
    apply hu0
    have : u ^ 3 = 0 := by linear_combination -hzeq
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  refine ⟨z, hzeq, hzne, ?_⟩
  by_contra hcon
  push Not at hcon
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hzne
  have t1 : ‖u ^ 3‖ ≤ ‖z‖ ^ 3 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hcon 3
  have t2 : ‖a * u * z ^ 2‖ ≤ ‖z‖ ^ 3 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖a‖ * ‖u‖ * ‖z‖ ^ 2 ≤ 1 * ‖z‖ * ‖z‖ ^ 2 := by
          gcongr
          exact a.norm_le_one
      _ = ‖z‖ ^ 3 := by ring
  have t3 : ‖b * z ^ 3‖ ≤ ‖z‖ ^ 3 := by
    rw [norm_mul, norm_pow]
    calc ‖b‖ * ‖z‖ ^ 3 ≤ 1 * ‖z‖ ^ 3 := by gcongr; exact b.norm_le_one
      _ = ‖z‖ ^ 3 := one_mul _
  have t4 : ‖z‖ ≤ ‖z‖ ^ 3 := by
    calc ‖z‖ = ‖u ^ 3 + a * u * z ^ 2 + b * z ^ 3‖ := by rw [← hzeq]
      _ ≤ max ‖u ^ 3 + a * u * z ^ 2‖ ‖b * z ^ 3‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖z‖ ^ 3 := max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le t1 t2)) t3
  have : ‖z‖ ^ 3 < ‖z‖ := by
    calc ‖z‖ ^ 3 < ‖z‖ ^ 1 := pow_lt_pow_right_of_lt_one₀ hzpos hz1 (by norm_num)
      _ = ‖z‖ := pow_one _
  linarith

/-- Construction of points: for $u \in \mathbb Z_p$ with $0 < \|u\| < 1$ there is a point $P \in E^1(\mathbb Q_p)$
with $x'(P) = u$ (Hensel's lemma applied to $Z = u^3 + auZ^2 + bZ^3$). -/
lemma exists_point_xPrime (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (u : ℤ_[p]) (hu0 : u ≠ 0)
    (hu1 : ‖u‖ < 1) :
    ∃ P : (curveQp a b).toAffine.Point, P ∈ E1 a b ∧ xPrime P = (u : ℚ_[p]) := by
  obtain ⟨z, hz, hz0, hzu⟩ := exists_hensel_z a b u hu0 hu1
  have hzq : (z : ℚ_[p]) = (u : ℚ_[p]) ^ 3 + a * u * (z : ℚ_[p]) ^ 2 + b * (z : ℚ_[p]) ^ 3 := by
    have h := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hz
    simpa using h
  have hz0q : (z : ℚ_[p]) ≠ 0 := fun h => hz0 (PadicInt.coe_eq_zero.1 h)
  have hΔq : 4 * (a : ℚ_[p]) ^ 3 + 27 * (b : ℚ_[p]) ^ 2 ≠ 0 := by
    intro h
    apply hΔ
    have h' : ((4 * a ^ 3 + 27 * b ^ 2 : ℤ_[p]) : ℚ_[p]) = 0 := by push_cast; exact h
    exact PadicInt.coe_eq_zero.1 h'
  haveI : (curveQp a b).IsElliptic := (isElliptic_shortCurve_iff _ _).2 hΔq
  have heq : (curveQp a b).toAffine.Equation ((u : ℚ_[p]) / z) (1 / z) := by
    rw [Affine.equation_iff]
    simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, shortCurve_a₆]
    field_simp
    linear_combination hzq
  have hns := (Affine.equation_iff_nonsingular).1 heq
  refine ⟨Affine.Point.some _ _ hns, (mem_E1_iff _).2 (Or.inr ⟨_, _, hns, rfl, ?_⟩), ?_⟩
  · rw [norm_div]
    exact (one_lt_div (norm_pos_iff.2 hz0q)).2 hzu
  · simp only [xPrime]
    field_simp

/-- **Theorem 4.1 (c)** (pdf p. 70). For $n \ge 1$, $E^n(\mathbb Q_p)$ is a subgroup of $E(\mathbb Q_p)$, and
$P \mapsto p^{-n}x(P)/y(P) \bmod p$ is a surjective homomorphism $E^n(\mathbb Q_p) \to \mathbb F_p$ with kernel
$E^{n+1}(\mathbb Q_p)$, i.e. an isomorphism $E^n(\mathbb Q_p)/E^{n+1}(\mathbb Q_p) \cong \mathbb F_p$. -/
@[kb "milne2006ec" "Ch. II, Theorem 4.1 (c), pdf p. 70"]
theorem theorem_4_1_c (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : EnSubgroup a b n hn →+ ZMod p,
      (∀ P : EnSubgroup a b n hn, φ P = residue (((p : ℚ_[p]) ^ n)⁻¹ * xPrime (P : (curveQp a b).toAffine.Point))) ∧
      Function.Surjective φ ∧ ∀ P : EnSubgroup a b n hn, φ P = 0 ↔ (P : (curveQp a b).toAffine.Point) ∈ En a b (n + 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  -- the scaled coordinate has norm at most one on `E^n`
  have hle : ∀ P : (curveQp a b).toAffine.Point, P ∈ En a b n →
      ‖((p : ℚ_[p]) ^ n)⁻¹ * xPrime P‖ ≤ 1 := by
    intro P hP
    have := norm_scaled_le n hP.2
    simpa using this
  have hadd : ∀ P Q : EnSubgroup a b n hn,
      residue (((p : ℚ_[p]) ^ n)⁻¹ * xPrime ((P + Q : EnSubgroup a b n hn) : (curveQp a b).toAffine.Point)) =
      residue (((p : ℚ_[p]) ^ n)⁻¹ * xPrime (P : (curveQp a b).toAffine.Point)) +
      residue (((p : ℚ_[p]) ^ n)⁻¹ * xPrime (Q : (curveQp a b).toAffine.Point)) := by
    intro P Q
    have hP : (P : (curveQp a b).toAffine.Point) ∈ En a b n := P.2
    have hQ : (Q : (curveQp a b).toAffine.Point) ∈ En a b n := Q.2
    rw [← residue_add (hle _ hP) (hle _ hQ)]
    apply residue_congr (by exact (Padic.nonarchimedean _ _).trans (max_le (hle _ hP) (hle _ hQ)))
    have := norm_scaled_le n (norm_xPrime_add_sub_le hn hP hQ)
    have e : ((p : ℚ_[p]) ^ n)⁻¹ * xPrime ((P + Q : EnSubgroup a b n hn) : (curveQp a b).toAffine.Point) -
        (((p : ℚ_[p]) ^ n)⁻¹ * xPrime (P : (curveQp a b).toAffine.Point) +
          ((p : ℚ_[p]) ^ n)⁻¹ * xPrime (Q : (curveQp a b).toAffine.Point)) =
        ((p : ℚ_[p]) ^ n)⁻¹ * (xPrime ((P : (curveQp a b).toAffine.Point) + (Q : (curveQp a b).toAffine.Point)) -
          (xPrime (P : (curveQp a b).toAffine.Point) + xPrime (Q : (curveQp a b).toAffine.Point))) := by
      have hc : ((P + Q : EnSubgroup a b n hn) : (curveQp a b).toAffine.Point) =
          (P : (curveQp a b).toAffine.Point) + (Q : (curveQp a b).toAffine.Point) := rfl
      rw [hc]
      ring
    rw [e]
    refine lt_of_le_of_lt this ?_
    exact zpow_lt_one_of_neg₀ hp (by omega)
  have hker : ∀ P : EnSubgroup a b n hn,
      residue (((p : ℚ_[p]) ^ n)⁻¹ * xPrime (P : (curveQp a b).toAffine.Point)) = 0 ↔
        (P : (curveQp a b).toAffine.Point) ∈ En a b (n + 1) := by
    intro P
    have hP : (P : (curveQp a b).toAffine.Point) ∈ En a b n := P.2
    rw [residue_eq_zero_iff (hle _ hP), norm_scaled_eq]
    constructor
    · intro h
      have h1 : ‖xPrime (P : (curveQp a b).toAffine.Point)‖ < (p : ℝ) ^ (-(n : ℤ)) := by
        have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
        rw [zpow_neg, zpow_natCast]
        calc ‖xPrime (P : (curveQp a b).toAffine.Point)‖
            = ((p : ℝ) ^ n)⁻¹ * ((p : ℝ) ^ n * ‖xPrime (P : (curveQp a b).toAffine.Point)‖) := by
              field_simp
          _ < ((p : ℝ) ^ n)⁻¹ * 1 := mul_lt_mul_of_pos_left h (by positivity)
          _ = ((p : ℝ) ^ n)⁻¹ := mul_one _
      exact ⟨hP.1, (norm_xPrime_lt_iff hP.1 n).1 h1⟩
    · intro h
      have h1 := (norm_xPrime_lt_iff hP.1 n).2 h.2
      have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
      rw [zpow_neg, zpow_natCast] at h1
      calc (p : ℝ) ^ n * ‖xPrime (P : (curveQp a b).toAffine.Point)‖ < (p : ℝ) ^ n * ((p : ℝ) ^ n)⁻¹ :=
            mul_lt_mul_of_pos_left h1 hpn
        _ = 1 := mul_inv_cancel₀ hpn.ne'
  refine ⟨AddMonoidHom.mk' (fun P => residue (((p : ℚ_[p]) ^ n)⁻¹ * xPrime (P : (curveQp a b).toAffine.Point))) hadd,
    fun P => rfl, ?_, fun P => hker P⟩
  intro t
  obtain ⟨τ, hτ⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) t
  by_cases hτ0 : τ = 0
  · refine ⟨0, ?_⟩
    subst hτ0
    rw [map_zero] at hτ
    subst hτ
    have e0 : xPrime (0 : (curveQp a b).toAffine.Point) = 0 := rfl
    show residue (_ * xPrime (0 : (curveQp a b).toAffine.Point)) = 0
    rw [e0, mul_zero, residue_eq_zero_iff (by simp)]
    simp
  · set u : ℤ_[p] := (p : ℤ_[p]) ^ n * τ with hu
    have huq : (u : ℚ_[p]) = (p : ℚ_[p]) ^ n * τ := by simp [hu]
    have hnorm : ‖(u : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      rw [huq, norm_mul, Padic.norm_p_pow]
      exact mul_le_of_le_one_right (by positivity) τ.norm_le_one
    have hu0 : u ≠ 0 := by
      intro h
      rw [hu] at h
      rcases mul_eq_zero.1 h with h | h
      · exact (pow_ne_zero n (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) h
      · exact hτ0 h
    have hu1 : ‖u‖ < 1 := by
      refine lt_of_le_of_lt hnorm ?_
      exact zpow_lt_one_of_neg₀ hp (by omega)
    obtain ⟨P, hP1, hPx⟩ := exists_point_xPrime a b hΔ u hu0 hu1
    have hPn : P ∈ En a b n := ⟨hP1, by rw [hPx]; exact hnorm⟩
    refine ⟨⟨P, hPn⟩, ?_⟩
    show residue (((p : ℚ_[p]) ^ n)⁻¹ * xPrime P) = t
    rw [hPx, huq, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (by exact_mod_cast (Fact.out : p.Prime).ne_zero)),
      one_mul, residue_coe, hτ]

/-- **Theorem 4.1 (d)** (pdf p. 70): the filtration is exhaustive, $\bigcap_n E^n(\mathbb Q_p) = \{O\}$. -/
@[kb "milne2006ec" "Ch. II, Theorem 4.1 (d), pdf p. 70"]
theorem theorem_4_1_d (a b : ℤ_[p]) (P : (curveQp a b).toAffine.Point) :
    (∀ n, 1 ≤ n → P ∈ En a b n) ↔ P = 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨fun h => ?_, fun h n _ => h ▸ zero_mem_En a b n⟩
  by_contra h0
  have h1 : P ∈ E1 a b := (h 1 le_rfl).1
  obtain ⟨n, hn, hx⟩ := exists_norm_xPrime h1 h0
  have := (h (n + 1) (by omega)).2
  rw [hx, zpow_le_zpow_iff_right₀ hp] at this
  push_cast at this
  omega

/-- **Theorem 4.1 (a)** (pdf p. 70), as a named statement: $E^0(\mathbb Q_p)$ is a subgroup of finite index in
$E(\mathbb Q_p)$. (Milne's proof: $E(\mathbb Q_p)$ is compact and $E^0(\mathbb Q_p)$ is open.) -/
@[kb "milne2006ec" "Ch. II, Theorem 4.1 (a), pdf p. 70"]
structure Theorem4_1a : Prop where
  finite : ∀ (p : ℕ) [Fact p.Prime] (a b : ℤ_[p]), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ∃ G : AddSubgroup (curveQp a b).toAffine.Point, (G : Set (curveQp a b).toAffine.Point) = E0 a b ∧
      G.FiniteIndex

/-- **Theorem 4.1 (b)** (pdf p. 70), as a named statement: $E^0(\mathbb Q_p)$ is a subgroup (p. 69: a line through
two points with nonsingular reduction meets the cubic again in such a point), and $P \mapsto \bar P$ is a
surjective homomorphism $E^0(\mathbb Q_p) \to \bar E^{ns}(\mathbb F_p)$ with kernel $E^1(\mathbb Q_p)$ (surjective
by Hensel's lemma), i.e. $E^0(\mathbb Q_p)/E^1(\mathbb Q_p) \cong \bar E^{ns}(\mathbb F_p)$. -/
@[kb "milne2006ec" "Ch. II, Theorem 4.1 (b), pdf p. 70"]
structure Theorem4_1b : Prop where
  iso : ∀ (p : ℕ) [Fact p.Prime] (a b : ℤ_[p]), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ∃ G : AddSubgroup (curveQp a b).toAffine.Point, (G : Set (curveQp a b).toAffine.Point) = E0 a b ∧
      ∃ ρ : G →+ (curveFp a b).toAffine.Point,
        (∀ P : G, toProjCoords (ρ P) = reducePoint (P : (curveQp a b).toAffine.Point)) ∧
        Function.Surjective ρ ∧ ∀ P : G, ρ P = 0 ↔ (P : (curveQp a b).toAffine.Point) ∈ E1 a b

/-- **Corollary 4.2** (pdf p. 71), injectivity: for $m$ not divisible by $p$, $P \mapsto mP$ is injective on
$E^1(\mathbb Q_p)$. -/
@[kb "milne2006ec" "Ch. II, Corollary 4.2, pdf p. 71"]
theorem corollary_4_2_injective (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {m : ℤ} (hm : ¬(p : ℤ) ∣ m)
    {P : (curveQp a b).toAffine.Point} (hP : P ∈ E1 a b) (hmP : m • P = 0) : P = 0 := by
  by_contra h0
  have hc : ¬ p ∣ m.natAbs := fun h => hm (Int.natCast_dvd.2 h)
  have hnorm : ‖((m.natAbs : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hc)
  refine nsmul_ne_zero_of_E1 hP h0 (c := m.natAbs) (by rw [hnorm]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)) ?_
  rcases Int.natAbs_eq m with h | h
  · rw [← natCast_zsmul, ← h]; exact hmP
  · have : (-m) • P = 0 := by rw [neg_smul, hmP, neg_zero]
    rw [← natCast_zsmul, ← neg_eq_iff_eq_neg.2 h]
    exact this

/-- **Corollary 4.2** (pdf p. 71), as a named statement: for every integer $m$ not divisible by $p$,
$P \mapsto mP$ is a bijection $E^1(\mathbb Q_p) \to E^1(\mathbb Q_p)$. Injectivity is
`corollary_4_2_injective`; Milne's proof of surjectivity sums a convergent series in the compact group
$E(\mathbb Q_p)$. -/
@[kb "milne2006ec" "Ch. II, Corollary 4.2, pdf p. 71"]
structure Corollary4_2 : Prop where
  bij : ∀ (p : ℕ) [Fact p.Prime] (a b : ℤ_[p]), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → ∀ m : ℤ, ¬(p : ℤ) ∣ m →
    Set.BijOn (fun P : (curveQp a b).toAffine.Point => m • P) (E1 a b) (E1 a b)

/-- **Proposition 5.4** (pdf p. 73): the group $E^1(\mathbb Q_p)$ is torsion-free. -/
@[kb "milne2006ec" "Ch. II, Proposition 5.4, pdf p. 73"]
theorem proposition_5_4 (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {P : (curveQp a b).toAffine.Point}
    (hP : P ∈ E1 a b) {m : ℕ} (hm : 0 < m) (hmP : m • P = 0) : P = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_contra h0
  -- p^k • P is a nonzero point of E1 for every k
  have key : ∀ k : ℕ, p ^ k • P ∈ E1 a b ∧ p ^ k • P ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨hP, h0⟩
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [pow_succ, mul_comm, mul_nsmul']
        have := (nsmul_mem_En_xPrime le_rfl (show p ^ k • P ∈ En a b 1 by rwa [En_one]) p).1
        rwa [En_one] at this
      · rw [pow_succ, mul_comm, mul_nsmul']
        refine nsmul_ne_zero_of_E1 h1 h2 ?_
        rw [Padic.norm_p]
  obtain ⟨k, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p (Fact.out : p.Prime).ne_one
  obtain ⟨h1, h2⟩ := key k
  have hnorm : ‖((m' : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm')
  refine nsmul_ne_zero_of_E1 h1 h2 (c := m') (by rw [hnorm]; exact inv_le_one_of_one_le₀ hp1.le) ?_
  rw [← mul_nsmul', mul_comm]
  simpa [mul_comm] using hmP

/-- **Corollary 5.5** (pdf p. 74): if $P = (x : y : 1) \in E(\mathbb Q_p)$ is a torsion point then
$x, y \in \mathbb Z_p$. -/
@[kb "milne2006ec" "Ch. II, Corollary 5.5, pdf p. 74"]
theorem corollary_5_5 (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {x y : ℚ_[p]}
    {h : (curveQp a b).toAffine.Nonsingular x y} (htors : IsOfFinAddOrder (Affine.Point.some x y h)) :
    ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 := by
  have hx : ‖x‖ ≤ 1 := by
    by_contra hx
    push_neg at hx
    have hE : Affine.Point.some x y h ∈ E1 a b := (mem_E1_iff _).2 (Or.inr ⟨x, y, h, rfl, hx⟩)
    obtain ⟨m, hm, hmP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 htors
    exact Affine.Point.some_ne_zero h (proposition_5_4 a b hΔ hE hm hmP)
  exact ⟨hx, norm_y_le_one (norm_coe_le_one a) (norm_coe_le_one b) hx (shortCurve_equation h.1)⟩

end NumberFieldKB.MilneEC.II
