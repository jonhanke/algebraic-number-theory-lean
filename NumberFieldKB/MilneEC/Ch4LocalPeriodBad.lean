import NumberFieldKB.MilneEC.Ch4LocalPeriod
import NumberFieldKB.MilneEC.Ch4Tamagawa

/-!
# Milne, *Elliptic Curves*, Remark IV.10.6 at bad reduction: the measure of $E_0(\mathbb Q_p)$

J. S. Milne, *Elliptic Curves* (2006; `milne2006ec`), Chapter IV, Remark 10.6, pdf p. 173. Milne's argument for
$\int_{E(\mathbb Q_p)}|\omega|_p = c_p N_p/p$ has two steps:

1. $|\omega|_p$ is invariant under translation by $E(\mathbb Q_p)$, and $E(\mathbb Q_p)$ is the disjoint union of
   the $c_p$ translates of the subgroup $E_0(\mathbb Q_p)$ of points with non-singular reduction, so
   $\int_{E(\mathbb Q_p)} = c_p\int_{E_0(\mathbb Q_p)}$;
2. $\int_{E_0(\mathbb Q_p)}|\omega|_p = N_p/p$, $N_p = \#\tilde E_{ns}(\mathbb F_p)$ (through
   $E_0/E_1 \cong \tilde E_{ns}(\mathbb F_p)$ and the formal group $E_1 \cong p\mathbb Z_p$).

This file proves step 2 for $p$ odd, at **every** reduction type, on the $x$-line model of the measure
(`omegaVolume`, Ch4LocalPeriod.lean): residue disc by residue disc, a non-singular point of the reduction
contributes $1/p$, the point at infinity (the region $|x|_p > 1$) contributes $1/p$, and the disc over the singular
point is exactly the complement of $E_0(\mathbb Q_p)$.

## Main results
* `GoodFibre`, `zeroComponentX`: the set of $x$-coordinates of the affine points of $E_0(\mathbb Q_p)$: $|x|_p > 1$,
  or $x \in \mathbb Z_p$ and every point of the reduction over $\bar x$ is non-singular.
* `card_point_eq_goodFibre`: for a Weierstrass cubic $V$ over $\mathbb F_p$, $p$ odd, possibly singular,
  $\#V_{ns}(\mathbb F_p) = 1 + \sum_{\bar x \text{ good}} \#\{v : v^2 = \Psi_2^2(\bar x)\}$.
* `omegaVolume_zeroComponent`: **step 2**, $\int_{E_0(\mathbb Q_p)}|\omega|_p = N_p/p$, $p$ odd, every minimal
  equation (indeed every integral one).
-/

open MeasureTheory QuadFormsKB.Analysis Polynomial
open scoped ENNReal

namespace NumberFieldKB.MilneEC.LocalPeriod

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Fibres of the reduction -/

/-- Every point of the Weierstrass cubic `V` with first coordinate `a` is non-singular. -/
def GoodFibre {k : Type*} [CommRing k] (V : WeierstrassCurve k) (a : k) : Prop :=
  ∀ b, V.toAffine.Equation a b → V.toAffine.Nonsingular a b

lemma psi_eq_zero_of_singular {k : Type*} [CommRing k] (V : WeierstrassCurve k) {a b : k}
    (he : V.toAffine.Equation a b) (hns : ¬ V.toAffine.Nonsingular a b) :
    V.a₁ * b - (3 * a ^ 2 + 2 * V.a₂ * a + V.a₄) = 0 ∧ 2 * b + V.a₁ * a + V.a₃ = 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  push Not at hns
  exact hns he

lemma eval_derivative_Ψ₂Sq {k : Type*} [CommRing k] (V : WeierstrassCurve k) (a : k) :
    V.Ψ₂Sq.derivative.eval a = 12 * a ^ 2 + 2 * V.b₂ * a + 2 * V.b₄ := by
  simp [WeierstrassCurve.Ψ₂Sq]
  ring

/-- On a fibre with a singular point (characteristic not 2) every point is that singular point. -/
lemma eq_of_singular (hp2 : p ≠ 2) (V : WeierstrassCurve (ZMod p)) {a b₀ b : ZMod p}
    (he₀ : V.toAffine.Equation a b₀) (hns : ¬ V.toAffine.Nonsingular a b₀) (he : V.toAffine.Equation a b) :
    b = b₀ := by
  have h2 := two_ne_zero_zmod hp2
  have hψ₀ := (psi_eq_zero_of_singular V he₀ hns).2
  have hF : V.Ψ₂Sq.eval a = 0 := by
    rw [← (equation_iff_sq hp2 V a b₀).mp he₀, hψ₀]; ring
  have hψ : (2 * b + V.a₁ * a + V.a₃) ^ 2 = 0 := by rw [(equation_iff_sq hp2 V a b).mp he, hF]
  have hψ' : 2 * b + V.a₁ * a + V.a₃ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hψ
  have : 2 * (b - b₀) = 0 := by linear_combination hψ' - hψ₀
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)

open scoped Classical in
/-- The number of non-singular points over `a` ($p$ odd): the number of square roots of $\Psi_2^2(a)$ on a good
fibre, and $0$ on the fibre of the singular point. -/
lemma card_nonsingular_fibre (hp2 : p ≠ 2) (V : WeierstrassCurve (ZMod p)) (a : ZMod p) :
    Nat.card {b : ZMod p // V.toAffine.Nonsingular a b} =
      if GoodFibre V a then Nat.card {v : ZMod p // v ^ 2 = V.Ψ₂Sq.eval a} else 0 := by
  have h2 := two_ne_zero_zmod hp2
  split_ifs with hg
  · have e1 : {b : ZMod p // V.toAffine.Nonsingular a b} ≃ {b : ZMod p // V.toAffine.Equation a b} :=
      Equiv.subtypeEquivRight fun b => ⟨fun h => h.1, fun h => hg b h⟩
    rw [Nat.card_congr e1]
    refine Nat.card_congr (Equiv.subtypeEquiv
      ((Equiv.mulLeft₀ 2 h2).trans (Equiv.addRight (V.a₁ * a + V.a₃))) ?_)
    intro y
    rw [equation_iff_sq hp2]
    simp [add_assoc]
  · unfold GoodFibre at hg
    push Not at hg
    obtain ⟨b₀, he₀, hns⟩ := hg
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨b, hb⟩
    have := eq_of_singular hp2 V he₀ hns hb.1
    subst this
    exact hns hb

/-- Points of a Weierstrass cubic (possibly singular) in affine coordinates, with the point at infinity. -/
def pointEquivOptionNS (V : WeierstrassCurve (ZMod p)) :
    V.toAffine.Point ≃ Option {xy : ZMod p × ZMod p // V.toAffine.Nonsingular xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h⟩
  invFun
    | none => .zero
    | some ⟨_, h⟩ => WeierstrassCurve.Affine.Point.some _ _ h
  left_inv := by
    intro P; cases P <;> rfl
  right_inv := by
    intro P; rcases P with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

open scoped Classical in
/-- **Non-singular points of a Weierstrass cubic over $\mathbb F_p$** ($p$ odd, singular or not):
$\#V_{ns}(\mathbb F_p) = 1 + \sum_{\bar x \text{ good}}\#\{v : v^2 = \Psi_2^2(\bar x)\}$. -/
theorem card_point_eq_goodFibre (hp2 : p ≠ 2) (V : WeierstrassCurve (ZMod p)) :
    Nat.card V.toAffine.Point = 1 + ∑ a : ZMod p,
      if GoodFibre V a then Nat.card {v : ZMod p // v ^ 2 = V.Ψ₂Sq.eval a} else 0 := by
  rw [Nat.card_congr (pointEquivOptionNS V), Finite.card_option,
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y : ZMod p => V.toAffine.Nonsingular x y)), Nat.card_sigma, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun a _ => card_nonsingular_fibre hp2 V a

/-- On a good fibre the cubic $\Psi_2^2$ is a unit or has a simple root modulo $p$ ($p$ odd). -/
lemma unit_or_simple_of_goodFibre (hp2 : p ≠ 2) (Wi : WeierstrassCurve ℤ_[p]) (x₀ : ℤ_[p])
    (hg : GoodFibre (Wi.map (PadicInt.toZMod (p := p))) (PadicInt.toZMod x₀)) :
    IsUnit (Wi.Ψ₂Sq.eval x₀) ∨ IsUnit (Wi.Ψ₂Sq.derivative.eval x₀) := by
  set V := Wi.map (PadicInt.toZMod (p := p))
  have hF : Wi.Ψ₂Sq.map (PadicInt.toZMod (p := p)) = V.Ψ₂Sq := by
    rw [WeierstrassCurve.map_Ψ₂Sq]
  have h2 := two_ne_zero_zmod hp2
  by_cases h0 : PadicInt.toZMod (Wi.Ψ₂Sq.eval x₀) = 0
  · right
    rw [isUnit_iff_toZMod_ne, toZMod_eval, ← Polynomial.derivative_map, hF, eval_derivative_Ψ₂Sq]
    rw [toZMod_eval, hF] at h0
    set a := PadicInt.toZMod x₀
    obtain ⟨b, hψ⟩ : ∃ b : ZMod p, 2 * b + V.a₁ * a + V.a₃ = 0 :=
      ⟨-(V.a₁ * a + V.a₃) / 2, by field_simp; ring⟩
    have he : V.toAffine.Equation a b := by
      rw [equation_iff_sq hp2, hψ, h0]; ring
    have hns := (WeierstrassCurve.Affine.nonsingular_iff' _ _).mp (hg b he)
    have hX : V.a₁ * b - (3 * a ^ 2 + 2 * V.a₂ * a + V.a₄) ≠ 0 := by
      rcases hns.2 with h | h
      · exact h
      · exact absurd hψ h
    intro hd
    apply hX
    have h4 : (4 : ZMod p) ≠ 0 := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄] at hd
    linear_combination (-1 : ZMod p) * hd + 2 * V.a₁ * hψ
  · left
    exact (isUnit_iff_toZMod_ne _).mpr h0

/-! ## The $x$-coordinates of $E_0(\mathbb Q_p)$ -/

/-- The reduction modulo $p$ of the integral model of `W`, over `ZMod p`. -/
noncomputable def reductionZMod (W : WeierstrassCurve ℚ_[p]) [W.IsIntegral ℤ_[p]] :
    WeierstrassCurve (ZMod p) :=
  (W.integralModel ℤ_[p]).map (PadicInt.toZMod (p := p))

/-- **The $x$-coordinates of the affine points of $E_0(\mathbb Q_p)$**: $|x|_p > 1$ (the kernel of reduction), or
$x \in \mathbb Z_p$ and every point of the reduction over $\bar x$ is non-singular. (Over the $x$-coordinate of the
singular point the only point of the reduction is the singular point itself, so this is the image of
$E_0(\mathbb Q_p)$ under $x$; see `mem_zeroComponentX_iff`.) -/
def zeroComponentX (W : WeierstrassCurve ℚ_[p]) [W.IsIntegral ℤ_[p]] : Set ℚ_[p] :=
  {x | 1 < ‖x‖ ∨ ∃ X : ℤ_[p], (X : ℚ_[p]) = x ∧ GoodFibre (reductionZMod W) (PadicInt.toZMod X)}

lemma toZMod_natCast (j : ℕ) : PadicInt.toZMod ((j : ℤ_[p])) = (j : ZMod p) := map_natCast _ j

open scoped Classical in
lemma zeroComponentX_eq (W : WeierstrassCurve ℚ_[p]) [W.IsIntegral ℤ_[p]] :
    zeroComponentX W = {x : ℚ_[p] | 1 < ‖x‖} ∪
      ⋃ j : Fin p, if GoodFibre (reductionZMod W) ((j : ℕ) : ZMod p) then
        Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹ else ∅ := by
  ext x
  simp only [zeroComponentX, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro (hx | ⟨X, rfl, hg⟩)
    · exact Or.inl hx
    · right
      obtain ⟨j, hj⟩ := exists_fin_close X
      have hball : (X : ℚ_[p]) ∈ Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹ := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have := (norm_sub_nat_le_iff X j).mpr hj
        simpa [zpow_neg_one] using this
      have hXj : PadicInt.toZMod X = ((j : ℕ) : ZMod p) := by
        rw [← toZMod_natCast]
        exact toZMod_eq_of_close (ball_subset_int _ hball).2
      refine ⟨j, ?_⟩
      rw [← hXj]
      simp only [hg, ↓reduceIte]
      exact hball
  · rintro (hx | ⟨j, hj⟩)
    · exact Or.inl hx
    · right
      split_ifs at hj with hg
      · obtain ⟨h1, h2⟩ := ball_subset_int _ hj
        refine ⟨⟨x, h1⟩, rfl, ?_⟩
        have : PadicInt.toZMod (⟨x, h1⟩ : ℤ_[p]) = ((j : ℕ) : ZMod p) := by
          rw [← toZMod_natCast]; exact toZMod_eq_of_close h2
        rw [this]; exact hg
      · exact absurd hj (Set.notMem_empty _)

lemma reductionZMod_eq_reduction (W : WeierstrassCurve ℚ_[p]) [W.IsMinimal ℤ_[p]] :
    reductionZMod W = (W.reduction ℤ_[p]).map (PadicInt.residueField (p := p) : _ →+* ZMod p) := by
  rw [WeierstrassCurve.reduction, WeierstrassCurve.map_map, reductionZMod]
  rfl

/-- **Milne's step 2, $p$ odd, every reduction type**: on a minimal equation,
$\int_{E_0(\mathbb Q_p)}|\omega|_p = N_p/p$ with $N_p = \#\tilde E_{ns}(\mathbb F_p)$ (Mathlib's `Point` type of
the reduction consists of its non-singular points): the region $|x|_p > 1$ gives $1/p$ and each good residue disc
gives (number of non-singular points over it)$/p$. -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (a), the measure of E_0(Q_p) is N_p/p (every reduction type, p odd), pdf p. 173"]
theorem omegaVolume_zeroComponent (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) [W.IsMinimal ℤ_[p]] :
    ∫⁻ x in zeroComponentX W, omegaDensity W x ∂haarP p =
      (Nat.card (W.reduction ℤ_[p]).toAffine.Point : ℝ≥0∞) / p := by
  classical
  set Wi : WeierstrassCurve ℤ_[p] := WeierstrassCurve.integralModel ℤ_[p] W with hWi
  have hW : W = Wi.map (algebraMap ℤ_[p] ℚ_[p]) :=
    (WeierstrassCurve.baseChange_integralModel_eq ℤ_[p] W).symm
  have hΨ : W.Ψ₂Sq = Wi.Ψ₂Sq.map (algebraMap ℤ_[p] ℚ_[p]) := by
    have := congrArg WeierstrassCurve.Ψ₂Sq hW
    rwa [WeierstrassCurve.map_Ψ₂Sq] at this
  set V := reductionZMod W with hV
  have hcard : Nat.card (W.reduction ℤ_[p]).toAffine.Point = Nat.card V.toAffine.Point := by
    rw [hV, reductionZMod_eq_reduction]
    exact (card_point_map_equiv (PadicInt.residueField (p := p)) _).symm
  have hF : Wi.Ψ₂Sq.map (PadicInt.toZMod (p := p)) = V.Ψ₂Sq := by
    rw [hV, reductionZMod, WeierstrassCurve.map_Ψ₂Sq]
  obtain ⟨hdeg, hlead⟩ := natDegree_Ψ₂Sq_int hp2 Wi
  have hmeasB : ∀ j : Fin p, MeasurableSet (if GoodFibre V ((j : ℕ) : ZMod p) then
      Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹ else ∅) := by
    intro j; split_ifs
    · exact Metric.isClosed_closedBall.measurableSet
    · exact MeasurableSet.empty
  have hdisj : Pairwise (Function.onFun Disjoint fun j : Fin p =>
      if GoodFibre V ((j : ℕ) : ZMod p) then
        Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹ else ∅) := by
    intro i j hij
    have := balls_disjoint (p := p) hij
    simp only [Function.onFun] at this ⊢
    split_ifs
    · exact this
    all_goals simp
  have hdisjO : Disjoint {x : ℚ_[p] | 1 < ‖x‖} (⋃ j : Fin p,
      if GoodFibre V ((j : ℕ) : ZMod p) then
        Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹ else ∅) := by
    refine Set.disjoint_of_subset_right ?_ (balls_disjoint_outside (p := p))
    refine Set.iUnion_mono fun j => ?_
    split_ifs
    · exact le_rfl
    · exact Set.empty_subset _
  unfold omegaDensity
  rw [zeroComponentX_eq, hΨ, lintegral_union (MeasurableSet.iUnion hmeasB) hdisjO,
    lintegral_sqrtDensity_outside_aux hp2 Wi.Ψ₂Sq hdeg hlead,
    lintegral_iUnion hmeasB hdisj, tsum_fintype]
  have hterm : ∀ j : Fin p,
      ∫⁻ x in (if GoodFibre V ((j : ℕ) : ZMod p) then
        Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹ else ∅),
        sqrtDensity (Wi.Ψ₂Sq.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      ((if GoodFibre V ((j : ℕ) : ZMod p) then
        Nat.card {v : ZMod p // v ^ 2 = V.Ψ₂Sq.eval ((j : ℕ) : ZMod p)} else 0 : ℕ) : ℝ≥0∞) / p := by
    intro j
    split_ifs with hg
    · have hg' : GoodFibre (Wi.map (PadicInt.toZMod (p := p))) (PadicInt.toZMod ((j : ℕ) : ℤ_[p])) := by
        rw [toZMod_natCast]; exact hg
      rw [lintegral_ball_aux hp2 Wi.Ψ₂Sq _ (unit_or_simple_of_goodFibre hp2 Wi _ hg'), toZMod_eval,
        map_natCast, hF]
    · simp
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [sum_fin_zmod (fun a : ZMod p => (((if GoodFibre V a then
    Nat.card {v : ZMod p // v ^ 2 = V.Ψ₂Sq.eval a} else 0 : ℕ)) : ℝ≥0∞) / p)]
  rw [hcard, card_point_eq_goodFibre hp2 V, Nat.cast_add, Nat.cast_one, Nat.cast_sum, ENNReal.add_div]
  congr 1
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-! ## $E_0(\mathbb Q_p)$ in Formal Conjectures' sense has $x$-coordinates `zeroComponentX` (every $p$) -/

/-- On a fibre containing a singular point, that point is the only point (any characteristic): if
$2b_0 + a_1a + a_3 = 0$ then the equation at $b$ minus the equation at $b_0$ is $(b - b_0)^2 = 0$. -/
lemma eq_of_singular' {k : Type*} [CommRing k] [IsDomain k] (V : WeierstrassCurve k) {a b₀ b : k}
    (he₀ : V.toAffine.Equation a b₀) (hns : ¬ V.toAffine.Nonsingular a b₀) (he : V.toAffine.Equation a b) :
    b = b₀ := by
  have hψ₀ := (psi_eq_zero_of_singular V he₀ hns).2
  rw [WeierstrassCurve.Affine.equation_iff] at he₀ he
  have : (b - b₀) ^ 2 = 0 := by linear_combination he - he₀ - (b - b₀) * hψ₀
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

/-- A point over $\bar x$ is non-singular iff the whole fibre over $\bar x$ is. -/
lemma goodFibre_iff_nonsingular {k : Type*} [CommRing k] [IsDomain k] (V : WeierstrassCurve k) {a b : k}
    (he : V.toAffine.Equation a b) : GoodFibre V a ↔ V.toAffine.Nonsingular a b := by
  refine ⟨fun hg => hg b he, fun hn b' he' => ?_⟩
  by_contra hns
  have := eq_of_singular' V he' hns he
  subst this
  exact hns hn

lemma norm_le_one_iff_exists (x : ℚ_[p]) : ‖x‖ ≤ 1 ↔ ∃ a : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] a = x :=
  ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩

open WeierstrassCurve WeierstrassCurve.Projective FormalConjectures in
/-- **`zeroComponentX` is the set of $x$-coordinates of $E_0(\mathbb Q_p)$** (every prime): an affine point
$P = (x, y)$ of a minimal equation lies in Formal Conjectures' `nonsingularReduction` (the set whose translates
`tamagawaNumber` counts) iff $x \in$ `zeroComponentX W`. -/
theorem mem_nonsingularReduction_iff_mem_zeroComponentX (W : WeierstrassCurve ℚ_[p]) [W.IsMinimal ℤ_[p]]
    (P : ((W.integralModel ℤ_[p]).toProjective⁄ℚ_[p]).Point) (x y : ℚ_[p])
    (h : ((W.integralModel ℤ_[p])⁄ℚ_[p]).toAffine.Nonsingular x y)
    (hP : WeierstrassCurve.Projective.Point.toAffineLift P = WeierstrassCurve.Affine.Point.some x y h) :
    P ∈ nonsingularReduction ℚ_[p] (W.integralModel ℤ_[p]).toProjective ↔ x ∈ zeroComponentX W := by
  rw [Tamagawa.mem_nonsingularReduction_iff]
  set Wi := W.integralModel ℤ_[p]
  have key : ((¬ ∃ a : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] a = x) ∨
      ∃ a b : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] a = x ∧ algebraMap ℤ_[p] ℚ_[p] b = y ∧
        (Wi.map (IsLocalRing.residue ℤ_[p])).toAffine.Nonsingular
          (IsLocalRing.residue ℤ_[p] a) (IsLocalRing.residue ℤ_[p] b)) ↔ x ∈ zeroComponentX W := by
    simp only [zeroComponentX, Set.mem_ofPred_eq]
    rw [← norm_le_one_iff_exists, not_le]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨a, b, rfl, rfl, hn⟩
      refine ⟨a, rfl, ?_⟩
      have hn' : (reductionZMod W).toAffine.Nonsingular (PadicInt.toZMod a) (PadicInt.toZMod b) := by
        have := (WeierstrassCurve.Affine.map_nonsingular (Wi.map (IsLocalRing.residue ℤ_[p]))
          (f := (PadicInt.residueField (p := p) : _ →+* ZMod p)) (PadicInt.residueField (p := p)).injective
          (IsLocalRing.residue ℤ_[p] a) (IsLocalRing.residue ℤ_[p] b)).mpr hn
        exact this
      exact (goodFibre_iff_nonsingular _ hn'.1).mpr hn'
    · rintro ⟨X, rfl, hg⟩
      obtain ⟨b, hb⟩ := Tamagawa.exists_integral_y Wi (X : ℚ_[p]) y h.1 X rfl
      refine ⟨X, b, rfl, hb, ?_⟩
      have he : (reductionZMod W).toAffine.Equation (PadicInt.toZMod X) (PadicInt.toZMod b) := by
        have h1 := h.1
        rw [← hb] at h1
        have h2 := (WeierstrassCurve.Affine.map_equation Wi (f := algebraMap ℤ_[p] ℚ_[p])
          (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]) X b).mp h1
        have h3 := WeierstrassCurve.Affine.Equation.map (f := PadicInt.toZMod (p := p)) h2
        exact h3
      have hn := hg _ he
      have := (WeierstrassCurve.Affine.map_nonsingular (Wi.map (IsLocalRing.residue ℤ_[p]))
          (f := (PadicInt.residueField (p := p) : _ →+* ZMod p)) (PadicInt.residueField (p := p)).injective
          (IsLocalRing.residue ℤ_[p] X) (IsLocalRing.residue ℤ_[p] b)).mp hn
      exact this
  rw [← key]
  constructor
  · intro H; exact H x y h hP
  · intro H x' y' h' hP'
    rw [hP] at hP'
    injection hP' with h1 h2
    subst h1; subst h2
    exact H

end NumberFieldKB.MilneEC.LocalPeriod
