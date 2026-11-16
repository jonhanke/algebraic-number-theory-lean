import NumberFieldKB.MilneEC.Ch1CubicDefs
import NumberFieldKB.MilneEC.Ch1GroupLaw

/-!
# The chord and tangent construction: the line and its points

Part of the proof of associativity of the chord and tangent law (Milne, *Elliptic Curves*, Theorem I.3.1).
For `IsThirdPoint F P Q R` (Milne p. 34: `R` is the third point of the cubic `F = 0` on the line through `P`
and `Q`, the tangent line if `P = Q`), with `q` the second vector of the definition and
`ℓ = lineThrough P.rep q`:

* `ℓ` is a nonzero linear form;
* the points of $C \cap ℓ$ are exactly `P`, `Q`, `R`;
* at each of them, `ℓ` is the tangent line exactly when the point occurs at least twice among `P`, `Q`, `R`.
-/

set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

open Classical in
/-- The number of times `X` occurs among `P`, `Q`, `R`. -/
noncomputable def count3 (P Q R X : ℙ K (Fin 3 → K)) : ℕ :=
  (if X = P then 1 else 0) + (if X = Q then 1 else 0) + (if X = R then 1 else 0)

/-! ### The linear form of a line -/

theorem linCoeff_form (a b d : K) :
    linCoeff (C a * X 0 + C b * X 1 + C d * X 2 : MvPolynomial (Fin 3) K) 0 = a ∧
    linCoeff (C a * X 0 + C b * X 1 + C d * X 2 : MvPolynomial (Fin 3) K) 1 = b ∧
    linCoeff (C a * X 0 + C b * X 1 + C d * X 2 : MvPolynomial (Fin 3) K) 2 = d := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [linCoeff, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

theorem linCoeff_lineThrough_zero (p q : Fin 3 → K) :
    linCoeff (lineThrough p q) 0 = p 1 * q 2 - p 2 * q 1 :=
  (linCoeff_form _ _ _).1

theorem linCoeff_lineThrough_one (p q : Fin 3 → K) :
    linCoeff (lineThrough p q) 1 = p 2 * q 0 - p 0 * q 2 :=
  (linCoeff_form _ _ _).2.1

theorem linCoeff_lineThrough_two (p q : Fin 3 → K) :
    linCoeff (lineThrough p q) 2 = p 0 * q 1 - p 1 * q 0 :=
  (linCoeff_form _ _ _).2.2

theorem aeval_lineThrough (p q v : Fin 3 → K) :
    aeval v (lineThrough p q) = (p 1 * q 2 - p 2 * q 1) * v 0 + (p 2 * q 0 - p 0 * q 2) * v 1 +
      (p 0 * q 1 - p 1 * q 0) * v 2 := by
  simp [lineThrough]

theorem lineThrough_isHomogeneous (p q : Fin 3 → K) : (lineThrough p q).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X _ 0).add (isHomogeneous_C_mul_X _ 1)).add (isHomogeneous_C_mul_X _ 2)

/-- The cross product of two independent vectors is nonzero. -/
theorem cross_ne_zero {p q : Fin 3 → K} (hind : LinearIndependent K ![p, q]) :
    ¬ (p 1 * q 2 - p 2 * q 1 = 0 ∧ p 2 * q 0 - p 0 * q 2 = 0 ∧ p 0 * q 1 - p 1 * q 0 = 0) := by
  rintro ⟨h0, h1, h2⟩
  have key : ∀ i, p i = 0 := by
    intro i
    have h := (LinearIndependent.pair_iff.mp hind (q i) (-p i) (by
      funext j
      fin_cases i <;> fin_cases j <;> simp <;>
        first | ring1 | linear_combination h0 | linear_combination -h0 | linear_combination h1 |
          linear_combination -h1 | linear_combination h2 | linear_combination -h2)).2
    exact neg_eq_zero.mp h
  exact hind.ne_zero 0 (funext key)

theorem comb_of_smul {n : K} (hn : n ≠ 0) {v p q : Fin 3 → K} {a b : K}
    (h : n • v = a • p + b • q) : v = (n⁻¹ * a) • p + (n⁻¹ * b) • q := by
  rw [mul_smul, mul_smul, ← smul_add, ← h, inv_smul_smul₀ hn]

/-- A vector orthogonal to the cross product of two independent vectors lies in their span. -/
theorem exists_comb_of_dot {p q : Fin 3 → K} (hind : LinearIndependent K ![p, q]) (v : Fin 3 → K)
    (hv : (p 1 * q 2 - p 2 * q 1) * v 0 + (p 2 * q 0 - p 0 * q 2) * v 1 +
      (p 0 * q 1 - p 1 * q 0) * v 2 = 0) : ∃ σ τ : K, v = σ • p + τ • q := by
  by_cases h0 : p 1 * q 2 - p 2 * q 1 = 0
  · by_cases h1 : p 2 * q 0 - p 0 * q 2 = 0
    · by_cases h2 : p 0 * q 1 - p 1 * q 0 = 0
      · exact absurd ⟨h0, h1, h2⟩ (cross_ne_zero hind)
      · refine ⟨_, _, comb_of_smul h2 (a := v 0 * q 1 - v 1 * q 0) (b := p 0 * v 1 - p 1 * v 0) ?_⟩
        funext j
        fin_cases j <;> simp <;>
          first | ring1 | linear_combination hv | linear_combination -hv
    · refine ⟨_, _, comb_of_smul h1 (a := v 2 * q 0 - v 0 * q 2) (b := p 2 * v 0 - p 0 * v 2) ?_⟩
      funext j
      fin_cases j <;> simp <;>
        first | ring1 | linear_combination hv | linear_combination -hv
  · refine ⟨_, _, comb_of_smul h0 (a := v 1 * q 2 - v 2 * q 1) (b := p 1 * v 2 - p 2 * v 1) ?_⟩
    funext j
    fin_cases j <;> simp <;>
      first | ring1 | linear_combination hv | linear_combination -hv

theorem cross_rel {g p q : Fin 3 → K}
    (h1 : g 0 * p 0 + g 1 * p 1 + g 2 * p 2 = 0) (h2 : g 0 * q 0 + g 1 * q 1 + g 2 * q 2 = 0) :
    g 1 * (p 1 * q 2 - p 2 * q 1) = g 0 * (p 2 * q 0 - p 0 * q 2) ∧
    g 2 * (p 1 * q 2 - p 2 * q 1) = g 0 * (p 0 * q 1 - p 1 * q 0) ∧
    g 2 * (p 2 * q 0 - p 0 * q 2) = g 1 * (p 0 * q 1 - p 1 * q 0) := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-p 2) * h2 + q 2 * h1
  · linear_combination p 1 * h2 - q 1 * h1
  · linear_combination (-p 0) * h2 + q 0 * h1

theorem tangent_iff_dot {p q : Fin 3 → K} (hind : LinearIndependent K ![p, q]) (g : Fin 3 → K) :
    (∃ c : K, g 0 = c * (p 1 * q 2 - p 2 * q 1) ∧ g 1 = c * (p 2 * q 0 - p 0 * q 2) ∧
      g 2 = c * (p 0 * q 1 - p 1 * q 0)) ↔
    (g 0 * p 0 + g 1 * p 1 + g 2 * p 2 = 0 ∧ g 0 * q 0 + g 1 * q 1 + g 2 * q 2 = 0) := by
  constructor
  · rintro ⟨c, e0, e1, e2⟩
    rw [e0, e1, e2]
    constructor <;> ring
  · rintro ⟨h1, h2⟩
    obtain ⟨r01, r02, r12⟩ := cross_rel h1 h2
    by_cases n0 : p 1 * q 2 - p 2 * q 1 = 0
    · by_cases n1 : p 2 * q 0 - p 0 * q 2 = 0
      · by_cases n2 : p 0 * q 1 - p 1 * q 0 = 0
        · exact absurd ⟨n0, n1, n2⟩ (cross_ne_zero hind)
        · refine ⟨g 2 / (p 0 * q 1 - p 1 * q 0), ?_, ?_, ?_⟩
          · rw [div_mul_eq_mul_div, eq_div_iff n2]; linear_combination -r02
          · rw [div_mul_eq_mul_div, eq_div_iff n2]; linear_combination -r12
          · rw [div_mul_eq_mul_div, eq_div_iff n2]
      · refine ⟨g 1 / (p 2 * q 0 - p 0 * q 2), ?_, ?_, ?_⟩
        · rw [div_mul_eq_mul_div, eq_div_iff n1]; linear_combination -r01
        · rw [div_mul_eq_mul_div, eq_div_iff n1]
        · rw [div_mul_eq_mul_div, eq_div_iff n1]; linear_combination r12
    · refine ⟨g 0 / (p 1 * q 2 - p 2 * q 1), ?_, ?_, ?_⟩
      · rw [div_mul_eq_mul_div, eq_div_iff n0]
      · rw [div_mul_eq_mul_div, eq_div_iff n0]; linear_combination r01
      · rw [div_mul_eq_mul_div, eq_div_iff n0]; linear_combination r02

/-! ### Restriction to the line -/

theorem aeval_comb (G : MvPolynomial (Fin 3) K) (p q : Fin 3 → K) (σ τ : K) :
    aeval (σ • p + τ • q) G = eval ![σ, τ] (lineRestriction G p q) := by
  unfold lineRestriction
  rw [eval_aeval_line]
  have h2 : (σ • p + τ • q : Fin 3 → K) = fun j => p j * σ + q j * τ := by
    funext j; simp [mul_comm]
  rw [h2]
  rfl

theorem polar_comb_p (F : MvPolynomial (Fin 3) K) (p q : Fin 3 → K) (σ τ : K) :
    ∑ j, aeval (σ • p + τ • q) (pderiv j F) * p j =
      eval ![σ, τ] (pderiv 0 (lineRestriction F p q)) := by
  have h := pderiv_aeval_fin_three (fun j => C (p j) * X 0 + C (q j) * X 1) 0 F
  have e : pderiv 0 (lineRestriction F p q) =
      ∑ j, lineRestriction (pderiv j F) p q * C (p j) := by
    unfold lineRestriction
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [pderiv_X]
  rw [e]
  simp only [map_sum, map_mul, eval_C]
  simp_rw [aeval_comb]

theorem polar_comb_q (F : MvPolynomial (Fin 3) K) (p q : Fin 3 → K) (σ τ : K) :
    ∑ j, aeval (σ • p + τ • q) (pderiv j F) * q j =
      eval ![σ, τ] (pderiv 1 (lineRestriction F p q)) := by
  have h := pderiv_aeval_fin_three (fun j => C (p j) * X 0 + C (q j) * X 1) 1 F
  have e : pderiv 1 (lineRestriction F p q) =
      ∑ j, lineRestriction (pderiv j F) p q * C (q j) := by
    unfold lineRestriction
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [pderiv_X]
  rw [e]
  simp only [map_sum, map_mul, eval_C]
  simp_rw [aeval_comb]

theorem isTangentForm_iff {F : MvPolynomial (Fin 3) K} {p q : Fin 3 → K}
    (hind : LinearIndependent K ![p, q]) {Z : ℙ K (Fin 3 → K)} {σ τ : K}
    (hZ : Z.rep = σ • p + τ • q) :
    IsTangentForm F (lineThrough p q) Z ↔
      eval ![σ, τ] (pderiv 0 (lineRestriction F p q)) = 0 ∧
      eval ![σ, τ] (pderiv 1 (lineRestriction F p q)) = 0 := by
  rw [← polar_comb_p, ← polar_comb_q, Fin.sum_univ_three, Fin.sum_univ_three]
  rw [← tangent_iff_dot hind (fun j => aeval (σ • p + τ • q) (pderiv j F))]
  unfold IsTangentForm
  rw [hZ]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, ?_, ?_⟩
    · have := hc 0; rw [linCoeff_lineThrough_zero] at this; exact this
    · have := hc 1; rw [linCoeff_lineThrough_one] at this; exact this
    · have := hc 2; rw [linCoeff_lineThrough_two] at this; exact this
  · rintro ⟨c, h0, h1, h2⟩
    refine ⟨c, fun j => ?_⟩
    fin_cases j
    · have e := linCoeff_lineThrough_zero p q
      rw [← e] at h0; exact h0
    · have e := linCoeff_lineThrough_one p q
      rw [← e] at h1; exact h1
    · have e := linCoeff_lineThrough_two p q
      rw [← e] at h2; exact h2

theorem mem_inter_iff {F : MvPolynomial (Fin 3) K} {p q : Fin 3 → K}
    (hind : LinearIndependent K ![p, q]) (Z : ℙ K (Fin 3 → K)) :
    Z ∈ projectivePoints F K ∩ projectivePoints (lineThrough p q) K ↔
      ∃ σ τ : K, Z.rep = σ • p + τ • q ∧ eval ![σ, τ] (lineRestriction F p q) = 0 := by
  constructor
  · rintro ⟨hF, hℓ⟩
    have hℓ' : aeval Z.rep (lineThrough p q) = 0 := hℓ
    have hF' : aeval Z.rep F = 0 := hF
    rw [aeval_lineThrough] at hℓ'
    obtain ⟨σ, τ, hσ⟩ := exists_comb_of_dot hind Z.rep hℓ'
    refine ⟨σ, τ, hσ, ?_⟩
    rw [hσ, aeval_comb] at hF'
    exact hF'
  · rintro ⟨σ, τ, hZ, h⟩
    refine ⟨?_, ?_⟩
    · show aeval Z.rep F = 0
      rw [hZ, aeval_comb]; exact h
    · show aeval Z.rep (lineThrough p q) = 0
      rw [hZ, aeval_lineThrough]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

/-! ### Points of the projective plane -/

theorem rep_mk_eq_smul {w : Fin 3 → K} (hw : w ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ (Projectivization.mk K w hw).rep = a • w := by
  obtain ⟨c, hc, h⟩ := exists_smul_rep w hw
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [eq_inv_smul_iff₀ hc]
  exact h.symm

theorem eq_of_rep_smul {Z Y : ℙ K (Fin 3 → K)} {w : Fin 3 → K} {hw : w ≠ 0}
    (hY : Y = Projectivization.mk K w hw) {a : K} (h : Z.rep = a • w) : Z = Y :=
  ((Projectivization.mk_rep Z).symm.trans
    ((Projectivization.mk_eq_mk_iff' K _ _ Z.rep_nonzero hw).mpr ⟨a, h.symm⟩)).trans hY.symm

theorem mk_comb_eq_iff {P : ℙ K (Fin 3 → K)} {q : Fin 3 → K}
    (hind : LinearIndependent K ![P.rep, q]) {s t : K} (hne : s • P.rep + t • q ≠ 0) :
    Projectivization.mk K _ hne = P ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact mk_comb_ne hind s hne ht h.symm
  · rintro rfl
    have hs : s • P.rep ≠ 0 := by simpa using hne
    have : Projectivization.mk K (s • P.rep + (0 : K) • q) hne = Projectivization.mk K (s • P.rep) hs :=
      (Projectivization.mk_eq_mk_iff' K _ _ hne hs).mpr ⟨1, by simp⟩
    rw [this]
    exact mk_smul_eq hs

theorem mk_comb_eq_mk_iff {P : ℙ K (Fin 3 → K)} {q : Fin 3 → K}
    (hind : LinearIndependent K ![P.rep, q]) {s t : K} (hne : s • P.rep + t • q ≠ 0)
    (hq0 : q ≠ 0) :
    Projectivization.mk K _ hne = Projectivization.mk K q hq0 ↔ s = 0 := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have h0 : s • P.rep + (t - a) • q = 0 := by
      have : s • P.rep + (t - a) • q = (s • P.rep + t • q) - a • q := by module
      rw [this, ← ha, sub_self]
    exact (LinearIndependent.pair_iff.mp hind _ _ h0).1
  · rintro rfl
    exact ⟨t, by simp⟩

theorem proportional_of {s t σ τ : K} (hst : s ≠ 0 ∨ t ≠ 0) (hστ : σ ≠ 0 ∨ τ ≠ 0)
    (h : t * σ - s * τ = 0) : ∃ a : K, a ≠ 0 ∧ σ = a * s ∧ τ = a * t := by
  by_cases hs : s = 0
  · have ht : t ≠ 0 := hst.resolve_left (not_not.mpr hs)
    subst hs
    have hσ : σ = 0 := by
      have : t * σ = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left ht
    subst hσ
    have hτ : τ ≠ 0 := hστ.resolve_left (not_not.mpr rfl)
    exact ⟨τ / t, div_ne_zero hτ ht, by simp, by field_simp⟩
  · refine ⟨σ / s, ?_, by field_simp, ?_⟩
    · intro h0
      have hσ : σ = 0 := (div_eq_zero_iff.mp h0).resolve_right hs
      subst hσ
      have : s * τ = 0 := by linear_combination -h
      have hτ : τ = 0 := (mul_eq_zero.mp this).resolve_left hs
      rcases hστ with h' | h'
      · exact h' rfl
      · exact h' hτ
    · rw [div_mul_eq_mul_div, eq_div_iff hs]
      linear_combination -h

/-! ### Derivatives of the explicit binary cubics -/

theorem pderiv_ne_eval (c s t σ τ : K) :
    eval ![σ, τ] (pderiv 0 (C c * X 1 * X 0 * (C t * X 0 - C s * X 1) : MvPolynomial (Fin 2) K)) =
      c * (2 * t * σ * τ - s * τ ^ 2) ∧
    eval ![σ, τ] (pderiv 1 (C c * X 1 * X 0 * (C t * X 0 - C s * X 1) : MvPolynomial (Fin 2) K)) =
      c * (t * σ ^ 2 - 2 * s * σ * τ) := by
  constructor <;> simp [pderiv_mul, pderiv_X, Pi.single_apply] <;> ring

theorem pderiv_eq_eval (c s t σ τ : K) :
    eval ![σ, τ] (pderiv 0 (C c * X 1 * X 1 * (C t * X 0 - C s * X 1) : MvPolynomial (Fin 2) K)) =
      c * (t * τ ^ 2) ∧
    eval ![σ, τ] (pderiv 1 (C c * X 1 * X 1 * (C t * X 0 - C s * X 1) : MvPolynomial (Fin 2) K)) =
      c * (2 * t * σ * τ - 3 * s * τ ^ 2) := by
  constructor <;> simp [pderiv_mul, pderiv_X, Pi.single_apply] <;> ring

theorem isThirdPoint_line {F : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    (hsm : ∀ v : Fin 3 → K, v ≠ 0 → aeval v F = 0 → ∃ j, aeval v (pderiv j F) ≠ 0)
    {P Q R : ℙ K (Fin 3 → K)} (h : IsThirdPoint F P Q R) :
    ∃ ℓ : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 ∧ ℓ ≠ 0 ∧
      (∀ X : ℙ K (Fin 3 → K),
        X ∈ projectivePoints F K ∩ projectivePoints ℓ K ↔ (X = P ∨ X = Q ∨ X = R)) ∧
      (∀ X : ℙ K (Fin 3 → K), (X = P ∨ X = Q ∨ X = R) →
        (IsTangentForm F ℓ X ↔ 2 ≤ count3 P Q R X)) := by
  obtain ⟨q, c, s, t, hc, hind, hQ, htan, ⟨hne, hR⟩, hb⟩ := h
  have hq0 : q ≠ 0 := hind.ne_zero 1
  have hst : s ≠ 0 ∨ t ≠ 0 := by
    by_contra hh
    push Not at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp at hne
  have hRP : R = P ↔ t = 0 := by rw [hR]; exact mk_comb_eq_iff hind hne
  obtain ⟨a, ha, hrep⟩ := rep_mk_eq_smul hne
  rw [← hR] at hrep
  have hrepR : R.rep = (a * s) • P.rep + (a * t) • q := by rw [hrep]; module
  refine ⟨lineThrough P.rep q, lineThrough_isHomogeneous _ _, ?_, ?_, ?_⟩
  · intro h0
    apply cross_ne_zero hind
    have e0 := linCoeff_lineThrough_zero P.rep q
    have e1 := linCoeff_lineThrough_one P.rep q
    have e2 := linCoeff_lineThrough_two P.rep q
    rw [h0] at e0 e1 e2
    simp only [linCoeff, map_zero] at e0 e1 e2
    exact ⟨e0.symm, e1.symm, e2.symm⟩
  · intro Z
    rw [mem_inter_iff hind]
    by_cases hPQ : P = Q
    · have hev : ∀ σ τ : K, eval ![σ, τ] (lineRestriction F P.rep q) =
          c * τ * τ * (t * σ - s * τ) := by
        intro σ τ
        rw [hb, ite_X_of_eq hPQ]
        simp
      constructor
      · rintro ⟨σ, τ, hZ, hz⟩
        rw [hev] at hz
        have hστ : σ ≠ 0 ∨ τ ≠ 0 := by
          by_contra hh
          push Not at hh
          apply Z.rep_nonzero
          rw [hZ, hh.1, hh.2]; simp
        rcases mul_eq_zero.mp hz with h1 | h1
        · have hτ : τ = 0 := by simpa [hc] using h1
          left
          exact eq_of_rep_smul (P.mk_rep.symm) (a := σ) (by rw [hZ, hτ]; simp)
        · obtain ⟨b, hb0, hσ, hτ⟩ := proportional_of hst hστ h1
          right; right
          refine eq_of_rep_smul hR (a := b) ?_
          rw [hZ, hσ, hτ]; module
      · rintro (h1 | h1 | h1)
        · exact ⟨1, 0, by rw [h1]; simp, by rw [hev]; simp⟩
        · exact ⟨1, 0, by rw [h1, ← hPQ]; simp, by rw [hev]; simp⟩
        · exact ⟨a * s, a * t, by rw [h1, hrepR], by rw [hev]; ring⟩
    · obtain ⟨hq0', hQq⟩ := hQ hPQ
      have hev : ∀ σ τ : K, eval ![σ, τ] (lineRestriction F P.rep q) =
          c * τ * σ * (t * σ - s * τ) := by
        intro σ τ
        rw [hb, ite_X_of_ne hPQ]
        simp
      obtain ⟨a', ha', hrepQ⟩ := rep_mk_eq_smul hq0'
      rw [← hQq] at hrepQ
      constructor
      · rintro ⟨σ, τ, hZ, hz⟩
        rw [hev] at hz
        have hστ : σ ≠ 0 ∨ τ ≠ 0 := by
          by_contra hh
          push Not at hh
          apply Z.rep_nonzero
          rw [hZ, hh.1, hh.2]; simp
        rcases mul_eq_zero.mp hz with h1 | h1
        · rcases mul_eq_zero.mp h1 with h2 | h2
          · have hτ : τ = 0 := by simpa [hc] using h2
            left
            exact eq_of_rep_smul (P.mk_rep.symm) (a := σ) (by rw [hZ, hτ]; simp)
          · right; left
            exact eq_of_rep_smul hQq (a := τ) (by rw [hZ, h2]; simp)
        · obtain ⟨b, hb0, hσ, hτ⟩ := proportional_of hst hστ h1
          right; right
          refine eq_of_rep_smul hR (a := b) ?_
          rw [hZ, hσ, hτ]; module
      · rintro (h1 | h1 | h1)
        · exact ⟨1, 0, by rw [h1]; simp, by rw [hev]; simp⟩
        · exact ⟨0, a', by rw [h1, hrepQ]; simp, by rw [hev]; simp⟩
        · exact ⟨a * s, a * t, by rw [h1, hrepR], by rw [hev]; ring⟩
  · intro Z hZ
    by_cases hPQ : P = Q
    · have hZ' : Z = P ∨ Z = R := by
        rcases hZ with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inl (h1.trans hPQ.symm)
        · exact Or.inr h1
      rcases hZ' with h1 | h1
      · rw [h1, isTangentForm_iff hind (Z := P) (σ := 1) (τ := 0)
          (by simp), hb, ite_X_of_eq hPQ]
        obtain ⟨e0, e1⟩ := pderiv_eq_eval c s t 1 0
        rw [e0, e1]
        have hcnt : 2 ≤ count3 P Q R P := by
          unfold count3
          rw [if_pos rfl, if_pos hPQ]
          split_ifs <;> omega
        exact iff_of_true ⟨by simp, by simp⟩ hcnt
      · rw [h1, isTangentForm_iff hind (Z := R) (σ := a * s) (τ := a * t) hrepR, hb,
          ite_X_of_eq hPQ]
        obtain ⟨e0, e1⟩ := pderiv_eq_eval c s t (a * s) (a * t)
        rw [e0, e1]
        by_cases ht : t = 0
        · have hRP' : R = P := hRP.mpr ht
          have hcnt : 2 ≤ count3 P Q R R := by
            unfold count3
            rw [← hPQ, if_pos hRP', if_pos rfl]
            omega
          exact iff_of_true ⟨by simp [ht], by simp [ht]⟩ hcnt
        · have hRP' : ¬ R = P := fun h2 => ht (hRP.mp h2)
          have hcnt : count3 P Q R R = 1 := by
            unfold count3
            rw [← hPQ, if_neg hRP', if_pos rfl]
          refine iff_of_false ?_ (by omega)
          rintro ⟨h2, _⟩
          have h3 : c * a ^ 2 * t ^ 3 = 0 := by linear_combination h2
          simp [hc, ha, ht] at h3
    · obtain ⟨hq0', hQq⟩ := hQ hPQ
      have hRQ : R = Q ↔ s = 0 := by rw [hR, hQq]; exact mk_comb_eq_mk_iff hind hne hq0'
      obtain ⟨a', ha', hrepQ⟩ := rep_mk_eq_smul hq0'
      rw [← hQq] at hrepQ
      have hrepQ' : Q.rep = (0 : K) • P.rep + a' • q := by rw [hrepQ]; simp
      rcases hZ with h1 | h1 | h1
      · rw [h1, isTangentForm_iff hind (Z := P) (σ := 1) (τ := 0) (by simp), hb,
          ite_X_of_ne hPQ]
        obtain ⟨e0, e1⟩ := pderiv_ne_eval c s t 1 0
        rw [e0, e1]
        by_cases ht : t = 0
        · have hPR : P = R := (hRP.mpr ht).symm
          have hcnt : 2 ≤ count3 P Q R P := by
            unfold count3
            rw [if_pos rfl, if_neg hPQ, if_pos hPR]
          exact iff_of_true ⟨by simp, by simp [ht]⟩ hcnt
        · have hPR : ¬ P = R := fun h2 => ht (hRP.mp h2.symm)
          have hcnt : count3 P Q R P = 1 := by
            unfold count3
            rw [if_pos rfl, if_neg hPQ, if_neg hPR]
          refine iff_of_false ?_ (by omega)
          rintro ⟨_, h2⟩
          have h3 : c * t = 0 := by linear_combination h2
          simp [hc, ht] at h3
      · rw [h1, isTangentForm_iff hind (Z := Q) (σ := 0) (τ := a') hrepQ', hb,
          ite_X_of_ne hPQ]
        obtain ⟨e0, e1⟩ := pderiv_ne_eval c s t 0 a'
        rw [e0, e1]
        by_cases hs : s = 0
        · have hQR : Q = R := (hRQ.mpr hs).symm
          have hcnt : 2 ≤ count3 P Q R Q := by
            unfold count3
            rw [if_neg (Ne.symm hPQ), if_pos rfl, if_pos hQR]
          exact iff_of_true ⟨by simp [hs], by simp⟩ hcnt
        · have hQR : ¬ Q = R := fun h2 => hs (hRQ.mp h2.symm)
          have hcnt : count3 P Q R Q = 1 := by
            unfold count3
            rw [if_neg (Ne.symm hPQ), if_pos rfl, if_neg hQR]
          refine iff_of_false ?_ (by omega)
          rintro ⟨h2, _⟩
          have h3 : c * a' ^ 2 * s = 0 := by linear_combination -h2
          simp [hc, ha', hs] at h3
      · rw [h1, isTangentForm_iff hind (Z := R) (σ := a * s) (τ := a * t) hrepR, hb,
          ite_X_of_ne hPQ]
        obtain ⟨e0, e1⟩ := pderiv_ne_eval c s t (a * s) (a * t)
        rw [e0, e1]
        by_cases hs : s = 0
        · have hRQ' : R = Q := hRQ.mpr hs
          have hcnt : 2 ≤ count3 P Q R R := by
            unfold count3
            rw [if_pos hRQ', if_pos rfl]
            split_ifs <;> omega
          exact iff_of_true ⟨by simp [hs], by simp [hs]⟩ hcnt
        · by_cases ht : t = 0
          · have hRP' : R = P := hRP.mpr ht
            have hcnt : 2 ≤ count3 P Q R R := by
              unfold count3
              rw [if_pos hRP', if_pos rfl]
              split_ifs <;> omega
            exact iff_of_true ⟨by simp [ht], by simp [ht]⟩ hcnt
          · have hRP' : ¬ R = P := fun h2 => ht (hRP.mp h2)
            have hRQ' : ¬ R = Q := fun h2 => hs (hRQ.mp h2)
            have hcnt : count3 P Q R R = 1 := by
              unfold count3
              rw [if_neg hRP', if_neg hRQ', if_pos rfl]
            refine iff_of_false ?_ (by omega)
            rintro ⟨h2, _⟩
            have h3 : c * a ^ 2 * s * t ^ 2 = 0 := by linear_combination h2
            simp [hc, ha, hs, ht] at h3

end NumberFieldKB.MilneEC.Bezout
