import NumberFieldKB.MilneEC.Ch1Projective
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, Elliptic Curves, Chapter I, Section 3: the group law on a cubic curve; Mordell's theorem

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §3 (pdf pp. 33–37) and Theorem 2.1 (pdf p. 28):
the chord and tangent construction on a nonsingular projective plane cubic, Theorem 3.1 (the
construction makes $C(k)$ a commutative group), Proposition 3.2, and Mordell's finite basis theorem.

**The third point.** Let $C = C_F$ be a projective plane cubic and $P, Q \in C(k)$.  If $P \neq Q$, the
line through them is $\{sp + tq\}$ for representatives `p`, `q`; if $P = Q$ the line is the tangent line at
`P` (the polar line of Exercise 1.17), spanned by `p` and any `q` on it independent of `p`.  The restriction
$\varphi(S, T) = F(Sp + Tq)$ is a binary cubic form vanishing at $(1 : 0)$ (the point `P`) and at $(0 : 1)$
(the point `Q`) when $P \neq Q$, and to order 2 at $(1 : 0)$ when $P = Q$.  The third point $PQ$ is the
remaining zero $(s : t)$: $\varphi = c\, T \cdot \ell \cdot (tS - sT)$ with $\ell = S$ (resp. $T$).  This
covers Milne's conventions (p. 34): $PQ = Q$ when the line is tangent at `Q`, and $PP = P$ at a point of
inflection.  `IsThirdPoint F P Q R` says that `R` is $PQ$.

**Scope.** Milne assumes `k` perfect "for simplicity"; the construction (existence and uniqueness of
the third point in $C(k)$, `exists_unique_isThirdPoint`) is proved here for every field.  Associativity of
the group law is the named statement `Thm3_1` (Milne sketches a proof by Proposition 3.2 and refers to
Fulton for the degenerate cases; Section 4 deduces it from the Riemann–Roch theorem).
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-- The restriction of `F` to the line spanned by `p` and `q`: the binary form $F(Sp + Tq)$, with
$S$ = `X 0` and $T$ = `X 1`. -/
noncomputable def lineRestriction (F : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) :
    MvPolynomial (Fin 2) k :=
  aeval (fun j => C (p j) * X 0 + C (q j) * X 1) F

/-- The polar pairing $\sum_j (\partial F/\partial X_j)(p)\, q_j$: `q` lies on the tangent line at `p` when
it vanishes. -/
noncomputable def polarPairing (F : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) : k :=
  ∑ j : Fin 3, eval p (pderiv j F) * q j

/-! ### Algebra of binary forms and of the restriction to a line -/

/-- Substituting a change of basis of the line into the restriction. -/
theorem lineRestriction_lin (F : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) (a b c d : k) :
    lineRestriction F (a • p + b • q) (c • p + d • q) =
      aeval ![C a * X 0 + C c * X 1, C b * X 0 + C d * X 1] (lineRestriction F p q) := by
  unfold lineRestriction
  rw [comp_aeval_apply]
  refine congrArg (fun w => aeval w F) ?_
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, aeval_C, aeval_X,
    algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Evaluating a substituted polynomial at a point with coordinates in an extension field. -/
theorem aeval_aeval_line (G : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) {K : Type*} [Field K]
    [Algebra k K] (s t : K) :
    aeval ![s, t] (aeval (fun j => C (p j) * X 0 + C (q j) * X 1) G : MvPolynomial (Fin 2) k) =
      aeval (fun j => algebraMap k K (p j) * s + algebraMap k K (q j) * t) G := by
  rw [comp_aeval_apply]
  refine congrArg (fun w => aeval w G) ?_
  funext j
  simp

/-- Evaluating a substituted polynomial. -/
theorem eval_aeval_line (G : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) (s t : k) :
    eval ![s, t] (aeval (fun j => C (p j) * X 0 + C (q j) * X 1) G) =
      eval (fun j => p j * s + q j * t) G := by
  simpa [aeval_eq_eval] using aeval_aeval_line G p q (K := k) s t

/-- The polar pairing is the coefficient of $S^2 T$ in the restriction to the line. -/
theorem polarPairing_eq_eval (F : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) :
    polarPairing F p q = eval ![1, 0] (pderiv 1 (lineRestriction F p q)) := by
  unfold lineRestriction polarPairing
  rw [pderiv_aeval_fin_three]
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_aeval_line]
  simp [pderiv_X]

theorem monomial_form (a : k) (i j : ℕ) :
    (C a * X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) k) =
      monomial (Finsupp.single 0 i + Finsupp.single 1 j) a := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial]
  simp

theorem degree_fin_two (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- A homogeneous polynomial in two variables is a combination of the monomials of its degree. -/
theorem binary_shape (φ : MvPolynomial (Fin 2) k) (n : ℕ) (h : φ.IsHomogeneous n) :
    φ = ∑ i ∈ Finset.range (n + 1),
      C (φ.coeff (Finsupp.single 0 (n - i) + Finsupp.single 1 i)) * X 0 ^ (n - i) * X 1 ^ i := by
  ext d
  rw [coeff_sum]
  simp_rw [monomial_form, coeff_monomial]
  by_cases hd : d 0 + d 1 = n
  · rw [Finset.sum_eq_single (d 1)]
    · have : Finsupp.single 0 (n - d 1) + Finsupp.single 1 (d 1) = d := by
        ext i; fin_cases i <;> simp; omega
      simp only [this, ite_true]
    · intro i _ hi
      have hne : ¬ (Finsupp.single 0 (n - i) + Finsupp.single 1 i = d) := fun heq => hi (by
        have := congrArg (fun f => f 1) heq
        simpa using this)
      simp only [hne, ite_false]
    · intro hmem
      exfalso; apply hmem
      rw [Finset.mem_range]; omega
  · rw [h.coeff_eq_zero (by rw [degree_fin_two]; exact hd)]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hne : ¬ (Finsupp.single 0 (n - i) + Finsupp.single 1 i = d) := fun heq => hd (by
      have h0 := congrArg (fun f => f 0) heq
      have h1 := congrArg (fun f => f 1) heq
      simp at h0 h1
      omega)
    simp only [hne, ite_false]

/-- A binary cubic form is a combination of the four monomials of degree 3. -/
theorem binary_cubic_shape (φ : MvPolynomial (Fin 2) k) (h : φ.IsHomogeneous 3) :
    ∃ a0 a1 a2 a3 : k, φ = C a0 * X 0 ^ 3 + C a1 * X 0 ^ 2 * X 1 + C a2 * X 0 * X 1 ^ 2 +
      C a3 * X 1 ^ 3 := by
  refine ⟨φ.coeff (Finsupp.single 0 3), φ.coeff (Finsupp.single 0 2 + Finsupp.single 1 1),
    φ.coeff (Finsupp.single 0 1 + Finsupp.single 1 2), φ.coeff (Finsupp.single 1 3),
    (binary_shape φ 3 h).trans ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, zero_add, pow_zero,
    pow_one, mul_one, Nat.sub_zero, Finsupp.single_zero, add_zero]

/-- A binary quadratic form is a combination of the three monomials of degree 2. -/
theorem binary_quadratic_shape (φ : MvPolynomial (Fin 2) k) (h : φ.IsHomogeneous 2) :
    ∃ a0 a1 a2 : k, φ = C a0 * X 0 ^ 2 + C a1 * X 0 * X 1 + C a2 * X 1 ^ 2 := by
  refine ⟨φ.coeff (Finsupp.single 0 2), φ.coeff (Finsupp.single 0 1 + Finsupp.single 1 1),
    φ.coeff (Finsupp.single 1 2), (binary_shape φ 2 h).trans ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, zero_add, pow_zero,
    pow_one, mul_one, Nat.sub_zero, Finsupp.single_zero, add_zero]

/-- The linear form $aS + bT$. -/
noncomputable def lin (a b : k) : MvPolynomial (Fin 2) k := C a * X 0 + C b * X 1

/-- The four coefficient functionals of a binary cubic: the coefficients of $S^3$, $S^2T$, $ST^2$,
$T^3$ (extracted by evaluation and differentiation, so that no characteristic hypothesis is needed). -/
noncomputable def cubicCoeffs (f : MvPolynomial (Fin 2) k) : k × k × k × k :=
  (eval ![1, 0] f, eval ![1, 0] (pderiv 1 f), eval ![0, 1] (pderiv 0 f), eval ![0, 1] f)

/-- The coefficients of a product of three linear forms. -/
theorem cubicCoeffs_lin_mul (c a1 b1 a2 b2 a3 b3 : k) :
    cubicCoeffs (C c * lin a1 b1 * lin a2 b2 * lin a3 b3) =
      (c * (a1 * a2 * a3), c * (a1 * a2 * b3 + a1 * b2 * a3 + b1 * a2 * a3),
        c * (a1 * b2 * b3 + b1 * a2 * b3 + b1 * b2 * a3), c * (b1 * b2 * b3)) := by
  simp only [cubicCoeffs, lin, pderiv_mul, pderiv_C, pderiv_X, map_add, map_mul, eval_C, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_apply]
  simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The coefficients of a binary cubic written with four coefficients. -/
theorem cubicCoeffs_shape (a0 a1 a2 a3 : k) :
    cubicCoeffs (C a0 * X 0 ^ 3 + C a1 * X 0 ^ 2 * X 1 + C a2 * X 0 * X 1 ^ 2 + C a3 * X 1 ^ 3 :
      MvPolynomial (Fin 2) k) = (a0, a1, a2, a3) := by
  simp [cubicCoeffs, pderiv_X]

/-- Substituting into a linear form. -/
theorem lin_sub (α β γ δ a b : k) :
    aeval ![lin α γ, lin β δ] (lin a b) = lin (a * α + b * β) (a * γ + b * δ) := by
  simp only [lin, map_add, map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The factor selected in the definition of `IsThirdPoint` when the two points are equal. -/
theorem ite_X_of_eq {P Q : ℙ k (Fin 3 → k)} {_ : Decidable (P = Q)} (h : P = Q) :
    (if P = Q then (X 1 : MvPolynomial (Fin 2) k) else X 0) = X 1 := by
  simp [h]

/-- The factor selected in the definition of `IsThirdPoint` when the two points differ. -/
theorem ite_X_of_ne {P Q : ℙ k (Fin 3 → k)} {_ : Decidable (P = Q)} (h : ¬ P = Q) :
    (if P = Q then (X 1 : MvPolynomial (Fin 2) k) else X 0) = X 0 := by
  simp [h]

open Classical in
/-- `R` is the third point $PQ$ of intersection of `C_F` with the line through `P` and `Q` (the tangent
line at `P` when $P = Q$), counted with multiplicity (p. 34). -/
@[kb "milne2006ec" "Ch. I, §3, Def. of the third point PQ, pdf p. 34"]
def IsThirdPoint (F : MvPolynomial (Fin 3) k) (P Q R : ℙ k (Fin 3 → k)) : Prop :=
  ∃ (q : Fin 3 → k) (c s t : k), c ≠ 0 ∧ LinearIndependent k ![P.rep, q] ∧
    (P ≠ Q → ∃ hq : q ≠ 0, Q = Projectivization.mk k q hq) ∧
    (P = Q → polarPairing F P.rep q = 0) ∧
    (∃ h : s • P.rep + t • q ≠ 0, R = Projectivization.mk k _ h) ∧
    lineRestriction F P.rep q =
      C c * X 1 * (if P = Q then X 1 else X 0) * (C t * X 0 - C s * X 1)

/-- A **nonsingular projective plane cubic** (p. 33): a nonsingular projective plane curve of degree 3. -/
@[kb "milne2006ec" "Ch. I, §3, nonsingular projective plane curve of degree 3, pdf p. 33"]
def IsNonsingularCubic (F : MvPolynomial (Fin 3) k) : Prop :=
  IsProjectivePlaneCurve F ∧ curveDegree F = 3 ∧ IsNonsingularProjCurve F

/-! ### A nonsingular cubic contains no line, and the tangent line -/

theorem IsNonsingularCubic.isHomogeneous {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F) :
    F.IsHomogeneous 3 := by
  have h := hF.1.1
  have h3 : F.totalDegree = 3 := hF.2.1
  rwa [h3] at h

/-- The chosen piece of a nonzero vector contains it. -/
theorem pieceIndex_coord_ne_zero {K : Type*} [Field K] (v : Fin 3 → K) (hv : v ≠ 0) :
    v (pieceIndex v) ≠ 0 := by
  unfold pieceIndex
  by_cases h2 : v 2 ≠ 0
  · simp [h2]
  · by_cases h1 : v 1 ≠ 0
    · simp [h2, h1]
    · have h0 : v 0 ≠ 0 := by
        intro h0; apply hv; funext i; fin_cases i <;> simp_all
      simp [h2, h1, h0]

/-- On a nonsingular cubic, the curve and its three partial derivatives have no common zero over the
algebraic closure (Exercise 1.17). -/
theorem IsNonsingularCubic.not_singular {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    (v : Fin 3 → AlgebraicClosure k) (hv : v ≠ 0) :
    ¬ (aeval v F = 0 ∧ ∀ j, aeval v (pderiv j F) = 0) := by
  rintro ⟨h0, hj⟩
  have hH := hF.isHomogeneous
  have hPmem : Projectivization.mk (AlgebraicClosure k) v hv ∈
      projectivePoints F (AlgebraicClosure k) := (mem_projectivePoints_mk hH v hv).mpr h0
  have hns := hF.2.2 _ hPmem
  obtain ⟨c, hc, hvc⟩ := exists_smul_rep v hv
  generalize (Projectivization.mk (AlgebraicClosure k) v hv) = P at hns hvc hPmem
  have hrep0 : aeval P.rep F = 0 := hPmem
  have hrepj : ∀ j, aeval P.rep (pderiv j F) = 0 := by
    intro j
    have h := hj j
    rw [hvc, aeval_smul_of_isHomogeneous hH.pderiv] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc)
  have hsing := ((exercise_1_17_singular hH P.rep P.rep_nonzero).2.mpr ⟨hrep0, hrepj⟩)
    (pieceIndex P.rep) (pieceIndex_coord_ne_zero _ P.rep_nonzero)
  rcases hns.2 with h | h
  · exact h hsing.2.1
  · exact h hsing.2.2

/-- At a point of a nonsingular cubic over `k`, some partial derivative is nonzero. -/
theorem IsNonsingularCubic.exists_partial_ne_zero {F : MvPolynomial (Fin 3) k}
    (hF : IsNonsingularCubic F) {p : Fin 3 → k} (hp : p ≠ 0) (hFp : eval p F = 0) :
    ∃ j, eval p (pderiv j F) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hv : (algebraMap k (AlgebraicClosure k) ∘ p) ≠ 0 := by
    intro h; apply hp; funext i
    have := congrFun h i
    simpa using this
  refine hF.not_singular _ hv ⟨?_, fun j => ?_⟩
  · rw [aeval_algebraMap_apply, aeval_eq_eval, hFp, map_zero]
  · rw [aeval_algebraMap_apply, aeval_eq_eval, hcon j, map_zero]

/-- A binary quadratic form over an algebraically closed field has a nontrivial zero. -/
theorem exists_root_binary_quadratic {K : Type*} [Field K] [IsAlgClosed K] (α β γ : K) :
    ∃ s t : K, (s ≠ 0 ∨ t ≠ 0) ∧ α * s ^ 2 + β * s * t + γ * t ^ 2 = 0 := by
  by_cases hα : α = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hα]⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
      (Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ)
      (by rw [Polynomial.degree_quadratic hα]; norm_num)
    refine ⟨x, 1, Or.inr one_ne_zero, ?_⟩
    simp [Polynomial.IsRoot] at hx
    linear_combination hx

/-- **A nonsingular cubic contains no line**: the restriction of `F` to the line spanned by two
independent vectors is not the zero polynomial.  (Otherwise `F` vanishes on the line over the algebraic
closure; the partial derivatives of `F` along the line satisfy two linear relations, and the third
relation is a binary quadratic form, which has a zero over the algebraic closure; there `F` and all its
partial derivatives vanish, contradicting nonsingularity.) -/
theorem IsNonsingularCubic.lineRestriction_ne_zero {F : MvPolynomial (Fin 3) k}
    (hF : IsNonsingularCubic F) {p q : Fin 3 → k} (hpq : LinearIndependent k ![p, q]) :
    lineRestriction F p q ≠ 0 := by
  intro hφ
  have hH := hF.isHomogeneous
  obtain ⟨r, hr⟩ := exists_linearIndependent_cons_of_lt_finrank hpq
    (by simp : 2 < Module.finrank k (Fin 3 → k))
  set M : Matrix (Fin 3) (Fin 3) k := Matrix.of ![r, p, q] with hMdef
  have hM : IsUnit M := by
    refine Matrix.linearIndependent_row_iff_isUnit.mp ?_
    convert hr using 1
    funext i; fin_cases i <;> rfl
  set K := AlgebraicClosure k
  set line : Fin 3 → MvPolynomial (Fin 2) k := fun j => C (p j) * X 0 + C (q j) * X 1 with hline
  have hg : ∀ i, (line i).IsHomogeneous 1 := fun i =>
    (isHomogeneous_C_mul_X (p i) 0).add (isHomogeneous_C_mul_X (q i) 1)
  have hG : ∀ j, (aeval line (pderiv j F)).IsHomogeneous 2 := fun j => by
    simpa using (hH.pderiv (i := j)).aeval line hg
  have hφ' : aeval line F = 0 := hφ
  have hS : ∑ j, aeval line (pderiv j F) * C (p j) = 0 := by
    have h := pderiv_aeval_fin_three line 0 F
    rw [hφ', map_zero] at h
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h.symm
    simp [hline, pderiv_X]
  have hT : ∑ j, aeval line (pderiv j F) * C (q j) = 0 := by
    have h := pderiv_aeval_fin_three line 1 F
    rw [hφ', map_zero] at h
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h.symm
    simp [hline, pderiv_X]
  set Ψ : MvPolynomial (Fin 2) k := ∑ j, aeval line (pderiv j F) * C (r j) with hΨdef
  have hΨ : Ψ.IsHomogeneous 2 := by
    have : Ψ.IsHomogeneous (2 + 0) :=
      IsHomogeneous.sum _ _ _ fun j _ => (hG j).mul (isHomogeneous_C _ _)
    simpa using this
  obtain ⟨α, β, γ, hΨ'⟩ := binary_quadratic_shape Ψ hΨ
  obtain ⟨s, t, hst, hroot⟩ := exists_root_binary_quadratic (algebraMap k K α)
    (algebraMap k K β) (algebraMap k K γ)
  set g : Fin 3 → K := fun j => aeval ![s, t] (aeval line (pderiv j F)) with hgdef
  have hgj : ∀ j, g j =
      aeval (fun i => algebraMap k K (p i) * s + algebraMap k K (q i) * t) (pderiv j F) :=
    fun j => aeval_aeval_line _ p q s t
  have hp0 : ∑ j, g j * algebraMap k K (p j) = 0 := by
    have := congrArg (aeval ![s, t] : MvPolynomial (Fin 2) k →ₐ[k] K) hS
    simpa [map_sum, map_mul, hgdef] using this
  have hq0 : ∑ j, g j * algebraMap k K (q j) = 0 := by
    have := congrArg (aeval ![s, t] : MvPolynomial (Fin 2) k →ₐ[k] K) hT
    simpa [map_sum, map_mul, hgdef] using this
  have hr0 : ∑ j, g j * algebraMap k K (r j) = 0 := by
    have h1 : aeval ![s, t] Ψ = ∑ j, g j * algebraMap k K (r j) := by
      simp [hΨdef, map_sum, hgdef]
    have h2 : aeval ![s, t] Ψ = algebraMap k K α * s ^ 2 + algebraMap k K β * s * t +
        algebraMap k K γ * t ^ 2 := by
      rw [hΨ']; simp
    rw [← h1, h2, hroot]
  have hM' : IsUnit (M.map (algebraMap k K)) := hM.map (RingHom.mapMatrix (algebraMap k K))
  have hg0 : g = 0 := by
    refine Matrix.mulVec_injective_iff_isUnit.mpr hM' (show (M.map (algebraMap k K)).mulVec g =
      (M.map (algebraMap k K)).mulVec 0 from ?_)
    funext i
    rw [Fin.sum_univ_three] at hp0 hq0 hr0
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hMdef]
      linear_combination hr0
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hMdef]
      linear_combination hp0
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hMdef]
      linear_combination hq0
  set v : Fin 3 → K := fun i => algebraMap k K (p i) * s + algebraMap k K (q i) * t with hvdef
  have hv : v ≠ 0 := by
    intro hv0
    have hx : Matrix.vecMul ![0, s, t] (M.map (algebraMap k K)) =
        Matrix.vecMul 0 (M.map (algebraMap k K)) := by
      funext j
      have := congrFun hv0 j
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hMdef, hvdef] at this ⊢
      linear_combination this
    have hx' := Matrix.vecMul_injective_iff_isUnit.mpr hM' hx
    have hs : s = 0 := by simpa using congrFun hx' 1
    have ht : t = 0 := by simpa using congrFun hx' 2
    rcases hst with h | h
    · exact h hs
    · exact h ht
  refine hF.not_singular v hv ⟨?_, fun j => ?_⟩
  · rw [← aeval_aeval_line F p q s t]
    have : aeval line F = 0 := hφ'
    rw [this, map_zero]
  · rw [← hgj, hg0]; rfl

/-- Change of basis of the line, in terms of linear forms. -/
theorem lineRestriction_lin' (F : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) (a b c d : k) :
    lineRestriction F (a • p + b • q) (c • p + d • q) =
      aeval ![lin a c, lin b d] (lineRestriction F p q) :=
  lineRestriction_lin F p q a b c d

/-- The restriction of a homogeneous polynomial to a line is homogeneous of the same degree. -/
theorem lineRestriction_isHomogeneous {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    (p q : Fin 3 → k) : (lineRestriction F p q).IsHomogeneous d := by
  have hg : ∀ i, (C (p i) * X 0 + C (q i) * X 1 : MvPolynomial (Fin 2) k).IsHomogeneous 1 :=
    fun i => (isHomogeneous_C_mul_X (p i) 0).add (isHomogeneous_C_mul_X (q i) 1)
  have h := hF.aeval (fun j => C (p j) * X 0 + C (q j) * X 1) hg
  rw [one_mul] at h
  exact h

/-- Three of the four coefficients of the restriction to a line. -/
theorem cubicCoeffs_lineRestriction (F : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) :
    (cubicCoeffs (lineRestriction F p q)).1 = eval p F ∧
      (cubicCoeffs (lineRestriction F p q)).2.1 = polarPairing F p q ∧
      (cubicCoeffs (lineRestriction F p q)).2.2.2 = eval q F := by
  refine ⟨?_, (polarPairing_eq_eval F p q).symm, ?_⟩
  · have := eval_aeval_line F p q 1 0
    simpa [cubicCoeffs, lineRestriction] using this
  · have := eval_aeval_line F p q 0 1
    simpa [cubicCoeffs, lineRestriction] using this

/-- The polar form at `p` as a linear map. -/
noncomputable def polarLin (F : MvPolynomial (Fin 3) k) (p : Fin 3 → k) :
    (Fin 3 → k) →ₗ[k] k :=
  ∑ j : Fin 3, eval p (pderiv j F) • (LinearMap.proj j : (Fin 3 → k) →ₗ[k] k)

theorem polarLin_apply (F : MvPolynomial (Fin 3) k) (p q : Fin 3 → k) :
    polarLin F p q = polarPairing F p q := by
  simp [polarLin, polarPairing, LinearMap.sum_apply]

/-- Euler's identity: a point of the curve lies on its own tangent line. -/
theorem polarPairing_self {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous 3) (p : Fin 3 → k)
    (hp : eval p F = 0) : polarPairing F p p = 0 := by
  have e := euler_eval hF (K := k) p
  simp only [aeval_eq_eval, hp, mul_zero] at e
  unfold polarPairing
  rw [← e]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The kernel of the polar form at a nonsingular point is two-dimensional. -/
theorem IsNonsingularCubic.finrank_ker_polarLin {F : MvPolynomial (Fin 3) k}
    (hF : IsNonsingularCubic F) {p : Fin 3 → k} (hp : p ≠ 0) (hFp : eval p F = 0) :
    Module.finrank k (LinearMap.ker (polarLin F p)) = 2 := by
  have hne : polarLin F p ≠ 0 := by
    obtain ⟨j, hj⟩ := hF.exists_partial_ne_zero hp hFp
    intro h; apply hj
    have := LinearMap.congr_fun h (Pi.single j 1)
    simpa [polarLin_apply, polarPairing, Pi.single_apply] using this
  have hr := LinearMap.finrank_range_add_finrank_ker (polarLin F p)
  have h1 : Module.finrank k (LinearMap.range (polarLin F p)) = 1 := by
    apply le_antisymm
    · simpa using Submodule.finrank_le (LinearMap.range (polarLin F p))
    · apply Nat.one_le_iff_ne_zero.mpr
      intro h0
      exact hne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
  rw [h1] at hr
  simp at hr
  omega

/-- At a point of a nonsingular cubic there is a vector independent of the point on the tangent line. -/
theorem IsNonsingularCubic.exists_tangent_vector {F : MvPolynomial (Fin 3) k}
    (hF : IsNonsingularCubic F) {p : Fin 3 → k} (hp : p ≠ 0) (hFp : eval p F = 0) :
    ∃ q, LinearIndependent k ![p, q] ∧ polarPairing F p q = 0 := by
  have hpW : p ∈ LinearMap.ker (polarLin F p) := by
    rw [LinearMap.mem_ker, polarLin_apply]
    exact polarPairing_self hF.isHomogeneous p hFp
  have h2 := hF.finrank_ker_polarLin hp hFp
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := k)
    (M := LinearMap.ker (polarLin F p)) (by omega) (x := ⟨p, hpW⟩) (by simpa using hp)
  refine ⟨y, ?_, ?_⟩
  · have := hy.map' (LinearMap.ker (polarLin F p)).subtype (Submodule.ker_subtype _)
    convert this using 1
    funext i; fin_cases i <;> rfl
  · have := y.2
    rwa [LinearMap.mem_ker, polarLin_apply] at this

/-- Any two vectors on the tangent line, one of them independent of the point, span it. -/
theorem IsNonsingularCubic.tangent_span {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    {p q q' : Fin 3 → k} (hpq : LinearIndependent k ![p, q]) (hFp : eval p F = 0)
    (hq : polarPairing F p q = 0) (hq' : polarPairing F p q' = 0) :
    ∃ a b : k, q' = a • p + b • q := by
  have hp0 : p ≠ 0 := hpq.ne_zero 0
  have hker := hF.finrank_ker_polarLin hp0 hFp
  have hle : Submodule.span k (Set.range ![p, q]) ≤ LinearMap.ker (polarLin F p) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · show p ∈ _
      rw [SetLike.mem_coe, LinearMap.mem_ker, polarLin_apply]
      exact polarPairing_self hF.isHomogeneous p hFp
    · show q ∈ _
      rw [SetLike.mem_coe, LinearMap.mem_ker, polarLin_apply]
      exact hq
  have hspan : Module.finrank k (Submodule.span k (Set.range ![p, q])) = 2 := by
    simpa using finrank_span_eq_card hpq
  have heq := Submodule.eq_of_le_of_finrank_eq hle (hspan.trans hker.symm)
  have hq'W : q' ∈ LinearMap.ker (polarLin F p) := by
    rw [LinearMap.mem_ker, polarLin_apply]; exact hq'
  rw [← heq] at hq'W
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hq'W
  exact ⟨c 0, c 1, by rw [← hc]; simp [Fin.sum_univ_two]⟩

/-- Existence of the third point. -/
theorem IsNonsingularCubic.exists_isThirdPoint {F : MvPolynomial (Fin 3) k}
    (hF : IsNonsingularCubic F) {P Q : ℙ k (Fin 3 → k)} (hP : P ∈ projectivePoints F k)
    (hQ : Q ∈ projectivePoints F k) : ∃ R, IsThirdPoint F P Q R := by
  have hH := hF.isHomogeneous
  have hP0 : eval P.rep F = 0 := by
    have h : aeval P.rep F = 0 := hP
    simpa [aeval_eq_eval] using h
  have hQ0 : eval Q.rep F = 0 := by
    have h : aeval Q.rep F = 0 := hQ
    simpa [aeval_eq_eval] using h
  by_cases hPQ : P = Q
  · subst hPQ
    obtain ⟨q, hind, hpol⟩ := hF.exists_tangent_vector P.rep_nonzero hP0
    obtain ⟨a0, a1, a2, a3, hsh⟩ :=
      binary_cubic_shape _ (lineRestriction_isHomogeneous hH P.rep q)
    have hco := cubicCoeffs_shape a0 a1 a2 a3
    rw [← hsh] at hco
    obtain ⟨e0, e1, e3⟩ := cubicCoeffs_lineRestriction F P.rep q
    rw [hco] at e0 e1 e3
    simp only at e0 e1 e3
    rw [hP0] at e0
    rw [hpol] at e1
    have hne := hF.lineRestriction_ne_zero hind
    have h23 : ¬ (a2 = 0 ∧ a3 = 0) := by
      rintro ⟨h2, h3⟩
      apply hne
      rw [hsh, e0, e1, h2, h3]
      simp
    have hne' : (-a3) • P.rep + a2 • q ≠ 0 := by
      intro h0
      obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hind _ _ h0
      exact h23 ⟨h2, by simpa using h1⟩
    refine ⟨Projectivization.mk k _ hne', q, 1, -a3, a2, one_ne_zero, hind,
      fun h => absurd rfl h, fun _ => hpol, ⟨hne', rfl⟩, ?_⟩
    rw [ite_X_of_eq rfl, hsh, e0, e1]
    simp only [map_zero, map_neg, map_one]
    ring
  · have hind : LinearIndependent k ![P.rep, Q.rep] :=
      Projectivization.linearIndependent_pair_iff_ne.mpr hPQ
    obtain ⟨a0, a1, a2, a3, hsh⟩ :=
      binary_cubic_shape _ (lineRestriction_isHomogeneous hH P.rep Q.rep)
    have hco := cubicCoeffs_shape a0 a1 a2 a3
    rw [← hsh] at hco
    obtain ⟨e0, e1, e3⟩ := cubicCoeffs_lineRestriction F P.rep Q.rep
    rw [hco] at e0 e1 e3
    simp only at e0 e1 e3
    rw [hP0] at e0
    rw [hQ0] at e3
    have hne := hF.lineRestriction_ne_zero hind
    have h12 : ¬ (a1 = 0 ∧ a2 = 0) := by
      rintro ⟨h1, h2⟩
      apply hne
      rw [hsh, e0, e3, h1, h2]
      simp
    have hne' : (-a2) • P.rep + a1 • Q.rep ≠ 0 := by
      intro h0
      obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hind _ _ h0
      exact h12 ⟨h2, by simpa using h1⟩
    refine ⟨Projectivization.mk k _ hne', Q.rep, 1, -a2, a1, one_ne_zero, hind,
      fun _ => ⟨Q.rep_nonzero, (Projectivization.mk_rep Q).symm⟩, fun h => absurd h hPQ,
      ⟨hne', rfl⟩, ?_⟩
    rw [ite_X_of_ne hPQ, hsh, e0, e3]
    simp only [map_zero, map_neg, map_one]
    ring

/-- A vector independent of `p` stays independent after adding a multiple of `p`. -/
theorem linearIndependent_pair_comb {p q : Fin 3 → k} (hind : LinearIndependent k ![p, q])
    (s : k) {t : k} (ht : t ≠ 0) : LinearIndependent k ![p, s • p + t • q] := by
  rw [LinearIndependent.pair_iff]
  intro x y h
  have h' := LinearIndependent.pair_iff.mp hind (x + y * s) (y * t) (by rw [← h]; module)
  have hy : y = 0 := by
    rcases mul_eq_zero.mp h'.2 with h | h
    · exact h
    · exact absurd h ht
  refine ⟨?_, hy⟩
  have := h'.1
  rw [hy] at this
  simpa using this

/-- A point `[s p + t q]` with `t ≠ 0` is different from the point `[p]`. -/
theorem mk_comb_ne {P : ℙ k (Fin 3 → k)} {q : Fin 3 → k} (hind : LinearIndependent k ![P.rep, q])
    (s : k) {t : k} (hne : s • P.rep + t • q ≠ 0) (ht : t ≠ 0) :
    P ≠ Projectivization.mk k (s • P.rep + t • q) hne := by
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k (s • P.rep + t • q) P.rep hne
    P.rep_nonzero).mp (h.symm.trans (Projectivization.mk_rep P).symm)
  have h0 : (a - s) • P.rep + (-t) • q = 0 := by
    have : (a - s) • P.rep + (-t) • q = a • P.rep - (s • P.rep + t • q) := by module
    rw [this, ha, sub_self]
  exact ht (by simpa using (LinearIndependent.pair_iff.mp hind _ _ h0).2)

/-- The point `[s p]` is `[p]`. -/
theorem mk_smul_eq {P : ℙ k (Fin 3 → k)} {s : k} (h : s • P.rep ≠ 0) :
    Projectivization.mk k (s • P.rep) h = P := by
  refine (Projectivization.mk_eq_mk_iff' k (s • P.rep) P.rep h P.rep_nonzero).mpr ⟨s, rfl⟩ |>.trans
    (Projectivization.mk_rep P)

/-- Uniqueness of the third point. -/
theorem IsNonsingularCubic.isThirdPoint_unique {F : MvPolynomial (Fin 3) k}
    (hF : IsNonsingularCubic F) {P Q R R' : ℙ k (Fin 3 → k)} (hP : P ∈ projectivePoints F k)
    (h : IsThirdPoint F P Q R) (h' : IsThirdPoint F P Q R') : R = R' := by
  have hP0 : eval P.rep F = 0 := by
    have h : aeval P.rep F = 0 := hP
    simpa [aeval_eq_eval] using h
  obtain ⟨q, c, s, t, hc, hind, hQ, htan, ⟨hne, hR⟩, hφ⟩ := h
  obtain ⟨q', c', s', t', hc', hind', hQ', htan', ⟨hne', hR'⟩, hφ'⟩ := h'
  subst hR hR'
  by_cases hPQ : P = Q
  · obtain ⟨α, β, hq'⟩ := hF.tangent_span hind hP0 (htan hPQ) (htan' hPQ)
    have hβ : β ≠ 0 := by
      rintro rfl
      have := LinearIndependent.pair_iff.mp hind' α (-1) (by rw [hq']; simp)
      simpa using this.2
    have hsub : lineRestriction F P.rep q' =
        aeval ![lin 1 α, lin 0 β] (lineRestriction F P.rep q) := by
      have := lineRestriction_lin' F P.rep q 1 0 α β
      rw [hq']
      simpa using this
    rw [ite_X_of_eq hPQ] at hφ hφ'
    have hφ2 : lineRestriction F P.rep q = C c * lin 0 1 * lin 0 1 * lin t (-s) := by
      rw [hφ]; simp only [lin, map_neg, map_zero, map_one]; ring
    have hφ2' : lineRestriction F P.rep q' = C c' * lin 0 1 * lin 0 1 * lin t' (-s') := by
      rw [hφ']; simp only [lin, map_neg, map_zero, map_one]; ring
    have key : C c' * lin 0 1 * lin 0 1 * lin t' (-s') =
        aeval ![lin 1 α, lin 0 β] (C c * lin 0 1 * lin 0 1 * lin t (-s)) := by
      rw [← hφ2', hsub, hφ2]
    simp only [map_mul, aeval_C, MvPolynomial.algebraMap_eq, lin_sub] at key
    have hc4 := congrArg cubicCoeffs key
    rw [cubicCoeffs_lin_mul, cubicCoeffs_lin_mul] at hc4
    simp only [Prod.mk.injEq] at hc4
    obtain ⟨_, _, e3, e4⟩ := hc4
    have e3' : c' * t' = c * β ^ 2 * t := by linear_combination e3
    have e4' : -(c' * s') = c * β ^ 2 * (t * α - s * β) := by linear_combination e4
    have hs : c' / (c * β ^ 3) * (s' + t' * α) = s := by
      field_simp
      linear_combination (-1) * e4' + α * e3'
    have ht : c' / (c * β ^ 3) * (t' * β) = t := by
      field_simp
      linear_combination e3'
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨c' / (c * β ^ 3), ?_⟩
    funext j
    rw [hq']
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (P.rep j) * hs + (q j) * ht
  · obtain ⟨hq0, hQq⟩ := hQ hPQ
    obtain ⟨hq0', hQq'⟩ := hQ' hPQ
    obtain ⟨β, hβq⟩ := (Projectivization.mk_eq_mk_iff' k q' q hq0' hq0).mp (hQq'.symm.trans hQq)
    have hβ : β ≠ 0 := by
      rintro rfl; apply hq0'; rw [← hβq]; simp
    have hsub : lineRestriction F P.rep q' =
        aeval ![lin 1 0, lin 0 β] (lineRestriction F P.rep q) := by
      have := lineRestriction_lin' F P.rep q 1 0 0 β
      rw [← hβq]
      simpa using this
    rw [ite_X_of_ne hPQ] at hφ hφ'
    have hφ2 : lineRestriction F P.rep q = C c * lin 0 1 * lin 1 0 * lin t (-s) := by
      rw [hφ]; simp only [lin, map_neg, map_zero, map_one]; ring
    have hφ2' : lineRestriction F P.rep q' = C c' * lin 0 1 * lin 1 0 * lin t' (-s') := by
      rw [hφ']; simp only [lin, map_neg, map_zero, map_one]; ring
    have key : C c' * lin 0 1 * lin 1 0 * lin t' (-s') =
        aeval ![lin 1 0, lin 0 β] (C c * lin 0 1 * lin 1 0 * lin t (-s)) := by
      rw [← hφ2', hsub, hφ2]
    simp only [map_mul, aeval_C, MvPolynomial.algebraMap_eq, lin_sub] at key
    have hc4 := congrArg cubicCoeffs key
    rw [cubicCoeffs_lin_mul, cubicCoeffs_lin_mul] at hc4
    simp only [Prod.mk.injEq] at hc4
    obtain ⟨_, e2, e3, _⟩ := hc4
    have e2' : c' * t' = c * β * t := by linear_combination e2
    have e3' : c' * s' = c * β ^ 2 * s := by linear_combination -e3
    have hs : c' / (c * β ^ 2) * s' = s := by
      field_simp
      linear_combination e3'
    have ht : c' / (c * β ^ 2) * (t' * β) = t := by
      field_simp
      linear_combination e2'
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨c' / (c * β ^ 2), ?_⟩
    funext j
    rw [← hβq]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (P.rep j) * hs + (q j) * ht

/-- The third point is symmetric in the two points. -/
theorem IsThirdPoint.comm {F : MvPolynomial (Fin 3) k} {P Q R : ℙ k (Fin 3 → k)}
    (h : IsThirdPoint F P Q R) : IsThirdPoint F Q P R := by
  by_cases hPQ : P = Q
  · subst hPQ; exact h
  · obtain ⟨q, c, s, t, hc, hind, hQ, htan, ⟨hne, hR⟩, hφ⟩ := h
    obtain ⟨hq0, hQq⟩ := hQ hPQ
    obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff' k Q.rep q Q.rep_nonzero hq0).mp
      ((Projectivization.mk_rep Q).trans hQq)
    have hu0 : u ≠ 0 := by
      rintro rfl; exact Q.rep_nonzero (by rw [← hu]; simp)
    have hsub : lineRestriction F Q.rep P.rep =
        aeval ![lin 0 1, lin u 0] (lineRestriction F P.rep q) := by
      have := lineRestriction_lin' F P.rep q 0 u 1 0
      rw [← hu]
      simpa using this
    rw [ite_X_of_ne hPQ] at hφ
    have hφ2 : lineRestriction F P.rep q = C c * lin 0 1 * lin 1 0 * lin t (-s) := by
      rw [hφ]; simp only [lin, map_neg, map_zero, map_one]; ring
    have hv : (-t) • Q.rep + (-(s * u)) • P.rep = (-u) • (s • P.rep + t • q) := by
      rw [← hu]; module
    have hw : (-t) • Q.rep + (-(s * u)) • P.rep ≠ 0 := by
      rw [hv]; exact smul_ne_zero (neg_ne_zero.mpr hu0) hne
    refine ⟨P.rep, c * u, -t, -(s * u), mul_ne_zero hc hu0,
      Projectivization.linearIndependent_pair_iff_ne.mpr (Ne.symm hPQ),
      fun _ => ⟨P.rep_nonzero, (Projectivization.mk_rep P).symm⟩, fun h => absurd h.symm hPQ,
      ⟨hw, ?_⟩, ?_⟩
    · rw [hR]
      refine (Projectivization.mk_eq_mk_iff' k _ _ hne hw).mpr ⟨(-u)⁻¹, ?_⟩
      rw [hv, inv_smul_smul₀ (neg_ne_zero.mpr hu0)]
    · rw [ite_X_of_ne (Ne.symm hPQ), hsub, hφ2]
      simp only [map_mul, aeval_C, MvPolynomial.algebraMap_eq, lin_sub]
      simp only [lin, map_neg, map_mul, map_add, map_zero, map_one]
      ring

/-- Given the third point `R` of `P, Q`, the third point of `P, R` is `Q`. -/
theorem IsThirdPoint.swap {F : MvPolynomial (Fin 3) k} {P Q R : ℙ k (Fin 3 → k)}
    (h : IsThirdPoint F P Q R) : IsThirdPoint F P R Q := by
  have h0 := h
  obtain ⟨q, c, s, t, hc, hind, hQ, htan, ⟨hne, hR⟩, hφ⟩ := h
  have hq0 : q ≠ 0 := hind.ne_zero 1
  by_cases ht : t = 0
  · -- the third point is `P` itself
    subst ht
    have hs : s ≠ 0 := by rintro rfl; apply hne; simp
    have hRP : R = P := by
      rw [hR]
      have hne2 : s • P.rep ≠ 0 := smul_ne_zero hs P.rep_nonzero
      have : Projectivization.mk k (s • P.rep + (0 : k) • q) hne = Projectivization.mk k (s • P.rep) hne2 :=
        (Projectivization.mk_eq_mk_iff' k _ _ hne hne2).mpr ⟨1, by simp⟩
      rw [this]
      exact mk_smul_eq hne2
    by_cases hPQ : P = Q
    · rw [hRP]; subst hPQ; rw [hRP] at h0; exact h0
    · rw [hRP]
      obtain ⟨hq1, hQq⟩ := hQ hPQ
      rw [ite_X_of_ne hPQ] at hφ
      have hφ2 : lineRestriction F P.rep q = C c * lin 0 1 * lin 1 0 * lin 0 (-s) := by
        rw [hφ]; simp only [lin, map_neg, map_zero, map_one]; ring
      have hpol : polarPairing F P.rep q = 0 := by
        have := (cubicCoeffs_lineRestriction F P.rep q).2.1
        rw [hφ2, cubicCoeffs_lin_mul] at this
        simp at this
        exact this.symm
      have hne2 : (0 : k) • P.rep + (1 : k) • q ≠ 0 := by simpa using hq1
      refine ⟨q, -(c * s), 0, 1, neg_ne_zero.mpr (mul_ne_zero hc hs), hind,
        fun h => absurd rfl h, fun _ => hpol, ⟨hne2, ?_⟩, ?_⟩
      · exact hQq.trans ((Projectivization.mk_eq_mk_iff' k _ _ hq1 hne2).mpr ⟨1, by simp⟩)
      · rw [ite_X_of_eq rfl, hφ]
        simp only [map_neg, map_mul, map_zero, map_one]
        ring
  · have hind2 := linearIndependent_pair_comb hind s ht
    have hRne : P ≠ R := by rw [hR]; exact mk_comb_ne hind s hne ht
    have hne2 : (-s) • P.rep + (1 : k) • (s • P.rep + t • q) ≠ 0 := by
      have : (-s) • P.rep + (1 : k) • (s • P.rep + t • q) = t • q := by module
      rw [this]; exact smul_ne_zero ht hq0
    by_cases hPQ : P = Q
    · subst hPQ
      rw [ite_X_of_eq rfl] at hφ
      have hφ2 : lineRestriction F P.rep q = C c * lin 0 1 * lin 0 1 * lin t (-s) := by
        rw [hφ]; simp only [lin, map_neg, map_zero, map_one]; ring
      have hsub : lineRestriction F P.rep (s • P.rep + t • q) =
          aeval ![lin 1 s, lin 0 t] (lineRestriction F P.rep q) := by
        have := lineRestriction_lin' F P.rep q 1 0 s t
        simpa using this
      have hne3 : (-1 : k) • P.rep + (0 : k) • (s • P.rep + t • q) ≠ 0 := by
        simpa using P.rep_nonzero
      refine ⟨s • P.rep + t • q, c * t ^ 3, -1, 0, mul_ne_zero hc (pow_ne_zero 3 ht), hind2,
        fun _ => ⟨hne, hR⟩, fun h => absurd h hRne, ⟨hne3, ?_⟩, ?_⟩
      · refine (Projectivization.mk_rep P).symm.trans ?_
        exact (Projectivization.mk_eq_mk_iff' k _ _ P.rep_nonzero hne3).mpr ⟨-1, by simp⟩
      · rw [ite_X_of_ne hRne, hsub, hφ2]
        simp only [map_mul, aeval_C, MvPolynomial.algebraMap_eq, lin_sub]
        simp only [lin, map_neg, map_mul, map_add, map_zero, map_one, map_pow]
        ring
    · obtain ⟨hq1, hQq⟩ := hQ hPQ
      rw [ite_X_of_ne hPQ] at hφ
      have hφ2 : lineRestriction F P.rep q = C c * lin 0 1 * lin 1 0 * lin t (-s) := by
        rw [hφ]; simp only [lin, map_neg, map_zero, map_one]; ring
      have hsub : lineRestriction F P.rep (s • P.rep + t • q) =
          aeval ![lin 1 s, lin 0 t] (lineRestriction F P.rep q) := by
        have := lineRestriction_lin' F P.rep q 1 0 s t
        simpa using this
      refine ⟨s • P.rep + t • q, c * t ^ 2, -s, 1, mul_ne_zero hc (pow_ne_zero 2 ht), hind2,
        fun _ => ⟨hne, hR⟩, fun h => absurd h hRne, ⟨hne2, ?_⟩, ?_⟩
      · have hne4 : t • q ≠ 0 := smul_ne_zero ht hq0
        refine hQq.trans ((Projectivization.mk_eq_mk_iff' k _ _ hq1 hne2).mpr ⟨t⁻¹, ?_⟩)
        have : (-s) • P.rep + (1 : k) • (s • P.rep + t • q) = t • q := by module
        rw [this, inv_smul_smul₀ ht]
      · rw [ite_X_of_ne hRne, hsub, hφ2]
        simp only [map_mul, aeval_C, MvPolynomial.algebraMap_eq, lin_sub]
        simp only [lin, map_neg, map_mul, map_add, map_zero, map_one, map_pow]
        ring

/-- The chord and tangent construction (p. 34): for a nonsingular cubic and $P, Q \in C(k)$ there is
exactly one third point $PQ$, and it lies in $C(k)$.  (Milne argues with Bezout's theorem and the Galois
action; here directly: the restriction of `F` to the line is a binary cubic with the known zeros, not
identically zero because a nonsingular cubic contains no line.) -/
@[kb "milne2006ec" "Ch. I, §3, the chord and tangent construction, pdf p. 34"]
theorem exists_unique_isThirdPoint {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    {P Q : ℙ k (Fin 3 → k)} (hP : P ∈ projectivePoints F k) (hQ : Q ∈ projectivePoints F k) :
    ∃! R, IsThirdPoint F P Q R := by
  obtain ⟨R, hR⟩ := hF.exists_isThirdPoint hP hQ
  exact ⟨R, hR, fun R' hR' => hF.isThirdPoint_unique hP hR' hR⟩

/-- The third point lies on the curve. -/
theorem IsThirdPoint.mem {F : MvPolynomial (Fin 3) k} {P Q R : ℙ k (Fin 3 → k)}
    (h : IsThirdPoint F P Q R) : R ∈ projectivePoints F k := by
  obtain ⟨q, c, s, t, hc, hind, hQ, htan, ⟨hne, hR⟩, hφ⟩ := h
  subst hR
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k (s • P.rep + t • q) hne
  show aeval (Projectivization.mk k _ hne).rep F = 0
  rw [← ha]
  have h1 := aeval_aeval_line F P.rep q (K := k) ((a : k) * s) ((a : k) * t)
  have h2 : aeval ![(a : k) * s, (a : k) * t] (lineRestriction F P.rep q) = 0 := by
    rw [hφ]
    split_ifs <;> simp only [map_mul, map_sub, aeval_C, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Algebra.algebraMap_self, RingHom.id_apply] <;> ring
  have h3 : ((a : kˣ) • (s • P.rep + t • q) : Fin 3 → k) =
      fun j => algebraMap k k (P.rep j) * ((a : k) * s) + algebraMap k k (q j) * ((a : k) * t) := by
    funext j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Units.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply]
    ring
  rw [h3, ← h1]
  exact h2

/-- The points $C(k)$, as a type. -/
abbrev CurvePoints (F : MvPolynomial (Fin 3) k) := ↥(projectivePoints F k)

/-- The third point $PQ$, as an operation on $C(k)$. -/
noncomputable def thirdPoint {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    (P Q : CurvePoints F) : CurvePoints F :=
  ⟨(exists_unique_isThirdPoint hF P.2 Q.2).exists.choose,
    (exists_unique_isThirdPoint hF P.2 Q.2).exists.choose_spec.mem⟩

/-- The third point `PQ` satisfies `IsThirdPoint`. -/
theorem isThirdPoint_thirdPoint {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    (P Q : CurvePoints F) : IsThirdPoint F P.1 Q.1 (thirdPoint hF P Q).1 :=
  (exists_unique_isThirdPoint hF P.2 Q.2).exists.choose_spec

/-- Any point satisfying `IsThirdPoint` is the third point `PQ`. -/
theorem thirdPoint_eq_of {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    {P Q R : CurvePoints F} (h : IsThirdPoint F P.1 Q.1 R.1) : thirdPoint hF P Q = R :=
  Subtype.ext ((exists_unique_isThirdPoint hF P.2 Q.2).unique (isThirdPoint_thirdPoint hF P Q) h)

/-- The third point is symmetric: $PQ = QP$. -/
theorem thirdPoint_comm {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    (P Q : CurvePoints F) : thirdPoint hF P Q = thirdPoint hF Q P :=
  (thirdPoint_eq_of hF (isThirdPoint_thirdPoint hF P Q).comm).symm

/-- $P(PQ) = Q$. -/
theorem thirdPoint_thirdPoint_left {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    (P Q : CurvePoints F) : thirdPoint hF P (thirdPoint hF P Q) = Q :=
  thirdPoint_eq_of hF (isThirdPoint_thirdPoint hF P Q).swap

/-- $Y(OY) = O$: the three points $O$, $Y$, $OY$ are collinear. -/
theorem thirdPoint_thirdPoint_right {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    (O Y : CurvePoints F) : thirdPoint hF Y (thirdPoint hF O Y) = O :=
  thirdPoint_eq_of hF (isThirdPoint_thirdPoint hF O Y).comm.swap

/-- The chord and tangent law of composition (p. 34): $P + Q = O(PQ)$. -/
@[kb "milne2006ec" "Ch. I, §3, Def. of P + Q = O(PQ), pdf p. 34"]
noncomputable def chordAdd {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    (O P Q : CurvePoints F) : CurvePoints F :=
  thirdPoint hF O (thirdPoint hF P Q)

/-- **Theorem 3.1** (p. 35), the parts proved in the text (p. 35): the law of composition is
commutative, `O` is a zero element, and $P' = P(OO)$ is a negative of `P`. -/
@[kb "milne2006ec" "Ch. I, Thm. 3.1 (commutativity, zero, negatives), pdf p. 35"]
theorem theorem_3_1_comm_zero_neg {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F)
    (O : CurvePoints F) :
    (∀ P Q, chordAdd hF O P Q = chordAdd hF O Q P) ∧ (∀ P, chordAdd hF O O P = P) ∧
      ∀ P, chordAdd hF O P (thirdPoint hF P (thirdPoint hF O O)) = O := by
  refine ⟨fun P Q => ?_, fun P => ?_, fun P => ?_⟩
  · unfold chordAdd; rw [thirdPoint_comm hF P Q]
  · unfold chordAdd; rw [thirdPoint_thirdPoint_left hF O P]
  · unfold chordAdd
    rw [thirdPoint_thirdPoint_left hF P (thirdPoint hF O O), thirdPoint_thirdPoint_left hF O O]

/-- **Theorem 3.1**, associativity (p. 35), as a named statement: for a nonsingular projective plane
cubic over a perfect field and $O \in C(k)$, the chord and tangent law is associative.  (Milne: sketch
by Proposition 3.2 with Fulton 1969, p. 124 for the degenerate cases; or by Riemann–Roch, §4.) -/
@[kb "milne2006ec" "Ch. I, Thm. 3.1 (associativity), pdf p. 35"]
structure Thm3_1 : Prop where
  assoc : ∀ (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k)
    (hF : IsNonsingularCubic F) (O P Q R : CurvePoints F),
    chordAdd hF O (chordAdd hF O P Q) R = chordAdd hF O P (chordAdd hF O Q R)

/-- **Theorem 3.1** (p. 35): the chord and tangent construction makes $C(k)$ into a commutative group
with zero `O` (given the named statement `Thm3_1` for associativity). -/
@[kb "milne2006ec" "Ch. I, Thm. 3.1, pdf p. 35", reducible]
noncomputable def theorem_3_1 (h : Thm3_1) {k : Type} [Field k] [PerfectField k]
    {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F) (O : CurvePoints F) :
    AddCommGroup (CurvePoints F) where
  add := chordAdd hF O
  add_assoc := h.assoc k F hF O
  zero := O
  zero_add := (theorem_3_1_comm_zero_neg hF O).2.1
  add_zero P := by
    show chordAdd hF O P O = P
    rw [(theorem_3_1_comm_zero_neg hF O).1 P O]
    exact (theorem_3_1_comm_zero_neg hF O).2.1 P
  neg P := thirdPoint hF P (thirdPoint hF O O)
  neg_add_cancel P := by
    show chordAdd hF O (thirdPoint hF P (thirdPoint hF O O)) P = O
    rw [(theorem_3_1_comm_zero_neg hF O).1]
    exact (theorem_3_1_comm_zero_neg hF O).2.2 P
  add_comm := (theorem_3_1_comm_zero_neg hF O).1
  nsmul := @nsmulRec _ ⟨O⟩ ⟨chordAdd hF O⟩
  zsmul := @zsmulRec _ ⟨O⟩ ⟨chordAdd hF O⟩ ⟨fun P => thirdPoint hF P (thirdPoint hF O O)⟩
    (@nsmulRec _ ⟨O⟩ ⟨chordAdd hF O⟩)

/-- The group of `theorem_3_1` has the chord and tangent addition and zero `O`. -/
theorem theorem_3_1_add (h : Thm3_1) {k : Type} [Field k] [PerfectField k]
    {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F) (O P Q : CurvePoints F) :
    (letI := theorem_3_1 h hF O; P + Q) = chordAdd hF O P Q ∧
      (letI := theorem_3_1 h hF O; (0 : CurvePoints F)) = O :=
  ⟨rfl, rfl⟩

/-- Collinear points in the group (used for Theorem 2.1 and Remark 4.11): with zero `O`,
$PQ = (OO) - P - Q$ (given the named statement `Thm3_1`). -/
theorem thirdPoint_eq_sub (h : Thm3_1) {k : Type} [Field k] [PerfectField k]
    {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F) (O P Q : CurvePoints F) :
    letI := theorem_3_1 h hF O
    thirdPoint hF P Q = thirdPoint hF O O - P - Q := by
  let _ := theorem_3_1 h hF O
  have key : ∀ Y : CurvePoints F, Y + thirdPoint hF O Y = thirdPoint hF O O := by
    intro Y
    show chordAdd hF O Y (thirdPoint hF O Y) = _
    unfold chordAdd
    rw [thirdPoint_thirdPoint_right hF O Y]
  have hPQ : P + Q = thirdPoint hF O (thirdPoint hF P Q) := rfl
  have h2 : thirdPoint hF P Q + (P + Q) = thirdPoint hF O O := by
    rw [hPQ]; exact key _
  rw [sub_sub]
  exact eq_sub_of_add_eq h2

/-- **Remark 4.11** (p. 43): choosing a different zero $O'$ translates the group law: $P +' Q = P + Q - O'$
in the group with zero `O` (given the named statement `Thm3_1`). -/
@[kb "milne2006ec" "Ch. I, Rem. 4.11, pdf p. 43"]
theorem remark_4_11 (h : Thm3_1) {k : Type} [Field k] [PerfectField k]
    {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F) (O O' P Q : CurvePoints F) :
    letI := theorem_3_1 h hF O
    chordAdd hF O' P Q = P + Q - O' := by
  let _ := theorem_3_1 h hF O
  have e1 : thirdPoint hF O' (thirdPoint hF P Q) =
      thirdPoint hF O O - O' - thirdPoint hF P Q := thirdPoint_eq_sub h hF O O' _
  have e2 : thirdPoint hF P Q = thirdPoint hF O O - P - Q := thirdPoint_eq_sub h hF O P Q
  show thirdPoint hF O' (thirdPoint hF P Q) = P + Q - O'
  rw [e1, e2]
  abel

/-- **Proposition 3.2** (p. 35), as a named statement (Milne: proof in general position, Walker 1950,
III 6.2 in general): over an algebraically closed field, if two cubic curves meet in exactly nine points,
then every cubic curve passing through eight of the points also passes through the ninth. -/
@[kb "milne2006ec" "Ch. I, Prop. 3.2, pdf p. 35"]
structure Prop3_2 : Prop where
  cayley_bacharach : ∀ (k : Type) [Field k] [IsAlgClosed k] (F G H : MvPolynomial (Fin 3) k),
    IsProjectivePlaneCurve F → curveDegree F = 3 → IsProjectivePlaneCurve G → curveDegree G = 3 →
    IsProjectivePlaneCurve H → curveDegree H = 3 →
    ∀ S : Finset (ℙ k (Fin 3 → k)), S.card = 9 →
      (S : Set _) = projectivePoints F k ∩ projectivePoints G k →
      ∀ P ∈ S, (∀ Q ∈ S, Q ≠ P → Q ∈ projectivePoints H k) → P ∈ projectivePoints H k

/-- The points obtained from a set `S` by successive chord and tangent constructions: the smallest set
containing `S` and closed under $P, Q \mapsto PQ$. -/
def chordTangentClosure (F : MvPolynomial (Fin 3) k) (S : Set (ℙ k (Fin 3 → k))) :
    Set (ℙ k (Fin 3 → k)) :=
  ⋂₀ {T | S ⊆ T ∧ ∀ P Q R, P ∈ T → Q ∈ T → IsThirdPoint F P Q R → R ∈ T}

/-- **Theorem 2.1 (Mordell's finite basis theorem)** (p. 28), as a named statement: for a nonsingular
cubic curve `C` over $\mathbb Q$ there is a finite set of points of $C(\mathbb Q)$ from which every point of
$C(\mathbb Q)$ is obtained by successive chord and tangent constructions. -/
@[kb "milne2006ec" "Ch. I, Thm. 2.1, pdf p. 28"]
structure Thm2_1 : Prop where
  finite_basis : ∀ F : MvPolynomial (Fin 3) ℚ, IsNonsingularCubic F →
    ∃ S : Set (ℙ ℚ (Fin 3 → ℚ)), S.Finite ∧ S ⊆ projectivePoints F ℚ ∧
      projectivePoints F ℚ ⊆ chordTangentClosure F S

/-- After Theorem 2.1 (p. 28): $C(\mathbb Q)$, if nonempty, is a finitely generated group (given the named
statements `Thm2_1` and `Thm3_1`): every third point $PQ$ equals $(OO) - P - Q$ in the group, so the
chord and tangent closure of `S` lies in the subgroup generated by `S` and `OO`. -/
@[kb "milne2006ec" "Ch. I, §2, after Thm. 2.1: C(Q) is finitely generated, pdf p. 28"]
theorem fg_of_thm2_1 (h₁ : Thm2_1) (h₃ : Thm3_1) {F : MvPolynomial (Fin 3) ℚ}
    (hF : IsNonsingularCubic F) (O : CurvePoints F) :
    letI := theorem_3_1 h₃ hF O
    AddGroup.FG (CurvePoints F) := by
  let _ := theorem_3_1 h₃ hF O
  obtain ⟨S, hSfin, hSsub, hSclo⟩ := h₁.finite_basis F hF
  rw [AddGroup.fg_iff]
  refine ⟨(Subtype.val ⁻¹' S) ∪ {thirdPoint hF O O}, ?_,
    (hSfin.preimage Subtype.val_injective.injOn).union (Set.finite_singleton _)⟩
  rw [eq_top_iff]
  intro x _
  have hx := Set.mem_sInter.mp (hSclo x.2)
    {y | ∃ hy : y ∈ projectivePoints F ℚ, (⟨y, hy⟩ : CurvePoints F) ∈
      AddSubgroup.closure ((Subtype.val ⁻¹' S) ∪ {thirdPoint hF O O})} ?_
  · obtain ⟨_, hyH⟩ := hx
    exact hyH
  · refine ⟨fun y hy => ⟨hSsub hy, AddSubgroup.subset_closure (Or.inl hy)⟩, ?_⟩
    intro P Q R hP hQ hPQR
    obtain ⟨hPm, hPH⟩ := hP
    obtain ⟨hQm, hQH⟩ := hQ
    have hRm := hPQR.mem
    refine ⟨hRm, ?_⟩
    have e : thirdPoint hF ⟨P, hPm⟩ ⟨Q, hQm⟩ = ⟨R, hRm⟩ := thirdPoint_eq_of hF hPQR
    have e2 : thirdPoint hF (⟨P, hPm⟩ : CurvePoints F) ⟨Q, hQm⟩ =
        thirdPoint hF O O - ⟨P, hPm⟩ - ⟨Q, hQm⟩ := thirdPoint_eq_sub h₃ hF O _ _
    rw [← e, e2]
    exact sub_mem (sub_mem (AddSubgroup.subset_closure (Or.inr rfl)) hPH) hQH

end NumberFieldKB.MilneEC
