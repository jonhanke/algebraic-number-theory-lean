import NumberFieldKB.MilneEC.Ch1Intersection
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Group.Translate
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Milne, Elliptic Curves, Chapter I, Section 1: projective plane curves; Bezout's theorem

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §1, subsections "Projective plane curves" and
"Bezout's theorem" (pdf pp. 19–22): projective plane curves and their points, the affine pieces,
Examples 1.15, 1.16, Exercise 1.17, Theorem 1.18 (Bezout, a named statement), Example 1.20 (with the
definition of a point of inflection), Remark 1.21.

Conventions.
* Homogeneous polynomials in three variables are elements of `MvPolynomial (Fin 3) k`, with
  $(X, Y, Z)$ = (`X 0`, `X 1`, `X 2`), as in Mathlib's `WeierstrassCurve.Projective`.
* The projective plane over a field `K` is Mathlib's `ℙ K (Fin 3 → K)`.
* The affine piece $U_i$ is where the `i`-th coordinate is nonzero.  Milne identifies $U_2$ with the plane
  by $(x : y : z) \mapsto (x/z, y/z)$, $U_1$ by $(x : y : z) \mapsto (x/y, z/y)$ and $U_0$ by
  $(x : y : z) \mapsto (y/x, z/x)$ (`pieceCoords`); the curve $C \cap U_i$ is then the affine curve of
  $F(1, Y, Z)$, $F(X, 1, Z)$, $F(X, Y, 1)$ (`dehomogenize`), each as a polynomial in the two remaining
  variables, in order.
* Notions at a point of a projective curve (nonsingularity, intersection numbers) are defined on one
  affine piece containing the point; we use the last nonzero coordinate (`pieceIndex`).  Exercise 1.17
  shows that nonsingularity does not depend on the piece.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-- **Projective plane curve** (p. 20): a nonconstant homogeneous polynomial `F ∈ k[X, Y, Z]` with no
repeated factor in $k^{\mathrm{al}}[X, Y, Z]$ defines a projective plane curve $C_F$ over `k`. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of projective plane curve, pdf p. 20"]
def IsProjectivePlaneCurve (F : MvPolynomial (Fin 3) k) : Prop :=
  F.IsHomogeneous F.totalDegree ∧ F.totalDegree ≠ 0 ∧
    Squarefree (baseChange (AlgebraicClosure k) F)

/-- The **degree** of a projective plane curve $C_F$ (p. 20) is the degree of `F`. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of the degree of a projective plane curve, pdf p. 20"]
noncomputable abbrev curveDegree (F : MvPolynomial (Fin 3) k) : ℕ := F.totalDegree

/-- The points of $C_F$ in a field `K` containing `k` (p. 20):
$C_F(K) = \{(x : y : z) \in \mathbb P^2(K) \mid F(x, y, z) = 0\}$ (well defined because `F` is
homogeneous; see `mem_projectivePoints_mk`). -/
@[kb "milne2006ec" "Ch. I, §1, Def. of C_F(K) for a projective curve, pdf p. 20"]
def projectivePoints (F : MvPolynomial (Fin 3) k) (K : Type*) [Field K] [Algebra k K] :
    Set (ℙ K (Fin 3 → K)) :=
  {P | aeval P.rep F = 0}

/-- Evaluating a homogeneous polynomial of degree `e` at a scalar multiple of a vector multiplies the
value by the `e`-th power of the scalar. -/
theorem aeval_smul_of_isHomogeneous {σ : Type*} {G : MvPolynomial σ k} {e : ℕ}
    (hG : G.IsHomogeneous e) {K : Type*} [Field K] [Algebra k K] (c : K) (v : σ → K) :
    aeval (c • v) G = c ^ e * aeval v G := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : (∑ i ∈ d.support, d i) = e := by
    have := hG (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have : ∏ i ∈ d.support, (c • v) i ^ d i = c ^ e * ∏ i ∈ d.support, v i ^ d i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
  rw [this]; ring

/-- A nonzero vector is a nonzero scalar multiple of the chosen representative of its class. -/
theorem exists_smul_rep {K : Type*} [Field K] (v : Fin 3 → K) (hv : v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ v = c • (Projectivization.mk K v hv).rep := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K v _ hv
    (Projectivization.mk K v hv).rep_nonzero).mp
    (Projectivization.mk_rep (Projectivization.mk K v hv)).symm
  exact ⟨a, a.ne_zero, ha.symm⟩

/-- Membership in $C_F(K)$ can be tested on any representative, because
$F(cx, cy, cz) = c^{\deg F} F(x, y, z)$ (p. 20). -/
theorem mem_projectivePoints_mk {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    {K : Type*} [Field K] [Algebra k K] (v : Fin 3 → K) (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ projectivePoints F K ↔ aeval v F = 0 := by
  obtain ⟨c, hc, hvc⟩ := exists_smul_rep v hv
  show aeval (Projectivization.mk K v hv).rep F = 0 ↔ _
  conv_rhs => rw [hvc, aeval_smul_of_isHomogeneous hF]
  simp [hc]

/-- The substitution giving the affine piece `i`: $F(1, Y, Z)$, $F(X, 1, Z)$, $F(X, Y, 1)$, the two
remaining variables renamed `X 0`, `X 1` in order. -/
noncomputable def pieceSubst {R : Type*} [CommRing R] : Fin 3 → Fin 3 → MvPolynomial (Fin 2) R
  | 0 => ![1, X 0, X 1]
  | 1 => ![X 0, 1, X 1]
  | 2 => ![X 0, X 1, 1]

/-- The affine curve $C_i = C \cap U_i$ (p. 20): `F` with the `i`-th variable set to 1. -/
@[kb "milne2006ec" "Ch. I, §1, the affine pieces C_0, C_1, C_2 of a projective curve, pdf p. 20"]
noncomputable def dehomogenize {R : Type*} [CommRing R] (i : Fin 3) (F : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 2) R :=
  aeval (pieceSubst i) F

/-- The affine coordinates on the piece $U_i$ of a vector `v` with `v i ≠ 0` (p. 20). -/
noncomputable def pieceCoords {K : Type*} [Field K] (i : Fin 3) (v : Fin 3 → K) : K × K :=
  match i with
  | 0 => (v 1 / v 0, v 2 / v 0)
  | 1 => (v 0 / v 1, v 2 / v 1)
  | 2 => (v 0 / v 2, v 1 / v 2)

/-- The value of the dehomogenization at the affine coordinates of `v` is the value of `F` at the
vector `v` scaled to have `i`-th coordinate 1. -/
theorem evalAt_dehomogenize (F : MvPolynomial (Fin 3) k) {K : Type*} [Field K] [Algebra k K]
    (i : Fin 3) (v : Fin 3 → K) (hv : v i ≠ 0) :
    evalAt (dehomogenize i F) (pieceCoords i v) = aeval ((v i)⁻¹ • v) F := by
  unfold evalAt dehomogenize
  rw [comp_aeval_apply]
  refine congrArg (fun w => aeval w F) ?_
  funext j
  fin_cases i <;> fin_cases j <;>
    simp_all [pieceSubst, pieceCoords, div_eq_inv_mul]

/-- On the piece $U_i$, the points of $C_F$ are the points of the affine curve $C_i$ (p. 20). -/
@[kb "milne2006ec" "Ch. I, §1, C ∩ U_i is the affine curve C_i, pdf p. 20"]
theorem aeval_eq_zero_iff_mem_piece {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    {K : Type*} [Field K] [Algebra k K] (i : Fin 3) (v : Fin 3 → K) (hv : v i ≠ 0) :
    aeval v F = 0 ↔ pieceCoords i v ∈ affinePoints (dehomogenize i F) K := by
  show _ ↔ evalAt _ _ = 0
  rw [evalAt_dehomogenize F i v hv, aeval_smul_of_isHomogeneous hF]
  simp [hv]

/-- $\mathbb P^2 = U_0 \cup U_1 \cup U_2$ (p. 20): every nonzero vector has a nonzero coordinate. -/
theorem exists_ne_zero_coord {K : Type*} [Field K] (v : Fin 3 → K) (hv : v ≠ 0) : ∃ i, v i ≠ 0 := by
  by_contra h
  exact hv (funext fun i => not_not.mp (not_exists.mp h i))

open Classical in
/-- The piece used to define local notions at a point: the last nonzero coordinate. -/
noncomputable def pieceIndex {K : Type*} [Field K] (v : Fin 3 → K) : Fin 3 :=
  if v 2 ≠ 0 then 2 else if v 1 ≠ 0 then 1 else 0

/-- `P` is a **nonsingular point** of the projective curve $C_F$ (p. 21): it is a nonsingular point of the
affine piece containing it (Exercise 1.17 shows that the choice of piece does not matter). -/
@[kb "milne2006ec" "Ch. I, §1, nonsingular points of a projective curve, pdf p. 21"]
def IsNonsingularProjPoint (F : MvPolynomial (Fin 3) k) {K : Type*} [Field K] [Algebra k K]
    (P : ℙ K (Fin 3 → K)) : Prop :=
  IsNonsingularPoint (dehomogenize (pieceIndex P.rep) F) (pieceCoords (pieceIndex P.rep) P.rep)

/-- A projective plane curve is **nonsingular** if all its points over $k^{\mathrm{al}}$ are
nonsingular. -/
@[kb "milne2006ec" "Ch. I, §1, nonsingular projective plane curve, pdf p. 21"]
def IsNonsingularProjCurve (F : MvPolynomial (Fin 3) k) : Prop :=
  ∀ P ∈ projectivePoints F (AlgebraicClosure k), IsNonsingularProjPoint F P

/-- The gradient of `F` at a vector `v`, as the linear form
$(\partial F/\partial X)_v X + (\partial F/\partial Y)_v Y + (\partial F/\partial Z)_v Z$ over `K`
(the polar line of Exercise 1.17). -/
noncomputable def polarLine (F : MvPolynomial (Fin 3) k) {K : Type*} [Field K] [Algebra k K]
    (v : Fin 3 → K) : MvPolynomial (Fin 3) K :=
  ∑ j : Fin 3, C (aeval v (pderiv j F)) * X j

/-- Chain rule for a partial derivative of a substitution `F(s_0, s_1, s_2)`. -/
theorem pderiv_aeval_fin_three (s : Fin 3 → MvPolynomial (Fin 2) k) (a : Fin 2)
    (F : MvPolynomial (Fin 3) k) :
    pderiv a (aeval s F) = ∑ j, aeval s (pderiv j F) * pderiv a (s j) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, aeval_X, pderiv_mul, hp]
    simp only [pderiv_mul, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · simp [pderiv_X, Pi.single_apply]

/-- The two variables of the affine piece `i`, as variables of the projective coordinates. -/
def pieceVar : Fin 3 → Fin 2 → Fin 3
  | 0 => ![1, 2]
  | 1 => ![0, 2]
  | 2 => ![0, 1]

theorem pieceVar_ne (i : Fin 3) (a : Fin 2) : pieceVar i a ≠ i := by
  revert i a; decide

theorem exists_pieceVar (i j : Fin 3) (h : j ≠ i) : ∃ a, pieceVar i a = j := by
  revert i j; decide

theorem pderiv_pieceSubst (i j : Fin 3) (a : Fin 2) :
    pderiv a (pieceSubst i j : MvPolynomial (Fin 2) k) = if j = pieceVar i a then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> simp [pieceSubst, pieceVar, pderiv_X]

/-- Partial derivatives commute with dehomogenization, up to the renaming of variables. -/
theorem pderiv_dehomogenize (F : MvPolynomial (Fin 3) k) (i : Fin 3) (a : Fin 2) :
    pderiv a (dehomogenize i F) = dehomogenize i (pderiv (pieceVar i a) F) := by
  unfold dehomogenize
  rw [pderiv_aeval_fin_three]
  simp [pderiv_pieceSubst]

/-- The value of a partial derivative of the dehomogenization. -/
theorem evalAt_pderiv_dehomogenize {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    {K : Type*} [Field K] [Algebra k K] (i : Fin 3) (v : Fin 3 → K) (hv : v i ≠ 0) (a : Fin 2) :
    evalAt (pderiv a (dehomogenize i F)) (pieceCoords i v) =
      ((v i)⁻¹) ^ (d - 1) * aeval v (pderiv (pieceVar i a) F) := by
  rw [pderiv_dehomogenize, evalAt_dehomogenize _ i v hv,
    aeval_smul_of_isHomogeneous hF.pderiv]

/-- Euler's identity evaluated at a vector. -/
theorem euler_eval {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    {K : Type*} [Field K] [Algebra k K] (v : Fin 3 → K) :
    ∑ j, v j * aeval v (pderiv j F) = d * aeval v F := by
  have := congrArg (aeval v) hF.sum_X_mul_pderiv
  simpa [map_sum, nsmul_eq_mul] using this

/-- A point is singular on the affine piece `i` exactly when `F` and its partial derivatives vanish
at a representative. -/
theorem isSingularPoint_dehomogenize_iff {F : MvPolynomial (Fin 3) k} {d : ℕ}
    (hF : F.IsHomogeneous d) {K : Type*} [Field K] [Algebra k K] (v : Fin 3 → K) (i : Fin 3)
    (hv : v i ≠ 0) :
    IsSingularPoint (dehomogenize i F) (pieceCoords i v) ↔
      aeval v F = 0 ∧ ∀ j, aeval v (pderiv j F) = 0 := by
  have hu : ((v i)⁻¹) ^ (d - 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hv)
  have hmem := aeval_eq_zero_iff_mem_piece hF i v hv
  unfold IsSingularPoint
  have h0 : (pieceCoords i v ∈ affinePoints (dehomogenize i F) K) ↔ aeval v F = 0 := hmem.symm
  rw [h0]
  have hX := evalAt_pderiv_dehomogenize hF i v hv 0
  have hY := evalAt_pderiv_dehomogenize hF i v hv 1
  change _ ∧ evalAt (pderiv 0 _) _ = 0 ∧ evalAt (pderiv 1 _) _ = 0 ↔ _
  rw [hX, hY]
  simp only [mul_eq_zero, hu, false_or]
  constructor
  · rintro ⟨hF0, hg0, hg1⟩
    refine ⟨hF0, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      have e := euler_eval hF v
      rw [hF0, mul_zero, Finset.sum_eq_single j] at e
      · exact (mul_eq_zero.mp e).resolve_left hv
      · intro l _ hl
        obtain ⟨a, ha⟩ := exists_pieceVar j l hl
        subst ha
        fin_cases a
        · simp [hg0]
        · simp [hg1]
      · simp
    · obtain ⟨a, ha⟩ := exists_pieceVar i j hj
      subst ha
      fin_cases a
      · exact hg0
      · exact hg1
  · rintro ⟨hF0, hg⟩
    exact ⟨hF0, hg _, hg _⟩

/-- **Exercise 1.17** (p. 21), first part: for a point `P = (v)` of a projective curve $C_F$ (`F`
homogeneous), the following are equivalent: `P` is singular on the affine curve $C_i$ for some `i` with
$v_i \neq 0$; `P` is singular on $C_i$ for every such `i`; $F$ and its three partial derivatives vanish at
`P`. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.17, pdf p. 21"]
theorem exercise_1_17_singular {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    {K : Type*} [Field K] [Algebra k K] (v : Fin 3 → K) (hv : v ≠ 0) :
    ((∃ i, v i ≠ 0 ∧ IsSingularPoint (dehomogenize i F) (pieceCoords i v)) ↔
      aeval v F = 0 ∧ ∀ j, aeval v (pderiv j F) = 0) ∧
    ((∀ i, v i ≠ 0 → IsSingularPoint (dehomogenize i F) (pieceCoords i v)) ↔
      aeval v F = 0 ∧ ∀ j, aeval v (pderiv j F) = 0) := by
  constructor
  · constructor
    · rintro ⟨i, hi, h⟩
      exact (isSingularPoint_dehomogenize_iff hF v i hi).mp h
    · intro h
      obtain ⟨i, hi⟩ := exists_ne_zero_coord v hv
      exact ⟨i, hi, (isSingularPoint_dehomogenize_iff hF v i hi).mpr h⟩
  · constructor
    · intro h
      obtain ⟨i, hi⟩ := exists_ne_zero_coord v hv
      exact (isSingularPoint_dehomogenize_iff hF v i hi).mp (h i hi)
    · intro h i hi
      exact (isSingularPoint_dehomogenize_iff hF v i hi).mpr h

/-- The dehomogenization of the polar line. -/
theorem dehomogenize_polarLine (F : MvPolynomial (Fin 3) k) {K : Type*} [Field K] [Algebra k K]
    (v : Fin 3 → K) (i : Fin 3) :
    dehomogenize i (polarLine F v) = ∑ j, C (aeval v (pderiv j F)) * pieceSubst i j := by
  simp only [dehomogenize, polarLine, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]

/-- Algebraic identity behind Exercise 1.17 (second part). -/
theorem tangent_algebra {R : Type*} [CommRing R] (p q r X0 X1 cx cy c u : R)
    (hp : p = -(q * cx + r * cy)) (hcu : c * u = 1) :
    p + q * X0 + r * X1 = c * (u * q * (X0 - cx) + u * r * (X1 - cy)) := by
  subst hp
  linear_combination (-(q * (X0 - cx) + r * (X1 - cy))) * hcu

/-- **Exercise 1.17** (p. 21), second part: at a nonsingular point, the polar line
$L : \sum_j (\partial F/\partial X_j)_P X_j = 0$ meets each piece $U_i$ containing `P` in the tangent line to
$C_i$ at `P`: the dehomogenization of `L` is a nonzero multiple of the tangent line. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.17, polar line, pdf p. 21"]
theorem exercise_1_17_tangent {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    {K : Type*} [Field K] [Algebra k K] (v : Fin 3 → K) (hFv : aeval v F = 0) (i : Fin 3)
    (hv : v i ≠ 0) :
    ∃ c : K, c ≠ 0 ∧
      dehomogenize i (polarLine F v) = C c * tangentLine (dehomogenize i F) (pieceCoords i v) := by
  refine ⟨(v i) ^ (d - 1), pow_ne_zero _ hv, ?_⟩
  have hX := evalAt_pderiv_dehomogenize hF i v hv 0
  have hY := evalAt_pderiv_dehomogenize hF i v hv 1
  have e := euler_eval hF v
  rw [hFv, mul_zero, Fin.sum_univ_three] at e
  have hcu : C ((v i) ^ (d - 1)) * C (((v i)⁻¹) ^ (d - 1)) = (1 : MvPolynomial (Fin 2) K) := by
    rw [← C_mul, ← mul_pow, mul_inv_cancel₀ hv, one_pow, C_1]
  unfold tangentLine
  rw [dX, dY, dehomogenize_polarLine, Fin.sum_univ_three]
  have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases h3 with rfl | rfl | rfl
  · rw [show pieceVar 0 0 = 1 from rfl] at hX
    rw [show pieceVar 0 1 = 2 from rfl] at hY
    rw [hX, hY]
    generalize aeval v (pderiv 0 F) = g0 at *
    generalize aeval v (pderiv 1 F) = g1 at *
    generalize aeval v (pderiv 2 F) = g2 at *
    have hf : g0 = -(g1 * (v 1 / v 0) + g2 * (v 2 / v 0)) := by
      field_simp; linear_combination e
    have hp : (C g0 : MvPolynomial (Fin 2) K) = -(C g1 * C (v 1 / v 0) + C g2 * C (v 2 / v 0)) := by
      rw [hf]; simp only [map_neg, map_add, map_mul]
    have := tangent_algebra _ _ _ (X 0) (X 1) _ _ _ _ hp hcu
    simp only [pieceSubst, pieceCoords, map_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    linear_combination this
  · rw [show pieceVar 1 0 = 0 from rfl] at hX
    rw [show pieceVar 1 1 = 2 from rfl] at hY
    rw [hX, hY]
    generalize aeval v (pderiv 0 F) = g0 at *
    generalize aeval v (pderiv 1 F) = g1 at *
    generalize aeval v (pderiv 2 F) = g2 at *
    have hf : g1 = -(g0 * (v 0 / v 1) + g2 * (v 2 / v 1)) := by
      field_simp; linear_combination e
    have hp : (C g1 : MvPolynomial (Fin 2) K) = -(C g0 * C (v 0 / v 1) + C g2 * C (v 2 / v 1)) := by
      rw [hf]; simp only [map_neg, map_add, map_mul]
    have := tangent_algebra _ _ _ (X 0) (X 1) _ _ _ _ hp hcu
    simp only [pieceSubst, pieceCoords, map_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    linear_combination this
  · rw [show pieceVar 2 0 = 0 from rfl] at hX
    rw [show pieceVar 2 1 = 1 from rfl] at hY
    rw [hX, hY]
    generalize aeval v (pderiv 0 F) = g0 at *
    generalize aeval v (pderiv 1 F) = g1 at *
    generalize aeval v (pderiv 2 F) = g2 at *
    have hf : g2 = -(g0 * (v 0 / v 2) + g1 * (v 1 / v 2)) := by
      field_simp; linear_combination e
    have hp : (C g2 : MvPolynomial (Fin 2) K) = -(C g0 * C (v 0 / v 2) + C g1 * C (v 1 / v 2)) := by
      rw [hf]; simp only [map_neg, map_add, map_mul]
    have := tangent_algebra _ _ _ (X 0) (X 1) _ _ _ _ hp hcu
    simp only [pieceSubst, pieceCoords, map_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    linear_combination this

/-- The intersection number $I(P, C_F \cap C_G)$ of two projective plane curves at a point `P`
(p. 21): the intersection number of the affine curves $C_i$, $D_i$ at `P`, on the piece $U_i$ containing
`P` given by `pieceIndex`. -/
@[kb "milne2006ec" "Ch. I, §1, intersection numbers of projective curves, pdf p. 21"]
noncomputable def projIntersectionNumber (F G : MvPolynomial (Fin 3) k) {K : Type*} [Field K]
    [Algebra k K] (P : ℙ K (Fin 3 → K)) : ℕ :=
  intersectionNumberAt (dehomogenize (pieceIndex P.rep) F) (dehomogenize (pieceIndex P.rep) G)
    (pieceCoords (pieceIndex P.rep) P.rep)

/-- Two projective plane curves have **no irreducible component in common** (p. 21): no irreducible
polynomial of `k[X, Y, Z]` divides both equations. -/
def NoCommonComponent {σ : Type*} (F G : MvPolynomial σ k) : Prop :=
  ∀ h : MvPolynomial σ k, Irreducible h → h ∣ F → ¬ h ∣ G

/-- **Theorem 1.18 (Bezout)** (p. 21), as a named statement (Milne refers to Fulton 1969, Chap. 5, and
Silverman–Tate 1992, Appendix A): let $C_F$, $C_G$ be projective plane curves over `k` of degrees `m`,
`n` with no irreducible component in common. Then they meet over $k^{\mathrm{al}}$ in finitely many
points, and $\sum_{P} I(P, C \cap D) = mn$. -/
@[kb "milne2006ec" "Ch. I, Thm. 1.18, pdf p. 21"]
structure Thm1_18 : Prop where
  bezout : ∀ (k : Type) [Field k] (F G : MvPolynomial (Fin 3) k),
    IsProjectivePlaneCurve F → IsProjectivePlaneCurve G → NoCommonComponent F G →
    ∃ S : Finset (ℙ (AlgebraicClosure k) (Fin 3 → AlgebraicClosure k)),
      (S : Set _) = projectivePoints F (AlgebraicClosure k) ∩ projectivePoints G (AlgebraicClosure k) ∧
      ∑ P ∈ S, projIntersectionNumber F G P = curveDegree F * curveDegree G

/-- The Weierstrass cubic $Y^2Z - (X^3 + aXZ^2 + bZ^3)$. -/
noncomputable def weierstrassCubic (a b : k) : MvPolynomial (Fin 3) k :=
  X 1 ^ 2 * X 2 - (X 0 ^ 3 + C a * X 0 * X 2 ^ 2 + C b * X 2 ^ 3)

/-- The point $(0 : 1 : 0)$. -/
noncomputable def pointAtInfinity (K : Type*) [Field K] : ℙ K (Fin 3 → K) :=
  Projectivization.mk K ![0, 1, 0] (by simp)

/-- The Weierstrass cubic is homogeneous of degree 3. -/
theorem weierstrassCubic_isHomogeneous (a b : k) : (weierstrassCubic a b).IsHomogeneous 3 := by
  unfold weierstrassCubic
  refine IsHomogeneous.sub ((isHomogeneous_X_pow 1 2).mul (isHomogeneous_X k 2)) ?_
  refine IsHomogeneous.add (IsHomogeneous.add (isHomogeneous_X_pow 0 3) ?_)
    (isHomogeneous_C_mul_X_pow b 2 3)
  exact (isHomogeneous_C_mul_X a 0).mul (isHomogeneous_X_pow 2 2)

/-- The value of the Weierstrass cubic at a vector. -/
theorem aeval_weierstrassCubic (a b : k) {K : Type*} [Field K] [Algebra k K] (v : Fin 3 → K) :
    aeval v (weierstrassCubic a b) =
      v 1 ^ 2 * v 2 - (v 0 ^ 3 + algebraMap k K a * v 0 * v 2 ^ 2 + algebraMap k K b * v 2 ^ 3) := by
  simp [weierstrassCubic]

/-- The coordinates of the representative of the point at infinity. -/
theorem pointAtInfinity_rep (K : Type*) [Field K] :
    (pointAtInfinity K).rep 0 = 0 ∧ (pointAtInfinity K).rep 2 = 0 ∧
      (pointAtInfinity K).rep 1 ≠ 0 := by
  obtain ⟨c, hc, hvc⟩ := exists_smul_rep (![0, 1, 0] : Fin 3 → K) (by simp)
  have h0 := congrFun hvc 0
  have h1 := congrFun hvc 1
  have h2 := congrFun hvc 2
  change _ = c * (pointAtInfinity K).rep 0 at h0
  change _ = c * (pointAtInfinity K).rep 1 at h1
  change _ = c * (pointAtInfinity K).rep 2 at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp h0.symm).resolve_left hc
  · exact (mul_eq_zero.mp h2.symm).resolve_left hc
  · intro h; rw [h, mul_zero] at h1; exact one_ne_zero h1

/-- **Example 1.15** (p. 20): the curve $Y^2Z = X^3 + aXZ^2 + bZ^3$ meets the line at infinity $Z = 0$
only at $(0 : 1 : 0)$. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.15, pdf p. 20"]
theorem example_1_15 (a b : k) (K : Type*) [Field K] [Algebra k K] (P : ℙ K (Fin 3 → K)) :
    P ∈ projectivePoints (weierstrassCubic a b) K ∧ P.rep 2 = 0 ↔ P = pointAtInfinity K := by
  constructor
  · rintro ⟨hP, h2⟩
    have hP' : aeval P.rep (weierstrassCubic a b) = 0 := hP
    rw [aeval_weierstrassCubic, h2] at hP'
    have h0 : P.rep 0 = 0 := by
      have : P.rep 0 ^ 3 = 0 := by linear_combination -hP'
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have h1 : P.rep 1 ≠ 0 := by
      intro h1
      apply P.rep_nonzero
      funext j
      fin_cases j <;> simp [h0, h1, h2]
    rw [← Projectivization.mk_rep P]
    unfold pointAtInfinity
    refine (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr ⟨Units.mk0 (P.rep 1) h1, ?_⟩
    funext j
    fin_cases j <;> simp [h0, h2]
  · rintro rfl
    obtain ⟨h0, h2, h1⟩ := pointAtInfinity_rep K
    refine ⟨?_, h2⟩
    show aeval (pointAtInfinity K).rep (weierstrassCubic a b) = 0
    rw [aeval_weierstrassCubic, h0, h2]
    simp

/-- **Example 1.16** (p. 20): the curve $Y^2Z = X^3 + aXZ^2 + bZ^3$ is covered by the two affine pieces
$C_2 : Y^2 = X^3 + aX + b$ and $C_1 : Z = X^3 + aXZ^2 + bZ^3$. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.16, pdf p. 20"]
theorem example_1_16 (a b : k) :
    dehomogenize 2 (weierstrassCubic a b) = X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 + C b) ∧
    dehomogenize 1 (weierstrassCubic a b) = X 1 - (X 0 ^ 3 + C a * X 0 * X 1 ^ 2 + C b * X 1 ^ 3) ∧
    ∀ (K : Type*) [Field K] [Algebra k K], ∀ P ∈ projectivePoints (weierstrassCubic a b) K,
      P.rep 2 ≠ 0 ∨ P.rep 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [dehomogenize, weierstrassCubic, pieceSubst]
  · simp [dehomogenize, weierstrassCubic, pieceSubst]
  · intro K _ _ P hP
    by_contra hcon
    have h2 : P.rep 2 = 0 := by
      by_contra h; exact hcon (Or.inl h)
    have h1 : P.rep 1 = 0 := by
      by_contra h; exact hcon (Or.inr h)
    have hP' : aeval P.rep (weierstrassCubic a b) = 0 := hP
    rw [aeval_weierstrassCubic, h2] at hP'
    have h0 : P.rep 0 = 0 := by
      have : P.rep 0 ^ 3 = 0 := by linear_combination -hP'
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    apply P.rep_nonzero
    funext j
    fin_cases j <;> simp [h0, h1, h2]

/-- **Point of inflection** (p. 22): a nonsingular point `P` of $C_F$ is a point of inflection (flex) if
the intersection number of the tangent line (the polar line of Exercise 1.17) with `C` at `P` is at
least 3. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of point of inflection, pdf p. 22"]
def IsFlex (F : MvPolynomial (Fin 3) k) {K : Type*} [Field K] [Algebra k K]
    (P : ℙ K (Fin 3 → K)) : Prop :=
  P ∈ projectivePoints F K ∧ IsNonsingularProjPoint F P ∧
    3 ≤ projIntersectionNumber (polarLine F P.rep) (baseChange K F) P

theorem pieceIndex_pointAtInfinity (K : Type*) [Field K] :
    pieceIndex (pointAtInfinity K).rep = 1 := by
  obtain ⟨_, h2, h1⟩ := pointAtInfinity_rep K
  unfold pieceIndex
  simp [h2, h1]

theorem pieceCoords_pointAtInfinity (K : Type*) [Field K] :
    pieceCoords 1 (pointAtInfinity K).rep = (0, 0) := by
  obtain ⟨h0, h2, _⟩ := pointAtInfinity_rep K
  simp [pieceCoords, h0, h2]

/-- The Taylor expansion at the origin is the polynomial itself. -/
theorem translate_zero_self (f : MvPolynomial (Fin 2) k) : translate f ((0, 0) : k × k) = f := by
  show aeval ![X 0 + C 0, X 1 + C 0] f = f
  have : (![X 0 + C (0 : k), X 1 + C (0 : k)] : Fin 2 → MvPolynomial (Fin 2) k) = X := by
    ext i; fin_cases i <;> simp
  rw [this]
  exact aeval_X_left_apply f

theorem projIntersectionNumber_pointAtInfinity (F G : MvPolynomial (Fin 3) k) :
    projIntersectionNumber F G (pointAtInfinity k) =
      localIntersectionNumber (dehomogenize 1 F) (dehomogenize 1 G) := by
  unfold projIntersectionNumber intersectionNumberAt
  rw [pieceIndex_pointAtInfinity, pieceCoords_pointAtInfinity, translate_zero_self,
    translate_zero_self]

/-- Core of Example 1.20: $I(c Y, Y - (X^3 + aXY^2 + bY^3)) = 3$ for a nonzero constant `c`. -/
theorem weierstrass_local_intersection {I : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ}
    (hI : IsIntersectionNumber I) (a b u : k) (hu : u ≠ 0) :
    I (C u * X 1) (X 1 - (X 0 ^ 3 + C a * X 0 * X 1 ^ 2 + C b * X 1 ^ 3)) = 3 := by
  set g : MvPolynomial (Fin 2) k := X 1 - (X 0 ^ 3 + C a * X 0 * X 1 ^ 2 + C b * X 1 ^ 3) with hg
  have hnd : ∀ p : MvPolynomial (Fin 2) k, eval (![1, 0] : Fin 2 → k) p ≠ 0 → ¬ X 1 ∣ p := by
    intro p hp hd
    have := map_dvd (eval (![1, 0] : Fin 2 → k)) hd
    simp only [eval_X] at this
    exact hp (zero_dvd_iff.mp (by simpa using this))
  have hNg : NoCommonFactorAtOrigin (X 1) g :=
    ncf_X_of_not_dvd 1 (hnd g (by simp [hg]))
  have hu' : IsUnit (C u : MvPolynomial (Fin 2) k) := (IsUnit.mk0 u hu).map C
  have hN3 : NoCommonFactorAtOrigin (X 1) ((-1 * X 0 * X 0) * X 0 : MvPolynomial (Fin 2) k) :=
    ncf_X_of_not_dvd 1 (hnd _ (by simp))
  have hN2 : NoCommonFactorAtOrigin (X 1) (-1 * X 0 * X 0 : MvPolynomial (Fin 2) k) :=
    hN3.of_dvd_right (dvd_mul_right _ _)
  have hN1 : NoCommonFactorAtOrigin (X 1) (-1 * X 0 : MvPolynomial (Fin 2) k) :=
    hN2.of_dvd_right (dvd_mul_right _ _)
  have hNm1 : NoCommonFactorAtOrigin (X 1) (-1 : MvPolynomial (Fin 2) k) :=
    hN1.of_dvd_right (dvd_mul_right _ _)
  have hNx : NoCommonFactorAtOrigin (X 1) (X 0 : MvPolynomial (Fin 2) k) :=
    hN3.of_dvd_right (dvd_mul_left _ _)
  have hIx : I (X 1) (X 0) = 1 := by rw [hI.symm _ _ hNx]; exact hI.X_Y
  have hI0 : I (X 1) (-1) = 0 := hI.eq_zero _ _ hNm1 (by simp)
  have hI3 : I (X 1) ((-1 * X 0 * X 0) * X 0) = 3 := by
    rw [hI.mul_right _ _ _ hN2 hNx, hI.mul_right _ _ _ hN1 hNx, hI.mul_right _ _ _ hNm1 hNx,
      hI0, hIx]
  have hgeq : g = (-1 * X 0 * X 0) * X 0 +
      (1 - C a * X 0 * X 1 - C b * X 1 ^ 2) * X 1 := by
    rw [hg]; ring
  have hIg : I (X 1) g = 3 := by
    rw [hgeq, hI.add_mul_right _ _ _ hN3, hI3]
  have hNg' : NoCommonFactorAtOrigin g (X 1) := hNg.symm
  have hNu : NoCommonFactorAtOrigin g (C u) := fun d _ hd =>
    eval_zero_ne_zero_of_isUnit (isUnit_of_dvd_unit hd hu')
  have hNux : NoCommonFactorAtOrigin (C u * X 1) g :=
    hNg.of_dvd_left (hu'.mul_left_dvd.mpr dvd_rfl)
  rw [hI.symm _ _ hNux, hI.mul_right _ _ _ hNu hNg',
    hI.eq_zero _ _ hNu (by simpa using hu), hI.symm _ _ hNg', hIg]

/-- **Example 1.20** (p. 22): the curve $Y^2Z = X^3 + aXZ^2 + bZ^3$ meets the line at infinity at
$P = (0 : 1 : 0)$ with $I(P, L_\infty \cap C) = I(Z, Z - X^3 - aXZ^2 - bZ^3) = I(Z, X^3) = 3$; the
tangent line at `P` is the line at infinity, so `P` is a point of inflection.  (Given the named
statement `Prop1_8`, which makes the dimension satisfy the properties (a)–(e).) -/
@[kb "milne2006ec" "Ch. I, Ex. 1.20, pdf p. 22"]
theorem example_1_20 (h : Prop1_8) {k : Type} [Field k] (a b : k) :
    projIntersectionNumber (X 2) (weierstrassCubic a b) (pointAtInfinity k) = 3 ∧
    polarLine (weierstrassCubic a b) (pointAtInfinity k).rep =
      C ((pointAtInfinity k).rep 1 ^ 2) * X 2 ∧
    IsFlex (weierstrassCubic a b) (pointAtInfinity k) := by
  have hI := h.isIntersectionNumber k
  obtain ⟨h0, h2, h1⟩ := pointAtInfinity_rep k
  have hpolar : polarLine (weierstrassCubic a b) (pointAtInfinity k).rep =
      C ((pointAtInfinity k).rep 1 ^ 2) * X 2 := by
    simp [polarLine, Fin.sum_univ_three, weierstrassCubic, h0, h2]
  have e1 := (example_1_16.{0, 0} a b).2.1
  refine ⟨?_, hpolar, ?_⟩
  · rw [projIntersectionNumber_pointAtInfinity, e1]
    have : dehomogenize 1 (X 2 : MvPolynomial (Fin 3) k) = C 1 * X 1 := by
      simp [dehomogenize, pieceSubst]
    rw [this]
    exact weierstrass_local_intersection hI a b 1 one_ne_zero
  · have hmem := ((example_1_15 a b k (pointAtInfinity k)).mpr rfl).1
    refine ⟨hmem, ?_, ?_⟩
    · unfold IsNonsingularProjPoint
      rw [pieceIndex_pointAtInfinity, pieceCoords_pointAtInfinity]
      refine ⟨?_, Or.inr ?_⟩
      · have := (aeval_eq_zero_iff_mem_piece (weierstrassCubic_isHomogeneous a b) 1
          (pointAtInfinity k).rep h1).mp hmem
        rwa [pieceCoords_pointAtInfinity] at this
      · rw [e1]
        simp [evalAt, dY]
    · rw [hpolar, projIntersectionNumber_pointAtInfinity]
      have hb : baseChange k (weierstrassCubic a b) = weierstrassCubic a b := by
        simp only [baseChange, Algebra.algebraMap_self]
        exact map_id _
      have hc : dehomogenize 1 (C ((pointAtInfinity k).rep 1 ^ 2) * X 2 : MvPolynomial (Fin 3) k) =
          C ((pointAtInfinity k).rep 1 ^ 2) * X 1 := by
        simp [dehomogenize, pieceSubst]
      rw [hb, hc, e1]
      exact (weierstrass_local_intersection hI a b _ (pow_ne_zero 2 h1)).ge

/-! ### Factors of homogeneous polynomials -/

/-- Components of a product: the sum over pairs of component degrees. -/
theorem homogeneousComponent_mul_eq {σ : Type*} (p q : MvPolynomial σ k) (n : ℕ) :
    homogeneousComponent n (p * q) = ∑ i ∈ Finset.range (p.totalDegree + 1),
      ∑ j ∈ Finset.range (q.totalDegree + 1),
        if n = i + j then homogeneousComponent i p * homogeneousComponent j q else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent p, ← sum_homogeneousComponent q]
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [homogeneousComponent_of_mem (n := i + j)]
  rw [mem_homogeneousSubmodule]
  exact (homogeneousComponent_isHomogeneous i p).mul (homogeneousComponent_isHomogeneous j q)

/-- The lowest and highest nonzero homogeneous components of a nonzero polynomial. -/
theorem exists_component_bounds {σ : Type*} {p : MvPolynomial σ k} (hp : p ≠ 0) :
    ∃ a b, a ≤ b ∧ b ≤ p.totalDegree ∧ homogeneousComponent a p ≠ 0 ∧
      homogeneousComponent b p ≠ 0 ∧ (∀ i < a, homogeneousComponent i p = 0) ∧
      ∀ i, b < i → homogeneousComponent i p = 0 := by
  have hex : ∃ i, homogeneousComponent i p ≠ 0 := by
    by_contra h
    replace h : ∀ i, homogeneousComponent i p = 0 := fun i => by_contra fun hi => h ⟨i, hi⟩
    apply hp
    rw [← sum_homogeneousComponent p]
    exact Finset.sum_eq_zero fun i _ => h i
  have hbd : ∀ i, p.totalDegree < i → homogeneousComponent i p = 0 :=
    fun i hi => homogeneousComponent_eq_zero i p hi
  classical
  have ha_le : Nat.find hex ≤ p.totalDegree := by
    by_contra h
    exact Nat.find_spec hex (hbd _ (not_le.mp h))
  refine ⟨Nat.find hex, Nat.findGreatest (fun i => homogeneousComponent i p ≠ 0) p.totalDegree,
    Nat.le_findGreatest ha_le (Nat.find_spec hex), Nat.findGreatest_le _, Nat.find_spec hex,
    Nat.findGreatest_spec (P := fun i => homogeneousComponent i p ≠ 0) ha_le (Nat.find_spec hex),
    fun i hi => by simpa using Nat.find_min hex hi, fun i hi => ?_⟩
  by_cases h : p.totalDegree < i
  · exact hbd i h
  · have := Nat.findGreatest_is_greatest (P := fun i => homogeneousComponent i p ≠ 0) hi
      (not_lt.mp h)
    simpa using this

/-- The lowest component of a product of polynomials is the product of the lowest components. -/
theorem homogeneousComponent_mul_low {σ : Type*} {p q : MvPolynomial σ k} {a c : ℕ}
    (ha : a ≤ p.totalDegree) (hc : c ≤ q.totalDegree)
    (hpa : ∀ i < a, homogeneousComponent i p = 0) (hqc : ∀ j < c, homogeneousComponent j q = 0) :
    homogeneousComponent (a + c) (p * q) = homogeneousComponent a p * homogeneousComponent c q := by
  rw [homogeneousComponent_mul_eq, Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro j _ hj
      have : ¬ (a + c = a + j) := by omega
      rw [ite_eq_right_iff]; exact fun h => absurd h this
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h : a + c = i + j
    · rcases lt_or_gt_of_ne hi with h1 | h1
      · simp [h, hpa i h1]
      · simp [h, hqc j (by omega)]
    · simp [h]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The highest component of a product of polynomials is the product of the highest components. -/
theorem homogeneousComponent_mul_high {σ : Type*} {p q : MvPolynomial σ k} {b e : ℕ}
    (hb : b ≤ p.totalDegree) (he : e ≤ q.totalDegree)
    (hpb : ∀ i, b < i → homogeneousComponent i p = 0)
    (hqe : ∀ j, e < j → homogeneousComponent j q = 0) :
    homogeneousComponent (b + e) (p * q) = homogeneousComponent b p * homogeneousComponent e q := by
  rw [homogeneousComponent_mul_eq, Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      have : ¬ (b + e = b + j) := by omega
      rw [ite_eq_right_iff]; exact fun h => absurd h this
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h : b + e = i + j
    · rcases lt_or_gt_of_ne hi with h1 | h1
      · simp [h, hqe j (by omega)]
      · simp [h, hpb i h1]
    · simp [h]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- A polynomial with a single nonzero component is homogeneous. -/
theorem isHomogeneous_of_bounds {σ : Type*} {p : MvPolynomial σ k} {a : ℕ}
    (hlow : ∀ i < a, homogeneousComponent i p = 0)
    (hhigh : ∀ i, a < i → homogeneousComponent i p = 0) : p.IsHomogeneous a := by
  intro d hd
  by_contra hne
  have h1 : (homogeneousComponent (Finsupp.weight 1 d) p).coeff d ≠ 0 := by
    have hdeg : d.degree = Finsupp.weight 1 d := by rw [Finsupp.degree_eq_weight_one]; rfl
    rw [coeff_homogeneousComponent]
    simpa [hdeg] using hd
  rcases lt_or_gt_of_ne hne with h | h
  · rw [hlow _ h] at h1; simp at h1
  · rw [hhigh _ h] at h1; simp at h1

/-- Factors of a homogeneous polynomial over a field are homogeneous. -/
theorem isHomogeneous_of_mul_isHomogeneous {σ : Type*} {G H : MvPolynomial σ k} {d : ℕ}
    (h : (G * H).IsHomogeneous d) (hG : G ≠ 0) (hH : H ≠ 0) :
    (∃ a, G.IsHomogeneous a) ∧ ∃ c, H.IsHomogeneous c := by
  obtain ⟨a, b, hab, hb, ha0, hb0, hal, hbh⟩ := exists_component_bounds hG
  obtain ⟨c, e, hce, he, hc0, he0, hcl, heh⟩ := exists_component_bounds hH
  have hz : ∀ n, n ≠ d → homogeneousComponent n (G * H) = 0 := by
    intro n hn
    rw [homogeneousComponent_of_mem (n := d) ((mem_homogeneousSubmodule _ _).mpr h)]
    simp [hn]
  have h1 := homogeneousComponent_mul_low (hab.trans hb) (hce.trans he) hal hcl
  have h2 := homogeneousComponent_mul_high hb he hbh heh
  have n1 : homogeneousComponent (a + c) (G * H) ≠ 0 := by
    rw [h1]; exact mul_ne_zero ha0 hc0
  have n2 : homogeneousComponent (b + e) (G * H) ≠ 0 := by
    rw [h2]; exact mul_ne_zero hb0 he0
  have e1 : a + c = d := by by_contra hh; exact n1 (hz _ hh)
  have e2 : b + e = d := by by_contra hh; exact n2 (hz _ hh)
  have hab' : a = b := by omega
  have hce' : c = e := by omega
  subst hab' hce'
  exact ⟨⟨a, isHomogeneous_of_bounds hal hbh⟩, ⟨c, isHomogeneous_of_bounds hcl heh⟩⟩

/-! ### Helper lemmas for Remark 1.21 -/

/-- The total degree does not change under an injective change of coefficients. -/
theorem totalDegree_map_of_injective_field {σ : Type*} {K : Type*} [Field K] (f : k →+* K)
    (hf : Function.Injective f) (p : MvPolynomial σ k) : (map f p).totalDegree = p.totalDegree := by
  unfold totalDegree
  rw [support_map_of_injective _ hf]

/-- A polynomial that becomes a unit after extending the field of coefficients is a unit. -/
theorem isUnit_of_isUnit_baseChange {σ : Type*} (K : Type*) [Field K] [Algebra k K]
    {p : MvPolynomial σ k} (hp : IsUnit (baseChange K p)) : IsUnit p := by
  have hd := (isUnit_iff_totalDegree_of_isReduced.mp hp).2
  rw [totalDegree_map_of_injective_field _ (algebraMap k K).injective] at hd
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  rw [totalDegree_eq_zero_iff_eq_C] at hd
  rw [hd]
  refine (IsUnit.mk0 (p.coeff 0) ?_).map C
  intro h0
  apply hp0
  rw [hd, h0, C_0]

/-- A nonzero polynomial with positive total degree is not a unit, and conversely. -/
theorem totalDegree_ne_zero_of_not_isUnit {σ : Type*} {p : MvPolynomial σ k} (hp0 : p ≠ 0)
    (hp : ¬ IsUnit p) : p.totalDegree ≠ 0 := by
  intro h
  apply hp
  rw [totalDegree_eq_zero_iff_eq_C] at h
  rw [h]
  refine (IsUnit.mk0 (p.coeff 0) ?_).map C
  intro h0
  apply hp0
  rw [h, h0, C_0]

/-- Ring isomorphisms preserve squarefreeness. -/
theorem squarefree_map_mulEquiv {A B : Type*} [CommMonoid A] [CommMonoid B] (e : A ≃* B) {x : A}
    (hx : Squarefree x) : Squarefree (e x) := by
  intro y hy
  have h1 : e.symm y * e.symm y ∣ x := by
    have := map_dvd e.symm hy
    simpa using this
  simpa using (hx _ h1).map e

/-- The piece index points to a nonzero coordinate. -/
theorem pieceIndex_spec {K : Type*} [Field K] (v : Fin 3 → K) (hv : v ≠ 0) :
    v (pieceIndex v) ≠ 0 := by
  classical
  unfold pieceIndex
  by_cases h2 : v 2 ≠ 0
  · simp [h2]
  · by_cases h1 : v 1 ≠ 0
    · simp [h2, h1]
    · have h0 : v 0 ≠ 0 := fun h0 => hv (by funext j; fin_cases j <;> simp_all)
      simp [h2, h1, h0]

/-- A point of the projective curve is nonsingular exactly when some partial derivative of `F` does not
vanish at a representative. -/
theorem isNonsingularProjPoint_iff {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    {K : Type*} [Field K] [Algebra k K] (P : ℙ K (Fin 3 → K)) (hP : P ∈ projectivePoints F K) :
    IsNonsingularProjPoint F P ↔ ¬ ∀ j, aeval P.rep (pderiv j F) = 0 := by
  have hi := pieceIndex_spec P.rep P.rep_nonzero
  have hP' : aeval P.rep F = 0 := hP
  have hmem := (aeval_eq_zero_iff_mem_piece hF (pieceIndex P.rep) P.rep hi).mp hP'
  have hs := isSingularPoint_iff_not_nonsingular _ hmem
  unfold IsNonsingularProjPoint
  have : IsNonsingularPoint (dehomogenize (pieceIndex P.rep) F)
      (pieceCoords (pieceIndex P.rep) P.rep) ↔
      ¬ IsSingularPoint (dehomogenize (pieceIndex P.rep) F)
        (pieceCoords (pieceIndex P.rep) P.rep) := by
    rw [hs, not_not]
  rw [this, isSingularPoint_dehomogenize_iff hF P.rep _ hi]
  simp [hP']

/-- **Remark 1.21** (p. 22), first part (from Bezout's theorem, the named statement `Thm1_18`, and
Remark 1.4): if a projective plane curve $C_F$ has two components, i.e. $F = GH$ with `G`, `H`
nonconstant, then $C_F$ has a singular point over $k^{\mathrm{al}}$. -/
@[kb "milne2006ec" "Ch. I, Rem. 1.21, pdf p. 22"]
theorem remark_1_21_singular (hB : Thm1_18) {k : Type} [Field k] {F G H : MvPolynomial (Fin 3) k}
    (hF : IsProjectivePlaneCurve F) (hGH : F = G * H) (hG : G.totalDegree ≠ 0)
    (hH : H.totalDegree ≠ 0) :
    ∃ P ∈ projectivePoints F (AlgebraicClosure k), ¬ IsNonsingularProjPoint F P := by
  obtain ⟨hFh, hFd, hFsq⟩ := hF
  have hG0 : G ≠ 0 := by rintro rfl; exact hG (by simp)
  have hH0 : H ≠ 0 := by rintro rfl; exact hH (by simp)
  have hFhom : (G * H).IsHomogeneous F.totalDegree := hGH ▸ hFh
  obtain ⟨⟨a, hGa⟩, ⟨c, hHc⟩⟩ := isHomogeneous_of_mul_isHomogeneous hFhom hG0 hH0
  have hGh : G.IsHomogeneous G.totalDegree := by rw [hGa.totalDegree hG0]; exact hGa
  have hHh : H.IsHomogeneous H.totalDegree := by rw [hHc.totalDegree hH0]; exact hHc
  have hmap : baseChange (AlgebraicClosure k) F =
      baseChange (AlgebraicClosure k) G * baseChange (AlgebraicClosure k) H := by
    rw [hGH]; exact map_mul _ _ _
  have hGc : IsProjectivePlaneCurve G := ⟨hGh, hG, by
    rw [hmap] at hFsq; exact hFsq.of_mul_left⟩
  have hHc' : IsProjectivePlaneCurve H := ⟨hHh, hH, by
    rw [hmap] at hFsq; exact hFsq.of_mul_right⟩
  have hnc : NoCommonComponent G H := by
    intro h hirr hhG hhH
    have h2 : h * h ∣ F := hGH ▸ mul_dvd_mul hhG hhH
    have h3 := map_dvd (map (algebraMap k (AlgebraicClosure k))) h2
    rw [map_mul] at h3
    have h4 : IsUnit (baseChange (AlgebraicClosure k) h) := hFsq _ h3
    exact hirr.not_isUnit (isUnit_of_isUnit_baseChange (AlgebraicClosure k) h4)
  obtain ⟨S, hS, hsum⟩ := hB.bezout k G H hGc hHc' hnc
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp only [Finset.sum_empty, curveDegree] at hsum
    exact (Nat.mul_pos (Nat.pos_of_ne_zero hG) (Nat.pos_of_ne_zero hH)).ne' hsum.symm
  obtain ⟨P, hPS⟩ := hne
  have hPmem : P ∈ projectivePoints G (AlgebraicClosure k) ∩
      projectivePoints H (AlgebraicClosure k) := hS ▸ Finset.mem_coe.mpr hPS
  have hPG : aeval P.rep G = 0 := hPmem.1
  have hPH : aeval P.rep H = 0 := hPmem.2
  have hPF : P ∈ projectivePoints F (AlgebraicClosure k) := by
    show aeval P.rep F = 0
    rw [hGH, map_mul, hPG, zero_mul]
  refine ⟨P, hPF, ?_⟩
  rw [isNonsingularProjPoint_iff hFh P hPF, not_not]
  intro j
  rw [hGH, pderiv_mul, map_add, map_mul, map_mul, hPG, hPH]
  simp

/-- **Remark 1.21** (p. 22): every nonsingular projective plane curve is geometrically irreducible
(from Bezout's theorem, the named statement `Thm1_18`). -/
@[kb "milne2006ec" "Ch. I, Rem. 1.21, pdf p. 22"]
theorem remark_1_21 (hB : Thm1_18) {k : Type} [Field k] {F : MvPolynomial (Fin 3) k}
    (hF : IsProjectivePlaneCurve F) (hns : IsNonsingularProjCurve F) :
    Irreducible (baseChange (AlgebraicClosure k) F) := by
  classical
  obtain ⟨hFh, hFd, hFsq⟩ := hF
  have hbij : Function.Bijective
      (algebraMap (AlgebraicClosure k) (AlgebraicClosure (AlgebraicClosure k))) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure k)
  by_contra hirr
  have hF0 : F ≠ 0 := by rintro rfl; simp at hFd
  have hdeg : (baseChange (AlgebraicClosure k) F).totalDegree = F.totalDegree :=
    totalDegree_map_of_injective_field _ (algebraMap k (AlgebraicClosure k)).injective F
  have hF'0 : baseChange (AlgebraicClosure k) F ≠ 0 := by
    intro h
    apply hF0
    exact map_injective (algebraMap k (AlgebraicClosure k)) (algebraMap k _).injective
      (h.trans (map_zero _).symm)
  have hnu : ¬ IsUnit (baseChange (AlgebraicClosure k) F) := fun hu =>
    hFd (by rw [← hdeg]; exact (isUnit_iff_totalDegree_of_isReduced.mp hu).2)
  have hred : ∃ G H : MvPolynomial (Fin 3) (AlgebraicClosure k),
      baseChange (AlgebraicClosure k) F = G * H ∧ ¬ IsUnit G ∧ ¬ IsUnit H := by
    by_contra hno
    exact hirr ⟨hnu, fun a b hab => by
      by_contra h
      exact hno ⟨a, b, hab, fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩⟩
  obtain ⟨G, H, hGH, hGnu, hHnu⟩ := hred
  have hG0 : G ≠ 0 := by
    rintro rfl; rw [zero_mul] at hGH; exact hF'0 hGH
  have hH0 : H ≠ 0 := by
    rintro rfl; rw [mul_zero] at hGH; exact hF'0 hGH
  have hGd := totalDegree_ne_zero_of_not_isUnit hG0 hGnu
  have hHd := totalDegree_ne_zero_of_not_isUnit hH0 hHnu
  have hF'h : (baseChange (AlgebraicClosure k) F).IsHomogeneous
      (baseChange (AlgebraicClosure k) F).totalDegree := by
    rw [hdeg]; exact hFh.map _
  have hcurve : IsProjectivePlaneCurve (baseChange (AlgebraicClosure k) F) := by
    refine ⟨hF'h, by rw [hdeg]; exact hFd, ?_⟩
    let e : AlgebraicClosure k ≃+* AlgebraicClosure (AlgebraicClosure k) :=
      RingEquiv.ofBijective _ hbij
    have := squarefree_map_mulEquiv (mapEquiv (Fin 3) e).toMulEquiv hFsq
    exact this
  obtain ⟨P, hPF', hPns⟩ := remark_1_21_singular hB hcurve hGH hGd hHd
  rw [isNonsingularProjPoint_iff hF'h P hPF', not_not] at hPns
  have hPF'0 : aeval P.rep (baseChange (AlgebraicClosure k) F) = 0 := hPF'
  choose v hv using fun j => hbij.2 (P.rep j)
  have hvw : algebraMap (AlgebraicClosure k) (AlgebraicClosure (AlgebraicClosure k)) ∘ v =
      P.rep := funext hv
  have key : ∀ g : MvPolynomial (Fin 3) k,
      aeval P.rep (baseChange (AlgebraicClosure k) g) = 0 → aeval v g = 0 := by
    intro g hg
    rw [aeval_map_algebraMap (AlgebraicClosure k), ← hvw] at hg
    exact (aeval_algebraMap_eq_zero_iff_of_injective
      (AlgebraicClosure (AlgebraicClosure k)) hbij.1).mp hg
  have hv0 : v ≠ 0 := by
    intro h
    apply P.rep_nonzero
    funext j
    simpa [h] using (hv j).symm
  have hP0 : Projectivization.mk (AlgebraicClosure k) v hv0 ∈
      projectivePoints F (AlgebraicClosure k) :=
    (mem_projectivePoints_mk hFh v hv0).mpr (key F hPF'0)
  have hns0 := hns _ hP0
  rw [isNonsingularProjPoint_iff hFh _ hP0] at hns0
  apply hns0
  intro j
  obtain ⟨c, hc, hvc⟩ := exists_smul_rep v hv0
  have h1 := key (pderiv j F) (by
    have h2 := hPns j
    rw [pderiv_map] at h2
    exact h2)
  rw [hvc, aeval_smul_of_isHomogeneous hFh.pderiv] at h1
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc)

end NumberFieldKB.MilneEC
