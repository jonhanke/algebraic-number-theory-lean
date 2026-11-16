import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import QuadFormsKB.Citation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Milne, *Elliptic Curves*, Chapter II §1: plane cubics and Weierstrass form

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

Projective plane curves are given by forms $F \in k[X, Y, Z]$ = `MvPolynomial (Fin 3) k` with
$(X, Y, Z) = $ (`X 0`, `X 1`, `X 2`), the convention of Mathlib's `WeierstrassCurve.Projective`. A point is a
nonzero vector $P \in k^3$. Milne's general cubic form (proof of Proposition 1.2) is
$c_1X^3 + c_2X^2Y + c_3X^2Z + c_4XY^2 + c_5XYZ + c_6XZ^2 + c_7Y^3 + c_8Y^2Z + c_9YZ^2 + c_{10}Z^3$
(`cubicForm c`, with 0-based indices: `c 0` is Milne's $c_1$, …, `c 9` is $c_{10}$).

Local definitions (Chapter I's notions, specialized; the parallel Chapter I job has general versions and the
integration job should add comparison lemmas):
* `IsNonsingularPlaneCurve F`: no point of the curve over an algebraic closure where all three partial derivatives
  vanish (Milne I §1).
* `lineIntersectionDivisible F P Q n`: the restriction $T \mapsto F(P + TQ)$ of $F$ to the line through $P$ and
  $Q$ is divisible by $T^n$, i.e. $I(P, L \cap C) \ge n$ for the line $L = PQ$ (Milne I §1: for a line, the
  intersection number at $P$ is the order of vanishing of the restriction of $F$).
* `IsInflectionPoint F P`: $P$ is a nonsingular point of $C$ and the tangent line $L$ at $P$ has
  $I(P, L \cap C) \ge 3$ (Milne I §1, p. 19).

Contents: Proposition 1.2; the converse in Definition 1.1 ($O = (0:1:0)$ is an inflection point of a Weierstrass
cubic); Aside 1.3 (the Hessian; the inflection criterion as a named statement); Nagell's reduction of a cubic with
a rational point to Weierstrass form (pdf pp. 56–57) as a named statement.
-/

namespace NumberFieldKB.MilneEC.II

open MvPolynomial

variable {k : Type*} [Field k]

/-- Milne's general cubic form $c_1X^3 + c_2X^2Y + c_3X^2Z + c_4XY^2 + c_5XYZ + c_6XZ^2 + c_7Y^3 + c_8Y^2Z +
c_9YZ^2 + c_{10}Z^3$ (proof of Proposition 1.2, p. 54), indices shifted to `c 0`, …, `c 9`. -/
noncomputable def cubicForm (c : Fin 10 → k) : MvPolynomial (Fin 3) k :=
  C (c 0) * X 0 ^ 3 + C (c 1) * X 0 ^ 2 * X 1 + C (c 2) * X 0 ^ 2 * X 2 + C (c 3) * X 0 * X 1 ^ 2 +
    C (c 4) * X 0 * X 1 * X 2 + C (c 5) * X 0 * X 2 ^ 2 + C (c 6) * X 1 ^ 3 + C (c 7) * X 1 ^ 2 * X 2 +
    C (c 8) * X 1 * X 2 ^ 2 + C (c 9) * X 2 ^ 3

/-- Exponent triples of the ten cubic monomials. -/
def cubicExp : Fin 10 → Fin 3 → ℕ :=
  ![![3,0,0], ![2,1,0], ![2,0,1], ![1,2,0], ![1,1,1], ![1,0,2], ![0,3,0], ![0,2,1], ![0,1,2], ![0,0,3]]

/-- Exponent vectors of the ten cubic monomials, as finitely supported functions. -/
noncomputable def cubicMon (i : Fin 10) : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (cubicExp i)

/-- Coordinates of `cubicMon`. -/
theorem cubicMon_apply (i : Fin 10) (j : Fin 3) : cubicMon i j = cubicExp i j := rfl

/-- The ten exponent triples are distinct. -/
theorem cubicExp_injective : Function.Injective cubicExp := by decide

/-- The ten cubic monomials are distinct. -/
theorem cubicMon_injective : Function.Injective cubicMon := fun i j h =>
  cubicExp_injective (funext fun l => by rw [← cubicMon_apply, ← cubicMon_apply, h])

/-- `cubicForm` as a sum of monomials. -/
theorem cubicForm_eq_sum (c : Fin 10 → k) :
    cubicForm c = ∑ i, monomial (cubicMon i) (c i) := by
  simp [Fin.sum_univ_succ, monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_three, cubicMon_apply,
    cubicExp, cubicForm]
  ring

/-- Every exponent triple of total degree 3 is one of the ten. -/
theorem exists_cubicExp (a b c : ℕ) (h : a + b + c = 3) : ∃ j, cubicExp j = ![a, b, c] := by
  have hc : c = 3 - a - b := by omega
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  subst hc
  interval_cases a <;> interval_cases b <;>
    first
    | (exfalso; omega)
    | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩ | exact ⟨3, by decide⟩
    | exact ⟨4, by decide⟩ | exact ⟨5, by decide⟩ | exact ⟨6, by decide⟩ | exact ⟨7, by decide⟩
    | exact ⟨8, by decide⟩ | exact ⟨9, by decide⟩

/-- Every homogeneous polynomial of degree 3 in $X, Y, Z$ is a `cubicForm`. -/
theorem exists_cubicForm {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous 3) : ∃ c, F = cubicForm c := by
  refine ⟨fun i => F.coeff (cubicMon i), ?_⟩
  rw [cubicForm_eq_sum]
  ext d
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases h : ∃ j, cubicMon j = d
  · obtain ⟨j, rfl⟩ := h
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [ite_eq_right_iff]
      intro h
      exact absurd (cubicMon_injective h) hb
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra hne
      have hdeg : d.degree = 3 := by
        by_contra hd
        exact hne (hF.coeff_eq_zero hd)
      apply h
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hdeg
      obtain ⟨j, hj⟩ := exists_cubicExp (d 0) (d 1) (d 2) hdeg
      refine ⟨j, ?_⟩
      ext l
      fin_cases l <;> simp [cubicMon_apply, hj]
    · intro i _
      rw [ite_eq_right_iff]
      intro h'
      exact absurd ⟨i, h'⟩ h
/-- A projective plane curve $F = 0$ is nonsingular if at every point with coordinates in an algebraic closure
of $k$, some partial derivative of $F$ is nonzero (Milne I §1). -/
def IsNonsingularPlaneCurve (F : MvPolynomial (Fin 3) k) : Prop :=
  ∀ P : Fin 3 → AlgebraicClosure k, P ≠ 0 → eval P (F.map (algebraMap k (AlgebraicClosure k))) = 0 →
    ∃ i, eval P ((pderiv i F).map (algebraMap k (AlgebraicClosure k))) ≠ 0

/-- The restriction of $F$ to the line $P + TQ$, a polynomial in $T$. -/
noncomputable def restrictLine (F : MvPolynomial (Fin 3) k) (P Q : Fin 3 → k) : Polynomial k :=
  aeval (fun i => Polynomial.C (P i) + Polynomial.C (Q i) * Polynomial.X) F

/-- $I(P, L \cap C) \ge n$ for the line $L$ through $P$ and $Q$: the restriction of $F$ to $L$ vanishes to
order at least $n$ at $P$. -/
def lineIntersectionDivisible (F : MvPolynomial (Fin 3) k) (P Q : Fin 3 → k) (n : ℕ) : Prop :=
  Polynomial.X ^ n ∣ restrictLine F P Q

/-- The tangent line at $P$: the points $Q$ with $\sum_i \partial_iF(P)\,Q_i = 0$. -/
def OnTangentLine (F : MvPolynomial (Fin 3) k) (P Q : Fin 3 → k) : Prop :=
  ∑ i, eval P (pderiv i F) * Q i = 0

/-- $P$ is a *point of inflection* of the curve $F = 0$ (Milne I §1): a nonsingular point of the curve such that
the tangent line $L$ at $P$ has $I(P, L \cap C) \ge 3$. -/
def IsInflectionPoint (F : MvPolynomial (Fin 3) k) (P : Fin 3 → k) : Prop :=
  P ≠ 0 ∧ eval P F = 0 ∧ (∃ i, eval P (pderiv i F) ≠ 0) ∧
    ∃ Q : Fin 3 → k, LinearIndependent k ![P, Q] ∧ OnTangentLine F P Q ∧ lineIntersectionDivisible F P Q 3

/-- The linear change of variables $F \mapsto F(A\vec v)$ for a $3 \times 3$ matrix $A$ (column vectors). -/
noncomputable def linearChange (A : Matrix (Fin 3) (Fin 3) k) (F : MvPolynomial (Fin 3) k) :
    MvPolynomial (Fin 3) k :=
  bind₁ (fun i => ∑ j, C (A i j) * X j) F

/-- The point $(0 : 1 : 0)$. -/
def pointO : Fin 3 → k := ![0, 1, 0]

/-- Chain rule for `bind₁`. -/
theorem pderiv_bind₁_eq (f : Fin 3 → MvPolynomial (Fin 3) k) (i : Fin 3) (F : MvPolynomial (Fin 3) k) :
    pderiv i (bind₁ f F) = ∑ j, bind₁ f (pderiv j F) * pderiv i (f j) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, bind₁_X_right, Derivation.leibniz, hp, smul_eq_mul,
      Finset.mul_sum, pderiv_X]
    simp only [map_add, map_mul, bind₁_X_right, add_mul, Finset.sum_add_distrib, Pi.single_apply]
    simp [mul_ite, ite_mul, mul_assoc]

/-- Evaluation of a linear change of variables, over any ring map out of `k`. -/
theorem eval₂_linearChange {K : Type*} [Field K] (φ : k →+* K) (A : Matrix (Fin 3) (Fin 3) k)
    (P : Fin 3 → K) (F : MvPolynomial (Fin 3) k) :
    eval₂ φ P (linearChange A F) = eval₂ φ ((A.map φ).mulVec P) F := by
  have := eval₂Hom_bind₁ φ P (fun i => ∑ j, C (A i j) * X j) F
  simp only [coe_eval₂Hom] at this
  rw [linearChange, this]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Chain rule for a linear change of variables. -/
theorem eval₂_pderiv_linearChange {K : Type*} [Field K] (φ : k →+* K) (A : Matrix (Fin 3) (Fin 3) k)
    (P : Fin 3 → K) (F : MvPolynomial (Fin 3) k) (i : Fin 3) :
    eval₂ φ P (pderiv i (linearChange A F)) =
      ∑ j, eval₂ φ ((A.map φ).mulVec P) (pderiv j F) * φ (A j i) := by
  rw [linearChange, pderiv_bind₁_eq, eval₂_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : pderiv i (∑ l, C (A j l) * X l : MvPolynomial (Fin 3) k) = C (A j i) := by
    simp [map_sum, pderiv_X, Pi.single_apply]
  rw [h, eval₂_mul, eval₂_C, ← linearChange, eval₂_linearChange]

/-- The `k`-valued evaluation. -/
theorem eval_linearChange (A : Matrix (Fin 3) (Fin 3) k) (P : Fin 3 → k) (F : MvPolynomial (Fin 3) k) :
    eval P (linearChange A F) = eval (A.mulVec P) F := by
  have := eval₂_linearChange (RingHom.id k) A P F
  simpa using this

/-- Chain rule for a linear change of variables, `k`-valued. -/
theorem eval_pderiv_linearChange (A : Matrix (Fin 3) (Fin 3) k) (P : Fin 3 → k) (F : MvPolynomial (Fin 3) k)
    (i : Fin 3) :
    eval P (pderiv i (linearChange A F)) = ∑ j, eval (A.mulVec P) (pderiv j F) * A j i := by
  have := eval₂_pderiv_linearChange (RingHom.id k) A P F i
  simpa using this

/-- Restriction to a line commutes with a linear change of variables. -/
theorem restrictLine_linearChange (A : Matrix (Fin 3) (Fin 3) k) (v w : Fin 3 → k)
    (F : MvPolynomial (Fin 3) k) :
    restrictLine (linearChange A F) v w = restrictLine F (A.mulVec v) (A.mulVec w) := by
  unfold restrictLine linearChange
  rw [aeval_bind₁]
  refine congrArg (fun g => aeval g F) (funext fun i => ?_)
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, aeval_C, aeval_X,
    Polynomial.algebraMap_eq, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]

/-- A linear change of variables preserves homogeneity. -/
theorem isHomogeneous_linearChange {F : MvPolynomial (Fin 3) k} {n : ℕ} (hF : F.IsHomogeneous n)
    (A : Matrix (Fin 3) (Fin 3) k) : (linearChange A F).IsHomogeneous n := by
  have := hF.eval₂ (C : k →+* MvPolynomial (Fin 3) k) (fun i => ∑ j, C (A i j) * X j)
    (fun r => isHomogeneous_C _ _) (n := 1) (fun i => by
      refine IsHomogeneous.sum _ _ _ fun j _ => ?_
      simpa using (isHomogeneous_C _ (A i j)).mul (isHomogeneous_X k j))
  rw [linearChange, bind₁, aeval_def, algebraMap_eq]
  simpa using this

/-- An invertible linear change of variables preserves nonsingularity. -/
theorem isNonsingular_linearChange {A : Matrix (Fin 3) (Fin 3) k} (hA : IsUnit A.det)
    {F : MvPolynomial (Fin 3) k} (h : IsNonsingularPlaneCurve F) :
    IsNonsingularPlaneCurve (linearChange A F) := by
  intro P hP hval
  set φ := algebraMap k (AlgebraicClosure k)
  have hdet : (A.map φ).det ≠ 0 := by
    have : (A.map φ).det = φ A.det := by
      simpa [RingHom.mapMatrix_apply] using (RingHom.map_det φ A).symm
    rw [this]
    exact (map_ne_zero φ).2 hA.ne_zero
  have hQ : (A.map φ).mulVec P ≠ 0 := fun h0 => hP (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)
  rw [eval_map, eval₂_linearChange] at hval
  obtain ⟨j, hj⟩ := h _ hQ (by rw [eval_map]; exact hval)
  by_contra hcon
  push Not at hcon
  apply hj
  have h0 : Matrix.vecMul (fun j => eval ((A.map φ).mulVec P) ((pderiv j F).map φ)) (A.map φ) = 0 := by
    ext i
    have := hcon i
    rw [eval_map, eval₂_pderiv_linearChange] at this
    simpa [Matrix.vecMul, dotProduct, eval_map] using this
  have := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
  exact congrFun this j


/-- Euler's identity at a point of a homogeneous cubic on the curve: the gradient annihilates the point. -/
theorem euler_cubic {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous 3) {O : Fin 3 → k}
    (hOC : eval O F = 0) : ∑ i, eval O (pderiv i F) * O i = 0 := by
  have h := congrArg (eval O) hF.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, hOC, mul_zero] at h
  simpa [mul_comm] using h

/-- Given a nonzero linear form vanishing at a nonzero vector, there is a complementary vector in its kernel. -/
theorem exists_tangent_complement {g O : Fin 3 → k} (hg : g ≠ 0) (hO : O ≠ 0)
    (hgO : ∑ i, g i * O i = 0) :
    ∃ Q : Fin 3 → k, LinearIndependent k ![O, Q] ∧ ∑ i, g i * Q i = 0 := by
  let f : (Fin 3 → k) →ₗ[k] k := ∑ i, g i • LinearMap.proj i
  have hf : ∀ v, f v = ∑ i, g i * v i := by intro v; simp [f]
  obtain ⟨i0, hi0⟩ : ∃ i, g i ≠ 0 := by
    by_contra h; push Not at h; exact hg (funext h)
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨Pi.single i0 (t / g i0), ?_⟩
    rw [hf]
    simp [Pi.single_apply]
    field_simp
  have hker : Module.finrank k (LinearMap.ker f) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
    omega
  have hle : Submodule.span k {O} ≤ LinearMap.ker f := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hf]; exact hgO
  have hlt : Submodule.span k {O} < LinearMap.ker f := by
    refine lt_of_le_of_ne hle fun h => ?_
    have := congrArg (fun S : Submodule k (Fin 3 → k) => Module.finrank k S) h
    rw [finrank_span_singleton hO, hker] at this
    omega
  obtain ⟨Q, hQK, hQn⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨Q, ?_, by rw [← hf]; exact hQK⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    rcases hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hO
  · exfalso
    apply hQn
    rw [Submodule.mem_span_singleton]
    refine ⟨-s / t, ?_⟩
    have : t • Q = -(s • O) := eq_neg_of_add_eq_zero_right hst
    have h2 : (-s / t) • O = Q := by
      have : Q = (t⁻¹) • (t • Q) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [this, ‹t • Q = -(s • O)›, smul_neg, smul_smul, ← neg_smul]
      congr 1
      field_simp
    exact h2

/-- A matrix with columns `(Q, O, R)`, where `R` is off the tangent line. -/
theorem exists_adapted_matrix {g O Q : Fin 3 → k} (hg : g ≠ 0) (hgO : ∑ i, g i * O i = 0)
    (hli : LinearIndependent k ![O, Q]) (hgQ : ∑ i, g i * Q i = 0) :
    ∃ A : Matrix (Fin 3) (Fin 3) k, IsUnit A.det ∧ (∀ j, A j 0 = Q j) ∧ (∀ j, A j 1 = O j) ∧
      ∑ j, g j * A j 2 ≠ 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i, g i ≠ 0 := by
    by_contra h; push Not at h; exact hg (funext h)
  set R : Fin 3 → k := Pi.single i0 1 with hRdef
  have hR : ∑ j, g j * R j = g i0 := by simp [hRdef, Pi.single_apply]
  refine ⟨Matrix.of fun j l => (![Q, O, R] l) j, ?_, fun j => rfl, fun j => rfl, by
    simpa [hR] using hi0⟩
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨w, hw, hAw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hcomp : ∀ j, Q j * w 0 + O j * w 1 + R j * w 2 = 0 := by
    intro j
    have := congrFun hAw j
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hw2 : w 2 = 0 := by
    have h0 := hcomp 0
    have h1 := hcomp 1
    have h2 := hcomp 2
    simp only [Fin.sum_univ_three] at hgQ hgO hR
    have : w 2 * g i0 = 0 := by
      rw [← hR]
      linear_combination g 0 * h0 + g 1 * h1 + g 2 * h2 - w 0 * hgQ - w 1 * hgO
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hi0
  rw [LinearIndependent.pair_iff] at hli
  obtain ⟨h1, h0⟩ := hli (w 1) (w 0) (by
    ext j
    have := hcomp j
    simp [hw2] at this
    simpa [add_comm, mul_comm] using this)
  apply hw
  ext i
  fin_cases i <;> simp [h0, h1, hw2]

/-- Composition of linear changes of variables. -/
theorem linearChange_mul (A B : Matrix (Fin 3) (Fin 3) k) (F : MvPolynomial (Fin 3) k) :
    linearChange (A * B) F = linearChange B (linearChange A F) := by
  unfold linearChange
  rw [bind₁_bind₁]
  refine congrArg (fun g => bind₁ g F) (funext fun i => ?_)
  simp only [map_sum, map_mul, bind₁_C_right, bind₁_X_right, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Scaling `Z` is the linear change by `diag(1, 1, μ)`. -/
theorem linearChange_diagonal (μ : k) (F : MvPolynomial (Fin 3) k) :
    linearChange (Matrix.diagonal ![1, 1, μ]) F = bind₁ ![X 0, X 1, C μ * X 2] F := by
  unfold linearChange
  refine congrArg (fun g => bind₁ g F) (funext fun i => ?_)
  fin_cases i <;> simp [Matrix.diagonal, Fin.sum_univ_three]

/-- If the second column of `A` is `O` then `A (0, 1, 0) = O`. -/
theorem A_mulVec_pointO {A : Matrix (Fin 3) (Fin 3) k} {O : Fin 3 → k} (h : ∀ j, A j 1 = O j) :
    A.mulVec pointO = O := by
  ext j
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, pointO, h]

/-- The partial derivatives of `cubicForm c` at `(0 : 1 : 0)`. -/
theorem cubicForm_partials_pointO (c : Fin 10 → k) :
    eval pointO (pderiv 0 (cubicForm c)) = c 3 ∧ eval pointO (pderiv 1 (cubicForm c)) = 3 * c 6 ∧
    eval pointO (pderiv 2 (cubicForm c)) = c 7 ∧ eval pointO (cubicForm c) = c 6 := by
  simp [cubicForm, pointO, pderiv_X]
  ring

/-- Final step of (b): the coefficients are matched with a Weierstrass equation. -/
theorem cubicForm_weierstrass (c : Fin 10 → k) (h1 : c 1 = 0) (h3 : c 3 = 0) (h6 : c 6 = 0)
    (h0 : c 0 ≠ 0) (h7 : c 7 ≠ 0) :
    ∃ (μ lam : k) (W : WeierstrassCurve k), μ ≠ 0 ∧ lam ≠ 0 ∧
      bind₁ ![X 0, X 1, C μ * X 2] (cubicForm c) = C lam * W.toProjective.polynomial := by
  set μ : k := -c 0 / c 7 with hμ
  set lam : k := -c 0 with hlam
  have hμ0 : μ ≠ 0 := div_ne_zero (neg_ne_zero.2 h0) h7
  have hl0 : lam ≠ 0 := neg_ne_zero.2 h0
  refine ⟨μ, lam, ⟨c 4 / c 7, -c 2 / c 7, c 8 * μ / c 7, -c 5 * μ / c 7, -c 9 * μ ^ 2 / c 7⟩, hμ0, hl0, ?_⟩
  have e7 : lam = c 7 * μ := by rw [hμ, hlam]; field_simp
  have e1 : lam * (c 4 / c 7) = c 4 * μ := by rw [e7]; field_simp
  have e2 : lam * (-c 2 / c 7) = - (c 2 * μ) := by rw [e7]; field_simp
  have e3 : lam * (c 8 * μ / c 7) = c 8 * μ ^ 2 := by rw [e7]; field_simp
  have e4 : lam * (-c 5 * μ / c 7) = - (c 5 * μ ^ 2) := by rw [e7]; field_simp
  have e6 : lam * (-c 9 * μ ^ 2 / c 7) = - (c 9 * μ ^ 3) := by rw [e7]; field_simp
  have f7 : (C lam : MvPolynomial (Fin 3) k) = C (c 7) * C μ := by rw [← C_mul, e7]
  have f1 : (C lam : MvPolynomial (Fin 3) k) * C (c 4 / c 7) = C (c 4) * C μ := by
    rw [← C_mul, ← C_mul, e1]
  have f2 : (C lam : MvPolynomial (Fin 3) k) * C (-c 2 / c 7) = - (C (c 2) * C μ) := by
    rw [← C_mul, ← C_mul, ← C_neg, e2]
  have f3 : (C lam : MvPolynomial (Fin 3) k) * C (c 8 * μ / c 7) = C (c 8) * C μ ^ 2 := by
    rw [← C_mul, ← C_pow, ← C_mul, e3]
  have f4 : (C lam : MvPolynomial (Fin 3) k) * C (-c 5 * μ / c 7) = - (C (c 5) * C μ ^ 2) := by
    rw [← C_mul, ← C_pow, ← C_mul, ← C_neg, e4]
  have f6 : (C lam : MvPolynomial (Fin 3) k) * C (-c 9 * μ ^ 2 / c 7) = - (C (c 9) * C μ ^ 3) := by
    rw [← C_mul, ← C_pow, ← C_mul, ← C_neg, e6]
  have f0 : (C (c 0) : MvPolynomial (Fin 3) k) = - C lam := by rw [hlam, C_neg, neg_neg]
  simp only [cubicForm, WeierstrassCurve.Projective.polynomial, map_add, map_mul, map_pow, bind₁_X_right,
    bind₁_C_right, h1, h3, h6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_zero, zero_mul]
  linear_combination X 0 ^ 3 * f0 - X 1 ^ 2 * X 2 * f7 - X 0 * X 1 * X 2 * f1 + X 0 ^ 2 * X 2 * f2
    - X 1 * X 2 ^ 2 * f3 + X 0 * X 2 ^ 2 * f4 + X 2 ^ 3 * f6

/-- If `c 0 = 0` the cubic contains the line `Z = 0` and has a singular point on it. -/
theorem cubicForm_c0_ne_zero (c : Fin 10 → k) (hns : IsNonsingularPlaneCurve (cubicForm c))
    (h1 : c 1 = 0) (h3 : c 3 = 0) (h6 : c 6 = 0) (h7 : c 7 ≠ 0) : c 0 ≠ 0 := by
  intro h0
  set φ := algebraMap k (AlgebraicClosure k)
  have hφ7 : φ (c 7) ≠ 0 := (map_ne_zero φ).2 h7
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (Polynomial.C (φ (c 7)) * Polynomial.X ^ 2 +
    Polynomial.C (φ (c 4)) * Polynomial.X + Polynomial.C (φ (c 2))) (by
      rw [Polynomial.degree_quadratic (by simpa using hφ7)]; norm_num)
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hy
  obtain ⟨i, hi⟩ := hns ![1, y, 0] (fun h => by simpa using congrFun h 0) (by
    simp [cubicForm, h0, h1, h3, h6])
  fin_cases i <;> simp [cubicForm, pderiv_X, h0, h1, h3, h6] at hi
  exact hi (by linear_combination hy)


/-- **Proposition 1.2 (a)** (pdf p. 54). Let $C : F = 0$ be a nonsingular curve given by a homogeneous cubic $F$ and $O \in C(k)$ a
nonsingular point. After an invertible linear change of variables, $O$ has coordinates $(0 : 1 : 0)$ and the
tangent line to $C$ at $O$ is $Z = 0$: there is an invertible $A$ with $A(0, 1, 0)^{\mathsf T}$ proportional to
$O$ and $\partial_X F'(0,1,0) = \partial_Y F'(0,1,0) = 0$ for $F' = F \circ A$. -/
@[kb "milne2006ec" "Ch. II, Proposition 1.2 (a), pdf p. 54"]
theorem proposition_1_2_a (F : MvPolynomial (Fin 3) k) (hF : F.IsHomogeneous 3) {O : Fin 3 → k} (hO : O ≠ 0) (hOC : eval O F = 0)
    (hns : ∃ i, eval O (pderiv i F) ≠ 0) :
    ∃ A : Matrix (Fin 3) (Fin 3) k, IsUnit A.det ∧ (∃ μ : k, μ ≠ 0 ∧ A.mulVec pointO = μ • O) ∧
      eval pointO (pderiv 0 (linearChange A F)) = 0 ∧ eval pointO (pderiv 1 (linearChange A F)) = 0 := by
  set g : Fin 3 → k := fun i => eval O (pderiv i F) with hg
  have hg0 : g ≠ 0 := by
    obtain ⟨i, hi⟩ := hns
    intro h; exact hi (congrFun h i)
  have hgO : ∑ i, g i * O i = 0 := euler_cubic hF hOC
  obtain ⟨Q, hli, hgQ⟩ := exists_tangent_complement hg0 hO hgO
  obtain ⟨A, hA, hc0, hc1, -⟩ := exists_adapted_matrix hg0 hgO hli hgQ
  refine ⟨A, hA, ⟨1, one_ne_zero, by rw [A_mulVec_pointO hc1, one_smul]⟩, ?_, ?_⟩
  · rw [eval_pderiv_linearChange, A_mulVec_pointO hc1]
    simpa [hc0] using hgQ
  · rw [eval_pderiv_linearChange, A_mulVec_pointO hc1]
    simpa [hc1] using hgO
/-- **Proposition 1.2 (b)** (pdf pp. 54–55). Let $C$ be a nonsingular cubic $F = 0$ with $(0 : 1 : 0) \in C(k)$
a point of inflection with tangent line $Z = 0$. Then, after dividing $F$ by a nonzero constant and replacing $Z$
by a multiple of $Z$, the equation of $C$ has the Weierstrass form (10):
$F(X, Y, \mu Z) = \lambda\,(Y^2Z + a_1XYZ + a_3YZ^2 - X^3 - a_2X^2Z - a_4XZ^2 - a_6Z^3)$. -/
@[kb "milne2006ec" "Ch. II, Proposition 1.2 (b), pdf p. 54"]
theorem proposition_1_2_b (c : Fin 10 → k) (hns : IsNonsingularPlaneCurve (cubicForm c))
    (hO : IsInflectionPoint (cubicForm c) pointO) (htan : OnTangentLine (cubicForm c) pointO ![1, 0, 0]) :
    ∃ (μ lam : k) (W : WeierstrassCurve k), μ ≠ 0 ∧ lam ≠ 0 ∧
      bind₁ ![X 0, X 1, C μ * X 2] (cubicForm c) = C lam * W.toProjective.polynomial := by
  obtain ⟨-, hFO, hex, Q, hli, hQtan, hdiv⟩ := hO
  obtain ⟨p3, p1, p7, p6⟩ := cubicForm_partials_pointO c
  have hc6 : c 6 = 0 := by rw [← p6]; exact hFO
  have hc3 : c 3 = 0 := by
    unfold OnTangentLine at htan
    rw [Fin.sum_univ_three, p3] at htan
    simpa using htan
  have hc7 : c 7 ≠ 0 := by
    intro h7
    obtain ⟨i, hi⟩ := hex
    fin_cases i <;> simp_all
  have hQ2 : Q 2 = 0 := by
    unfold OnTangentLine at hQtan
    rw [Fin.sum_univ_three, p3, p1, p7] at hQtan
    simpa [hc3, hc6, hc7] using hQtan
  have hQ0 : Q 0 ≠ 0 := by
    intro h0
    rw [LinearIndependent.pair_iff] at hli
    have := hli (-Q 1) 1 (by
      ext i
      fin_cases i <;> simp [pointO, h0, hQ2])
    simp at this
  have hres : restrictLine (cubicForm c) pointO Q =
      Polynomial.C (c 1 * Q 0 ^ 2) * Polynomial.X ^ 2 +
        Polynomial.C (c 0 * Q 0 ^ 3 + c 1 * Q 0 ^ 2 * Q 1) * Polynomial.X ^ 3 := by
    simp [restrictLine, cubicForm, pointO, hc3, hc6, hQ2]
    ring
  have hc1 : c 1 = 0 := by
    have := (Polynomial.X_pow_dvd_iff.1 hdiv) 2 (by norm_num)
    rw [hres] at this
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at this
    simpa [hQ0] using this
  exact cubicForm_weierstrass c hc1 hc3 hc6 (cubicForm_c0_ne_zero c hns hc1 hc3 hc6 hc7) hc7
/-- **Proposition 1.2** (pdf p. 54), assembled: a nonsingular cubic curve with a point of inflection $O \in C(k)$
is carried by an invertible linear change of variables to a Weierstrass cubic (10), with $O$ going to
$(0 : 1 : 0)$. -/
@[kb "milne2006ec" "Ch. II, Proposition 1.2, pdf p. 54"]
theorem proposition_1_2 (F : MvPolynomial (Fin 3) k) (hF : F.IsHomogeneous 3) (hns : IsNonsingularPlaneCurve F)
    {O : Fin 3 → k} (hO : IsInflectionPoint F O) :
    ∃ (A : Matrix (Fin 3) (Fin 3) k) (lam : k) (W : WeierstrassCurve k), IsUnit A.det ∧ lam ≠ 0 ∧
      (∃ μ : k, μ ≠ 0 ∧ A.mulVec pointO = μ • O) ∧ linearChange A F = C lam * W.toProjective.polynomial := by
  obtain ⟨hO0, hOC, hex, Q, hli, hQtan, hdiv⟩ := hO
  set g : Fin 3 → k := fun i => eval O (pderiv i F) with hg
  have hg0 : g ≠ 0 := by
    obtain ⟨i, hi⟩ := hex
    intro h; exact hi (congrFun h i)
  have hgO : ∑ i, g i * O i = 0 := euler_cubic hF hOC
  have hgQ : ∑ i, g i * Q i = 0 := hQtan
  obtain ⟨A, hA, hc0, hc1, hc2⟩ := exists_adapted_matrix hg0 hgO hli hgQ
  have hAO := A_mulVec_pointO hc1
  have hAe1 : A.mulVec ![1, 0, 0] = Q := by
    ext j
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hc0]
  obtain ⟨c, hc⟩ := exists_cubicForm (isHomogeneous_linearChange hF A)
  have hns' : IsNonsingularPlaneCurve (cubicForm c) := hc ▸ isNonsingular_linearChange hA hns
  have hd0 : eval pointO (pderiv 0 (cubicForm c)) = 0 := by
    rw [← hc, eval_pderiv_linearChange, hAO]
    simpa [hc0] using hgQ
  have hd2 : eval pointO (pderiv 2 (cubicForm c)) ≠ 0 := by
    rw [← hc, eval_pderiv_linearChange, hAO]
    simpa using hc2
  have htan : OnTangentLine (cubicForm c) pointO ![1, 0, 0] := by
    simp [OnTangentLine, Fin.sum_univ_three, hd0]
  have hinfl : IsInflectionPoint (cubicForm c) pointO := by
    refine ⟨?_, ?_, ⟨2, hd2⟩, ![1, 0, 0], ?_, htan, ?_⟩
    · intro h; have := congrFun h 1; simp [pointO] at this
    · rw [← hc, eval_linearChange, hAO]; exact hOC
    · rw [LinearIndependent.pair_iff]
      intro s t h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [pointO] at h0 h1
      exact ⟨h1, h0⟩
    · unfold lineIntersectionDivisible
      rw [← hc, restrictLine_linearChange, hAO, hAe1]
      exact hdiv
  obtain ⟨μ, lam, W, hμ, hlam, heq⟩ := proposition_1_2_b c hns' hinfl htan
  refine ⟨A * Matrix.diagonal ![1, 1, μ], lam, W, ?_, hlam, ⟨1, one_ne_zero, ?_⟩, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    simpa [hμ] using hA
  · rw [← Matrix.mulVec_mulVec]
    have : (Matrix.diagonal ![1, 1, μ]).mulVec pointO = pointO := by
      ext j; fin_cases j <;> simp [Matrix.mulVec_diagonal, pointO]
    rw [this, hAO, one_smul]
  · rw [linearChange_mul, hc, linearChange_diagonal, heq]
/-- **Definition 1.1**, (c) ⇒ (b) (pdf p. 53): on a Weierstrass cubic (10), $O = (0 : 1 : 0)$ is a point of
inflection (with tangent line $Z = 0$). -/
@[kb "milne2006ec" "Ch. II, Definition 1.1, (c) implies (b), pdf p. 53"]
theorem weierstrass_pointO_isInflectionPoint (W : WeierstrassCurve k) :
    IsInflectionPoint W.toProjective.polynomial pointO ∧
      OnTangentLine W.toProjective.polynomial pointO ![1, 0, 0] := by
  have hT : OnTangentLine W.toProjective.polynomial pointO ![1, 0, 0] := by
    simp [OnTangentLine, Fin.sum_univ_three, pointO, WeierstrassCurve.Projective.polynomial, pderiv_X, Pi.single_apply]
  refine ⟨⟨?_, ?_, ⟨2, ?_⟩, ![1, 0, 0], ?_, hT, ?_⟩, hT⟩
  · intro h; have := congrFun h 1; simp [pointO] at this
  · simp [pointO, WeierstrassCurve.Projective.polynomial]
  · simp [pointO, WeierstrassCurve.Projective.polynomial, pderiv_X, Pi.single_apply]
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [pointO] at h0 h1
    exact ⟨h1, h0⟩
  · have : restrictLine W.toProjective.polynomial pointO ![1, 0, 0] = - Polynomial.X ^ 3 := by
      simp [restrictLine, pointO, WeierstrassCurve.Projective.polynomial]
    rw [lineIntersectionDivisible, this]
    exact (dvd_neg).2 dvd_rfl

/-- The Hessian $\det(\partial^2F/\partial X_i\partial X_j)$ of a plane curve (Aside 1.3, p. 57). -/
@[kb "milne2006ec" "Ch. II, Aside 1.3, pdf p. 57"]
noncomputable def hessian (F : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  (Matrix.of fun i j => pderiv i (pderiv j F)).det

/-- **Aside 1.3** (pdf p. 57): if $F$ is homogeneous of degree $d \ge 2$ then the Hessian is homogeneous of degree
$3(d - 2)$. -/
@[kb "milne2006ec" "Ch. II, Aside 1.3, pdf p. 57"]
theorem hessian_isHomogeneous {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d) (hd : 2 ≤ d) :
    (hessian F).IsHomogeneous (3 * (d - 2)) := by
  have h : ∀ i j, (pderiv i (pderiv j F)).IsHomogeneous (d - 2) := by
    intro i j
    have := (hF.pderiv (i := j)).pderiv (i := i)
    have e : d - 1 - 1 = d - 2 := by omega
    rwa [e] at this
  have key : ∀ a b c : MvPolynomial (Fin 3) k, a.IsHomogeneous (d - 2) → b.IsHomogeneous (d - 2) →
      c.IsHomogeneous (d - 2) → (a * b * c).IsHomogeneous (3 * (d - 2)) := by
    intro a b c ha hb hc
    have := (ha.mul hb).mul hc
    convert this using 1
    ring
  rw [hessian, Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  repeat first | apply MvPolynomial.IsHomogeneous.add | apply MvPolynomial.IsHomogeneous.sub | exact key _ _ _ (h _ _) (h _ _) (h _ _)

/-- **Aside 1.3** (pdf p. 57), the Hessian criterion (Fulton 1969, Chap. 5, p. 116), as a named statement: in
characteristic $\neq 2$, a nonsingular point $P$ of a plane curve $F = 0$ of degree $d$ is a point of inflection
iff $H(P) = 0$. (Milne adds that a nonsingular cubic therefore has 3 points of inflection over $k^{al}$; the
correct number is 9. Fulton requires the characteristic not to divide $d - 1$; for cubics, characteristic $\neq 2$.) -/
@[kb "milne2006ec" "Ch. II, Aside 1.3, pdf p. 57"]
structure HessianCriterion : Prop where
  iff : ∀ (k : Type) [Field k], (2 : k) ≠ 0 → ∀ F : MvPolynomial (Fin 3) k, F.IsHomogeneous 3 →
    ∀ P : Fin 3 → k, P ≠ 0 → eval P F = 0 → (∃ i, eval P (pderiv i F) ≠ 0) →
      (IsInflectionPoint F P ↔ eval P (hessian F) = 0)

/-- The affine chart $Z = 1$ of a plane curve: $f(X, Y) = F(X, Y, 1)$, with function field the fraction field of
$k[X, Y]/(f)$. -/
noncomputable abbrev chartZ (F : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 2) k :=
  bind₁ ![X 0, X 1, 1] F

/-- **Nagell's reduction** (pdf pp. 56–57, "Transforming a point to a point of inflection"), as a named
statement. A nonsingular plane cubic $C$ over $k$ with a point $O \in C(k)$ is isomorphic to a Weierstrass curve
(with $O \mapsto (0 : 1 : 0)$). Isomorphism classes of nonsingular projective curves are classified by their
function fields (Milne I §4), and translations on the Weierstrass curve move any point to $(0 : 1 : 0)$; so the
statement is that the function field of $C$ (the fraction field of the coordinate ring of the chart $Z = 1$,
after a linear change of variables making $Z = 0$ not a component, here assumed: $F(X, Y, 1)$ irreducible) is
$k$-isomorphic to the function field of an elliptic Weierstrass curve. -/
@[kb "milne2006ec" "Ch. II, §1, Transforming a point to a point of inflection, pdf pp. 56-57"]
structure NagellReduction : Prop where
  iso : ∀ (k : Type) [Field k] (F : MvPolynomial (Fin 3) k), F.IsHomogeneous 3 → IsNonsingularPlaneCurve F →
    (∃ O : Fin 3 → k, O ≠ 0 ∧ eval O F = 0) → Irreducible (chartZ F) →
    ∃ (W : WeierstrassCurve k), W.IsElliptic ∧
      Nonempty (FractionRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {chartZ F}) ≃ₐ[k] W.toAffine.FunctionField)

end NumberFieldKB.MilneEC.II
