import NumberFieldKB.MilneEC.Ch1BezoutDefs
import NumberFieldKB.MilneEC.Ch1Resultant

/-!
# Bezout's theorem: auxiliary facts for the assembly

Part of the proof of Milne, *Elliptic Curves*, Theorem I.1.18 (Bezout), after Fulton 1969, Chapter 5.

* `projIntersectionNumber_baseChange`, `projectivePoints_baseChange`: intersection numbers and points of
  curves over `k` are those of the curves with coefficients extended to `K`.
* `exists_line_avoiding`: over an infinite field, a line $X + tY + t^2Z = 0$ missing finitely many given
  points.
* `homogeneousComponent_dehomogenize`: the leading form of $F(X, Y, 1)$ is $F(X, Y, 0)$.
* `isRelPrime_of_forall_ne_zero`: over an algebraically closed field, two polynomials with no common zero
  other than the origin are relatively prime.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

/-! ### Base change -/

section BaseChange

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]

theorem translate_baseChange (f : MvPolynomial (Fin 2) k) (P : K × K) :
    translate (baseChange K f) P = translate f P := by
  show aeval _ (map (algebraMap k K) f) = aeval _ f
  exact aeval_map_algebraMap K _ f

theorem dehomogenize_baseChange (i : Fin 3) (F : MvPolynomial (Fin 3) k) :
    dehomogenize i (baseChange K F) = baseChange K (dehomogenize i F) := by
  unfold dehomogenize baseChange
  induction F using MvPolynomial.induction_on with
  | C c => simp [algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp, map_X, aeval_X]
    congr 1
    fin_cases i <;> fin_cases j <;> simp [pieceSubst]

theorem projIntersectionNumber_baseChange (F G : MvPolynomial (Fin 3) k) (P : ℙ K (Fin 3 → K)) :
    projIntersectionNumber (baseChange K F) (baseChange K G) P = projIntersectionNumber F G P := by
  unfold projIntersectionNumber intersectionNumberAt
  rw [dehomogenize_baseChange, dehomogenize_baseChange, translate_baseChange, translate_baseChange]

theorem projectivePoints_baseChange (F : MvPolynomial (Fin 3) k) :
    projectivePoints (baseChange K F) K = projectivePoints F K := by
  ext P
  simp [projectivePoints, baseChange, aeval_map_algebraMap]

theorem totalDegree_baseChange (F : MvPolynomial (Fin 3) k) :
    (baseChange K F).totalDegree = F.totalDegree := by
  simp [totalDegree, baseChange, support_map_of_injective _ (algebraMap k K).injective]

theorem isHomogeneous_baseChange {F : MvPolynomial (Fin 3) k} {m : ℕ} (hF : F.IsHomogeneous m) :
    (baseChange K F).IsHomogeneous m :=
  hF.map _

end BaseChange

variable {K : Type*} [Field K]

/-! ### A line missing finitely many points -/

/-- Over an infinite field, for finitely many nonzero vectors there is `t` with
$v_0 + t v_1 + t^2 v_2 \neq 0$ for all of them. -/
theorem exists_line_avoiding [Infinite K] (S : Finset (Fin 3 → K)) (hS : ∀ v ∈ S, v ≠ 0) :
    ∃ t : K, ∀ v ∈ S, v 0 + t * v 1 + t ^ 2 * v 2 ≠ 0 := by
  classical
  let q : (Fin 3 → K) → Polynomial K := fun v =>
    Polynomial.C (v 0) + Polynomial.C (v 1) * Polynomial.X + Polynomial.C (v 2) * Polynomial.X ^ 2
  have hq : ∀ v ∈ S, q v ≠ 0 := by
    intro v hv h0
    apply hS v hv
    have c0 := congrArg (fun r => Polynomial.coeff r 0) h0
    have c1 := congrArg (fun r => Polynomial.coeff r 1) h0
    have c2 := congrArg (fun r => Polynomial.coeff r 2) h0
    simp [q, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at c0 c1 c2
    funext i
    fin_cases i <;> simp [c0, c1, c2]
  let R : Finset K := S.biUnion fun v => (q v).roots.toFinset
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset R
  refine ⟨t, fun v hv h => ht ?_⟩
  refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hq v hv)]
  simp only [q, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  linear_combination h

/-- The matrix with rows $(0, 1, 0)$, $(0, 0, 1)$, $(1, t, t^2)$; its third row is the line of
`exists_line_avoiding`. -/
def lineMatrix (t : K) : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, t, t ^ 2]

theorem det_lineMatrix (t : K) : (lineMatrix t).det = 1 := by
  simp [lineMatrix, Matrix.det_fin_three]

theorem lineMatrix_mulVec_two (t : K) (v : Fin 3 → K) :
    (lineMatrix t).mulVec v 2 = v 0 + t * v 1 + t ^ 2 * v 2 := by
  simp [lineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-! ### The leading form of a dehomogenization -/

/-- $F(X, Y, 0)$, as a polynomial in two variables. -/
noncomputable def atInfinity (F : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 2) K :=
  aeval ![X 0, X 1, 0] F

/-- The term of the dehomogenization coming from one monomial. -/
noncomputable def dehomTerm (s : Fin 3 →₀ ℕ) (c : K) : MvPolynomial (Fin 2) K :=
  C c * X 0 ^ s 0 * X 1 ^ s 1

theorem dehomogenize_monomial (s : Fin 3 →₀ ℕ) (c : K) :
    dehomogenize 2 (monomial s c) = dehomTerm s c := by
  rw [dehomogenize, aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_three]
  simp [dehomTerm, pieceSubst, mul_assoc]

theorem atInfinity_monomial (s : Fin 3 →₀ ℕ) (c : K) :
    atInfinity (monomial s c) = if s 2 = 0 then dehomTerm s c else 0 := by
  simp only [atInfinity, aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_three, dehomTerm]
  split_ifs with h
  · simp [h, mul_assoc]
  · simp [zero_pow h]

theorem dehomTerm_isHomogeneous (s : Fin 3 →₀ ℕ) (c : K) :
    (dehomTerm s c).IsHomogeneous (s 0 + s 1) := by
  unfold dehomTerm
  have := ((isHomogeneous_C (Fin 2) c).mul (isHomogeneous_X_pow (R := K) (0 : Fin 2) (s 0))).mul
    (isHomogeneous_X_pow (R := K) (1 : Fin 2) (s 1))
  simpa using this

theorem degree_eq_of_mem_support {F : MvPolynomial (Fin 3) K} {m : ℕ} (hF : F.IsHomogeneous m)
    {s : Fin 3 →₀ ℕ} (hs : s ∈ F.support) : s 0 + s 1 + s 2 = m := by
  have := hF (mem_support_iff.mp hs)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_three] using this

theorem dehomogenize_eq_sum (F : MvPolynomial (Fin 3) K) :
    dehomogenize 2 F = ∑ s ∈ F.support, dehomTerm s (F.coeff s) := by
  conv_lhs => rw [F.as_sum]
  unfold dehomogenize
  rw [map_sum]
  exact Finset.sum_congr rfl fun s _ => dehomogenize_monomial s _

theorem atInfinity_eq_sum (F : MvPolynomial (Fin 3) K) :
    atInfinity F = ∑ s ∈ F.support, if s 2 = 0 then dehomTerm s (F.coeff s) else 0 := by
  conv_lhs => rw [F.as_sum]
  unfold atInfinity
  rw [map_sum]
  exact Finset.sum_congr rfl fun s _ => atInfinity_monomial s _

theorem totalDegree_dehomogenize_le {F : MvPolynomial (Fin 3) K} {m : ℕ} (hF : F.IsHomogeneous m) :
    (dehomogenize 2 F).totalDegree ≤ m := by
  rw [dehomogenize_eq_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  have h := degree_eq_of_mem_support hF hs
  exact ((dehomTerm_isHomogeneous s _).totalDegree_le).trans (by omega)

theorem homogeneousComponent_dehomogenize {F : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF : F.IsHomogeneous m) : homogeneousComponent m (dehomogenize 2 F) = atInfinity F := by
  rw [dehomogenize_eq_sum, atInfinity_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := degree_eq_of_mem_support hF hs
  rw [homogeneousComponent_of_mem (dehomTerm_isHomogeneous s _)]
  by_cases h2 : s 2 = 0
  · simp only [show s 0 + s 1 = m by omega, h2, ↓reduceIte]
  · simp only [h2, ↓reduceIte, ite_eq_right_iff]
    intro h'; omega

theorem aeval_atInfinity (F : MvPolynomial (Fin 3) K) (a b : K) :
    aeval ![a, b] (atInfinity F) = aeval ![a, b, 0] F := by
  unfold atInfinity
  rw [comp_aeval_apply]
  refine congrArg (fun w => aeval w F) ?_
  funext i
  fin_cases i <;> simp

/-! ### Relative primality from the absence of common zeros -/

/-- Over an algebraically closed field, a nonconstant polynomial in two variables has a zero other than
the origin. -/
theorem exists_zero_ne_origin [IsAlgClosed K] {h : MvPolynomial (Fin 2) K} (hh : ¬ IsUnit h)
    (h0 : h ≠ 0) : ∃ a b : K, (a, b) ≠ (0, 0) ∧ aeval ![a, b] h = 0 := by
  classical
  set H := yPolyEquiv h with hH
  have key : ∀ a b : K, aeval ![a, b] h =
      Polynomial.eval b (Polynomial.map (Polynomial.evalRingHom a) H) := by
    intro a b
    rw [hH]
    have e : ((aeval ![a, b] : MvPolynomial (Fin 2) K →ₐ[K] K) : MvPolynomial (Fin 2) K →+* K) =
        ((Polynomial.evalRingHom b).comp (Polynomial.mapRingHom (Polynomial.evalRingHom a))).comp
          (yPolyEquiv (k := K)).toAlgHom.toRingHom := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · simp
      · fin_cases i <;> simp
    exact congrArg (fun φ : MvPolynomial (Fin 2) K →+* K => φ h) e
  have hH0 : H ≠ 0 := by
    rw [hH]; exact (map_ne_zero_iff _ yPolyEquiv.injective).mpr h0
  by_cases hd : H.natDegree = 0
  · -- `h` is a polynomial in `X` alone, nonconstant
    have hc : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
    have hcd : (H.coeff 0).natDegree ≠ 0 := by
      intro hcd0
      apply hh
      set c0 := H.coeff 0 with hc0
      have e1 : c0 = Polynomial.C (c0.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hcd0
      have e2 : H = Polynomial.C (Polynomial.C (c0.coeff 0)) := by rw [hc, ← e1]
      have hne : c0.coeff 0 ≠ 0 := by
        intro hz; rw [hz] at e2; simp at e2; exact hH0 e2
      have e3 : h = C (c0.coeff 0) := by
        apply yPolyEquiv.injective; rw [← hH, e2]; simp
      rw [e3]; exact (isUnit_iff_ne_zero.mpr hne).map C
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (H.coeff 0)
      (by rw [Polynomial.degree_eq_natDegree (by rintro h'; simp [h'] at hcd)]; exact_mod_cast hcd)
    refine ⟨a, 1, by simp, ?_⟩
    rw [key, hc]
    simpa using ha
  · -- positive degree in `Y`
    set c := H.leadingCoeff
    have hc0 : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH0
    obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (insert 0 (c.roots.toFinset))
    have ha0 : a ≠ 0 := fun h' => ha (by simp [h'])
    have hca : c.eval a ≠ 0 := by
      intro h'
      exact ha (Finset.mem_insert_of_mem (by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hc0]; exact h'))
    have hdeg : (Polynomial.map (Polynomial.evalRingHom a) H).natDegree = H.natDegree :=
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hca
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_root (Polynomial.map (Polynomial.evalRingHom a) H)
      (by
        rw [Polynomial.degree_eq_natDegree (by
          intro h'; rw [h', Polynomial.natDegree_zero] at hdeg; exact hd hdeg.symm), hdeg]
        exact_mod_cast hd)
    exact ⟨a, b, by simp [ha0], by rw [key]; exact hb⟩

theorem isRelPrime_of_forall_ne_zero [IsAlgClosed K] {P Q : MvPolynomial (Fin 2) K} (hP : P ≠ 0)
    (h : ∀ a b : K, (a, b) ≠ (0, 0) → aeval ![a, b] P = 0 → aeval ![a, b] Q ≠ 0) :
    IsRelPrime P Q := by
  intro d hdP hdQ
  by_contra hd
  have hd0 : d ≠ 0 := by rintro rfl; exact hP (zero_dvd_iff.mp hdP)
  obtain ⟨a, b, hab, hz⟩ := exists_zero_ne_origin hd hd0
  obtain ⟨p, rfl⟩ := hdP
  obtain ⟨q, rfl⟩ := hdQ
  exact h a b hab (by rw [map_mul, hz, zero_mul]) (by rw [map_mul, hz, zero_mul])

end NumberFieldKB.MilneEC.Bezout
