import NumberFieldKB.MilneEC.Ch1Bezout
import NumberFieldKB.MilneEC.Ch1NinePointLocal

/-!
# Gradients: transversality and changes of coordinates

Part of the proof of associativity of the chord and tangent law (Milne, *Elliptic Curves*, Theorem I.3.1).

* `det_ne_zero_of_numAt_eq_one`: if $I_p(f, g) = 1$ then the gradients of `f` and `g` at `p` are linearly
  independent (Fulton 1969, §3.3, the transversal case).
* `pderiv_linSubst`: the chain rule for a linear substitution.
* `IsSmoothForm`: every nonzero zero of the form has a nonzero partial derivative;
  `Frame.nonsingAt`: in a good frame, a smooth form gives an affine curve nonsingular at every point.
-/

open MvPolynomial Matrix

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

theorem exists_gradient_relation {f g q : MvPolynomial (Fin 2) K} {p : K × K}
    (hp : p ∈ commonZeros f g) (h1 : numAt f g p = 1) (hq : evalAt q p = 0) :
    ∃ s u v : K, s ≠ 0 ∧ ∀ b, s * evalAt (pderiv b q) p =
      u * evalAt (pderiv b f) p + v * evalAt (pderiv b g) p := by
  have h0 := mk_eq_zero_of_numAt_eq_one (q := q) hp h1 hq
  rw [Ideal.Quotient.eq_zero_iff_mem, map_span_pair_eq,
    IsLocalization.mem_map_algebraMap_iff (pointIdeal p).primeCompl] at h0
  obtain ⟨⟨a, s⟩, hs⟩ := h0
  rw [← map_mul] at hs
  have hs' := IsLocalization.injective (LocalRingAt p)
    (Ideal.primeCompl_le_nonZeroDivisors (pointIdeal p)) hs
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp a.2
  have hsp : evalAt (s : MvPolynomial (Fin 2) K) p ≠ 0 := by
    have hy : (s : MvPolynomial (Fin 2) K) ∉ pointIdeal p := s.2
    simpa [pointIdeal, evalAt] using hy
  have heq : q * (s : MvPolynomial (Fin 2) K) = u * f + v * g := by
    simp only at hs'
    rw [hs', ← huv]
  have hpf : evalAt f p = 0 := hp.1
  have hpg : evalAt g p = 0 := hp.2
  refine ⟨evalAt (s : MvPolynomial (Fin 2) K) p, evalAt u p, evalAt v p, hsp, fun b => ?_⟩
  have := congrArg (fun r => aeval ![p.1, p.2] (pderiv b r)) heq
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul] at this
  simp only [evalAt] at hq hpf hpg ⊢
  rw [hq, hpf, hpg] at this
  linear_combination this

theorem det_ne_zero_of_numAt_eq_one {f g : MvPolynomial (Fin 2) K} {p : K × K}
    (hp : p ∈ commonZeros f g) (h1 : numAt f g p = 1) :
    evalAt (pderiv 0 f) p * evalAt (pderiv 1 g) p - evalAt (pderiv 1 f) p * evalAt (pderiv 0 g) p
      ≠ 0 := by
  intro hdet
  obtain ⟨s, u, v, hs, hr⟩ := exists_gradient_relation (q := X 0 - C p.1) hp h1 (by simp [evalAt])
  obtain ⟨s', u', v', hs', hr'⟩ :=
    exists_gradient_relation (q := X 1 - C p.2) hp h1 (by simp [evalAt])
  have q0 : ∀ b : Fin 2, evalAt (pderiv b (X 0 - C p.1 : MvPolynomial (Fin 2) K)) p =
      if b = 0 then 1 else 0 := by
    intro b; fin_cases b <;> simp [evalAt, pderiv_X]
  have q1 : ∀ b : Fin 2, evalAt (pderiv b (X 1 - C p.2 : MvPolynomial (Fin 2) K)) p =
      if b = 1 then 1 else 0 := by
    intro b; fin_cases b <;> simp [evalAt, pderiv_X]
  have e1 := hr 0
  have e2 := hr 1
  have e4 := hr' 1
  rw [q0] at e1 e2
  rw [q1] at e4
  simp only [ite_true, ite_false, mul_one, mul_zero, Fin.isValue, one_ne_zero] at e1 e2 e4
  generalize evalAt (pderiv 0 f) p = a at *
  generalize evalAt (pderiv 1 f) p = b at *
  generalize evalAt (pderiv 0 g) p = c at *
  generalize evalAt (pderiv 1 g) p = d at *
  have : s * s' = (a * d - b * c) * (u * v' - v * u') := by
    linear_combination s' * e1 + (u * a + v * c) * e4 - (u' * a + v' * c) * e2
  rw [hdet, zero_mul] at this
  exact mul_ne_zero hs hs' this

theorem linSubst_add (A : Matrix (Fin 3) (Fin 3) K) (G H : MvPolynomial (Fin 3) K) :
    linSubst A (G + H) = linSubst A G + linSubst A H := by
  simp [linSubst]

theorem linSubst_mul_X(A : Matrix (Fin 3) (Fin 3) K) (G : MvPolynomial (Fin 3) K) (i : Fin 3) :
    linSubst A (G * X i) = linSubst A G * ∑ l, C (A i l) * X l := by
  simp [linSubst]

theorem pderiv_linSubst (A : Matrix (Fin 3) (Fin 3) K) (F : MvPolynomial (Fin 3) K) (j : Fin 3) :
    pderiv j (linSubst A F) = ∑ i, C (A i j) * linSubst A (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [linSubst]
  | add p q hp hq =>
    rw [linSubst_add, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, linSubst_add, mul_add]
  | mul_X p i hp =>
    have hd : pderiv j (∑ l, C (A i l) * (X l : MvPolynomial (Fin 3) K)) = C (A i j) := by
      simp [pderiv_X, Pi.single_apply]
    have hpd : ∀ l, linSubst A (pderiv l (p * X i)) =
        linSubst A (pderiv l p) * (∑ l, C (A i l) * X l) +
          (if i = l then linSubst A p else 0) := by
      intro l
      rw [pderiv_mul, pderiv_X, Pi.single_apply, linSubst_add, linSubst_mul_X]
      by_cases h : i = l
      · simp [h, linSubst]
      · simp [h, linSubst]
    rw [linSubst_mul_X, pderiv_mul, hp, hd]
    simp only [hpd, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true,Finset.sum_mul, mul_assoc]
    ring

/-- A **smooth form**: every nonzero zero has a nonzero partial derivative (the projective curve is
nonsingular, over the field of coefficients). -/
def IsSmoothForm (F : MvPolynomial (Fin 3) K) : Prop :=
  ∀ v : Fin 3 → K, v ≠ 0 → aeval v F = 0 → ∃ j, aeval v (pderiv j F) ≠ 0

/-- In the chart $Z = 1$ after an invertible substitution, a smooth form of degree `m ≥ 1` gives an affine
curve which is nonsingular at each of its points. -/
theorem nonsingAt_dehomogenize_linSubst {F : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF : F.IsHomogeneous m) (hm : m ≠ 0) (hsm : IsSmoothForm F) {A : Matrix (Fin 3) (Fin 3) K}
    (hA : IsUnit A.det) {p : K × K} (hp : evalAt (dehomogenize 2 (linSubst A F)) p = 0) :
    evalAt (pderiv 0 (dehomogenize 2 (linSubst A F))) p ≠ 0 ∨
      evalAt (pderiv 1 (dehomogenize 2 (linSubst A F))) p ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  have hF' := isHomogeneous_linSubst hF A
  set w : Fin 3 → K := ![p.1, p.2, 1] with hw
  have hw2 : w 2 ≠ 0 := by simp [hw]
  have hw0 : w ≠ 0 := fun h => hw2 (by rw [h]; rfl)
  have hpc : pieceCoords 2 w = p := by
    simp [pieceCoords, hw]
  have hsing : IsSingularPoint (dehomogenize 2 (linSubst A F)) (pieceCoords 2 w) := by
    rw [hpc]
    exact ⟨hp, h0, h1⟩
  obtain ⟨hFw, hdw⟩ := (isSingularPoint_dehomogenize_iff hF' w 2 hw2).mp hsing
  have hAt : Aᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact hA.ne_zero
  have hA0 : A.det ≠ 0 := hA.ne_zero
  have hg : (fun i => aeval (A *ᵥ w) (pderiv i F)) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hAt
    funext j
    have := hdw j
    rw [pderiv_linSubst] at this
    simp only [map_sum, map_mul, aeval_C, aeval_linSubst, Algebra.algebraMap_self,
      RingHom.id_apply] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have hAw : A *ᵥ w ≠ 0 := fun h => hw0 (Matrix.eq_zero_of_mulVec_eq_zero hA0 h)
  obtain ⟨j, hj⟩ := hsm (A *ᵥ w) hAw (by rw [← aeval_linSubst]; exact hFw)
  exact hj (congrFun hg j)

end NumberFieldKB.MilneEC.Bezout
