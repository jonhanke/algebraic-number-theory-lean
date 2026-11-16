import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4VarietyZeta
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Milne, Elliptic Curves, Chapter IV §10: good reduction of a Weierstrass curve

Comparison of `HasGoodReductionAt` (Ch4VarietyZeta) for the projective Weierstrass cubic with $p \nmid \Delta$.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC.VarietyZeta

open WeierstrassCurve

/-- Nonsingularity as a complete intersection for the Weierstrass cubic over a field is
`IsNonsingularCurve`. -/
theorem isNonsingularCI_weierstrass_iff {k : Type*} [Field k] (W : WeierstrassCurve k) :
    IsNonsingularCI (n := 2) (fun _ : Fin 1 => W.toProjective.polynomial) ↔
      NumberFieldKB.MilneEC.II.IsNonsingularCurve W := by
  have hp : (W.baseChange (AlgebraicClosure k)).toProjective.polynomial =
      W.toProjective.polynomial.map (algebraMap k (AlgebraicClosure k)) :=
    WeierstrassCurve.Projective.map_polynomial W.toProjective _
  unfold IsNonsingularCI NumberFieldKB.MilneEC.II.IsNonsingularCurve
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  have hX : ∀ j : Fin 3, eval x ((pderiv j W.toProjective.polynomial).map
      (algebraMap k (AlgebraicClosure k))) =
      eval x (pderiv j ((W.baseChange (AlgebraicClosure k)).toProjective.polynomial)) := by
    intro j
    rw [hp, pderiv_map]
  have hNS : (W.baseChange (AlgebraicClosure k)).toProjective.Nonsingular x ↔
      (W.baseChange (AlgebraicClosure k)).toProjective.Equation x ∧
      ¬ ∀ j : Fin 3, eval x (pderiv j ((W.baseChange (AlgebraicClosure k)).toProjective.polynomial))
        = 0 := by
    unfold WeierstrassCurve.Projective.Nonsingular
    simp only [WeierstrassCurve.Projective.polynomialX, WeierstrassCurve.Projective.polynomialY,
      WeierstrassCurve.Projective.polynomialZ]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro (h|h|h) hj
      exacts [h (hj 0), h (hj 1), h (hj 2)]
    · intro h
      by_contra h'
      push Not at h'
      apply h
      intro j
      fin_cases j
      exacts [h'.1, h'.2.1, h'.2.2]
  have hLI : LinearIndependent (AlgebraicClosure k)
      (fun (_ : Fin 1) (j : Fin 3) => eval x ((pderiv j W.toProjective.polynomial).map
        (algebraMap k (AlgebraicClosure k)))) ↔
      ¬ ∀ j : Fin 3, eval x (pderiv j ((W.baseChange (AlgebraicClosure k)).toProjective.polynomial))
        = 0 := by
    rw [linearIndependent_unique_iff]
    simp only [hX, ne_eq, funext_iff, Pi.zero_apply]
  have hE : (∀ _ : Fin 1, eval x (W.toProjective.polynomial.map
      (algebraMap k (AlgebraicClosure k))) = 0) ↔
      (W.baseChange (AlgebraicClosure k)).toProjective.Equation x := by
    rw [← hp]
    exact forall_const _
  rw [hNS, hLI, hE]
  exact ⟨fun h e => ⟨e, h e⟩, fun h e => (h e).2⟩

/-- Negating the equation changes neither the zero set nor nonvanishing of the gradient. -/
theorem isNonsingularCI_neg_iff {K : Type*} [Field K] (G : MvPolynomial (Fin 3) K) :
    IsNonsingularCI (n := 2) (fun _ : Fin 1 => -G) ↔ IsNonsingularCI (n := 2) (fun _ : Fin 1 => G) := by
  unfold IsNonsingularCI
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  simp only [linearIndependent_unique_iff, map_neg, neg_eq_zero, _root_.funext_iff,
    Pi.zero_apply, ne_eq, forall_const]

/-- The `Z`-partial of the Weierstrass cubic at `(0 : 1 : 0)` is `1`. -/
theorem eval_pderiv_Z {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    eval ![0, 1, 0] (pderiv 2 W.toProjective.polynomial) = 1 := by
  have := WeierstrassCurve.Projective.eval_polynomialZ (W' := W.toProjective) ![0, 1, 0]
  simpa [WeierstrassCurve.Projective.polynomialZ] using this

theorem eval_map_e (P : MvPolynomial (Fin 3) ℤ) :
    eval ![0, 1, 0] (P.map (Int.castRingHom ℚ)) = ((eval ![0, 1, 0] P : ℤ) : ℚ) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, hp]
    simp only [MvPolynomial.map_X, eval_X]
    fin_cases n <;> simp

theorem scaling_pm (W : WeierstrassCurve ℤ) (G : MvPolynomial (Fin 3) ℤ)
    (h : IsPrimitiveScaling (W.toProjective.polynomial.map (Int.castRingHom ℚ)) G) :
    G = W.toProjective.polynomial ∨ G = -W.toProjective.polynomial := by
  obtain ⟨⟨c, hc, hGc⟩, hprim⟩ := h
  set F := W.toProjective.polynomial with hF
  have h1 : eval ![0, 1, 0] (pderiv 2 (F.map (Int.castRingHom ℚ))) = 1 := by
    have := eval_pderiv_Z (W.map (Int.castRingHom ℚ))
    rwa [WeierstrassCurve.Projective.map_polynomial W.toProjective] at this
  have h2 : eval ![0, 1, 0] (pderiv 2 (G.map (Int.castRingHom ℚ))) = c := by
    rw [hGc, pderiv_C_mul, map_mul, eval_C, h1, mul_one]
  set m : ℤ := eval ![0, 1, 0] (pderiv 2 G) with hm
  have h3 : (m : ℚ) = c := by
    rw [← h2, pderiv_map, eval_map_e]
  have h4 : G = C m * F := by
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [hGc, ← h3]
    simp
  have h5 : m.natAbs = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨i, hi⟩ := hprim q hq
    apply hi
    rw [h4, coeff_C_mul]
    exact Dvd.dvd.mul_right (Int.natCast_dvd.2 hqd) _
  rcases Int.natAbs_eq_iff.1 h5 with h6 | h6
  · left; rw [h4, h6]; simp
  · right; rw [h4, h6]; simp

theorem not_dvd_coeff_weierstrass (W : WeierstrassCurve ℤ) (q : ℕ) (hq : q.Prime) :
    ∃ m, ¬ (q : ℤ) ∣ W.toProjective.polynomial.coeff m := by
  by_contra h
  push Not at h
  have := Fact.mk hq
  have h0 : W.toProjective.polynomial.map (Int.castRingHom (ZMod q)) = 0 := by
    ext m
    rw [coeff_map]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (h m)
  have := eval_pderiv_Z (W.map (Int.castRingHom (ZMod q)))
  rw [WeierstrassCurve.Projective.map_polynomial W.toProjective, h0] at this
  simp at this

/-- **Good reduction of a Weierstrass curve** (Milne pdf p. 170 with Ch. II, Theorem 2.4(a)): the projective cubic of
an integral Weierstrass equation has good reduction at $p$ in the sense of `HasGoodReductionAt` iff
$p \nmid \Delta$. -/
@[kb "milne2006ec" "Ch. IV, §10, good reduction of a Weierstrass cubic is p ∤ Δ, pdf p. 170"]
theorem goodReduction_weierstrass_iff (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    HasGoodReductionAt (n := 2)
      (fun _ : Fin 1 => (W.map (Int.castRingHom ℚ)).toProjective.polynomial) p ↔
      ¬ (p : ℤ) ∣ W.Δ := by
  have hQ : (W.map (Int.castRingHom ℚ)).toProjective.polynomial =
      W.toProjective.polynomial.map (Int.castRingHom ℚ) :=
    WeierstrassCurve.Projective.map_polynomial W.toProjective _
  have hZ : (W.map (Int.castRingHom (ZMod p))).toProjective.polynomial =
      W.toProjective.polynomial.map (Int.castRingHom (ZMod p)) :=
    WeierstrassCurve.Projective.map_polynomial W.toProjective _
  have hCI : IsNonsingularCI (n := 2)
      (fun _ : Fin 1 => W.toProjective.polynomial.map (Int.castRingHom (ZMod p))) ↔
        ¬ (p : ℤ) ∣ W.Δ := by
    rw [← hZ, isNonsingularCI_weierstrass_iff, NumberFieldKB.MilneEC.II.theorem_2_4_a_nonsingular,
      WeierstrassCurve.map_Δ, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp
  rw [← hCI]
  unfold HasGoodReductionAt
  simp only [hQ]
  constructor
  · rintro ⟨G, hG, hns⟩
    have hG0 : G = fun _ => G 0 := by
      funext i
      rw [Subsingleton.elim i 0]
    rw [hG0] at hns
    rcases scaling_pm W (G 0) (hG 0) with h | h
    · rw [h] at hns; exact hns
    · rw [h] at hns
      simp only [map_neg] at hns
      exact (isNonsingularCI_neg_iff _).1 hns
  · intro h
    exact ⟨fun _ => W.toProjective.polynomial, fun _ => ⟨⟨1, one_ne_zero, by simp⟩,
      not_dvd_coeff_weierstrass W⟩, h⟩

end NumberFieldKB.MilneEC.VarietyZeta
