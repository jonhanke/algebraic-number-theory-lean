import NumberFieldKB.MilneEC.Ch1CubicLocal
import NumberFieldKB.MilneEC.Ch1CubicGrad
import NumberFieldKB.MilneEC.Ch1BezoutAux

/-!
# Milne, Elliptic Curves, Remark I.1.13, first part

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, Remark 1.13 (p. 19), after Fulton 1969, §3.3,
property (5): the intersection number of two affine plane curves at a common point `P` is 1 if and only if
`P` is nonsingular on both curves and the tangent lines there are distinct.

* (⇒) If $I_P = 1$ the gradients at `P` are independent (`det_ne_zero_of_numAt_eq_one`).
* (⇐) If they are independent, $\mathcal O_P/(f, g) \cong K$ (`numAt_eq_one_of_det`).

The second part of the remark ($I_P \ge m_P(C)\,m_P(D)$, with equality if and only if there is no common
tangent) is not proved here; `Remark1_13` stays a named statement (loose end).
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC.Bezout

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]

theorem evalAt_baseChange (q : MvPolynomial (Fin 2) k) (P : K × K) :
    evalAt (baseChange K q) P = evalAt q P := by
  simp [evalAt, baseChange, aeval_map_algebraMap]

theorem evalAt_pderiv_baseChange (q : MvPolynomial (Fin 2) k) (i : Fin 2) (P : K × K) :
    evalAt (pderiv i (baseChange K q)) P = evalAt (pderiv i q) P := by
  rw [baseChange, pderiv_map, ← baseChange, evalAt_baseChange]

theorem intersectionNumberAt_baseChange (f g : MvPolynomial (Fin 2) k) (P : K × K) :
    intersectionNumberAt f g P = numAt (baseChange K f) (baseChange K g) P := by
  rw [← intersectionNumberAt_eq_numAt]
  unfold intersectionNumberAt
  rw [translate_baseChange, translate_baseChange]

/-- Two tangent lines (with nonzero gradients) are associated exactly when the gradients are
proportional. -/
theorem associated_lines_iff (x y a b c d : K) (hab : a ≠ 0 ∨ b ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    Associated (C a * (X 0 - C x) + C b * (X 1 - C y) : MvPolynomial (Fin 2) K)
        (C c * (X 0 - C x) + C d * (X 1 - C y)) ↔ a * d - b * c = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨e, he⟩ := (isUnit_iff_eq_C_of_isReduced).mp u.isUnit
    rw [he.2] at hu
    have h0 := congrArg (pderiv 0) hu
    have h1 := congrArg (pderiv 1) hu
    simp [pderiv_X] at h0 h1
    have h0' : a * e = c := C_injective (Fin 2) K (by rw [C_mul, mul_comm]; exact h0)
    have h1' : b * e = d := C_injective (Fin 2) K (by rw [C_mul, mul_comm]; exact h1)
    rw [← h0', ← h1']; ring
  · intro hdet
    rcases hab with ha | hb
    · have hc0 : c ≠ 0 := by
        intro hc
        have hd : d = 0 := by
          have : a * d = 0 := by rw [hc] at hdet; linear_combination hdet
          exact (mul_eq_zero.mp this).resolve_left ha
        rcases hcd with h | h <;> contradiction
      have hu : IsUnit (C (c / a) : MvPolynomial (Fin 2) K) :=
        (isUnit_iff_ne_zero.mpr (div_ne_zero hc0 ha)).map C
      refine ⟨hu.unit, ?_⟩
      rw [IsUnit.unit_spec]
      have hd : d = b * (c / a) := by field_simp; linear_combination hdet
      rw [hd]
      have h1 : (C a : MvPolynomial (Fin 2) K) * C (c / a) = C c := by
        rw [← C_mul]; congr 1; field_simp
      simp only [map_mul]
      linear_combination (X 0 - C x) * h1
    · have hd0 : d ≠ 0 := by
        intro hd
        have hc : c = 0 := by
          have : b * c = 0 := by rw [hd] at hdet; linear_combination -hdet
          exact (mul_eq_zero.mp this).resolve_left hb
        rcases hcd with h | h <;> contradiction
      have hu : IsUnit (C (d / b) : MvPolynomial (Fin 2) K) :=
        (isUnit_iff_ne_zero.mpr (div_ne_zero hd0 hb)).map C
      refine ⟨hu.unit, ?_⟩
      rw [IsUnit.unit_spec]
      have hc : c = a * (d / b) := by field_simp; linear_combination -hdet
      rw [hc]
      have h1 : (C b : MvPolynomial (Fin 2) K) * C (d / b) = C d := by
        rw [← C_mul]; congr 1; field_simp
      simp only [map_mul]
      linear_combination (X 1 - C y) * h1

end NumberFieldKB.MilneEC.Bezout

namespace NumberFieldKB.MilneEC

open Bezout in
/-- **Remark 1.13** (p. 19), first part, proved: at an isolated common point `P`, $I(P, C \cap D) = 1$ if
and only if `P` is nonsingular on both curves and the tangent lines there are distinct (Fulton 1969,
§3.3). This is the field `eq_one_iff` of the named statement `Remark1_13`. -/
@[kb "milne2006ec" "Ch. I, Rem. 1.13 (first part), pdf p. 19"]
theorem remark_1_13_eq_one_iff (k : Type) [Field k] (K : Type) [Field K] [Algebra k K]
    (f g : MvPolynomial (Fin 2) k) (P : K × K) (hf : P ∈ affinePoints f K)
    (hg : P ∈ affinePoints g K) (_hiso : IsIsolatedPoint f g P) :
    intersectionNumberAt f g P = 1 ↔ IsNonsingularPoint f P ∧ IsNonsingularPoint g P ∧
      ¬ Associated (tangentLine f P) (tangentLine g P) := by
  rw [intersectionNumberAt_baseChange]
  have hP : P ∈ commonZeros (baseChange K f) (baseChange K g) :=
    ⟨by rw [evalAt_baseChange]; exact hf, by rw [evalAt_baseChange]; exact hg⟩
  have e00 := evalAt_pderiv_baseChange f 0 P
  have e01 := evalAt_pderiv_baseChange f 1 P
  have e10 := evalAt_pderiv_baseChange g 0 P
  have e11 := evalAt_pderiv_baseChange g 1 P
  unfold IsNonsingularPoint tangentLine
  simp only [dX, dY]
  constructor
  · intro h1
    have hdet := det_ne_zero_of_numAt_eq_one hP h1
    rw [e00, e01, e10, e11] at hdet
    have hab : evalAt (pderiv 0 f) P ≠ 0 ∨ evalAt (pderiv 1 f) P ≠ 0 := by
      by_contra h; push Not at h; rw [h.1, h.2] at hdet; simp at hdet
    have hcd : evalAt (pderiv 0 g) P ≠ 0 ∨ evalAt (pderiv 1 g) P ≠ 0 := by
      by_contra h; push Not at h; rw [h.1, h.2] at hdet; simp at hdet
    refine ⟨⟨hf, hab⟩, ⟨hg, hcd⟩, fun hass => hdet ?_⟩
    exact (associated_lines_iff _ _ _ _ _ _ hab hcd).mp hass
  · rintro ⟨⟨-, hab⟩, ⟨-, hcd⟩, hnot⟩
    have hdet : evalAt (pderiv 0 f) P * evalAt (pderiv 1 g) P -
        evalAt (pderiv 1 f) P * evalAt (pderiv 0 g) P ≠ 0 :=
      fun h0 => hnot ((associated_lines_iff _ _ _ _ _ _ hab hcd).mpr h0)
    have hns : NonsingAt (baseChange K f) P :=
      ⟨hP.1, by rw [e00, e01]; exact hab⟩
    refine (numAt_eq_one_of_det hns hP.2 ?_).2
    rw [e00, e01, e10, e11]; exact hdet

end NumberFieldKB.MilneEC
