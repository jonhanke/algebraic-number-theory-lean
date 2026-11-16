import NumberFieldKB.MilneEC.Ch4Heights
import NumberFieldKB.MilneEC.Ch4Lattice
import Mathlib.Order.Northcott
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.Height.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Milne, Elliptic Curves, Chapter IV §6: the Néron–Tate pairing

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 6 ("The Néron-Tate
pairing"), Theorem 6.1.  Locators give the pdf page of the text `ectext6` (printed page = pdf page − 8).

Milne's pairing $B(x, y) = \hat h(x + y) - \hat h(x) - \hat h(y)$ on $E(\mathbb{Q})$ is `neronTatePairing`; it is
$\mathbb{Z}$-bilinear (Proposition 4.9).  Milne extends it to $E(\mathbb{Q}) \otimes \mathbb{R}$ and computes it in the
basis $e_i \otimes 1$, where $e_1, \dots, e_r$ is a $\mathbb{Z}$-basis of $E(\mathbb{Q})/E(\mathbb{Q})_{\mathrm{tors}}$: its
matrix is $(B(e_i, e_j))$.  Theorem 6.1 is stated here in that form: for every family $e_1, \dots, e_r$ of points
that is linearly independent over $\mathbb{Z}$ (for instance lifts of a basis of $E/E_{\mathrm{tors}}$), the matrix
$(B(e_i, e_j))$ is positive definite.  As in §4 the base field is any field with an admissible family of absolute
values and the Northcott property (number fields; Milne: $\mathbb{Q}$, and Remark 4.12).
-/

open WeierstrassCurve WeierstrassCurve.Affine Height

namespace NumberFieldKB.MilneEC

variable {K : Type*} [Field K] [AdmissibleAbsValues K] (W : Affine K) [W.IsElliptic] [DecidableEq K]

/-- The **Néron–Tate pairing** (pdf p. 139): $B(x, y) = \hat h(x + y) - \hat h(x) - \hat h(y)$, a
$\mathbb{Z}$-bilinear symmetric pairing on $E(K)$ (Proposition 4.9). -/
@[kb "milne2006ec" "Ch. IV, §6, definition of the Néron-Tate pairing, pdf p. 139"]
noncomputable def neronTatePairing (P Q : W.Point) : ℝ := polarPairingFun (canonicalHeight W) P Q

/-- Twice the canonical height of an integral combination $\sum_i m_i e_i$ is $\sum_{i,j} m_i m_j B(e_i, e_j)$
(bi-additivity of the pairing and $2\hat h(x) = B(x, x)$). -/
theorem two_canonicalHeight_sum {r : ℕ} (e : Fin r → W.Point) (m : Fin r → ℤ) :
    2 * canonicalHeight W (∑ i, m i • e i) =
      ∑ i, ∑ j, (m i : ℝ) * (m j : ℝ) * neronTatePairing W (e i) (e j) := by
  obtain ⟨Q, hQ⟩ := (isQuadraticForm_iff_exists_quadraticMap (by rw [ringChar.eq ℝ 0]; norm_num)
    (canonicalHeight W)).1 (prop_4_9 W)
  have hpol : ∀ x y, neronTatePairing W x y = Q.polarBilin x y := by
    intro x y
    simp [neronTatePairing, polarPairingFun, QuadraticMap.polar, hQ]
  have hself : ∀ x, 2 * canonicalHeight W x = Q.polarBilin x x := by
    intro x
    rw [← hQ]
    simp [QuadraticMap.polar_self]
  rw [hself]
  simp only [hpol, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **Theorem 6.1** (pdf p. 139).  The Néron–Tate pairing is positive definite on $E(K) \otimes \mathbb{R}$: for
points $e_1, \dots, e_r$ linearly independent over $\mathbb{Z}$, the matrix $(B(e_i, e_j))$ is positive definite. -/
@[kb "milne2006ec" "Ch. IV, Thm. 6.1, pdf p. 139"]
theorem thm_6_1 [Northcott (logHeight₁ (K := K))] {r : ℕ} (e : Fin r → W.Point)
    (he : LinearIndependent ℤ e) :
    (Matrix.of fun i j => neronTatePairing W (e i) (e j)).PosDef := by
  set M : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => neronTatePairing W (e i) (e j) with hM
  have hsymm : M.IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, hM, Matrix.of_apply, neronTatePairing, polarPairingFun]
    rw [add_comm (e j)]
    ring
  let c : (Fin r → ℤ) → (Fin r → ℝ) := fun m i => (m i : ℝ)
  let φ : (Fin r → ℤ) → W.Point := fun m => ∑ i, m i • e i
  have hq : ∀ m : (Fin r → ℤ), M.toQuadraticForm' (c m) = 2 * canonicalHeight W (φ m) := by
    intro m
    rw [two_canonicalHeight_sum]
    simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', c, hM, dotProduct,
      Matrix.mulVec, Finset.mul_sum, mul_assoc]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hinj : Function.Injective φ := by
    intro m m' h
    funext i
    have := Fintype.linearIndependent_iff.mp he (m - m') (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr h) i
    simpa [sub_eq_zero] using this
  have hmem : ∀ x : Fin r → ℝ, x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin r))) →
      ∃ m, x = c m := by
    intro x hx
    rw [Module.Basis.mem_span_iff_repr_mem] at hx
    choose m hm using fun i => hx i
    exact ⟨m, funext fun i => by simpa [c] using (hm i).symm⟩
  have hpd : M.toQuadraticForm'.PosDef := by
    refine lemma_6_2 M.toQuadraticForm' (Pi.basisFun ℝ (Fin r)) ?_ ?_
    · intro C
      refine ((thm_4_7_a W (C / 2)).preimage hinj.injOn).image c |>.subset ?_
      rintro x ⟨hx, hxC⟩
      obtain ⟨m, rfl⟩ := hmem x hx
      refine ⟨m, ?_, rfl⟩
      rw [hq] at hxC
      show canonicalHeight W (φ m) ≤ C / 2
      linarith
    · intro x hx h0
      obtain ⟨m, rfl⟩ := hmem x hx
      rw [hq] at h0
      have h1 : canonicalHeight W (φ m) = 0 := by linarith
      obtain ⟨k, hk, hk0⟩ := ((thm_4_7_b W (φ m)).1 h1).exists_nsmul_eq_zero
      have hlin := Fintype.linearIndependent_iff.mp he (fun i => (k : ℤ) * m i) (by
        have : k • φ m = 0 := hk0
        simp only [φ, Finset.smul_sum] at this
        simpa [mul_smul, natCast_zsmul] using this)
      funext i
      have := hlin i
      simp only [mul_eq_zero, Nat.cast_eq_zero] at this
      rcases this with h | h
      · omega
      · simp [c, h]
  exact Matrix.PosDef.of_toQuadraticForm' hsymm hpd

/-- Theorem 6.1 (pdf p. 139), "in particular, it is nondegenerate": the matrix $(B(e_i, e_j))$ is invertible. -/
@[kb "milne2006ec" "Ch. IV, Thm. 6.1, pdf p. 139"]
theorem thm_6_1_det_ne_zero [Northcott (logHeight₁ (K := K))] {r : ℕ} (e : Fin r → W.Point)
    (he : LinearIndependent ℤ e) :
    (Matrix.of fun i j => neronTatePairing W (e i) (e j)).det ≠ 0 :=
  (thm_6_1 W e he).det_pos.ne'

end NumberFieldKB.MilneEC
