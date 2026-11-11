import NumberFieldKB.ModularCurves.ModularPolynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The conjugates of $j_N$ at the cusp $\infty$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf pp. 192–196). For $\gamma \in \mathrm{SL}_2(\mathbb Z)$
with lower left entry $r$, the matrix $\mathrm{diag}(N, 1)\gamma$ is $\mathrm{SL}_2(\mathbb Z)$-equivalent to an upper
triangular $\begin{pmatrix} a & b \\ 0 & d \end{pmatrix}$ with $a = \gcd(N, r)$, $ad = N$. Hence
$j(N\gamma z) = j((az + b)/d)$, and with $z = N\tau$: $j(N \gamma (N\tau)) = j(a^2\tau + b/d)$
(`jN_smul_ofComplex_mul`).
-/

open UpperHalfPlane hiding I
open Complex
open scoped MatrixGroups

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- $a = \gcd(N, r)$ for the lower left entry $r$ of $\gamma$. -/
def cuspA (N : ℕ) (γ : SL(2, ℤ)) : ℕ := Nat.gcd N (γ 1 0).natAbs

theorem cuspA_dvd (N : ℕ) (γ : SL(2, ℤ)) : cuspA N γ ∣ N := Nat.gcd_dvd_left _ _

/-- Coordinates of the Möbius action of `SL(2,ℤ)` on `ℍ`, as a complex quotient. -/
theorem coe_sl_smul (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- The algebraic identity behind the reduction to upper triangular form. -/
theorem cusp_alg (a d τ p q r' s x y D w : ℂ) (hd : d ≠ 0)
    (hdet : p * s - q * (a * r') = 1) (hb : x * d * p + y * r' = 1)
    (hD : D ≠ 0) (hDd : D = a * r' * (a * d * τ) + s)
    (hw : w * D = (a * d) * (p * (a * d * τ) + q)) :
    (x * w + y) / (-r' * w + d * p) = a ^ 2 * τ + (x * (a * d) * q + y * s) / d := by
  have e1 : (-r' * w + d * p) * D = d := by
    linear_combination (-r') * hw + (d * p) * hDd + d * hdet
  have hden : -r' * w + d * p ≠ 0 := by
    intro h
    rw [h, zero_mul] at e1
    exact hd e1.symm
  rw [div_eq_iff hden]
  apply mul_right_cancel₀ hD
  have e2 : (x * w + y) * D = a ^ 2 * d * τ + x * (a * d) * q + y * s := by
    linear_combination x * hw + y * hDd + (a ^ 2 * d * τ) * hb
  rw [e2, mul_assoc _ (-r' * w + d * p) D, e1]
  field_simp
  ring

/-- **$j(N\gamma(N\tau)) = j(a^2\tau + b/d)$** with $a = \gcd(N, r)$, $d = N/a$, for some integer $b$. -/
theorem jN_smul_ofComplex_mul (N : ℕ) (hN : 1 ≤ N) (γ : SL(2, ℤ)) :
    ∃ b : ℤ, ∀ τ : ℍ, jN N (γ • ofComplex ((N : ℂ) * τ)) =
      jFun (ofComplex (((cuspA N γ : ℂ) ^ 2) * τ + (b : ℂ) / ((N / cuspA N γ : ℕ) : ℂ))) := by
  set a := cuspA N γ with ha
  obtain ⟨d, hd⟩ := cuspA_dvd N γ
  have hapos : 0 < a := Nat.gcd_pos_of_pos_left _ hN
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h] at hd; omega
    · exact h
  have hNd : N / a = d := by rw [hd]; exact Nat.mul_div_cancel_left d hapos
  obtain ⟨r', hr'⟩ : (a : ℤ) ∣ γ 1 0 := by
    have : a ∣ (γ 1 0).natAbs := Nat.gcd_dvd_right _ _
    exact Int.natCast_dvd.mpr this
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this
  have hgcd : (a : ℤ) = N * Int.gcdA N (γ 1 0) + γ 1 0 * Int.gcdB N (γ 1 0) := by
    have := Int.gcd_eq_gcd_ab (N : ℤ) (γ 1 0)
    simpa [ha, cuspA, Int.gcd] using this
  set u := Int.gcdA N (γ 1 0)
  set v := Int.gcdB N (γ 1 0)
  set x : ℤ := u * γ 1 1 with hx
  set y : ℤ := v - N * u * γ 0 1 with hy
  have hb : x * (d * γ 0 0) + y * r' = 1 := by
    have hN' : (N : ℤ) = a * d := by exact_mod_cast hd
    have h1 : (a : ℤ) * (x * (d * γ 0 0) + y * r') = a * 1 := by
      rw [hx, hy]
      have h3 := hgcd
      have h4 := hdet
      rw [hr', hN'] at h3
      rw [hr'] at h4
      rw [hN']
      linear_combination ((a : ℤ) * d * u) * h4 - h3
    have hane : (a : ℤ) ≠ 0 := by exact_mod_cast hapos.ne'
    exact mul_left_cancel₀ hane h1
  refine ⟨x * N * γ 0 1 + y * γ 1 1, fun τ => ?_⟩
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos0 : 0 < ((N : ℂ) * τ).im := by
    simpa using mul_pos hNc τ.im_pos
  set z1 : ℍ := γ • ofComplex ((N : ℂ) * τ) with hz1
  have hz0 : ofComplex ((N : ℂ) * τ) = ⟨(N : ℂ) * τ, hpos0⟩ := ofComplex_apply_of_im_pos hpos0
  have hz1c : (z1 : ℂ) = ((γ 0 0 : ℂ) * ((N : ℂ) * τ) + (γ 0 1 : ℂ)) /
      ((γ 1 0 : ℂ) * ((N : ℂ) * τ) + (γ 1 1 : ℂ)) := by
    rw [hz1, coe_sl_smul, hz0]
  have hDne : (γ 1 0 : ℂ) * ((N : ℂ) * τ) + (γ 1 1 : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      (ofComplex ((N : ℂ) * τ))
    rw [hz0] at this
    simpa [UpperHalfPlane.denom] using this
  have hWpos : 0 < ((N : ℂ) * z1).im := by
    simpa using mul_pos hNc z1.im_pos
  let W : ℍ := ⟨(N : ℂ) * z1, hWpos⟩
  have hWe : ofComplex ((N : ℂ) * z1) = W := ofComplex_apply_of_im_pos hWpos
  let σ : SL(2, ℤ) := ⟨!![x, y; -r', (d : ℤ) * γ 0 0], by
    rw [Matrix.det_fin_two]; simp; linarith⟩
  have hσ00 : σ 0 0 = x := rfl
  have hσ01 : σ 0 1 = y := rfl
  have hσ10 : σ 1 0 = -r' := rfl
  have hσ11 : σ 1 1 = d * γ 0 0 := rfl
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hNc' : (N : ℂ) = a * d := by exact_mod_cast hd
  have hfinal : ((σ • W : ℍ) : ℂ) = ((a : ℂ) ^ 2) * τ + ((x * N * γ 0 1 + y * γ 1 1 : ℤ) : ℂ) / (d : ℂ) := by
    rw [coe_sl_smul, hσ00, hσ01, hσ10, hσ11]
    have hWc : (W : ℂ) = (N : ℂ) * z1 := rfl
    have hr'c : (γ 1 0 : ℂ) = a * r' := by exact_mod_cast hr'
    rw [hWc, hz1c]
    push_cast
    rw [hr'c] at hDne ⊢
    rw [hNc'] at hDne ⊢
    have hdetc : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * (a * r') = 1 := by
      rw [← hr'c]; exact_mod_cast hdet
    have hbc : (x : ℂ) * d * γ 0 0 + y * r' = 1 := by
      have : ((x * (d * γ 0 0) + y * r' : ℤ) : ℂ) = 1 := by exact_mod_cast hb
      push_cast at this
      linear_combination this
    refine cusp_alg a d τ _ _ r' _ x y ((a : ℂ) * r' * (a * d * τ) + γ 1 1) _ hdne hdetc hbc
      hDne rfl ?_
    rw [mul_assoc, div_mul_cancel₀ _ hDne]
  have : ofComplex (((a : ℂ) ^ 2) * τ + ((x * N * γ 0 1 + y * γ 1 1 : ℤ) : ℂ) / (d : ℂ)) = σ • W := by
    rw [← hfinal, ofComplex_apply]
  rw [hNd]
  unfold jN
  rw [hWe, ← jFun_smul σ W]
  push_cast at this ⊢
  rw [this]

end NumberFieldKB.ModularCurves
