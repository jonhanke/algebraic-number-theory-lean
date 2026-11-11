import NumberFieldKB.ModularCurves.ComplexCuspCriterion
import NumberFieldKB.ModularCurves.JLocal
import NumberFieldKB.MilneEC.Ch5LevelOne
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The Laurent expansion of $j'(N\tau)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 3.3 (pdf p. 199). By Ramanujan's formulas
(`deriv_jFun`), $j' = -2\pi i\, E_4^2 E_6 / \Delta$, so $\tau \mapsto j'(N\tau)$ has the Laurent expansion
`jDerSer N` $= -2\pi i\, \widehat{E_4^2E_6}(q^N)/\hat\Delta(q^N)$ (`deriv_jFun_mul_eq`), with a pole of order $N$
(`valuation_jDerSer`): the series $D$ of `ComplexCuspCriterion.lean`.
-/

open UpperHalfPlane hiding I
open Polynomial Complex ModularForm TauCeti
open scoped WithZero Real

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

local notation "Δ" => ModularForm.discriminant

/-- $E_4^2 E_6$. -/
noncomputable abbrev derNum : ℍ → ℂ := (E₄ : ℍ → ℂ) ^ 2 * (E₆ : ℍ → ℂ)

theorem isQExp_derNum : IsQExp derNum :=
  ((IsQExp.of_modularForm E₄).pow 2).mul (IsQExp.of_modularForm E₆)

theorem coeff_qExpansion_derNum_zero : PowerSeries.coeff 0 (qExpansion 1 derNum) = 1 := by
  have h4 := IsQExp.of_modularForm E₄
  have h6 := IsQExp.of_modularForm E₆
  have e : qExpansion 1 derNum = qExpansion 1 (E₄ : ℍ → ℂ) ^ 2 * qExpansion 1 (E₆ : ℍ → ℂ) := by
    rw [derNum, (h4.pow 2).qExpansion_mul h6, pow_two, h4.qExpansion_mul h4, pow_two]
  rw [e, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
    E4_coeff, E6_coeff]
  simp

theorem valuation_qHat_scaleN_derNum {N : ℕ} (hN : 1 ≤ N) : Valued.v (qHat (scaleN N derNum)) = 1 := by
  have h0 : PowerSeries.coeff 0 (qExpansion 1 (scaleN N derNum)) ≠ 0 := by
    rw [qExpansion_scaleN_coeff hN isQExp_derNum]
    simp only [dilateCoeff, dvd_zero, ite_true, Nat.zero_div]
    rw [coeff_qExpansion_derNum_zero]
    exact one_ne_zero
  rw [qHat, valuation_ofPowerSeries h0 (fun i hi => absurd hi (Nat.not_lt_zero i))]
  rfl

/-- $j' = -2\pi i\, E_4^2 E_6 / \Delta$. -/
theorem deriv_jFun_eq (τ : ℍ) :
    deriv (jFun ∘ ofComplex) τ = -(2 * π * I) * derNum τ / discFun τ := by
  rw [deriv_jFun, discFun, discriminant_eq_E₄_cube_sub_E₆_sq]
  simp only [derNum, Pi.mul_apply, Pi.pow_apply]
  have hB : (E₄ τ ^ 3 - E₆ τ ^ 2 : ℂ) ≠ 0 := E4_cube_sub_E6_sq_ne_zero τ
  field_simp

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
/-- $j'(N\tau) = -2\pi i\, E_4^2E_6(N\tau)/\Delta(N\tau)$. -/
theorem deriv_jFun_mul_eq (τ : ℍ) :
    deriv (jFun ∘ ofComplex) (ofComplex ((N : ℂ) * τ) : ℂ) =
      -(2 * π * I) * scaleN N derNum τ / scaleN N discFun τ := by
  rw [deriv_jFun_eq]
  rfl

/-- **The Laurent expansion of $j'(N\tau)$**: $-2\pi i\, \widehat{E_4^2E_6}(q^N)/\hat\Delta(q^N)$. -/
def jDerSer : CuspField N :=
  (HahnSeries.C (-(2 * π * I)) * qHat (scaleN N derNum) / qHat (scaleN N discFun) : LaurentSeries ℂ)

/-- **$j'(N\tau)$ has a pole of order $N$ at $i\infty$.** -/
theorem valuation_jDerSer : lVal N (jDerSer N) = WithZero.exp (N : ℤ) := by
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  change Valued.v (HahnSeries.C (-(2 * π * I)) * qHat (scaleN N derNum) / qHat (scaleN N discFun) :
    LaurentSeries ℂ) = _
  rw [map_div₀, map_mul, valuation_C (neg_ne_zero.2 h2), valuation_qHat_scaleN_derNum (one_le_N N),
    valuation_qHat_scaleN_discFun (one_le_N N), one_mul, one_div, ← WithZero.exp_neg, neg_neg]

/-- **The cusp part of $L(W)$** with $D$ the expansion of $j'(N\tau)$. -/
theorem forall_infty_iff_jDerSer {h : X0C N} (hh : h ≠ 0) :
    (∀ P' : Place ℂ (X0C N), P'.restrict ℂ (RatFunc ℂ) = Place.infty ℂ → -(canonicalW N).coeff P' ≤ P'.ord h) ↔
    ∀ c : Cosets N, lVal N (cuspEmbC N c h * jDerSer N) ≤ WithZero.exp (-1 : ℤ) :=
  forall_infty_iff N (valuation_jDerSer N) hh

end NumberFieldKB.ModularCurves
