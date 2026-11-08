import NumberFieldKB.HeckeL.LocalGammaIdentities

/-!
# Local root numbers and a local proof that the root number has absolute value one

Tate's thesis decomposes the root number of a Hecke character $\chi$ of a number field $F$ into a product of
local root numbers, one for each finite place at which something happens (the places where $\chi$ is ramified
or the different is nontrivial), times the power of $i$ coming from the infinite places:
$$W(\chi) = i^{m(\chi)}\prod_{v}W_v(\chi)\qquad(\texttt{rootNumber\_eq\_prod}).$$
At a place where $\chi$ is unramified the local root number is $\chi_v(\varpi_v)^{d_v}$
(`localRootNumber_of_unramified`); at a ramified place it is Tate's integral $\varepsilon_v(\chi)$ rescaled
(`localRootNumber_of_ramified`). For a unitary character every local root number has absolute value one
(`norm_localRootNumber`), which gives a purely local proof that $|W(\chi)| = 1$
(`norm_rootNumber_eq_one_local`), in contrast to the global argument used earlier.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Set WithZero
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-- **The local root number** $W_v(\chi) = E_v(\chi)\,N(v)^{(a_v+d_v)/2}/C_v(\chi)$ at a finite place $v$, where
$E_v$ is the local dual constant, $a_v$ the conductor exponent, $d_v$ the different exponent and $C_v$ the local
standard constant. -/
def localRootNumber (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  dualConstLocal χ v * (((normV v ^ (χ.conductorExponent v + Analysis.diffExp v) : ℝ)) : ℂ) ^ (1 / 2 : ℂ) /
    (stdConstFactor χ v : ℂ)

/-- **Tate's decomposition of the root number**: $W(\chi) = i^{m(\chi)}\prod_{v\in S}W_v(\chi)$, the product over
the finite set of places where $\chi$ is ramified or the different is nontrivial. -/
theorem rootNumber_eq_prod (χ : HeckeCharacter F) :
    rootNumber χ = Complex.I ^ archExp χ * ∏ v ∈ constSet χ, localRootNumber χ v := by
  rw [rootNumber, dualConst, condDisc_eq_prod, ofReal_prod_cpow _ _ (fun v => (pow_pos (normV_pos v) _).le),
    stdConst, Complex.ofReal_prod]
  simp only [localRootNumber, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  ring

/-- **The local root number at an unramified place** is $W_v(\chi) = \chi_v(\varpi_v)^{d_v}$. -/
theorem localRootNumber_of_unramified (χ : HeckeCharacter F) {v : HeightOneSpectrum (𝓞 F)}
    (h : χ.IsUnramifiedAt v) :
    localRootNumber χ v = (χ.finiteComponent v (Analysis.ϖU v) : ℂ) ^ Analysis.diffExp v := by
  have h' : (χ⁻¹).IsUnramifiedAt v := by rwa [isUnramifiedAt_inv_iff]
  have ha : χ.conductorExponent v = 0 := (χ.conductorExponent_eq_zero_iff v).mpr h
  have hS1 : stdConstFactor χ v = (volO v).toReal := by rw [stdConstFactor, if_pos h]
  have hS2 : stdConstFactor χ⁻¹ v = (volO v).toReal := by rw [stdConstFactor, if_pos h']
  have hN : 0 < normV v ^ Analysis.diffExp v := pow_pos (normV_pos v) _
  have hvol : (volO v).toReal = (normV v ^ Analysis.diffExp v) ^ (-(1 : ℝ) / 2) := volO_toReal v
  have hvpos : 0 < (volO v).toReal := by
    rw [hvol]; exact Real.rpow_pos_of_pos hN _
  have key : (((normV v ^ Analysis.diffExp v : ℝ)) : ℂ) ^ (1 / 2 : ℂ) * ((volO v).toReal : ℂ) = 1 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hN.le, hvol,
      ← Complex.ofReal_mul, ← Real.rpow_add hN]
    norm_num
  unfold localRootNumber dualConstLocal
  rw [if_pos h, hS1, hS2, ha, zero_add]
  have hne : ((volO v).toReal : ℂ) ≠ 0 := by exact_mod_cast hvpos.ne'
  rw [div_eq_iff hne]
  linear_combination ((χ.finiteComponent v (Analysis.ϖU v) : ℂ) ^ Analysis.diffExp v * ((volO v).toReal : ℂ)) * key

/-- **The local root number at a ramified place** is Tate's integral $\varepsilon_v(\chi)$ times
$N(v)^{(a_v+d_v)/2}/\operatorname{vol}^\times(U_v^{(a_v)})$. -/
theorem localRootNumber_of_ramified (χ : HeckeCharacter F) {v : HeightOneSpectrum (𝓞 F)}
    (h : ¬ χ.IsUnramifiedAt v) :
    localRootNumber χ v = epsLocal χ v * (((normV v ^ (χ.conductorExponent v + Analysis.diffExp v) : ℝ)) : ℂ) ^
      (1 / 2 : ℂ) / ((tateHaarV v (unitFiltration v (χ.conductorExponent v))).toReal : ℂ) := by
  simp only [localRootNumber, dualConstLocal, stdConstFactor, if_neg h]

/-- **Every local root number of a unitary character has absolute value one**: $|W_v(\chi)| = 1$. -/
theorem norm_localRootNumber {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (v : HeightOneSpectrum (𝓞 F)) :
    ‖localRootNumber χ v‖ = 1 := by
  have hσ : χ.shift = 0 := (χ.shift_eq_zero_iff).mpr hχ
  by_cases h : χ.IsUnramifiedAt v
  · rw [localRootNumber_of_unramified χ h, norm_pow]
    have hn : ‖((χ.finiteComponent v (Analysis.ϖU v) : ℂˣ) : ℂ)‖ = 1 := by
      rw [HeckeCharacter.norm_finiteComponent_eq_rpow, hσ, Real.rpow_zero]
    rw [hn, one_pow]
  · have hpos : 0 < (tateHaarV v (unitFiltration v (χ.conductorExponent v))).toReal :=
      ENNReal.toReal_pos (tateHaarV_unitFiltration_pos v (conductorExponent_pos h)).ne'
        (tateHaarV_unitFiltration_lt_top v _).ne
    have hN : 0 < normV v ^ (χ.conductorExponent v + Analysis.diffExp v) := pow_pos (normV_pos v) _
    rw [localRootNumber_of_ramified χ h, norm_div, norm_mul, norm_epsLocal v χ hχ h,
      Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
    have hre : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [hre]
    have h1 : (normV v ^ (χ.conductorExponent v + Analysis.diffExp v)) ^ (-(1 / 2 : ℝ)) *
        (normV v ^ (χ.conductorExponent v + Analysis.diffExp v)) ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hN]; norm_num
    field_simp
    linear_combination h1

/-- **A local proof that $|W(\chi)| = 1$** for a unitary Hecke character, from Tate's local decomposition
(`rootNumber_eq_prod`) and the local bounds (`norm_localRootNumber`). -/
theorem norm_rootNumber_eq_one_local {χ : HeckeCharacter F} (hχ : χ.IsUnitary) : ‖rootNumber χ‖ = 1 := by
  rw [rootNumber_eq_prod, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, norm_prod,
    Finset.prod_eq_one fun v _ => norm_localRootNumber hχ v]

end

end NumberFieldKB.HeckeL
