import NumberFieldKB.HeckeL.ArchFourier
import NumberFieldKB.HeckeL.LocalEpsilon
import NumberFieldKB.HeckeL.Completed

/-!
# The zeta integral of the Fourier transform of the standard test function

$F$ is a number field and $\chi$ a Hecke character with shift $\sigma$, standard test function
$\Phi_\chi = f_\infty^\chi\otimes\bigotimes_vf_v$ (`heckePhi`). For $\operatorname{Re}s>\sigma+1$,
$$Z(\hat\Phi_\chi,\chi^{-1},s) = i^{m(\chi)}\pi^{r_2}\,E(\chi)\,A(\chi)^s\,L_\infty(s,\chi^{-1})\,L(s,\chi^{-1})
\qquad(\texttt{globalZeta\_fourier\_heckePhi}),$$
with $m(\chi) = \sum_{w\text{ real}}e_w+\sum_{w\text{ complex}}|k_w|$ (`archExp`), $A(\chi) = |d_F|N(\mathfrak f_\chi)$, and
$E(\chi) = \prod_vE_v(\chi)$ a finite product of local constants (`dualConst`): $E_v = N(\mathfrak d_v)^{-1}\chi_v(\varpi_v)^{d_v}$
at an unramified place and Tate's integral $\varepsilon_v(\chi)$ (`epsLocal`) at a ramified place.

Ingredients: the infinity type of $\chi^{-1}$ (exponents negated, same signs, frequencies negated); the archimedean
Fourier transforms (`ArchFourier.lean`): $\hat f_\infty^\chi = i^{m(\chi)}f_\infty^{\chi^{-1}}$; the local computations at
the finite places (`LocalEpsilon.lean`).
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

open GlobalZeta LocalZeta

/-! ### The infinity type of $\chi^{-1}$ -/

theorem inv_realComponent (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) (x : ℝˣ) :
    (((χ⁻¹).realComponent hw x : ℂˣ) : ℂ) = ((χ.realComponent hw x : ℂˣ) : ℂ)⁻¹ := by
  show (((χ.realComponent hw x)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val]

theorem inv_complexComponent (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsComplex) (z : ℂˣ) :
    (((χ⁻¹).complexComponent hw z : ℂˣ) : ℂ) = ((χ.complexComponent hw z : ℂˣ) : ℂ)⁻¹ := by
  show (((χ.complexComponent hw z)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val]

theorem realExponent_inv (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) :
    (χ⁻¹).realExponent hw = -χ.realExponent hw := by
  refine (χ⁻¹).realExponent_unique hw fun x hx => ?_
  rw [inv_realComponent, χ.realComponent_apply hw, abs_of_pos hx, if_neg (not_lt.mpr hx.le), mul_one,
    Complex.cpow_neg]

theorem realSign_inv (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) :
    (χ⁻¹).realSign hw = χ.realSign hw := by
  unfold HeckeCharacter.realSign
  rw [inv_realComponent]
  rcases χ.realSign_eq hw with h | h <;> unfold HeckeCharacter.realSign at h <;> rw [h] <;> norm_num

theorem eW_inv (χ : HeckeCharacter F) (w : {w : InfinitePlace F // w.IsReal}) : eW χ⁻¹ w = eW χ w := by
  rw [eW, eW, realSign_inv]

theorem complexComponent_inv_eq (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsComplex) :
    (χ⁻¹).complexExponent hw = -χ.complexExponent hw ∧ (χ⁻¹).complexFrequency hw = -χ.complexFrequency hw := by
  refine (χ⁻¹).complexComponent_unique hw fun z => ?_
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hn : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [inv_complexComponent, χ.complexComponent_apply hw, mul_inv, Complex.cpow_neg, zpow_neg]

theorem kW_inv (χ : HeckeCharacter F) (w : {w : InfinitePlace F // w.IsComplex}) : kW χ⁻¹ w = -kW χ w :=
  (complexComponent_inv_eq χ w.2).2

/-- $m(\chi) = \sum_{w\text{ real}}e_w+\sum_{w\text{ complex}}|k_w|$: the archimedean root number is $i^{m(\chi)}$. -/
def archExp (χ : HeckeCharacter F) : ℕ :=
  (∑ w : {w : InfinitePlace F // w.IsReal}, eW χ w) + ∑ w : {w : InfinitePlace F // w.IsComplex}, (kW χ w).natAbs

theorem signExp_le_one (ε : ℂ) : signExp ε ≤ 1 := by
  unfold signExp; split_ifs <;> omega

/-! ### The archimedean dual integral -/

theorem zetaIntegral_const_mul {K : Type*} [NontriviallyNormedField K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (ν : Measure Kˣ) (c : ℂ) (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    zetaIntegral ν (fun x => c * f x) χ s = c * zetaIntegral ν f χ s := by
  rw [zetaIntegral, zetaIntegral, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [zetaIntegrand]
  ring

/-- $\hat f_\infty^\chi = i^{m(\chi)}f_\infty^{\chi^{-1}}$, as a product over the places. -/
theorem fourierInfSchwartz_archTest (χ : HeckeCharacter F) (y : V) :
    SchwartzBruhat.fourierInfSchwartz (archTest χ) y =
      (∏ w, Complex.I ^ eW χ w * fRe (eW χ⁻¹ w) (y.1 w)) *
        ∏ w, Complex.I ^ (kW χ w).natAbs * fCk (kW χ⁻¹ w) (y.2 w) := by
  rw [SchwartzBruhat.coe_fourierInfSchwartz]
  have h : (archTest χ : V → ℂ) = fun x => (∏ w, fRe (eW χ w) (x.1 w)) * ∏ w, fCk (kW χ w) (x.2 w) :=
    funext (archTest_apply χ)
  rw [h, QuadFormsKB.Analysis.fourierInf_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [fourierR_fRe (e := eW χ w) (signExp_le_one _), eW_inv]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [fourierC_fCk, kW_inv]

/-- **The archimedean dual integral**: $Z_\infty(\hat f_\infty^\chi,\chi^{-1},s) = i^{m(\chi)}\pi^{r_2}L_\infty(s,\chi^{-1})$ for
$\operatorname{Re}s>\sigma$. -/
theorem archZeta_fourier_archTest (χ : HeckeCharacter F) {s : ℂ} (hs : 0 < s.re - χ.shift) :
    archZeta (SchwartzBruhat.fourierInfSchwartz (archTest χ)) χ⁻¹ s =
      Complex.I ^ archExp χ * (Real.pi : ℂ) ^ nrComplexPlaces F * gammaInf χ⁻¹ s := by
  have hs' : 0 < s.re + (χ⁻¹).shift := by rw [shift_inv]; linarith
  rw [archZeta_eq_prod (fr := fun w y => Complex.I ^ eW χ w * fRe (eW χ⁻¹ w) y)
    (fc := fun w z => Complex.I ^ (kW χ w).natAbs * fCk (kW χ⁻¹ w) z)
    (cr := fun w => ((χ⁻¹).realComponent w.2 : ℝˣ →* ℂˣ))
    (cc := fun w => ((χ⁻¹).complexComponent w.2 : ℂˣ →* ℂˣ)) s _ χ⁻¹
    (fourierInfSchwartz_archTest χ) (fun u => by rw [onIdeles_infEmb]; rfl)]
  simp only [zetaIntegral_const_mul]
  have hr : ∀ w : {w : InfinitePlace F // w.IsReal},
      zetaIntegral tateHaarR (fRe (eW χ⁻¹ w)) ((χ⁻¹).realComponent w.2 : ℝˣ →* ℂˣ) s =
        Complex.Gammaℝ (s + (χ⁻¹).realExponent w.2 + eW χ⁻¹ w) := fun w =>
    zetaIntegral_real_infType _ ((χ⁻¹).realComponent_apply w.2) ((χ⁻¹).realSign_eq w.2) (by
      have := (χ⁻¹).re_realExponent w.2
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (signExp ((χ⁻¹).realSign w.2) : ℝ) := Nat.cast_nonneg _
      linarith)
  have hc : ∀ w : {w : InfinitePlace F // w.IsComplex},
      zetaIntegral tateHaarC (fCk (kW χ⁻¹ w)) ((χ⁻¹).complexComponent w.2 : ℂˣ →* ℂˣ) s =
        Real.pi * Complex.Gammaℂ (s + (χ⁻¹).complexExponent w.2 / 2 + (kW χ⁻¹ w).natAbs / 2) := fun w =>
    zetaIntegral_complex_infType _ ((χ⁻¹).complexComponent_apply w.2) (by
      have := (χ⁻¹).re_complexExponent w.2
      simp only [Complex.add_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
      norm_num
      have : (0 : ℝ) ≤ |(((χ⁻¹).complexFrequency w.2 : ℤ) : ℝ)| := abs_nonneg _
      linarith)
  simp only [hr, hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, gammaInf, archExp, pow_add,
    Finset.prod_pow_eq_pow_sum]
  ring

/-! ### The finite places -/

theorem ramSet_inv (χ : HeckeCharacter F) : ramSet χ⁻¹ = ramSet χ := by
  ext v; simp [mem_ramSet, isUnramifiedAt_inv_iff]

theorem constSet_inv (χ : HeckeCharacter F) : constSet χ⁻¹ = constSet χ := by
  rw [constSet, constSet, ramSet_inv]

theorem conductor_inv (χ : HeckeCharacter F) : (χ⁻¹).conductor = χ.conductor := by
  simp only [HeckeCharacter.conductor, conductorExponent_inv]

theorem condDisc_inv (χ : HeckeCharacter F) : condDisc χ⁻¹ = condDisc χ := by
  rw [condDisc, condDisc, condNorm, condNorm, conductor_inv]

/-- $N(\mathfrak f_\chi) = \prod_{v\text{ ramified}}N(v)^{a_v}$. -/
theorem condNorm_eq_prod (χ : HeckeCharacter F) :
    condNorm χ = ∏ v ∈ ramSet χ, normV v ^ χ.conductorExponent v := by
  rw [condNorm, HeckeCharacter.conductor, finprod_eq_prod_of_mulSupport_subset (s := ramSet χ) _ (fun v hv => by
    rw [Finset.mem_coe, mem_ramSet]
    intro h
    apply hv
    simp [(χ.conductorExponent_eq_zero_iff v).mpr h]), map_prod]
  push_cast
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_pow]
  push_cast
  rfl

theorem conductorExponent_eq_zero_of_notMem {χ : HeckeCharacter F} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ ramSet χ) : χ.conductorExponent v = 0 :=
  (χ.conductorExponent_eq_zero_iff v).mpr (by simpa [mem_ramSet] using hv)

/-- **$A(\chi) = \prod_vN(v)^{a_v+d_v}$** over the places of `constSet χ`. -/
theorem condDisc_eq_prod (χ : HeckeCharacter F) :
    condDisc χ = ∏ v ∈ constSet χ, normV v ^ (χ.conductorExponent v + Analysis.diffExp v) := by
  have hc : constSet χ = ramSet χ ∪ diffSet F := rfl
  rw [condDisc, condNorm_eq_prod, ← prod_normV_pow_diffExp, hc]
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib, mul_comm]
  congr 1
  · exact Finset.prod_subset (Finset.subset_union_left (s₁ := ramSet χ) (s₂ := diffSet F)) fun v _ hv => by
      rw [conductorExponent_eq_zero_of_notMem hv, pow_zero]
  · exact Finset.prod_subset (Finset.subset_union_right (s₁ := ramSet χ) (s₂ := diffSet F)) fun v _ hv => by
      rw [diffExp_eq_zero hv, pow_zero]

/-- The local constant $E_v(\chi)$: $N(\mathfrak d_v)^{-1}\chi_v(\varpi_v)^{d_v}$ (unramified; the product of
$\operatorname{vol}(\mathcal O_v)$ and the constant $c_v(\chi^{-1}) = \operatorname{vol}(\mathcal O_v)$) or $\varepsilon_v(\chi)$ (ramified). -/
def dualConstLocal (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if χ.IsUnramifiedAt v then
    ((volO v).toReal : ℂ) * (χ.finiteComponent v (Analysis.ϖU v) : ℂ) ^ Analysis.diffExp v * stdConstFactor χ⁻¹ v
  else epsLocal χ v

/-- **$E(\chi) = \prod_vE_v(\chi)$**, a finite product. -/
def dualConst (χ : HeckeCharacter F) : ℂ := ∏ v ∈ constSet χ, dualConstLocal χ v

theorem zetaIntegral_fourierV_stdFv (χ : HeckeCharacter F) {s : ℂ} (hs : 0 < -χ.shift + s.re)
    (v : HeightOneSpectrum (𝓞 F)) :
    zetaIntegral (tateHaarV v) (Analysis.fourierV v (stdFv χ v)) ((χ⁻¹).finiteComponent v).toMonoidHom s =
      dualConstLocal χ v * (((normV v ^ (χ.conductorExponent v + Analysis.diffExp v) : ℝ)) : ℂ) ^ s *
        localL χ⁻¹ s v := by
  unfold stdFv dualConstLocal
  split_ifs with h
  · rw [zetaIntegral_fourierV_charO_inv χ h hs, (χ.conductorExponent_eq_zero_iff v).mpr h, zero_add,
      mul_pow, ofReal_pow_cpow (normV_pos v).le]
    ring
  · have h' : ¬ (χ⁻¹).IsUnramifiedAt v := by rwa [isUnramifiedAt_inv_iff]
    rw [zetaIntegral_fourierV_ram χ h hs, localL, if_neg h', mul_one, mul_comm]

theorem dualConstLocal_eq_one {χ : HeckeCharacter F} {v : HeightOneSpectrum (𝓞 F)} {s : ℂ} (hv : v ∉ constSet χ) :
    dualConstLocal χ v * (((normV v ^ (χ.conductorExponent v + Analysis.diffExp v) : ℝ)) : ℂ) ^ (s : ℂ) = 1 := by
  have hv' := hv
  rw [← constSet_inv] at hv'
  simp only [constSet, Finset.mem_union, mem_ramSet, not_or, not_not] at hv
  have hd := diffExp_eq_zero (F := F) (v := v) (by simpa [diffSet] using hv.2)
  have h1 := stdConstFactor_eq_one hv'
  rw [dualConstLocal, if_pos hv.1, h1, hd, volO_toReal, hd, (χ.conductorExponent_eq_zero_iff v).mpr hv.1]
  simp

/-- **The Euler product of the dual zeta integral**: for $\operatorname{Re}s>\sigma+1$,
$$Z(\hat\Phi_\chi,\chi^{-1},s) = i^{m(\chi)}\pi^{r_2}E(\chi)A(\chi)^s\,L_\infty(s,\chi^{-1})\,L(s,\chi^{-1}).$$ -/
theorem globalZeta_fourier_heckePhi (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re - χ.shift) :
    globalZeta (heckePhi χ).fourier χ⁻¹ s =
      Complex.I ^ archExp χ * (Real.pi : ℂ) ^ nrComplexPlaces F * dualConst χ *
        ((condDisc χ : ℝ) : ℂ) ^ s * gammaInf χ⁻¹ s * heckeL χ⁻¹ s := by
  have hs' : 1 < s.re + (χ⁻¹).shift := by rw [shift_inv]; linarith
  rw [← coe_fourierSB, globalZeta_eq_archZeta_mul_finZeta]
  have harch : archZeta ((heckePhi χ).fourierSB).fInf χ⁻¹ s =
      Complex.I ^ archExp χ * (Real.pi : ℂ) ^ nrComplexPlaces F * gammaInf χ⁻¹ s :=
    archZeta_fourier_archTest χ (by linarith)
  have h1 := hasProd_finZeta (heckePhi χ).fourierSB χ⁻¹ hs'
  have h2 : HasProd (fun v => dualConstLocal χ v *
      (((normV v ^ (χ.conductorExponent v + Analysis.diffExp v) : ℝ)) : ℂ) ^ s)
      (dualConst χ * ((condDisc χ : ℝ) : ℂ) ^ s) := by
    rw [dualConst, condDisc_eq_prod, ofReal_prod_cpow _ _ (fun v => (pow_pos (normV_pos v) _).le),
      ← Finset.prod_mul_distrib]
    exact hasProd_prod_of_ne_finset_one fun v hv => dualConstLocal_eq_one hv
  have h3 := h2.mul (hasProd_heckeL χ⁻¹ hs')
  have heq : finZeta ((heckePhi χ).fourierSB).fv χ⁻¹ s = dualConst χ * ((condDisc χ : ℝ) : ℂ) ^ s *
      heckeL χ⁻¹ s := by
    refine h1.unique ?_
    convert h3 using 1
    funext v
    exact zetaIntegral_fourierV_stdFv χ (by linarith) v
  rw [harch, heq]
  ring

end

end NumberFieldKB.HeckeL
