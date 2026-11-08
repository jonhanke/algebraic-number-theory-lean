import NumberFieldKB.GlobalZeta.EulerProduct
import NumberFieldKB.LocalZeta.Complex

/-!
# The archimedean zeta integral as a product over the infinite places

$F$ is a number field, $F_\infty = \mathbb R^{r_1}\times\mathbb C^{r_2}$ (`mixedSpace F`) with Tate's measure
$\omega_\infty = \prod_{w\text{ real}}dx/|x|\prod_{w\text{ complex}}2\,dx\,dy/|z|^2$ on $F_\infty^\times$ (QuadFormsKB's
`omegaInf`). The archimedean factor $Z_\infty(f,\chi,s)$ (`archZeta`) is defined as one integral over $F_\infty^\times$.

* **`integral_omegaInf`**: $\int_{F_\infty^\times}H\,d\omega_\infty = \int_{F_\infty}H(x)\,|N(x)|^{-1}\,dx$ (self-dual $dx$).
* **`archZeta_eq_prod`**: for a product test function $f(x) = \prod_{w\text{ real}}f_w(x_w)\prod_{w\text{ complex}}f_w(z_w)$
  and a character with $\chi(x) = \prod_w\chi_w(x_w)$ on $F_\infty^\times$,
  $Z_\infty(f,\chi,s) = \prod_wZ(f_w,\chi_w,s)$, the product of the local zeta integrals at the real places
  (`tateHaarR`) and at the complex places (`tateHaarC`).
* **`archZeta_gaussInf_one`**: for QuadFormsKB's self-dual Gaussian `gaussInf` and the trivial character,
  $Z_\infty = \Gamma_{\mathbb R}(s)^{r_1}(\pi\Gamma_{\mathbb C}(s))^{r_2}$ for $\operatorname{Re}s>0$.

Tate's thesis, Cassels–Fröhlich Ch. XV, §2.5 and §4.4 [unverified locators].
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

open GlobalZeta LocalZeta

/-! ### Coordinates of archimedean units -/

/-- The coordinate at a real place of a unit of $F_\infty$. -/
def unitR (u : Vˣ) (w : {w : InfinitePlace F // w.IsReal}) : ℝˣ :=
  Units.map ((Pi.evalRingHom (fun _ => ℝ) w).comp (RingHom.fst _ _)).toMonoidHom u

/-- The coordinate at a complex place of a unit of $F_\infty$. -/
def unitC (u : Vˣ) (w : {w : InfinitePlace F // w.IsComplex}) : ℂˣ :=
  Units.map ((Pi.evalRingHom (fun _ => ℂ) w).comp (RingHom.snd _ _)).toMonoidHom u

@[simp] theorem coe_unitR (u : Vˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    ((unitR u w : ℝˣ) : ℝ) = (u : V).1 w := rfl

@[simp] theorem coe_unitC (u : Vˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    ((unitC u w : ℂˣ) : ℂ) = (u : V).2 w := rfl

theorem isUnit_iff_forall_ne_zero (x : V) :
    IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ ∀ w, x.2 w ≠ 0 := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  simp only [isUnit_iff_ne_zero]

/-- $|\det(x\cdot)| = \prod_{w\text{ real}}|x_w|\prod_{w\text{ complex}}|x_w|^2$ on $F_\infty$. -/
theorem abs_det_mulLeft_eq_prod (x : V) :
    |LinearMap.det (LinearMap.mulLeft ℝ x)| = (∏ w, |x.1 w|) * ∏ w, ‖x.2 w‖ ^ 2 := by
  rw [det_mulLeft_mixedSpace, abs_mul, Finset.abs_prod, Finset.abs_prod]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

theorem ideleNorm_infEmb (u : Vˣ) :
    ideleNorm F (infEmb F u) = |LinearMap.det (LinearMap.mulLeft ℝ (u : V))| := by
  have h1 : infPart (infEmb F u) = u := Units.ext rfl
  have h2 : finPart (infEmb F u) = 1 := Units.ext rfl
  rw [ideleNorm, h1, h2]
  simp [modAt_one]

/-! ### Integration against $\omega_\infty$ -/

/-- **$\int_{F_\infty^\times}H\,d\omega_\infty = \int_{F_\infty}H(x)\,|\det(x\cdot)|^{-1}\,dx$** with the self-dual $dx$;
the integrand on the right vanishes off $F_\infty^\times$ ($0^{-1} = 0$). -/
theorem integral_omegaInf (H : V → ℂ) :
    ∫ u : Vˣ, H u ∂omegaInf F =
      ∫ x, H x * ((|LinearMap.det (LinearMap.mulLeft ℝ x)| : ℝ) : ℂ)⁻¹ ∂Analysis.selfDualInf (F := F) := by
  have hemb : MeasurableEmbedding (Units.val : Vˣ → V) :=
    isOpenEmbedding_val_mixedSpace.measurableEmbedding
  have hdens : Measurable fun u : Vˣ =>
      ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (u : V))|⁻¹ :=
    ((continuous_abs_det_mulLeft (F := F)).comp Units.continuous_val).measurable.inv.ennreal_ofReal
  rw [omegaInf_eq, integral_withDensity_eq_integral_toReal_smul hdens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  set k : V → ℂ := fun x => H x * ((|LinearMap.det (LinearMap.mulLeft ℝ x)| : ℝ) : ℂ)⁻¹ with hk
  have hpt : ∀ u : Vˣ, (ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (u : V))|⁻¹).toReal • H u =
      k u := by
    intro u
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), Complex.real_smul, hk]
    push_cast
    ring
  simp_rw [hpt]
  rw [← hemb.integral_map, hemb.map_comap]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ x) = 0 := by
    by_contra h
    have hu : IsUnit (LinearMap.mulLeft ℝ x) :=
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
    obtain ⟨y, hy⟩ := (Module.End.isUnit_iff _).mp hu |>.surjective 1
    exact hx ⟨(isUnit_iff_exists_inv.mpr ⟨y, hy⟩).unit, rfl⟩
  simp [hk, hdet]

/-! ### The product formula -/

section Product

variable (fr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ) (fc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ)
  (cr : {w : InfinitePlace F // w.IsReal} → ℝˣ →* ℂˣ) (cc : {w : InfinitePlace F // w.IsComplex} → ℂˣ →* ℂˣ)
  (s : ℂ)

/-- The integrand at a real place, extended by $0$ to $\mathbb R$. -/
def gr (w : {w : InfinitePlace F // w.IsReal}) (x : ℝ) : ℂ :=
  if h : x = 0 then 0 else fr w x * (cr w (Units.mk0 x h) : ℂ) * ((|x| : ℝ) : ℂ) ^ s

/-- The integrand at a complex place, extended by $0$ to $\mathbb C$. -/
def gc (w : {w : InfinitePlace F // w.IsComplex}) (z : ℂ) : ℂ :=
  if h : z = 0 then 0 else fc w z * (cc w (Units.mk0 z h) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s

theorem integral_gr_eq (w : {w : InfinitePlace F // w.IsReal}) :
    ∫ x, gr fr cr s w x * ((|x| : ℝ) : ℂ)⁻¹ = zetaIntegral tateHaarR (fr w) (cr w) s := by
  rw [← integral_unitsHaar_mul_modulus continuous_distribHaarChar_real volume]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hu : (u : ℝ) ≠ 0 := u.ne_zero
  have hu' : ((|(u : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hu
  simp only [gr, dif_neg hu, zetaIntegrand, distribHaarChar_real, Units.mk0_val]
  field_simp

theorem integral_gc_eq (w : {w : InfinitePlace F // w.IsComplex}) :
    2 * ∫ z, gc fc cc s w z * ((‖z‖ ^ 2 : ℝ) : ℂ)⁻¹ = zetaIntegral tateHaarC (fc w) (cc w) s := by
  have h2 : (2 : ℂ) * ∫ z, gc fc cc s w z * ((‖z‖ ^ 2 : ℝ) : ℂ)⁻¹ =
      ∫ z, gc fc cc s w z * ((‖z‖ ^ 2 : ℝ) : ℂ)⁻¹ ∂muC := by
    rw [muC, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    norm_num
  rw [h2, ← integral_unitsHaar_mul_modulus continuous_distribHaarChar_complex muC]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hu' : ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  simp only [gc, dif_neg hu, zetaIntegrand, distribHaarChar_complex, Units.mk0_val]
  field_simp

variable {fr fc cr cc}

/-- **The archimedean zeta integral is the product of the local zeta integrals** over the infinite places, for a
product test function $f(x) = \prod_wf_w(x_w)$ and a character $\chi = \prod_w\chi_w$ on $F_\infty^\times$:
$$Z_\infty(f,\chi,s) = \prod_{w\text{ real}}Z(f_w,\chi_w,s)\prod_{w\text{ complex}}Z(f_w,\chi_w,s),$$
with Tate's measures $dx/|x|$ and $2\,dx\,dy/|z|^2$ (`tateHaarR`, `tateHaarC`). No convergence hypothesis:
both sides are Bochner integrals (and are $0$ together when not integrable). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (ζ_∞(f_∞, c_∞) = ∏_{p|∞} ζ_p(f_p, c_p))"]
theorem archZeta_eq_prod (f : SchwartzMap V ℂ) (χ : HeckeCharacter F)
    (hf : ∀ x, f x = (∏ w, fr w (x.1 w)) * ∏ w, fc w (x.2 w))
    (hχ : ∀ u : Vˣ, (χ.onIdeles (infEmb F u) : ℂ) =
      (∏ w, (cr w (unitR u w) : ℂ)) * ∏ w, (cc w (unitC u w) : ℂ)) :
    archZeta f χ s =
      (∏ w, zetaIntegral tateHaarR (fr w) (cr w) s) * ∏ w, zetaIntegral tateHaarC (fc w) (cc w) s := by
  set H : V → ℂ := fun x => (∏ w, gr fr cr s w (x.1 w)) * ∏ w, gc fc cc s w (x.2 w) with hH
  -- the integrand on the units is `H`
  have hunit : ∀ u : Vˣ, f (u : V) * (χ.onIdeles (infEmb F u) : ℂ) * (ideleNorm F (infEmb F u) : ℂ) ^ s =
      H u := by
    intro u
    have hr : ∀ w, (u : V).1 w ≠ 0 := ((isUnit_iff_forall_ne_zero (u : V)).mp u.isUnit).1
    have hc : ∀ w, (u : V).2 w ≠ 0 := ((isUnit_iff_forall_ne_zero (u : V)).mp u.isUnit).2
    have hgr : ∀ w, gr fr cr s w ((u : V).1 w) =
        fr w ((u : V).1 w) * (cr w (unitR u w) : ℂ) * ((|(u : V).1 w| : ℝ) : ℂ) ^ s := fun w => by
      rw [gr, dif_neg (hr w), show Units.mk0 _ (hr w) = unitR u w from Units.ext rfl]
    have hgc : ∀ w, gc fc cc s w ((u : V).2 w) =
        fc w ((u : V).2 w) * (cc w (unitC u w) : ℂ) * ((‖(u : V).2 w‖ ^ 2 : ℝ) : ℂ) ^ s := fun w => by
      rw [gc, dif_neg (hc w), show Units.mk0 _ (hc w) = unitC u w from Units.ext rfl]
    rw [hH]
    simp only [hgr, hgc, Finset.prod_mul_distrib]
    rw [hf, hχ, ideleNorm_infEmb, abs_det_mulLeft_eq_prod, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun w _ => abs_nonneg _)
        (Finset.prod_nonneg fun w _ => sq_nonneg _),
      ofReal_prod_cpow _ _ (fun w => abs_nonneg _), ofReal_prod_cpow _ _ (fun w => sq_nonneg _)]
    ring
  -- the density
  have hdens : ∀ x : V, H x * ((|LinearMap.det (LinearMap.mulLeft ℝ x)| : ℝ) : ℂ)⁻¹ =
      (∏ w, gr fr cr s w (x.1 w) * ((|x.1 w| : ℝ) : ℂ)⁻¹) *
        ∏ w, gc fc cc s w (x.2 w) * ((‖x.2 w‖ ^ 2 : ℝ) : ℂ)⁻¹ := by
    intro x
    rw [abs_det_mulLeft_eq_prod, hH, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Complex.ofReal_mul,
      Complex.ofReal_prod, Complex.ofReal_prod, mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
    ring
  have h1 : archZeta f χ s = ∫ u : Vˣ, H u ∂omegaInf F :=
    integral_congr_ae (Eventually.of_forall hunit)
  rw [h1, integral_omegaInf]
  simp_rw [hdens]
  rw [Analysis.selfDualInf, integral_smul_nnreal_measure, Measure.volume_eq_prod,
    integral_prod_mul (fun a : {w : InfinitePlace F // w.IsReal} → ℝ =>
      ∏ w, gr fr cr s w (a w) * ((|a w| : ℝ) : ℂ)⁻¹)
      (fun b : {w : InfinitePlace F // w.IsComplex} → ℂ =>
      ∏ w, gc fc cc s w (b w) * ((‖b w‖ ^ 2 : ℝ) : ℂ)⁻¹), volume_pi, volume_pi,
    integral_fintype_prod_eq_prod (fun w (a : ℝ) => gr fr cr s w a * ((|a| : ℝ) : ℂ)⁻¹),
    integral_fintype_prod_eq_prod (fun w (b : ℂ) => gc fc cc s w b * ((‖b‖ ^ 2 : ℝ) : ℂ)⁻¹)]
  simp_rw [integral_gr_eq, ← integral_gc_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

end Product

/-! ### The Gaussian and the trivial character -/

theorem coe_gaussR_eq : (LocalZeta.gaussR : ℝ → ℂ) = Analysis.gaussR := by
  funext x
  rw [LocalZeta.gaussR_apply, Analysis.gaussR]
  push_cast
  ring_nf

theorem coe_gaussCS_eq : (LocalZeta.gaussCS : ℂ → ℂ) = Analysis.gaussC := by
  funext z
  rw [LocalZeta.gaussCS_apply, Analysis.gaussC]

/-- **The archimedean zeta integral of the self-dual Gaussian** (trivial character): for $\operatorname{Re}s>0$,
$$Z_\infty(\Phi_\infty,1,s) = \Gamma_{\mathbb R}(s)^{r_1}\,(\pi\,\Gamma_{\mathbb C}(s))^{r_2},$$
$\Phi_\infty(x) = \prod_{w\text{ real}}e^{-\pi x_w^2}\prod_{w\text{ complex}}e^{-2\pi|x_w|^2}$ (QuadFormsKB's `gaussInf`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 and §4.4 [unverified locator] (the archimedean factors of ζ_F)"]
theorem archZeta_gaussInf_one {s : ℂ} (hs : 0 < s.re) :
    archZeta (Analysis.gaussInf (F := F)) 1 s =
      Complex.Gammaℝ s ^ nrRealPlaces F * (Real.pi * Complex.Gammaℂ s) ^ nrComplexPlaces F := by
  rw [archZeta_eq_prod (fr := fun _ => Analysis.gaussR) (fc := fun _ => Analysis.gaussC) (cr := fun _ => 1)
    (cc := fun _ => 1) s _ _ (fun x => by rw [Analysis.gaussInf_apply]; rfl) (fun u => by simp)]
  simp only [← coe_gaussR_eq, ← coe_gaussCS_eq, zetaIntegral_gaussian_real hs, zetaIntegral_gaussian_complex hs,
    Finset.prod_const, Finset.card_univ]

end

end NumberFieldKB.HeckeL
