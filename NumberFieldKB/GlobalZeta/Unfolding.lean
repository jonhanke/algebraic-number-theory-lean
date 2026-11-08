import NumberFieldKB.GlobalZeta.Basic
import NumberFieldKB.GlobalZeta.QFPort

/-!
# Unfolding integrals over the ideles

$F$ is a number field, $\mu$ = `tamIdeles F` Tate's measure on $\mathbb A_F^\times$, $\mu^1$ = `muIdeleOne F` the Haar
measure on $\mathbb A_F^1$ with $\mu = \mu^1\times dt/t$ (QuadFormsKB's `map_ideleSplit_tamIdeles`), and $D$ =
`ideleClassFD F` QuadFormsKB's fixed fundamental domain of $F^\times$ in $\mathbb A_F^1$.

* **`sec u`** $= s(e^u)$, the section of the norm with $\|s(e^u)\| = e^u$ (`ideleNorm_sec`): the idele with every
  archimedean component $e^{u/n}$, $n = [F:\mathbb Q]$, and every finite component $1$.
* **`lintegral_tamIdeles_unfold`**, **`integral_tamIdeles_unfold`** (Tate's unfolding, the step behind §4.4 of the
  thesis): for $h\ge0$ measurable, or $h$ integrable,
  $$\int_{\mathbb A_F^\times}h\,d\mu = \int_{\mathbb R}\int_D\sum_{\xi\in F^\times}h(\xi\,a\,s(e^u))\,d\mu^1(a)\,du.$$
* **`setIntegral_fd_inv`**, **`setIntegral_fd_mul_left`**: for $F^\times$-invariant $k$ on $\mathbb A_F^1$,
  $\int_Dk(a^{-1})\,d\mu^1 = \int_Dk\,d\mu^1$ and $\int_Dk(ba)\,d\mu^1 = \int_Dk\,d\mu^1$ ($b\in\mathbb A_F^1$).
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal

namespace NumberFieldKB.GlobalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### The section of the norm -/

variable (F) in
/-- **The section** $u\mapsto s(e^u)$ of the idele norm: archimedean components $e^{u/n}$, finite components $1$. -/
def sec (u : ℝ) : (Adeles F)ˣ := normSectionHom F (Multiplicative.ofAdd u)

theorem ideleNorm_sec (u : ℝ) : ideleNorm F (sec F u) = Real.exp u :=
  QFPort.ideleNorm_normSectionHom _

theorem sec_add (u w : ℝ) : sec F (u + w) = sec F u * sec F w := by
  rw [sec, ofAdd_add, map_mul]; rfl

theorem sec_neg (u : ℝ) : sec F (-u) = (sec F u)⁻¹ := by
  rw [sec, ofAdd_neg, map_inv]; rfl

theorem sec_zero : sec F 0 = 1 := by
  rw [sec, ofAdd_zero, map_one]

theorem continuous_sec : Continuous (sec F) := continuous_normSectionHom.comp continuous_ofAdd

theorem finPart_sec (u : ℝ) : finPart (sec F u) = 1 := Units.ext rfl

/-! ### $F^\times$ acting on $\mathbb A_F^1$ -/

theorem coe_diagUnitsOneEquiv_smul (ξ : Fˣ) (a : ideleOne F) :
    ((QFPort.diagUnitsOneEquiv ξ • a : ideleOne F) : (Adeles F)ˣ) = diagUnits F ξ * a := rfl

instance : (muIdeleOne F).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-! ### Splitting and unfolding -/

/-- **$\int_{\mathbb A_F^\times}h\,d\mu = \int_{\mathbb R}\int_{\mathbb A_F^1}h(a\,s(e^u))\,d\mu^1(a)\,du$** for measurable $h\ge0$. -/
theorem lintegral_tamIdeles_split (h : (Adeles F)ˣ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ g, h g ∂tamIdeles F = ∫⁻ u : ℝ, ∫⁻ a, h ((a : (Adeles F)ˣ) * sec F u) ∂muIdeleOne F := by
  have he : ((ideleSplit F) : (Adeles F)ˣ → ideleOne F × Multiplicative ℝ) =
      (ideleSplit F).toHomeomorph.toMeasurableEquiv := rfl
  have hmeas : Measurable fun p : ideleOne F × Multiplicative ℝ => h ((ideleSplit F).symm p) :=
    hh.comp (ideleSplit F).symm.continuous.measurable
  have h1 : ∫⁻ g, h g ∂tamIdeles F =
      ∫⁻ p, h ((ideleSplit F).symm p) ∂(tamIdeles F).map (ideleSplit F) := by
    rw [he, lintegral_map_equiv]
    refine lintegral_congr fun g => ?_
    change h g = h ((ideleSplit F).symm (ideleSplit F g))
    rw [(ideleSplit F).symm_apply_apply]
  rw [h1, map_ideleSplit_tamIdeles, lintegral_prod_symm _ hmeas.aemeasurable,
    show (dtt : Measure (Multiplicative ℝ)) = Measure.map ofAddMeasurableEquiv volume from rfl,
    lintegral_map_equiv]
  rfl

/-- Unfolding over $F^\times$ on $\mathbb A_F^1$: $\int_{\mathbb A_F^1}k\,d\mu^1 = \int_D\sum_{\xi\in F^\times}k(\xi a)\,d\mu^1$. -/
theorem lintegral_ideleOne_unfold (k : ideleOne F → ℝ≥0∞) (hk : Measurable k) :
    ∫⁻ a, k a ∂muIdeleOne F =
      ∫⁻ a in ideleClassFD F, ∑' ξ : Fˣ, k (QFPort.diagUnitsOneEquiv ξ • a) ∂muIdeleOne F := by
  rw [isFundamentalDomain_ideleClassFD.lintegral_eq_tsum'',
    ← lintegral_tsum (f := fun γ a => k (γ • a)) fun γ => (hk.comp (measurable_const_smul γ)).aemeasurable]
  refine lintegral_congr fun a => ?_
  exact (QFPort.diagUnitsOneEquiv.tsum_eq (fun γ => k (γ • a))).symm

/-- **Tate's unfolding** for measurable $h\ge0$:
$\int_{\mathbb A_F^\times}h\,d\mu = \int_{\mathbb R}\int_D\sum_{\xi\in F^\times}h(\xi\,a\,s(e^u))\,d\mu^1(a)\,du$. -/
theorem lintegral_tamIdeles_unfold (h : (Adeles F)ˣ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ g, h g ∂tamIdeles F = ∫⁻ u : ℝ, ∫⁻ a in ideleClassFD F,
      ∑' ξ : Fˣ, h (diagUnits F ξ * ((a : (Adeles F)ˣ) * sec F u)) ∂muIdeleOne F := by
  rw [lintegral_tamIdeles_split h hh]
  refine lintegral_congr fun u => ?_
  refine (lintegral_ideleOne_unfold (fun a : ideleOne F => h ((a : (Adeles F)ˣ) * sec F u))
    (hh.comp ((continuous_subtype_val.mul continuous_const).measurable))).trans ?_
  refine lintegral_congr fun a => tsum_congr fun ξ => ?_
  rw [coe_diagUnitsOneEquiv_smul, mul_assoc]

/-- Unfolding over $F^\times$ on $\mathbb A_F^1$ for an integrable function. -/
theorem integral_ideleOne_unfold (k : ideleOne F → ℂ) (hk : Integrable k (muIdeleOne F)) :
    ∫ a, k a ∂muIdeleOne F =
      ∫ a in ideleClassFD F, ∑' ξ : Fˣ, k (QFPort.diagUnitsOneEquiv ξ • a) ∂muIdeleOne F := by
  have hD := isFundamentalDomain_ideleClassFD (F := F)
  rw [hD.integral_eq_tsum'' k hk]
  have hmeas : ∀ γ : diagUnitsOne F, AEStronglyMeasurable (fun a => k (γ • a))
      ((muIdeleOne F).restrict (ideleClassFD F)) := fun γ =>
    (hk.1.comp_quasiMeasurePreserving (measurePreserving_smul γ (muIdeleOne F)).quasiMeasurePreserving).restrict
  have hfin : ∑' γ : diagUnitsOne F, ∫⁻ a in ideleClassFD F, ‖k (γ • a)‖ₑ ∂muIdeleOne F ≠ ⊤ := by
    rw [← hD.lintegral_eq_tsum'' fun a => ‖k a‖ₑ]
    exact hk.2.ne
  rw [← integral_tsum hmeas hfin]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  exact (QFPort.diagUnitsOneEquiv.tsum_eq (fun γ => k (γ • a))).symm

/-- **Tate's unfolding** for an integrable function $h$ on $\mathbb A_F^\times$:
$\int_{\mathbb A_F^\times}h\,d\mu = \int_{\mathbb R}\int_D\sum_{\xi\in F^\times}h(\xi\,a\,s(e^u))\,d\mu^1(a)\,du$. -/
theorem integral_tamIdeles_unfold (h : (Adeles F)ˣ → ℂ) (hh : Integrable h (tamIdeles F)) :
    ∫ g, h g ∂tamIdeles F = ∫ u : ℝ, ∫ a in ideleClassFD F,
      ∑' ξ : Fˣ, h (diagUnits F ξ * ((a : (Adeles F)ˣ) * sec F u)) ∂muIdeleOne F := by
  set e := (ideleSplit F).toHomeomorph.toMeasurableEquiv
  have he : ((ideleSplit F) : (Adeles F)ˣ → ideleOne F × Multiplicative ℝ) = e := rfl
  set H : ideleOne F × Multiplicative ℝ → ℂ := fun p => h ((ideleSplit F).symm p)
  have hHe : H ∘ e = h := funext fun g => by
    change h ((ideleSplit F).symm (ideleSplit F g)) = h g
    rw [(ideleSplit F).symm_apply_apply]
  have hH : Integrable H ((muIdeleOne F).prod dtt) := by
    rw [← map_ideleSplit_tamIdeles, he, integrable_map_equiv, hHe]
    exact hh
  have h1 : ∫ g, h g ∂tamIdeles F = ∫ p, H p ∂(muIdeleOne F).prod dtt := by
    rw [← map_ideleSplit_tamIdeles, he, integral_map_equiv]
    exact congrArg (fun φ => ∫ g, φ g ∂tamIdeles F) hHe.symm
  rw [h1, integral_prod_symm H hH,
    show (dtt : Measure (Multiplicative ℝ)) = Measure.map ofAddMeasurableEquiv volume from rfl,
    integral_map_equiv]
  have hae : ∀ᵐ t ∂(Measure.map ofAddMeasurableEquiv volume : Measure (Multiplicative ℝ)),
      Integrable (fun a => H (a, t)) (muIdeleOne F) := hH.prod_left_ae
  replace hae := ofAddMeasurableEquiv.measurableEmbedding.ae_map_iff.mp hae
  refine integral_congr_ae (hae.mono fun u hu => ?_)
  change ∫ a, H (a, ofAddMeasurableEquiv u) ∂muIdeleOne F = _
  rw [integral_ideleOne_unfold _ hu]
  refine integral_congr_ae (Eventually.of_forall fun a => tsum_congr fun ξ => ?_)
  change h ((ideleSplit F).symm (_, Multiplicative.ofAdd u)) = _
  rw [QFPort.ideleSplit_symm_apply, coe_diagUnitsOneEquiv_smul, mul_assoc]
  rfl

/-! ### Changing the fundamental domain -/

/-- The preimage of the fundamental domain under a measure-preserving map commuting with $F^\times$ (up to an
automorphism of $F^\times$) is again a fundamental domain. -/
theorem isFundamentalDomain_preimage {f : ideleOne F → ideleOne F}
    (hf : MeasurePreserving f (muIdeleOne F) (muIdeleOne F)) {e : diagUnitsOne F → diagUnitsOne F}
    (he : Function.Bijective e) (hef : ∀ γ : diagUnitsOne F, ∀ a, f (e γ • a) = γ • f a) :
    IsFundamentalDomain (diagUnitsOne F) (f ⁻¹' ideleClassFD F) (muIdeleOne F) :=
  isFundamentalDomain_ideleClassFD.preimage_of_equiv hf.quasiMeasurePreserving he fun γ a => hef γ a

/-- **Inversion**: $\int_Dk(a^{-1})\,d\mu^1 = \int_Dk\,d\mu^1$ for $F^\times$-invariant $k$ ($\mu^1$ is inversion
invariant, $\mathbb A_F^1$ being abelian, and $D^{-1}$ is again a fundamental domain). -/
theorem setIntegral_fd_inv {k : ideleOne F → ℂ} (hk : ∀ (γ : diagUnitsOne F) a, k (γ • a) = k a) :
    ∫ a in ideleClassFD F, k a⁻¹ ∂muIdeleOne F = ∫ a in ideleClassFD F, k a ∂muIdeleOne F := by
  have hmp : MeasurePreserving (fun a : ideleOne F => a⁻¹) (muIdeleOne F) (muIdeleOne F) :=
    Measure.measurePreserving_inv _
  have hD' : IsFundamentalDomain (diagUnitsOne F) ((fun a : ideleOne F => a⁻¹) ⁻¹' ideleClassFD F)
      (muIdeleOne F) :=
    isFundamentalDomain_preimage hmp (e := fun γ => γ⁻¹) inv_involutive.bijective fun γ a => by
      rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_comm]
      rfl
  have h1 := hmp.setIntegral_preimage_emb (MeasurableEquiv.inv (ideleOne F)).measurableEmbedding k
    ((fun a : ideleOne F => a⁻¹) ⁻¹' ideleClassFD F)
  have h2 : (fun a : ideleOne F => a⁻¹) ⁻¹' ((fun a : ideleOne F => a⁻¹) ⁻¹' ideleClassFD F) = ideleClassFD F := by
    ext a; simp
  rw [h2] at h1
  rw [h1]
  exact hD'.setIntegral_eq isFundamentalDomain_ideleClassFD hk

/-- **Translation**: $\int_Dk(ba)\,d\mu^1 = \int_Dk\,d\mu^1$ for $F^\times$-invariant $k$ and $b\in\mathbb A_F^1$. -/
theorem setIntegral_fd_mul_left {k : ideleOne F → ℂ} (hk : ∀ (γ : diagUnitsOne F) a, k (γ • a) = k a)
    (b : ideleOne F) :
    ∫ a in ideleClassFD F, k (b * a) ∂muIdeleOne F = ∫ a in ideleClassFD F, k a ∂muIdeleOne F := by
  have hmp : ∀ c : ideleOne F, MeasurePreserving (fun a : ideleOne F => c * a) (muIdeleOne F) (muIdeleOne F) :=
    fun c => measurePreserving_mul_left _ c
  have hD' : IsFundamentalDomain (diagUnitsOne F) ((fun a : ideleOne F => b⁻¹ * a) ⁻¹' ideleClassFD F)
      (muIdeleOne F) :=
    isFundamentalDomain_preimage (hmp b⁻¹) (e := id) Function.bijective_id fun γ a => by
      change b⁻¹ * (γ • a) = γ • (b⁻¹ * a)
      rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]
  have h1 := (hmp b).setIntegral_preimage_emb (MeasurableEquiv.mulLeft b).measurableEmbedding k
    ((fun a : ideleOne F => b⁻¹ * a) ⁻¹' ideleClassFD F)
  have h2 : (fun a : ideleOne F => b * a) ⁻¹' ((fun a : ideleOne F => b⁻¹ * a) ⁻¹' ideleClassFD F) =
      ideleClassFD F := by
    ext a; simp
  rw [h2] at h1
  rw [h1]
  exact hD'.setIntegral_eq isFundamentalDomain_ideleClassFD hk

end

end NumberFieldKB.GlobalZeta
