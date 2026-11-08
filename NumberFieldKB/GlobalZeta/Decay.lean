import NumberFieldKB.GlobalZeta.Theta

/-!
# Decay of the theta integral and the Mellin transform

$F$ is a number field, $\Psi$ an admissible function (majorized, with convergent theta series), $\chi$ a unitary
Hecke character.

* **Decay** (`norm_thetaInt_sub_le`, `isBigO_thetaInt_sub`): $f_{\Psi,\chi}(t) - c = O(t^{-r})$ as $t\to\infty$ for
  every $r$, where $c = \Psi(0)\int_D\chi(a\,s(t))\,d\mu^1$ is the contribution of $\gamma = 0$. Tate bounds the theta
  series directly; here the bound comes from the convergence theorem: the majorant
  $B(u) = \int_D\sum_{\xi\in F^\times}\Psi_N(\xi\,a\,s(e^u))\,d\mu^1(a)$ is antitone in $u$ (the archimedean
  components of $s(e^u)$ grow), and $\int_{\mathbb R}e^{u\sigma}B(u)\,du<\infty$ for every $\sigma>1$ by unfolding
  (`lintegral_majB_lt_top`), so $B(u)\le Ke^{-u\sigma}$ (`majB_le`).
* **Local integrability** on $(0,\infty)$ (`locallyIntegrableOn_thetaInt`).
* **The Mellin identity** (`globalZeta_eq_mellin`): for $\operatorname{Re}s>1$,
  $Z(\Psi,\chi,s) = \int_0^\infty t^{s-1}(f_{\Psi,\chi}(t) - c)\,dt$, the unfolding of Tate's §4.4.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set Asymptotics
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal nonZeroDivisors

namespace NumberFieldKB.GlobalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "V" => mixedSpace F

/-! ### Measurability -/

/-- A pointwise convergent series of measurable complex functions is measurable. -/
theorem measurable_tsum_of_summable {ι α : Type*} [Countable ι] [MeasurableSpace α] {f : ι → α → ℂ}
    (hf : ∀ i, Measurable (f i)) (hs : ∀ x, Summable fun i => f i x) : Measurable fun x => ∑' i, f i x := by
  refine measurable_of_tendsto_metrizable' (u := (atTop : Filter (Finset ι)))
    (fun s => Finset.measurable_sum s fun i _ => hf i) ?_
  exact tendsto_pi_nhds.mpr fun x => (hs x).hasSum

theorem measurable_theta {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) : Measurable (theta Ψ) := by
  refine measurable_tsum_of_summable (fun γ => ?_) hΨ.summable
  by_cases hγ : γ = 0
  · subst hγ
    simp only [map_zero, mul_zero]
    exact measurable_const
  · have : (fun g : (Adeles F)ˣ => Ψ ((g : Adeles F) * diagRing F γ)) =
        fun g => Ψ ((g * diagUnits F (Units.mk0 γ hγ) : (Adeles F)ˣ) : Adeles F) := funext fun g => rfl
    rw [this]
    exact hΨ.measurable.comp (measurable_mul_const _)

theorem measurable_sec_log : Measurable fun t : ℝ => sec F (Real.log t) :=
  continuous_sec.measurable.comp Real.measurable_log

theorem measurable_pt : Measurable fun p : ℝ × ideleOne F => pt p.2 p.1 :=
  (continuous_subtype_val.measurable.comp measurable_snd).mul (measurable_sec_log.comp measurable_fst)

theorem measurable_thetaIntegrand {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) (χ : HeckeCharacter F) :
    Measurable fun p : ℝ × ideleOne F => (χ.onIdeles (pt p.2 p.1) : ℂ) * theta Ψ (pt p.2 p.1) :=
  (χ.continuous_coe_onIdeles.measurable.comp measurable_pt).mul ((measurable_theta hΨ).comp measurable_pt)

theorem aestronglyMeasurable_thetaInt {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) (χ : HeckeCharacter F)
    (μ : Measure ℝ) [SFinite μ] : AEStronglyMeasurable (thetaInt Ψ χ) μ :=
  ((measurable_thetaIntegrand hΨ χ).aestronglyMeasurable (μ := μ.prod
    ((muIdeleOne F).restrict (ideleClassFD F)))).integral_prod_right'

/-! ### The majorant along the section -/

/-- $c_u = (e^u)^{1/n}$, the archimedean components of $s(e^u)$. -/
abbrev secScale (u : ℝ) : ℝ := Real.exp u ^ ((Module.finrank ℚ F : ℝ)⁻¹)

theorem secScale_pos (u : ℝ) : 0 < secScale (F := F) u := Real.rpow_pos_of_pos (Real.exp_pos u) _

theorem secScale_mono {u w : ℝ} (h : u ≤ w) : secScale (F := F) u ≤ secScale (F := F) w :=
  Real.rpow_le_rpow (Real.exp_pos u).le (Real.exp_le_exp.mpr h) (by positivity)

theorem val_infPart_sec (u : ℝ) :
    ((infPart (sec F u) : (mixedSpace F)ˣ) : V) =
      ((fun _ => secScale (F := F) u, fun _ => ((secScale (F := F) u : ℝ) : ℂ)) : V) := rfl

theorem norm_infPart_mul_sec (g : (Adeles F)ˣ) (u : ℝ) :
    ‖((infPart (g * sec F u) : (mixedSpace F)ˣ) : V)‖ = secScale (F := F) u * ‖((infPart g : (mixedSpace F)ˣ) : V)‖ := by
  rw [QFPort.infPart_mul, Units.val_mul, val_infPart_sec]
  have : ((infPart g : (mixedSpace F)ˣ) : V) *
      ((fun _ => secScale (F := F) u, fun _ => ((secScale (F := F) u : ℝ) : ℂ)) : V) =
      secScale (F := F) u • ((infPart g : (mixedSpace F)ˣ) : V) := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · simp only [Prod.fst_mul, Pi.mul_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Prod.snd_mul, Pi.mul_apply, Prod.smul_snd, Pi.smul_apply, Complex.real_smul]
      ring
  rw [this, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos (secScale_pos u)]

theorem finPart_mul_sec (g : (Adeles F)ˣ) (u : ℝ) : finPart (g * sec F u) = finPart g := by
  rw [QFPort.finPart_mul, finPart_sec, mul_one]

/-- **The majorant decreases along the section.** -/
theorem majorant_mul_sec_antitone (N : ℕ) {C : ℝ} (hC : 0 ≤ C) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ)
    (g : (Adeles F)ˣ) : Antitone fun u => majorant N C e (g * sec F u) := by
  intro u w huw
  simp only [majorant, finPart_mul_sec, norm_infPart_mul_sec]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (by
    split_ifs <;> norm_num))
  refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ N)
  gcongr
  exact secScale_mono huw

/-- $B(u) = \int_D\sum_{\xi\in F^\times}\Psi_N(\xi\,a\,s(e^u))\,d\mu^1(a)$. -/
def majB (N : ℕ) (C : ℝ) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in ideleClassFD F, ∑' ξ : Fˣ, majorant N C e (diagUnits F ξ * ((a : (Adeles F)ˣ) * sec F u)) ∂muIdeleOne F

theorem majB_antitone (N : ℕ) {C : ℝ} (hC : 0 ≤ C) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    Antitone (majB (F := F) N C e) := by
  intro u w huw
  refine lintegral_mono fun a => ENNReal.tsum_le_tsum fun ξ => ?_
  have h := majorant_mul_sec_antitone N hC e (diagUnits F ξ * (a : (Adeles F)ˣ)) huw
  simpa only [mul_assoc] using h

theorem ideleNorm_diagUnits_mul_pt (ξ : Fˣ) (a : ideleOne F) (u : ℝ) :
    ideleNorm F (diagUnits F ξ * ((a : (Adeles F)ˣ) * sec F u)) = Real.exp u := by
  rw [ideleNorm_mul, ideleNorm_diagUnits, one_mul, ideleNorm_mul, mem_ideleOne.mp a.2, one_mul, ideleNorm_sec]

/-- **$\int_{\mathbb R}e^{u\sigma}B(u)\,du<\infty$** for $\sigma>1$ and $N>n\sigma$ (unfolding the convergence theorem). -/
theorem lintegral_majB_lt_top {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : Module.finrank ℚ F * σ < N) {C : ℝ}
    (hC : 0 ≤ C) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ∫⁻ u, majB (F := F) N C e u * ENNReal.ofReal (Real.exp u ^ σ) < ⊤ := by
  have h := lintegral_majorant_lt_top (F := F) hσ hN hC e
  rw [lintegral_tamIdeles_unfold (fun g => majorant N C e g * ENNReal.ofReal (ideleNorm F g ^ σ))
    ((measurable_majorant N C e).mul ((continuous_ideleNorm.measurable.pow_const σ).ennreal_ofReal))] at h
  refine lt_of_eq_of_lt (lintegral_congr fun u => ?_) h
  simp_rw [ideleNorm_diagUnits_mul_pt]
  rw [majB, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun a => ?_
  rw [ENNReal.tsum_mul_right]

/-- **The majorant decays**: $B(u)\le K\,e^{-(u-1)\sigma}$ with $K = \int e^{w\sigma}B(w)\,dw$. -/
theorem majB_le {σ : ℝ} (hσ : 0 < σ) (N : ℕ) {C : ℝ} (hC : 0 ≤ C) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) (u : ℝ) :
    majB (F := F) N C e u ≤
      (∫⁻ w, majB (F := F) N C e w * ENNReal.ofReal (Real.exp w ^ σ)) * ENNReal.ofReal (Real.exp (-((u - 1) * σ))) := by
  set K := ∫⁻ w, majB (F := F) N C e w * ENNReal.ofReal (Real.exp w ^ σ)
  have h1 : majB (F := F) N C e u * ENNReal.ofReal (Real.exp ((u - 1) * σ)) ≤ K := by
    calc majB (F := F) N C e u * ENNReal.ofReal (Real.exp ((u - 1) * σ))
        = ∫⁻ _w in Icc (u - 1) u, majB (F := F) N C e u * ENNReal.ofReal (Real.exp ((u - 1) * σ)) := by
          rw [setLIntegral_const, Real.volume_Icc, sub_sub_cancel, ENNReal.ofReal_one, mul_one]
      _ ≤ ∫⁻ w in Icc (u - 1) u, majB (F := F) N C e w * ENNReal.ofReal (Real.exp w ^ σ) := by
          refine setLIntegral_mono' measurableSet_Icc fun w hw => mul_le_mul' (majB_antitone N hC e hw.2) ?_
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.exp_mul]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw.1 hσ.le)
      _ ≤ K := setLIntegral_le_lintegral _ _
  have hpos : ENNReal.ofReal (Real.exp ((u - 1) * σ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  calc majB (F := F) N C e u = majB (F := F) N C e u * ENNReal.ofReal (Real.exp ((u - 1) * σ)) *
        ENNReal.ofReal (Real.exp (-((u - 1) * σ))) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one, mul_one]
    _ ≤ K * ENNReal.ofReal (Real.exp (-((u - 1) * σ))) := mul_le_mul_left h1 _

theorem majB_lt_top {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : Module.finrank ℚ F * σ < N) {C : ℝ}
    (hC : 0 ≤ C) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) (u : ℝ) : majB (F := F) N C e u < ⊤ :=
  lt_of_le_of_lt (majB_le (zero_lt_one.trans hσ) N hC e u)
    (ENNReal.mul_lt_top (lintegral_majB_lt_top hσ hN hC e) ENNReal.ofReal_lt_top)

/-! ### The theta integral minus its constant term -/

theorem summable_units {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) (g : (Adeles F)ˣ) :
    Summable fun ξ : Fˣ => Ψ ((diagUnits F ξ * g : (Adeles F)ˣ) : Adeles F) := by
  have h := (hΨ.summable g).comp_injective Units.val_injective
  refine h.congr fun ξ => ?_
  simp only [Function.comp_apply, Units.val_mul, coe_diagUnits, mul_comm]

/-- The remainder integrand $\chi(a\,s(t))\sum_{\xi\in F^\times}\Psi(\xi\,a\,s(t))$. -/
def remInt (Ψ : Adeles F → ℂ) (χ : HeckeCharacter F) (t : ℝ) (a : ideleOne F) : ℂ :=
  (χ.onIdeles (pt a t) : ℂ) * ∑' ξ : Fˣ, Ψ ((diagUnits F ξ * pt a t : (Adeles F)ˣ) : Adeles F)

theorem measurable_remInt {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) (χ : HeckeCharacter F) (t : ℝ) :
    Measurable (remInt Ψ χ t) := by
  refine (χ.continuous_coe_onIdeles.measurable.comp ?_).mul (measurable_tsum_of_summable (fun ξ => ?_)
    fun a => summable_units hΨ _)
  · exact continuous_subtype_val.measurable.mul_const _
  · exact hΨ.measurable.comp ((continuous_subtype_val.measurable.mul_const _).const_mul _)

theorem enorm_remInt_le {Ψ : Adeles F → ℂ} {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {N : ℕ} {C : ℝ}
    {e : HeightOneSpectrum (𝓞 F) →₀ ℤ}
    (hb : ∀ g : (Adeles F)ˣ,
      ‖Ψ g‖ ≤ C * ((1 + ‖(infPart g : V)‖) ^ N)⁻¹ * (if InBox e (ideleIdeal F (finPart g)) then 1 else 0))
    (t : ℝ) (a : ideleOne F) :
    ‖remInt Ψ χ t a‖ₑ ≤ ∑' ξ : Fˣ, majorant N C e (diagUnits F ξ * ((a : (Adeles F)ˣ) * sec F (Real.log t))) := by
  rw [remInt, enorm_mul, ← ofReal_norm, HeckeCharacter.norm_onIdeles_of_isUnitary hχ, ENNReal.ofReal_one, one_mul]
  refine (enorm_tsum_le_tsum_enorm).trans (ENNReal.tsum_le_tsum fun ξ => ?_)
  rw [← ofReal_norm]
  exact IsMajorized.enorm_le hb _

theorem lintegral_remInt_le {Ψ : Adeles F → ℂ} {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {N : ℕ} {C : ℝ}
    {e : HeightOneSpectrum (𝓞 F) →₀ ℤ}
    (hb : ∀ g : (Adeles F)ˣ,
      ‖Ψ g‖ ≤ C * ((1 + ‖(infPart g : V)‖) ^ N)⁻¹ * (if InBox e (ideleIdeal F (finPart g)) then 1 else 0))
    (t : ℝ) : ∫⁻ a in ideleClassFD F, ‖remInt Ψ χ t a‖ₑ ∂muIdeleOne F ≤ majB (F := F) N C e (Real.log t) :=
  lintegral_mono fun a => enorm_remInt_le hχ hb t a

/-- The constant term $c(t) = \Psi(0)\int_D\chi(a\,s(t))\,d\mu^1(a)$. -/
def constPart (Ψ : Adeles F → ℂ) (χ : HeckeCharacter F) (t : ℝ) : ℂ :=
  Ψ 0 * ∫ a in ideleClassFD F, (χ.onIdeles (pt a t) : ℂ) ∂muIdeleOne F

theorem integrableOn_onIdeles {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (t : ℝ) :
    IntegrableOn (fun a : ideleOne F => (χ.onIdeles (pt a t) : ℂ)) (ideleClassFD F) (muIdeleOne F) := by
  refine Measure.integrableOn_of_bounded (M := 1) muIdeleOne_fd_lt_top.ne ?_ (Eventually.of_forall fun a => ?_)
  · exact (χ.continuous_coe_onIdeles.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
  · exact (HeckeCharacter.norm_onIdeles_of_isUnitary hχ _).le

/-- **The theta integral splits** into the constant term and the remainder, when the remainder is integrable
(for instance, for every $t>0$: `integrableOn_remInt`). -/
theorem thetaInt_eq_add {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) {χ : HeckeCharacter F} (hχ : χ.IsUnitary)
    {t : ℝ} (hint : IntegrableOn (remInt Ψ χ t) (ideleClassFD F) (muIdeleOne F)) :
    thetaInt Ψ χ t = constPart Ψ χ t + ∫ a in ideleClassFD F, remInt Ψ χ t a ∂muIdeleOne F := by
  unfold thetaInt constPart
  have hpt : ∀ a : ideleOne F, (χ.onIdeles (pt a t) : ℂ) * theta Ψ (pt a t) =
      Ψ 0 * (χ.onIdeles (pt a t) : ℂ) + remInt Ψ χ t a := fun a => by
    rw [theta_eq_add (hΨ.summable _), remInt]; ring
  simp_rw [hpt]
  rw [integral_add ((integrableOn_onIdeles hχ t).const_mul _) hint, integral_const_mul]

theorem exists_majorant_bound {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) (σ : ℝ) :
    ∃ N : ℕ, Module.finrank ℚ F * σ < N ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ e : HeightOneSpectrum (𝓞 F) →₀ ℤ,
      ∀ g : (Adeles F)ˣ,
        ‖Ψ g‖ ≤ C * ((1 + ‖(infPart g : V)‖) ^ N)⁻¹ * (if InBox e (ideleIdeal F (finPart g)) then 1 else 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt_finrank_mul (F := F) σ
  exact ⟨N, hN, hΨ.bound N⟩

theorem integrableOn_remInt {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) {χ : HeckeCharacter F} (hχ : χ.IsUnitary)
    (t : ℝ) : IntegrableOn (remInt Ψ χ t) (ideleClassFD F) (muIdeleOne F) := by
  obtain ⟨N, hN, C, hC, e, hb⟩ := exists_majorant_bound hΨ 2
  refine ⟨(measurable_remInt hΨ χ t).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (lintegral_remInt_le hχ hb t) (majB_lt_top one_lt_two hN hC e _)

/-- **The decay bound**: $|f_{\Psi,\chi}(t) - c(t)|\le K\,e^\sigma\,t^{-\sigma}$ for $t>0$. -/
theorem norm_thetaInt_sub_le {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) {χ : HeckeCharacter F} (hχ : χ.IsUnitary)
    {σ : ℝ} (hσ : 1 < σ) : ∃ K : ℝ, ∀ t : ℝ, 0 < t →
      ‖thetaInt Ψ χ t - constPart Ψ χ t‖ ≤ K * t ^ (-σ) := by
  obtain ⟨N, hN, C, hC, e, hb⟩ := exists_majorant_bound hΨ σ
  set K := ∫⁻ w, majB (F := F) N C e w * ENNReal.ofReal (Real.exp w ^ σ)
  have hK : K < ⊤ := lintegral_majB_lt_top hσ hN hC e
  refine ⟨K.toReal * Real.exp σ, fun t ht => ?_⟩
  rw [thetaInt_eq_add hΨ hχ (integrableOn_remInt hΨ hχ t), add_sub_cancel_left]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  have h1 := (lintegral_remInt_le (Ψ := Ψ) hχ hb t).trans (majB_le (zero_lt_one.trans hσ) N hC e (Real.log t))
  have h2 : (∫⁻ a in ideleClassFD F, ENNReal.ofReal ‖remInt Ψ χ t a‖ ∂muIdeleOne F).toReal ≤
      (K * ENNReal.ofReal (Real.exp (-((Real.log t - 1) * σ)))).toReal := by
    refine ENNReal.toReal_mono (ENNReal.mul_lt_top hK ENNReal.ofReal_lt_top).ne ?_
    simp_rw [ofReal_norm]
    exact h1
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_assoc]
  congr 1
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  congr 1
  ring

/-! ### The constant term for the two kinds of characters -/

/-- The constant term $c_{\Psi,\chi}$: $\Psi(0)\operatorname{vol}(F^\times\backslash\mathbb A_F^1) = \Psi(0)\rho_F$ for $\chi = 1$, and
$0$ otherwise. -/
def constTerm (Ψ : Adeles F → ℂ) (χ : HeckeCharacter F) : ℂ :=
  if χ = 1 then Ψ 0 * (dedekindZeta_residue F : ℂ) else 0

/-- **The characters handled by the Mellin argument**: the trivial character, and unitary characters that are
not trivial on $\mathbb A_F^1$ (every Hecke character reduces to one of these by a shift of $s$). -/
def IsNormalized (χ : HeckeCharacter F) : Prop :=
  χ.IsUnitary ∧ (χ = 1 ∨ ∃ b : ideleOne F, χ.onIdeles b ≠ 1)

theorem constPart_eq_constTerm (Ψ : Adeles F → ℂ) {χ : HeckeCharacter F} (hχ : IsNormalized χ) (t : ℝ) :
    constPart Ψ χ t = constTerm Ψ χ := by
  unfold constPart constTerm
  rcases hχ.2 with rfl | hnt
  · rw [if_pos rfl]
    congr 1
    simp_rw [HeckeCharacter.one_onIdeles, Units.val_one]
    rw [setIntegral_const, Complex.real_smul, mul_one, measureReal_fd]
  · have h1 : χ ≠ 1 := fun h => by
      obtain ⟨b, hb⟩ := hnt
      subst h
      exact hb rfl
    rw [if_neg h1, setIntegral_onIdeles_eq_zero χ hnt, mul_zero]

theorem IsNormalized.inv {χ : HeckeCharacter F} (hχ : IsNormalized χ) : IsNormalized χ⁻¹ := by
  refine ⟨fun c => ?_, ?_⟩
  · show ‖(((χ c)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, hχ.1 c, inv_one]
  · rcases hχ.2 with rfl | ⟨b, hb⟩
    · exact Or.inl (inv_eq_one.mpr rfl)
    · refine Or.inr ⟨b, fun h => hb ?_⟩
      have := congrArg (fun z : ℂˣ => (z : ℂ)) h
      simp only [HeckeCharacter.inv_onIdeles, Units.val_one, inv_eq_one] at this
      exact Units.ext this

/-- **Decay of the theta integral**: $f_{\Psi,\chi}(t) - c_{\Psi,\chi} = O(t^r)$ at $\infty$ for every real $r$. -/
theorem isBigO_thetaInt_sub {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) {χ : HeckeCharacter F} (hχ : IsNormalized χ)
    (r : ℝ) : (fun t => thetaInt Ψ χ t - constTerm Ψ χ) =O[atTop] (· ^ r) := by
  set σ := max 2 (-r)
  have hσ : 1 < σ := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  obtain ⟨K, hK⟩ := norm_thetaInt_sub_le hΨ hχ.1 hσ
  have hK0 : 0 ≤ K := (norm_nonneg _).trans ((hK 1 one_pos).trans (by rw [Real.one_rpow, mul_one]))
  refine isBigO_iff.mpr ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [← constPart_eq_constTerm Ψ hχ t, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  refine (hK t ht0).trans (mul_le_mul_of_nonneg_left ?_ hK0)
  exact Real.rpow_le_rpow_of_exponent_le ht (by have := le_max_right 2 (-r); linarith)

/-! ### Local integrability and the Mellin identity -/

/-- **The theta integral is locally integrable on $(0,\infty)$.** -/
theorem locallyIntegrableOn_thetaInt {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) {χ : HeckeCharacter F}
    (hχ : IsNormalized χ) : LocallyIntegrableOn (thetaInt Ψ χ) (Ioi 0) := by
  obtain ⟨K, hK⟩ := norm_thetaInt_sub_le hΨ hχ.1 one_lt_two
  have hK0 : 0 ≤ K := (norm_nonneg _).trans ((hK 1 one_pos).trans (by rw [Real.one_rpow, mul_one]))
  intro x hx
  have hx0 : 0 < x := hx
  refine ⟨Ioo (x / 2) (2 * x), mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  refine Measure.integrableOn_of_bounded (M := K * ((x / 2) ^ 2)⁻¹ + ‖constTerm Ψ χ‖) measure_Ioo_lt_top.ne
    (aestronglyMeasurable_thetaInt hΨ χ _) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := lt_trans (by linarith) ht.1
  have h1 := hK t ht0
  rw [constPart_eq_constTerm Ψ hχ t] at h1
  have h2 : t ^ (-(2 : ℝ)) ≤ ((x / 2) ^ 2)⁻¹ := by
    rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ht.1.le 2)
  calc ‖thetaInt Ψ χ t‖ ≤ ‖thetaInt Ψ χ t - constTerm Ψ χ‖ + ‖constTerm Ψ χ‖ := by
        rw [add_comm]; exact norm_le_insert' _ _
    _ ≤ K * ((x / 2) ^ 2)⁻¹ + ‖constTerm Ψ χ‖ := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hK0)

theorem pt_exp (a : ideleOne F) (u : ℝ) : pt a (Real.exp u) = (a : (Adeles F)ˣ) * sec F u := by
  rw [pt, Real.log_exp]

/-- **The Mellin identity** (Tate's §4.4 unfolding): for $\operatorname{Re}s>1$,
$Z(\Psi,\chi,s) = \int_0^\infty t^{s-1}\bigl(f_{\Psi,\chi}(t) - c_{\Psi,\chi}\bigr)\,dt$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (ζ(f, c) as an integral over t of the theta integral)"]
theorem globalZeta_eq_mellin {Ψ : Adeles F → ℂ} (hΨ : IsAdmissible Ψ) {χ : HeckeCharacter F} (hχ : IsNormalized χ)
    {s : ℂ} (hs : 1 < s.re) :
    globalZeta Ψ χ s = mellin (fun t => thetaInt Ψ χ t - constTerm Ψ χ) s := by
  have hshift : χ.shift = 0 := (HeckeCharacter.shift_eq_zero_iff χ).mpr hχ.1
  have hint := integrable_globalZetaIntegrand hΨ.toIsMajorized χ (s := s) (by rw [hshift, add_zero]; exact hs)
  rw [globalZeta, integral_tamIdeles_unfold _ hint]
  have hinner : ∀ u : ℝ, ∫ a in ideleClassFD F, ∑' ξ : Fˣ,
      globalZetaIntegrand Ψ χ s (diagUnits F ξ * ((a : (Adeles F)ˣ) * sec F u)) ∂muIdeleOne F =
      ((Real.exp u : ℝ) : ℂ) ^ s * (thetaInt Ψ χ (Real.exp u) - constTerm Ψ χ) := by
    intro u
    have h1 : ∀ a : ideleOne F, ∑' ξ : Fˣ,
        globalZetaIntegrand Ψ χ s (diagUnits F ξ * ((a : (Adeles F)ˣ) * sec F u)) =
        ((Real.exp u : ℝ) : ℂ) ^ s * remInt Ψ χ (Real.exp u) a := by
      intro a
      simp only [globalZetaIntegrand, HeckeCharacter.onIdeles_diagUnits_mul, ideleNorm_diagUnits_mul_pt, remInt,
        pt_exp]
      rw [← tsum_mul_left, ← tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      ring
    simp_rw [h1]
    rw [integral_const_mul, thetaInt_eq_add hΨ hχ.1 (integrableOn_remInt hΨ hχ.1 _), constPart_eq_constTerm _ hχ,
      add_sub_cancel_left]
  simp_rw [hinner]
  rw [mellin, ← integral_comp_exp]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hx : ((Real.exp u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'
  simp only [Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_sub _ _ hx, Complex.cpow_one]
  field_simp

end

end NumberFieldKB.GlobalZeta
