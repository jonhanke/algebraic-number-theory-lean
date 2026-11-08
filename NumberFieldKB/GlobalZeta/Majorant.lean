import NumberFieldKB.GlobalZeta.Convergence

/-!
# Factorizable Schwartz–Bruhat functions are majorized

$F$ is a number field. For $\Phi = f_\infty\otimes\bigotimes_v f_v$ with $f_\infty$ Schwartz on $F_\infty$, $f_v$ locally
constant with compact support (`IsSchwartzBruhatLC`) and $f_v = \mathbf 1_{\mathcal O_v}$ outside a finite set
$S$:

* **`finprod_eq_prod_mul_indicator`**: $\prod_vf_v(x_v) = \prod_{v\in S}f_v(x_v)\cdot\mathbf 1[x_v\in\mathcal O_v\ \forall v\notin S]$,
  so the finite part is measurable (`measurable_finprod`; the set is open in $\mathbb A_f$);
* **`exists_finprod_bound`**: $|\prod_vf_v(x_v)|\le M\,\mathbf 1[\mathfrak a(x)\in\text{box}]$ on $\mathbb A_f^\times$;
* **`isMajorized_of_factors`**: $\Phi$ is majorized (`IsMajorized`), hence (`Convergence.lean`) its zeta integral
  converges absolutely for $\operatorname{Re}s+\sigma>1$;
* **`SchwartzBruhat.isMajorized`**, **`SchwartzBruhat.isMajorized_fourier`**: this applies to every factorizable
  Schwartz–Bruhat function and to its Fourier transform ($\hat f_\infty$ is Schwartz, $\hat f_v$ is locally constant with
  compact support, and $\hat f_v = \mathbf 1_{\mathcal O_v}$ when $f_v = \mathbf 1_{\mathcal O_v}$ and $v\nmid\mathfrak d$).
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set WithZero
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal nonZeroDivisors

namespace NumberFieldKB.GlobalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "V" => mixedSpace F

open LocalZeta

/-! ### The finite part -/

section FinitePart

variable (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The finite adeles integral outside $S$. -/
def integralOutside : Set AF := {x | ∀ v, v ∉ S → (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) v ∈
  v.adicCompletionIntegers F}

theorem isOpen_integralOutside : IsOpen (integralOutside (F := F) S) :=
  RestrictedProduct.isOpen_forall_imp_mem (fun v => isOpen_adicCompletionIntegers v)

theorem ballIndV_zero_zero_apply (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    Analysis.ballIndV v 0 0 y = if y ∈ v.adicCompletionIntegers F then 1 else 0 := by
  by_cases h : y ∈ v.adicCompletionIntegers F
  · rw [if_pos h]
    refine Set.indicator_of_mem ?_ _
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    show Valued.v (y - 0) ≤ exp (-(0 : ℤ))
    rw [sub_zero, neg_zero, exp_zero]; exact h
  · rw [if_neg h]
    refine Set.indicator_of_notMem ?_ _
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    show ¬ Valued.v (y - 0) ≤ exp (-(0 : ℤ))
    rw [sub_zero, neg_zero, exp_zero]; exact h

variable {fv S}

theorem finprod_eq_prod_mul_indicator (hout : ∀ v ∉ S, fv v = Analysis.ballIndV v 0 0) (x : AF) :
    ∏ᶠ v, fv v (x v) = (∏ v ∈ S, fv v (x v)) * (integralOutside (F := F) S).indicator 1 x := by
  have hfin : {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite := x.2
  by_cases hx : x ∈ integralOutside S
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS
    apply hv
    show fv v (x v) = 1
    rw [hout v hvS, ballIndV_zero_zero_apply, if_pos (hx v hvS)]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    simp only [integralOutside, Set.mem_ofPred_eq, not_forall] at hx
    obtain ⟨v, hvS, hv⟩ := hx
    rw [finprod_eq_prod_of_mulSupport_subset (s := S ∪ hfin.toFinset) _ fun w hw => by
      by_contra h
      apply hw
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.coe_toFinset,
        Set.mem_setOf_eq, not_or, not_not] at h
      show fv w (x w) = 1
      rw [hout w h.1, ballIndV_zero_zero_apply, if_pos h.2]]
    refine Finset.prod_eq_zero (i := v) (Finset.mem_union_right _ (by simpa using hv)) ?_
    rw [hout v hvS, ballIndV_zero_zero_apply, if_neg hv]

theorem measurable_finprod (hS : ∀ v ∈ S, IsSchwartzBruhatLC v (fv v))
    (hout : ∀ v ∉ S, fv v = Analysis.ballIndV v 0 0) : Measurable fun x : AF => ∏ᶠ v, fv v (x v) := by
  simp_rw [finprod_eq_prod_mul_indicator hout]
  refine Measurable.mul ?_ (measurable_one.indicator (isOpen_integralOutside S).measurableSet)
  refine Finset.measurable_prod S fun v hv => ?_
  have hc : Continuous fun x : AF => x v := RestrictedProduct.continuous_eval v
  exact (hS v hv).measurable.comp hc.measurable

/-- **The finite part is bounded by a box indicator**: $|\prod_vf_v(z_v)|\le M\,\mathbf 1[\mathfrak a(z)\in\text{box}]$
on $\mathbb A_f^\times$. -/
theorem exists_finprod_bound (hS : ∀ v ∈ S, IsSchwartzBruhatLC v (fv v))
    (hout : ∀ v ∉ S, fv v = Analysis.ballIndV v 0 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ e : HeightOneSpectrum (𝓞 F) →₀ ℤ, ∀ z : AFˣ,
      ‖∏ᶠ v, fv v ((z : AF) v)‖ ≤ M * (if InBox e (ideleIdeal F z) then 1 else 0) := by
  set Nf : HeightOneSpectrum (𝓞 F) → ℤ := fun v => if h : v ∈ S then (hS v h).exists_support.choose else 0
  set Cf : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if h : v ∈ S then max 1 (hS v h).exists_bound.choose else 1
  have hNf : ∀ v ∈ S, ∀ y, fv v y ≠ 0 → Valued.v y ≤ exp (Nf v) := fun v hv y hy => by
    simp only [Nf, dif_pos hv]; exact (hS v hv).exists_support.choose_spec y hy
  have hCf : ∀ v ∈ S, ∀ y, ‖fv v y‖ ≤ Cf v := fun v hv y => by
    simp only [Cf, dif_pos hv]; exact ((hS v hv).exists_bound.choose_spec y).trans (le_max_right _ _)
  have hCf0 : ∀ v, 0 ≤ Cf v := fun v => by
    simp only [Cf]; split_ifs
    · exact zero_le_one.trans (le_max_left _ _)
    · exact zero_le_one
  set e : HeightOneSpectrum (𝓞 F) →₀ ℤ := Finsupp.onFinset S (fun v => if v ∈ S then Nf v else 0)
    fun v hv => by by_contra h; exact hv (if_neg h)
  have he : ∀ v, e v = if v ∈ S then Nf v else 0 := fun v => Finsupp.onFinset_apply
  refine ⟨∏ v ∈ S, Cf v, Finset.prod_nonneg fun v _ => hCf0 v, e, fun z => ?_⟩
  rw [finprod_eq_prod_mul_indicator hout, norm_mul, norm_prod]
  split_ifs with hbox
  · rw [mul_one]
    refine mul_le_of_le_one_right (Finset.prod_nonneg fun v _ => norm_nonneg _) ?_ |>.trans ?_
    · by_cases h : (z : AF) ∈ integralOutside S <;> simp [Set.indicator, h]
    · exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v hv => hCf v hv _
  · rw [mul_zero]
    simp only [InBox, not_forall, not_le] at hbox
    obtain ⟨v, hv⟩ := hbox
    rw [count_ideleIdeal] at hv
    have hval : exp (e v) < Valued.v ((z : AF) v) := by
      rw [valued_eq_exp_ordAt, exp_lt_exp]; omega
    by_cases hvS : v ∈ S
    · have h0 : fv v ((z : AF) v) = 0 := by
        by_contra h
        have := hNf v hvS _ h
        rw [he, if_pos hvS] at hval
        exact absurd this (not_le.mpr hval)
      rw [Finset.prod_eq_zero hvS (by rw [h0, norm_zero]), zero_mul]
    · have hnot : (z : AF) ∉ integralOutside S := fun h => by
        have h1 := h v hvS
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
        rw [he, if_neg hvS, exp_zero] at hval
        exact absurd h1 (not_le.mpr hval)
      rw [Set.indicator_of_notMem hnot, norm_zero, mul_zero]

end FinitePart

/-! ### Majorized factorizable functions -/

/-- **A Schwartz bound on $F_\infty$**: $|f(x)|\le C(1+\|x\|)^{-N}$. -/
theorem SchwartzMap.exists_bound_one_add_norm (f : SchwartzMap V ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V, ‖f x‖ ≤ C * ((1 + ‖x‖) ^ N)⁻¹ := by
  set C := 2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  refine ⟨C, by positivity, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖x‖) ^ N := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact h

theorem infPart_val (g : (Adeles F)ˣ) : ((infPart g : (mixedSpace F)ˣ) : V) = (g : Adeles F).1 := rfl

theorem finPart_val (g : (Adeles F)ˣ) : ((finPart g : AFˣ) : AF) = (g : Adeles F).2 := rfl

/-- **Factorizable functions are majorized**: $\Phi = f_\infty\otimes\bigotimes_vf_v$ with $f_\infty$ Schwartz, $f_v$ locally
constant with compact support, and $f_v = \mathbf 1_{\mathcal O_v}$ outside $S$. -/
theorem isMajorized_of_factors (f : SchwartzMap V ℂ) (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∈ S, IsSchwartzBruhatLC v (fv v))
    (hout : ∀ v ∉ S, fv v = Analysis.ballIndV v 0 0) :
    IsMajorized (fun x : Adeles F => f x.1 * ∏ᶠ v, fv v (x.2 v)) := by
  refine ⟨?_, fun N => ?_⟩
  · exact ((f.continuous.comp (continuous_fst.comp Units.continuous_val)).measurable).mul
      ((measurable_finprod hS hout).comp (continuous_snd.comp Units.continuous_val).measurable)
  · obtain ⟨C, hC, hf⟩ := SchwartzMap.exists_bound_one_add_norm f N
    obtain ⟨M, hM, e, hfin⟩ := exists_finprod_bound hS hout
    refine ⟨C * M, mul_nonneg hC hM, e, fun g => ?_⟩
    rw [norm_mul, mul_comm C M, mul_assoc M, mul_comm M, mul_assoc]
    refine mul_le_mul (hf _) ?_ (norm_nonneg _) (by positivity)
    calc _ = ‖∏ᶠ v, fv v ((finPart g : AF) v)‖ := rfl
      _ ≤ _ := hfin _

end

end GlobalZeta

open GlobalZeta LocalZeta

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "V" => mixedSpace F

namespace SchwartzBruhat

variable (Φ : SchwartzBruhat F)

theorem isSchwartzBruhatLC (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ Φ.S) : IsSchwartzBruhatLC v (Φ.fv v) :=
  IsSchwartzBruhatLC.of_isSchwartzBruhatV (Φ.isSchwartzBruhat v hv)

/-- **A factorizable Schwartz–Bruhat function is majorized.** -/
theorem isMajorized : IsMajorized (Φ : Adeles F → ℂ) :=
  isMajorized_of_factors Φ.fInf Φ.fv Φ.S Φ.isSchwartzBruhatLC Φ.eq_charO

/-- $\hat{\mathbf 1}_{\mathcal O_v} = \mathbf 1_{\mathcal O_v}$ at a place not dividing the different. -/
theorem fourierV_ballIndV_zero_zero {v : HeightOneSpectrum (𝓞 F)} (hv : Analysis.diffExp v = 0) :
    Analysis.fourierV v (Analysis.ballIndV v 0 0) = Analysis.ballIndV v 0 0 := by
  rw [Analysis.fourierV_ballIndV_eq]
  funext y
  have hvol : (Analysis.selfDualV v).real (Analysis.latticeV v 0) = 1 := by
    rw [Analysis.selfDualV_real_Ov, hv, pow_zero, Real.one_rpow]
  rw [hvol, zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, Complex.ofReal_one, mul_one, mul_one, hv]
  simp

/-- The places outside which $\hat f_v = \mathbf 1_{\mathcal O_v}$: those in $S$ and those dividing the different. -/
def fourierS : Finset (HeightOneSpectrum (𝓞 F)) := Φ.S ∪ Analysis.finite_support_diffExp.toFinset

theorem fourier_eq_charO (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Φ.fourierS) :
    Analysis.fourierV v (Φ.fv v) = Analysis.ballIndV v 0 0 := by
  simp only [fourierS, Finset.mem_union, Set.Finite.mem_toFinset, Function.mem_support, not_or, not_not] at hv
  rw [Φ.eq_charO v hv.1, fourierV_ballIndV_zero_zero (by exact_mod_cast hv.2)]

theorem fourier_isSchwartzBruhatLC (v : HeightOneSpectrum (𝓞 F)) (_hv : v ∈ Φ.fourierS) :
    IsSchwartzBruhatLC v (Analysis.fourierV v (Φ.fv v)) := by
  by_cases h : v ∈ Φ.S
  · exact (Φ.isSchwartzBruhatLC v h).fourierV
  · rw [Φ.eq_charO v h]
    exact (IsSchwartzBruhatLC.of_isSchwartzBruhatV (isSchwartzBruhatV_ballIndV v 0 0)).fourierV

theorem fourier_eq (y : Adeles F) :
    Φ.fourier y = fourierInfSchwartz Φ.fInf y.1 * ∏ᶠ v, Analysis.fourierV v (Φ.fv v) (y.2 v) := by
  rw [SchwartzBruhat.fourier, coe_fourierInfSchwartz]

/-- **The Fourier transform of a factorizable Schwartz–Bruhat function is majorized.** -/
theorem isMajorized_fourier : IsMajorized Φ.fourier := by
  have h := isMajorized_of_factors (fourierInfSchwartz Φ.fInf) (fun v => Analysis.fourierV v (Φ.fv v)) Φ.fourierS
    Φ.fourier_isSchwartzBruhatLC Φ.fourier_eq_charO
  have he : Φ.fourier = fun x : Adeles F =>
      fourierInfSchwartz Φ.fInf x.1 * ∏ᶠ v, Analysis.fourierV v (Φ.fv v) (x.2 v) :=
    funext Φ.fourier_eq
  rw [he]
  exact h

end SchwartzBruhat

end

end NumberFieldKB
