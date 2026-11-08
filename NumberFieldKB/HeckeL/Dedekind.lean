import NumberFieldKB.HeckeL.Basic

/-!
# The Dedekind zeta function from Tate's thesis

$F$ is a number field with $r_1$ real and $r_2$ complex places and discriminant $d_F$. For the trivial character the
Hecke $L$-function is the Dedekind zeta function, $L(s,1) = \prod_v(1-N(v)^{-s})^{-1} = \zeta_F(s)$.

The test function is $\Phi_0 = \Phi_\infty\otimes\bigotimes_v\mathbf 1_{\mathcal O_v}$ (`dedekindPhi`), $\Phi_\infty$ the
self-dual Gaussian. Its Fourier transform is $\hat\Phi_0 = \Phi_\infty\otimes\bigotimes_vN(\mathfrak d_v)^{-1/2}
\mathbf 1_{\mathfrak d_v^{-1}}$ (`dualPhi`, `coe_dualPhi`), and for $\operatorname{Re}s>1$:

* `globalZeta_dedekindPhi`: $Z(\Phi_0,1,s) = |d_F|^{-1/2}\,\Gamma_{\mathbb R}(s)^{r_1}(\pi\Gamma_{\mathbb C}(s))^{r_2}\,\zeta_F(s)$;
* `globalZeta_dualPhi`: $Z(\hat\Phi_0,1,s) = |d_F|^{s-1/2}\,Z(\Phi_0,1,s)$.

Tate's thesis, Cassels–Fröhlich Ch. XV, §4.4 [unverified locator]; Neukirch, *Algebraic Number Theory*, Ch. VII,
Cor. 5.11 [unverified locator].
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-! ### Scaling a local zeta integral -/

/-- **Scaling**: $Z(f(a\,\cdot),\chi,s) = \chi(a)^{-1}|a|^{-s}Z(f,\chi,s)$ for a left-invariant measure on $F_v^\times$. -/
theorem zetaIntegral_comp_mul {v : HeightOneSpectrum (𝓞 F)} (μ : Measure (v.adicCompletion F)ˣ)
    [μ.IsMulLeftInvariant] (f : v.adicCompletion F → ℂ) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (a : (v.adicCompletion F)ˣ) :
    zetaIntegral μ (fun x => f ((a : v.adicCompletion F) * x)) χ s =
      ((χ a : ℂ))⁻¹ * ((distribHaarChar (v.adicCompletion F) a : ℝ) : ℂ) ^ (-s) * zetaIntegral μ f χ s := by
  conv_rhs => rw [zetaIntegral, ← integral_mul_left_eq_self _ a, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have ha : ((χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hpos : (0 : ℝ) < distribHaarChar (v.adicCompletion F) a := distribHaarChar_pos' a
  have hpos' : ((distribHaarChar (v.adicCompletion F) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [zetaIntegrand, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hpos.le (distribHaarChar_pos' u).le, Complex.cpow_neg]
  have hc : ((distribHaarChar (v.adicCompletion F) a : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  field_simp

/-! ### Lattices and the different -/

/-- $\mathbf 1_{\mathfrak p_v^{-k}}(x) = \mathbf 1_{\mathcal O_v}(\varpi_v^kx)$. -/
theorem ballIndV_neg_eq (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (x : v.adicCompletion F) :
    Analysis.ballIndV v 0 (-(k : ℤ)) x =
      Analysis.ballIndV v 0 0 (((Analysis.ϖU v ^ (k : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) := by
  have key : Valued.v x ≤ WithZero.exp (k : ℤ) ↔
      Valued.v (((Analysis.ϖU v ^ (k : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ≤ 1 := by
    rw [Valuation.map_mul, valued_ϖU_zpow]
    rcases eq_or_ne (Valued.v x) 0 with h | h
    · simp [h]
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨WithZero.log (Valued.v x), (WithZero.exp_log h).symm⟩
      rw [hm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_le_exp]
      omega
  unfold Analysis.ballIndV
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, sub_zero, neg_neg, neg_zero, WithZero.exp_zero]
  by_cases h : Valued.v x ≤ WithZero.exp (k : ℤ)
  · rw [if_pos h, if_pos (key.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (key.mpr h'))]

/-- **The Fourier transform of $\mathbf 1_{\mathcal O_v}$** is $\operatorname{vol}(\mathcal O_v)\mathbf 1_{\mathfrak d_v^{-1}}$,
$\mathfrak d_v^{-1} = \mathfrak p_v^{-d_v}$ (QuadFormsKB's `fourierV_ballIndV_eq`). -/
theorem fourierV_charO (v : HeightOneSpectrum (𝓞 F)) :
    Analysis.fourierV v (Analysis.ballIndV v 0 0) =
      fun y => ((volO v).toReal : ℂ) * Analysis.ballIndV v 0 (-(Analysis.diffExp v : ℤ)) y := by
  rw [Analysis.fourierV_ballIndV_eq]
  funext y
  simp only [zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, neg_zero, zero_sub]
  rw [volO_eq_ofReal, ENNReal.toReal_ofReal measureReal_nonneg]
  ring

/-! ### The test function and its Fourier transform -/

theorem isUnramifiedAt_one (v : HeightOneSpectrum (𝓞 F)) : (1 : HeckeCharacter F).IsUnramifiedAt v :=
  fun _ _ => rfl

theorem shift_one : (1 : HeckeCharacter F).shift = 0 :=
  (HeckeCharacter.shift_eq_zero_iff _).mpr fun c => by simp

variable (F) in
/-- **The test function for $\zeta_F$**: $\Phi_0 = \Phi_\infty\otimes\bigotimes_v\mathbf 1_{\mathcal O_v}$, $\Phi_\infty$ the
self-dual Gaussian (the standard test function of the trivial character). -/
def dedekindPhi : SchwartzBruhat F := stdPhi 1 Analysis.gaussInf

theorem dedekindPhi_fv (v : HeightOneSpectrum (𝓞 F)) : (dedekindPhi F).fv v = Analysis.ballIndV v 0 0 := by
  show stdFv 1 v = _
  rw [stdFv, if_pos (isUnramifiedAt_one v)]

/-- The local component $N(\mathfrak d_v)^{-1/2}\mathbf 1_{\mathfrak d_v^{-1}}$ of $\hat\Phi_0$. -/
def dualFv (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : ℂ :=
  ((volO v).toReal : ℂ) * Analysis.ballIndV v 0 (-(Analysis.diffExp v : ℤ)) y

variable (F) in
/-- **The Fourier transform of $\Phi_0$** as a factorizable Schwartz–Bruhat function:
$\Phi_\infty\otimes\bigotimes_vN(\mathfrak d_v)^{-1/2}\mathbf 1_{\mathfrak d_v^{-1}}$ (`coe_dualPhi`). -/
def dualPhi : SchwartzBruhat F where
  fInf := Analysis.gaussInf
  fv := dualFv
  S := (Analysis.finite_support_diffExp (F := F)).toFinset
  isSchwartzBruhat := fun v _ => ⟨1, fun _ => ((volO v).toReal : ℂ), fun _ => 0,
    fun _ => -(Analysis.diffExp v : ℤ), by funext y; simp [dualFv]⟩
  eq_charO := fun v hv => by
    have hd : Analysis.diffExp v = 0 := by simpa using hv
    funext y
    rw [dualFv, volO_toReal, hd]
    simp

theorem coe_dualPhi : (dualPhi F : Adeles F → ℂ) = (dedekindPhi F).fourier := by
  funext y
  rw [SchwartzBruhat.apply, SchwartzBruhat.fourier]
  congr 1
  · change Analysis.gaussInf y.1 = Analysis.fourierInf (⇑(Analysis.gaussInf (F := F))) y.1
    rw [show (⇑(Analysis.gaussInf (F := F)) : mixedSpace F → ℂ) = Analysis.gaussInfFun from
      funext Analysis.gaussInf_apply, Analysis.fourierInf_gaussInfFun]
  · refine finprod_congr fun v => ?_
    rw [dedekindPhi_fv, fourierV_charO]
    rfl

/-! ### The local and global zeta integrals -/

/-- The places dividing the different. -/
def diffSet (F : Type) [Field F] [NumberField F] : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Analysis.finite_support_diffExp (F := F)).toFinset

theorem diffExp_eq_zero {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ diffSet F) : Analysis.diffExp v = 0 := by
  simpa [diffSet] using hv

/-- **$\prod_vN(v)^{d_v} = |d_F|$** (QuadFormsKB's `finprod_absNorm_pow_diffExp`, $N(\mathfrak d_F) = |d_F|$). -/
theorem prod_normV_pow_diffExp : ∏ v ∈ diffSet F, normV v ^ Analysis.diffExp v = |(discr F : ℝ)| := by
  have h := Analysis.finprod_absNorm_pow_diffExp (F := F)
  rw [finprod_eq_prod_of_mulSupport_subset (s := diffSet F) _ (fun v hv => by
    by_contra h'
    apply hv
    simp [diffExp_eq_zero h'])] at h
  have h2 := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at h2
  simpa [normV] using h2

theorem abs_discr_pos : 0 < |(discr F : ℝ)| :=
  abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F))

/-- At a place: $\operatorname{vol}(\mathcal O_v)\,(N(v)^s)^{d_v} = (N(v)^{d_v})^{s-1/2}$. -/
theorem volO_mul_cpow (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    ((volO v).toReal : ℂ) * ((normV v : ℂ) ^ s) ^ Analysis.diffExp v =
      (((normV v ^ Analysis.diffExp v : ℝ)) : ℂ) ^ (s - 1 / 2) := by
  have hM : 0 < normV v ^ Analysis.diffExp v := pow_pos (normV_pos v) _
  rw [volO_toReal, ← ofReal_pow_cpow (normV_pos v).le, Complex.ofReal_cpow hM.le, Complex.cpow_sub _ _
    (by exact_mod_cast hM.ne'), show (((-(1 : ℝ) / 2 : ℝ)) : ℂ) = -(1 / 2 : ℂ) by push_cast; ring,
    Complex.cpow_neg]
  ring

/-- **The local zeta integral of $\hat\Phi_0$**: $Z(N(\mathfrak d_v)^{-1/2}\mathbf 1_{\mathfrak d_v^{-1}},1,s) =
(N(v)^{d_v})^{s-1/2}\,Z(\mathbf 1_{\mathcal O_v},1,s)$. -/
theorem zetaIntegral_dualFv (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    zetaIntegral (tateHaarV v) (dualFv v) ((1 : HeckeCharacter F).finiteComponent v).toMonoidHom s =
      (((normV v ^ Analysis.diffExp v : ℝ)) : ℂ) ^ (s - 1 / 2) *
        zetaIntegral (tateHaarV v) ((dedekindPhi F).fv v) ((1 : HeckeCharacter F).finiteComponent v).toMonoidHom s := by
  set d := Analysis.diffExp v
  have h1 : zetaIntegral (tateHaarV v) (dualFv v) ((1 : HeckeCharacter F).finiteComponent v).toMonoidHom s =
      ((volO v).toReal : ℂ) * zetaIntegral (tateHaarV v)
        (fun x => Analysis.ballIndV v 0 0 (((Analysis.ϖU v ^ (d : ℤ) : (v.adicCompletion F)ˣ) :
          v.adicCompletion F) * x)) ((1 : HeckeCharacter F).finiteComponent v).toMonoidHom s := by
    rw [zetaIntegral, zetaIntegral, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [zetaIntegrand, dualFv, ballIndV_neg_eq]
    ring
  rw [h1, zetaIntegral_comp_mul, dedekindPhi_fv, ← volO_mul_cpow]
  have hχ : ((((1 : HeckeCharacter F).finiteComponent v).toMonoidHom (Analysis.ϖU v ^ (d : ℤ)) : ℂˣ) : ℂ) = 1 := rfl
  have hmod : ((distribHaarChar (v.adicCompletion F) (Analysis.ϖU v ^ (d : ℤ)) : ℝ) : ℂ) ^ (-s) =
      ((normV v : ℂ) ^ s) ^ d := by
    rw [zpow_natCast, distribHaarChar_ϖU_pow, ofReal_pow_cpow (modV_pos' v).le, modV_cpow, neg_neg]
  rw [hχ, hmod, inv_one, one_mul]
  ring

/-- $\prod_v(N(v)^{d_v})^{s-1/2} = |d_F|^{s-1/2}$, a finite product. -/
theorem hasProd_diff_cpow (s : ℂ) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => (((normV v ^ Analysis.diffExp v : ℝ)) : ℂ) ^ (s - 1 / 2))
      (((|(discr F : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)) := by
  rw [← prod_normV_pow_diffExp, ofReal_prod_cpow _ _ (fun v => (pow_pos (normV_pos v) _).le)]
  exact hasProd_prod_of_ne_finset_one fun v hv => by
    rw [diffExp_eq_zero hv, pow_zero, Complex.ofReal_one, Complex.one_cpow]

/-- **$Z(\hat\Phi_0,1,s) = |d_F|^{s-1/2}Z(\Phi_0,1,s)$** for $\operatorname{Re}s>1$. -/
theorem globalZeta_dualPhi {s : ℂ} (hs : 1 < s.re) :
    globalZeta (dualPhi F : Adeles F → ℂ) 1 s =
      (((|(discr F : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)) * globalZeta (dedekindPhi F : Adeles F → ℂ) 1 s := by
  have hs' : 1 < s.re + (1 : HeckeCharacter F).shift := by rw [shift_one, add_zero]; exact hs
  rw [globalZeta_eq_archZeta_mul_finZeta, globalZeta_eq_archZeta_mul_finZeta]
  have h1 := hasProd_finZeta (dualPhi F) 1 hs'
  have h2 := (hasProd_diff_cpow (F := F) s).mul (hasProd_finZeta (dedekindPhi F) 1 hs')
  have heq : (dualPhi F).fv = dualFv := rfl
  rw [h1.unique (by convert h2 using 1; funext v; rw [heq, zetaIntegral_dualFv])]
  change archZeta Analysis.gaussInf 1 s * _ = _ * (archZeta Analysis.gaussInf 1 s * _)
  ring

/-- $C_1 = \prod_v\operatorname{vol}(\mathcal O_v) = |d_F|^{-1/2}$. -/
theorem stdConst_one : stdConst (1 : HeckeCharacter F) = (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
  have h1 := hasProd_stdConstFactor (1 : HeckeCharacter F)
  have h2 := hasProd_volO (F := F)
  rw [muFinUnits_OHatUnits, ENNReal.toReal_ofReal ohatVol_pos.le] at h2
  have h3 : (fun v => (stdConstFactor (1 : HeckeCharacter F) v : ℂ)) = fun v => ((volO v).toReal : ℂ) := by
    funext v; rw [stdConstFactor, if_pos (isUnramifiedAt_one v)]
  rw [h3] at h1
  change stdConst 1 = ohatVol F
  exact_mod_cast h1.unique h2

/-- The Euler factor of $\zeta_F$: $L_v(s,1) = (1-N(v)^{-s})^{-1}$. -/
theorem localL_one (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    localL 1 s v = (1 - (normV v : ℂ) ^ (-s))⁻¹ := by
  rw [localL, if_pos (isUnramifiedAt_one v)]
  congr 2
  show (1 : ℂ) * _ = _
  rw [one_mul]

/-- The archimedean factor $\Gamma_{\mathbb R}(s)^{r_1}(\pi\Gamma_{\mathbb C}(s))^{r_2}$. -/
def gammaInfOne (F : Type) [Field F] [NumberField F] (s : ℂ) : ℂ :=
  Complex.Gammaℝ s ^ nrRealPlaces F * (Real.pi * Complex.Gammaℂ s) ^ nrComplexPlaces F

/-- **$Z(\Phi_0,1,s) = |d_F|^{-1/2}\Gamma_{\mathbb R}(s)^{r_1}(\pi\Gamma_{\mathbb C}(s))^{r_2}L(s,1)$** for
$\operatorname{Re}s>1$. -/
theorem globalZeta_dedekindPhi {s : ℂ} (hs : 1 < s.re) :
    globalZeta (dedekindPhi F : Adeles F → ℂ) 1 s =
      ((Real.sqrt |(discr F : ℝ)|)⁻¹ : ℝ) * gammaInfOne F s * heckeL (1 : HeckeCharacter F) s := by
  have hs' : 1 < s.re + (1 : HeckeCharacter F).shift := by rw [shift_one, add_zero]; exact hs
  rw [dedekindPhi, globalZeta_stdPhi 1 _ hs', archZeta_gaussInf_one (by linarith), stdConst_one, gammaInfOne]
  ring

end

end NumberFieldKB.HeckeL
