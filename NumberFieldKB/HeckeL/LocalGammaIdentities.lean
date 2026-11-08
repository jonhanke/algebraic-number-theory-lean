import NumberFieldKB.HeckeL.RootNumber

/-!
# Tate's local identities for the gamma factor, and the absolute value of the local root number

$F$ is a number field, $v$ a finite place, $\chi$ a continuous quasi-character of $F_v^\times$ with
$|\chi| = |\cdot|_v^a$, and $\gamma_v(\chi,s)$ the factor of the local functional equation
$Z(\hat f,\chi^{-1},1-s) = \gamma_v(\chi,s)Z(f,\chi,s)$ (`LocalZeta.gammaFactorV`, Tate's $\rho(c)$). Tate's thesis
(Cassels–Fröhlich Ch. XV, §2.4 [unverified locator]) derives from Fourier inversion $\hat{\hat f}(x) = f(-x)$:

* **`gammaFactorV_mul_inv`**: $\gamma_v(\chi,s)\,\gamma_v(\chi^{-1},1-s) = \chi(-1)$ ($0<a+\operatorname{Re}s<1$);
* **`gammaFactorV_conj`**: $\gamma_v(\bar\chi,\bar s) = \chi(-1)\,\overline{\gamma_v(\chi,s)}$;
* **`norm_gammaFactorV`**: for unitary $\chi$ and $\operatorname{Re}s = \tfrac12$, $|\gamma_v(\chi,s)| = 1$.

For a Hecke character $\chi$ ramified at $v$, with conductor exponent $a_v\ge1$ and different exponent $d_v$, the
ramified computation (`zetaIntegral_fourierV_ram`) gives
$\gamma_v(\chi_v,s) = N(v)^{(a_v+d_v)(1-s)}\varepsilon_v(\chi)/\operatorname{vol}^\times(U_v^{(a_v)})$
(`gammaFactorV_ram`), and so, for unitary $\chi$, **the local absolute value of Tate's root-number integral**
(`norm_epsLocal`):
$$|\varepsilon_v(\chi)| = \operatorname{vol}^\times(U_v^{(a_v)})\,N(v)^{-(a_v+d_v)/2}.$$
This is Weil's $\kappa_v\bar\kappa_v = 1$ (*Basic Number Theory*, Ch. VII, §7 Prop. 13) in Tate's normalization;
the global root number satisfies $|W(\chi)| = 1$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Set WithZero
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil
open scoped ComplexConjugate

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

open GlobalZeta LocalZeta

/-! ### Fourier inversion and the reflection $x\mapsto -x$ -/

/-- **$\hat{\hat f}(y) = f(-y)$** for a Schwartz–Bruhat function (QuadFormsKB's Fourier inversion). -/
theorem fourierV_fourierV {f : Fv → ℂ} (hf : IsSchwartzBruhatLC v f) (y : Fv) :
    fourierV v (fourierV v f) y = f (-y) := by
  have h := congrFun (fourierInvV_fourierV_of_isSchwartzBruhat v (isSchwartzBruhatV_of_isSchwartzBruhatLC hf)) (-y)
  rw [← h, fourierInvV, fourierV]
  simp only [neg_mul, neg_neg]
  congr 1
  funext x
  rw [mul_comm x y]

/-- $\chi(-1)^2 = 1$. -/
theorem char_neg_one_sq (χ : Fvˣ →* ℂˣ) : ((χ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow]
  simp

theorem char_neg_one_inv (χ : Fvˣ →* ℂˣ) : ((χ (-1) : ℂˣ) : ℂ)⁻¹ = χ (-1) := by
  have h := char_neg_one_sq v χ
  have h' : ((χ (-1) : ℂˣ) : ℂ) * χ (-1) = 1 := by rw [← sq]; exact h
  exact inv_eq_of_mul_eq_one_right h'

theorem conj_char_neg_one (χ : Fvˣ →* ℂˣ) : conj ((χ (-1) : ℂˣ) : ℂ) = χ (-1) := by
  have h := char_neg_one_sq v χ
  have : ((χ (-1) : ℂˣ) : ℂ) = 1 ∨ ((χ (-1) : ℂˣ) : ℂ) = -1 := by
    have : (((χ (-1) : ℂˣ) : ℂ) - 1) * (((χ (-1) : ℂˣ) : ℂ) + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  rcases this with h1 | h1 <;> rw [h1] <;> simp

/-- **Reflection**: $Z(f(-\,\cdot),\chi,s) = \chi(-1)Z(f,\chi,s)$. -/
theorem zetaIntegral_comp_neg (μ : Measure Fvˣ) [μ.IsMulLeftInvariant] (f : Fv → ℂ) (χ : Fvˣ →* ℂˣ) (s : ℂ) :
    zetaIntegral μ (fun x => f (-x)) χ s = χ (-1) * zetaIntegral μ f χ s := by
  have h := zetaIntegral_comp_mul μ f χ s (-1)
  have hmod : distribHaarChar Fv (-1 : Fvˣ) = 1 :=
    distribHaarChar_eq_one_of_mem_unitsVSub
      (show Valued.v ((-1 : Fvˣ) : Fv) = 1 by rw [Units.val_neg, Units.val_one, Valuation.map_neg, map_one])
  simp only [Units.val_neg, Units.val_one, neg_one_mul, hmod, NNReal.coe_one, Complex.ofReal_one,
    Complex.one_cpow, mul_one] at h
  rw [h, char_neg_one_inv]

/-! ### $\gamma_v(\chi,s)\gamma_v(\chi^{-1},1-s) = \chi(-1)$ -/

theorem gammaFactorV_congr {χ χ' : Fvˣ →* ℂˣ} (h : χ = χ') (hχc : Continuous χ) (hχc' : Continuous χ') (s : ℂ) :
    gammaFactorV v hχc s = gammaFactorV v hχc' s := by
  subst h; rfl

/-- The level test function $\mathbf 1_{1+\mathfrak p_v^m}$ of `gammaFactorV`: Schwartz–Bruhat, and its zeta integral
is $\operatorname{vol}^\times(U_v^{(m)})\ne0$. -/
theorem gammaLevel_spec {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) (s : ℂ) :
    IsSchwartzBruhatLC v (ballIndV v 1 (gammaLevel v hχc)) ∧
      zetaIntegral (tateHaarV v) (ballIndV v 1 (gammaLevel v hχc)) χ s =
        (tateHaarV v (unitFiltration v (gammaLevel v hχc))).toReal ∧
      (tateHaarV v (unitFiltration v (gammaLevel v hχc))).toReal ≠ 0 := by
  have hm : 1 ≤ gammaLevel v hχc := (exists_unitFiltration_eq_one v hχc).choose_spec.1
  have hχm : ∀ u ∈ unitFiltration v (gammaLevel v hχc), χ u = 1 :=
    (exists_unitFiltration_eq_one v hχc).choose_spec.2
  refine ⟨IsSchwartzBruhatLC.of_isSchwartzBruhatV ⟨1, fun _ => 1, fun _ => 1, fun _ => gammaLevel v hχc,
    by funext x; simp⟩, zetaIntegral_ballIndV_one v hm hχm _ s, ?_⟩
  exact (ENNReal.toReal_pos (tateHaarV_unitFiltration_pos v hm).ne'
    (tateHaarV_unitFiltration_lt_top v _).ne).ne'

/-- **Tate's identity** $\gamma_v(\chi,s)\,\gamma_v(\chi^{-1},1-s) = \chi(-1)$ for $0<a+\operatorname{Re}s<1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4 [unverified locator] (ρ(c)ρ(ĉ) = c(−1))"]
theorem gammaFactorV_mul_inv {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) {s : ℂ} (hs0 : 0 < a + s.re) (hs1 : a + s.re < 1) :
    gammaFactorV v hχc s * gammaFactorV v (continuous_inv_char v hχc) (1 - s) = χ (-1) := by
  obtain ⟨hf0, hZ0, hne⟩ := gammaLevel_spec v hχc s
  set f0 := ballIndV v 1 (gammaLevel v hχc)
  have hs0' : 0 < -a + (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hs1' : -a + (1 - s).re < 1 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have h1 := zetaIntegral_fourierV_eq_gammaFactorV v hf0 hχc hχ hs0 hs1
  have h2 := zetaIntegral_fourierV_eq_gammaFactorV v hf0.fourierV (continuous_inv_char v hχc)
    (norm_inv_apply v hχ) hs0' hs1'
  have hinv : χ⁻¹⁻¹ = χ := by ext u; simp
  rw [hinv, sub_sub_cancel, h1] at h2
  have h3 : zetaIntegral (tateHaarV v) (fourierV v (fourierV v f0)) χ s = χ (-1) * zetaIntegral (tateHaarV v) f0 χ s := by
    rw [← zetaIntegral_comp_neg]
    congr 1
    funext x
    exact fourierV_fourierV v hf0 x
  rw [h3, hZ0] at h2
  have hne' : ((tateHaarV v (unitFiltration v (gammaLevel v hχc))).toReal : ℂ) ≠ 0 := by exact_mod_cast hne
  have key : (gammaFactorV v hχc s * gammaFactorV v (continuous_inv_char v hχc) (1 - s)) *
      ((tateHaarV v (unitFiltration v (gammaLevel v hχc))).toReal : ℂ) =
      χ (-1) * ((tateHaarV v (unitFiltration v (gammaLevel v hχc))).toReal : ℂ) := by
    linear_combination h2.symm
  exact mul_right_cancel₀ hne' key

/-! ### Complex conjugation -/

/-- The complex conjugate $\bar\chi$ of a quasi-character. -/
def conjChar (χ : Fvˣ →* ℂˣ) : Fvˣ →* ℂˣ := (Units.map (starRingEnd ℂ).toMonoidHom).comp χ

theorem conjChar_apply (χ : Fvˣ →* ℂˣ) (u : Fvˣ) : ((conjChar v χ u : ℂˣ) : ℂ) = conj ((χ u : ℂˣ) : ℂ) := rfl

theorem continuous_conjChar {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) : Continuous (conjChar v χ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Complex.continuous_conj.comp (Units.continuous_val.comp hχc)
  · have : (fun u => ((conjChar v χ u)⁻¹ : ℂˣ).val) = fun u => conj (((χ u)⁻¹ : ℂˣ) : ℂ) := by
      funext u
      simp only [Units.val_inv_eq_inv_val, conjChar_apply, map_inv₀]
    show Continuous (fun u => ((conjChar v χ u)⁻¹ : ℂˣ).val)
    rw [this]
    exact Complex.continuous_conj.comp (Units.continuous_val.comp (hχc.inv))

theorem norm_conjChar {χ : Fvˣ →* ℂˣ} {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) (u : Fvˣ) :
    ‖(conjChar v χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a := by
  rw [conjChar_apply, Complex.norm_conj, hχ]

/-- $\overline{Z(f,\chi,s)} = Z(\bar f,\bar\chi,\bar s)$. -/
theorem conj_zetaIntegral (μ : Measure Fvˣ) (f : Fv → ℂ) (χ : Fvˣ →* ℂˣ) (s : ℂ) :
    conj (zetaIntegral μ f χ s) = zetaIntegral μ (fun x => conj (f x)) (conjChar v χ) (conj s) := by
  rw [zetaIntegral, ← integral_conj, zetaIntegral]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [zetaIntegrand, map_mul, conjChar_apply]
  rw [conj_ofReal_cpow (distribHaarChar_pos' u)]

/-- $\overline{\hat f(y)} = \hat{\bar f}(-y)$. -/
theorem conj_fourierV (f : Fv → ℂ) (y : Fv) :
    conj (fourierV v f y) = fourierV v (fun x => conj (f x)) (-y) := by
  rw [fourierV, ← integral_conj, fourierV]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul, mul_neg, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem conjChar_inv (χ : Fvˣ →* ℂˣ) : conjChar v χ⁻¹ = (conjChar v χ)⁻¹ := by
  ext u
  simp only [conjChar_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]

/-- **Conjugation**: $\gamma_v(\bar\chi,\bar s) = \chi(-1)\,\overline{\gamma_v(\chi,s)}$ for $0<a+\operatorname{Re}s<1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4 [unverified locator] (ρ(c̄) = c(−1) conj ρ(c))"]
theorem gammaFactorV_conj {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) {s : ℂ} (hs0 : 0 < a + s.re) (hs1 : a + s.re < 1) :
    gammaFactorV v (continuous_conjChar v hχc) (conj s) = χ (-1) * conj (gammaFactorV v hχc s) := by
  obtain ⟨hf0, hZ0, hne⟩ := gammaLevel_spec v hχc s
  set f0 := ballIndV v 1 (gammaLevel v hχc)
  have hreal : (fun x => conj (f0 x)) = f0 := by
    funext x
    simp only [f0, ballIndV, Set.indicator_apply]
    split_ifs <;> simp
  have hcs0 : 0 < a + (conj s).re := by rwa [Complex.conj_re]
  have hcs1 : a + (conj s).re < 1 := by rwa [Complex.conj_re]
  have h1 := zetaIntegral_fourierV_eq_gammaFactorV v hf0 hχc hχ hs0 hs1
  have h2 := zetaIntegral_fourierV_eq_gammaFactorV v hf0 (continuous_conjChar v hχc) (norm_conjChar v hχ) hcs0 hcs1
  -- the zeta integral of f0 against the conjugate character
  have hZc : zetaIntegral (tateHaarV v) f0 (conjChar v χ) (conj s) =
      conj (zetaIntegral (tateHaarV v) f0 χ s) := by
    rw [conj_zetaIntegral, hreal]
  -- the dual side
  have hF : zetaIntegral (tateHaarV v) (fourierV v f0) (conjChar v χ)⁻¹ (1 - conj s) =
      conj (χ (-1) * zetaIntegral (tateHaarV v) (fourierV v f0) χ⁻¹ (1 - s)) := by
    have hχinv : ((χ⁻¹ (-1) : ℂˣ) : ℂ) = χ (-1) := by
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, char_neg_one_inv]
    rw [← hχinv, ← zetaIntegral_comp_neg, conj_zetaIntegral, ← conjChar_inv, map_sub, map_one]
    congr 1
    funext x
    rw [conj_fourierV, hreal, neg_neg]
  rw [hF, hZc, h1, map_mul, map_mul, conj_char_neg_one] at h2
  have hne' : conj ((tateHaarV v (unitFiltration v (gammaLevel v hχc))).toReal : ℂ) ≠ 0 := by
    rw [Complex.conj_ofReal]; exact_mod_cast hne
  rw [hZ0] at h2
  have key : gammaFactorV v (continuous_conjChar v hχc) (conj s) *
      conj ((tateHaarV v (unitFiltration v (gammaLevel v hχc))).toReal : ℂ) =
      (χ (-1) * conj (gammaFactorV v hχc s)) *
        conj ((tateHaarV v (unitFiltration v (gammaLevel v hχc))).toReal : ℂ) := by
    linear_combination -h2
  exact mul_right_cancel₀ hne' key

/-- **$|\gamma_v(\chi,s)| = 1$ for unitary $\chi$ on $\operatorname{Re}s = \tfrac12$.** -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4 [unverified locator] (|ρ(c)| = 1 for unitary c on the critical line)"]
theorem norm_gammaFactorV {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) (hχ : ∀ u, ‖(χ u : ℂ)‖ = 1) {s : ℂ}
    (hs : s.re = 1 / 2) : ‖gammaFactorV v hχc s‖ = 1 := by
  have hχa : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ (0 : ℝ) := fun u => by rw [hχ, Real.rpow_zero]
  have hs0 : 0 < 0 + s.re := by rw [hs]; norm_num
  have hs1 : 0 + s.re < 1 := by rw [hs]; norm_num
  have hm := gammaFactorV_mul_inv v hχc hχa hs0 hs1
  have hc := gammaFactorV_conj v hχc hχa hs0 hs1
  have hconj : conjChar v χ = χ⁻¹ := by
    ext u
    rw [conjChar_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact conj_eq_inv_of_norm_eq_one (hχ u)
  have hs' : conj s = 1 - s := by
    apply Complex.ext
    · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re, hs]; norm_num
    · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]; ring
  rw [gammaFactorV_congr v hconj _ (continuous_inv_char v hχc), hs'] at hc
  rw [hc, ← mul_assoc, mul_comm _ ((χ (-1) : ℂˣ) : ℂ), mul_assoc, Complex.mul_conj] at hm
  have h0 : ((χ (-1) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (Complex.normSq (gammaFactorV v hχc s) : ℂ) = 1 := by
    have := mul_left_cancel₀ h0 (hm.trans (mul_one _).symm)
    exact this
  have h3 : Complex.normSq (gammaFactorV v hχc s) = 1 := by exact_mod_cast h2
  rw [Complex.normSq_eq_norm_sq] at h3
  have hn := norm_nonneg (gammaFactorV v hχc s)
  nlinarith

/-! ### Ramified Hecke components: the local absolute value of $\varepsilon_v(\chi)$ -/

theorem finiteComponent_inv_eq (χ : HeckeCharacter F) :
    ((χ⁻¹).finiteComponent v).toMonoidHom = ((χ.finiteComponent v).toMonoidHom)⁻¹ := by
  ext u
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact inv_finiteComponent χ v u

/-- **The ramified gamma factor of a Hecke character**: if $\chi$ is ramified at $v$ (conductor exponent $a_v$) and
$0<\sigma+\operatorname{Re}s<1$, then
$\gamma_v(\chi_v,s)\operatorname{vol}^\times(U_v^{(a_v)}) = N(v)^{(a_v+d_v)(1-s)}\,\varepsilon_v(\chi)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ρ(c) for ramified c, a Gauss sum)"]
theorem gammaFactorV_ram (χ : HeckeCharacter F) (hχ : ¬ χ.IsUnramifiedAt v) {s : ℂ}
    (hs0 : 0 < χ.shift + s.re) (hs1 : χ.shift + s.re < 1) :
    gammaFactorV v (χ.finiteComponent v).continuous s *
        (tateHaarV v (unitFiltration v (χ.conductorExponent v))).toReal =
      (((normV v ^ (χ.conductorExponent v + diffExp v) : ℝ)) : ℂ) ^ (1 - s) * epsLocal χ v := by
  set n := χ.conductorExponent v
  have hn : 1 ≤ n := conductorExponent_pos hχ
  have hχn : ∀ u ∈ unitFiltration v n, (χ.finiteComponent v).toMonoidHom u = 1 :=
    (χ.conductorExponent_le_iff v n).mp le_rfl
  have hf : IsSchwartzBruhatLC v (ballIndV v 1 n) :=
    IsSchwartzBruhatLC.of_isSchwartzBruhatV (isSchwartzBruhatV_ballIndV v 1 n)
  have h1 := zetaIntegral_fourierV_eq_gammaFactorV v hf (χ.finiteComponent v).continuous
    (HeckeCharacter.norm_finiteComponent_eq_rpow χ v) hs0 hs1
  rw [zetaIntegral_ballIndV_one v hn hχn, ← finiteComponent_inv_eq,
    zetaIntegral_fourierV_ram χ hχ (by rw [Complex.sub_re, Complex.one_re]; linarith)] at h1
  exact h1.symm

/-- **The local absolute value of Tate's root-number integral**: for a unitary Hecke character $\chi$ ramified at
$v$, $|\varepsilon_v(\chi)| = \operatorname{vol}^\times(U_v^{(a_v)})\,N(v)^{-(a_v+d_v)/2}$. -/
@[kb "weil1973" "Ch. VII, §7, Prop. 13 (κ κ̄ = 1 for the Gaussian sum of a ramified character)"]
theorem norm_epsLocal (χ : HeckeCharacter F) (hχu : χ.IsUnitary) (hχ : ¬ χ.IsUnramifiedAt v) :
    ‖epsLocal χ v‖ = (tateHaarV v (unitFiltration v (χ.conductorExponent v))).toReal *
      (normV v ^ (χ.conductorExponent v + diffExp v)) ^ (-(1 / 2 : ℝ)) := by
  have hσ : χ.shift = 0 := (χ.shift_eq_zero_iff).mpr hχu
  set s : ℂ := 1 / 2
  have hsre : s.re = 1 / 2 := by simp [s]
  have hs0 : 0 < χ.shift + s.re := by rw [hσ, hsre]; norm_num
  have hs1 : χ.shift + s.re < 1 := by rw [hσ, hsre]; norm_num
  have h := gammaFactorV_ram v χ hχ hs0 hs1
  have hu : ∀ u, ‖((χ.finiteComponent v).toMonoidHom u : ℂ)‖ = 1 := fun u => by
    have := HeckeCharacter.norm_finiteComponent_eq_rpow χ v u
    rw [hσ, Real.rpow_zero] at this
    exact this
  have hg := norm_gammaFactorV v (χ.finiteComponent v).continuous hu hsre
  set N : ℝ := normV v ^ (χ.conductorExponent v + diffExp v)
  have hN : 0 < N := pow_pos (normV_pos v) _
  have hnorm := congrArg norm h
  rw [norm_mul, norm_mul, hg, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, Complex.norm_cpow_eq_rpow_re_of_pos hN] at hnorm
  have hre : (1 - s).re = 1 / 2 := by simp [s]; norm_num
  rw [hre] at hnorm
  have hpos : 0 < N ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hN _
  rw [Real.rpow_neg hN.le, hnorm]
  field_simp

end

end NumberFieldKB.HeckeL
