import NumberFieldKB.HeckeL.FourierSB

/-!
# The unramified gamma factor at a finite place (Tate's thesis)

$F$ is a number field, $v$ a finite place, $q = N(v)$, $d_v$ the exponent of the different, $\varpi$ a uniformizer, and
$\chi$ a continuous quasi-character of $F_v^\times$ trivial on $\mathcal O_v^\times$ (unramified), $|\chi| = |\cdot|_v^a$.
Tate's thesis (Cassels–Fröhlich Ch. XV, §2.5 [unverified locator]; Weil, *Basic Number Theory*, Ch. VII, §6
formula (7) and §7 Prop. 14 at the unramified places) computes $\rho(c)$ for unramified $c$:
$$Z(\hat f,\chi^{-1},1-s) = N(\mathfrak d_v)^{-1/2}\bigl(\chi(\varpi)q^{1-s}\bigr)^{d_v}\,
\frac{1-\chi(\varpi)q^{-s}}{1-\chi(\varpi)^{-1}q^{-(1-s)}}\,Z(f,\chi,s)$$
for every Schwartz–Bruhat $f$ and $0<a+\operatorname{Re}s<1$ (`zetaIntegral_fourierV_unram`); equivalently
$\gamma_v(\chi,s) = N(\mathfrak d_v)^{-1/2}(\chi(\varpi)q^{1-s})^{d_v}\,L(1-s,\chi^{-1})/L(s,\chi)$ with
$L(s,\chi) = (1-\chi(\varpi)q^{-s})^{-1}$ (`gammaFactorV_unram`). In Tate's language the factor
$N(\mathfrak d_v)^{-1/2}(\chi(\varpi)q^{1-s})^{d_v}$ is the local root number $\varepsilon_v$; it is $1$ when
$v\nmid\mathfrak d_F$.

*Proof* (Tate's): take $g = \mathbf 1_{\mathcal O_v}$ in the local functional equation; $\hat g = \operatorname{vol}(\mathcal O_v)
\mathbf 1_{\mathfrak p_v^{-d_v}}$ (`fourierV_charO`), a scaled copy of $g$, and both zeta integrals of $\mathbf 1_{\mathcal O_v}$
are geometric series (`zetaIntegral_tateHaarV_charO`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Set WithZero
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

theorem isSchwartzBruhatLC_charO (v : HeightOneSpectrum (𝓞 F)) : IsSchwartzBruhatLC v (charO v) := by
  rw [charO_eq_ballIndV]
  exact IsSchwartzBruhatLC.of_isSchwartzBruhatV (isSchwartzBruhatV_ballIndV v 0 0)

/-- $|\chi(\varpi)q^{-s}| < 1$ for $\operatorname{Re}s > -a$, so $1 - \chi(\varpi)q^{-s}\ne0$. -/
theorem one_sub_char_ϖ_ne_zero (v : HeightOneSpectrum (𝓞 F)) {χ : (v.adicCompletion F)ˣ →* ℂˣ} {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar (v.adicCompletion F) u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re) :
    1 - (χ (ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s) ≠ 0 := by
  have hr : ‖(χ (ϖU v) : ℂ) * ((modV v : ℝ) : ℂ) ^ s‖ < 1 := by
    have h1 : ‖(χ (ϖU v) : ℂ)‖ = (modV v : ℝ) ^ a := hχ _
    rw [norm_mul, h1, Complex.norm_cpow_eq_rpow_re_of_pos (modV_pos' v), ← Real.rpow_add (modV_pos' v)]
    exact Real.rpow_lt_one (modV_pos' v).le (modV_lt_one v) hs
  rw [← modV_cpow]
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hr
  exact lt_irrefl _ hr

/-- The dual integral of $\mathbf 1_{\mathcal O_v}$: $Z(\hat{\mathbf 1}_{\mathcal O_v},\chi,s) =
\operatorname{vol}(\mathcal O_v)(\chi(\varpi)^{-1}q^{s})^{d_v}Z(\mathbf 1_{\mathcal O_v},\chi,s)$ (any $\chi$, any $s$). -/
theorem zetaIntegral_fourierV_charO (v : HeightOneSpectrum (𝓞 F)) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) :
    zetaIntegral (tateHaarV v) (fourierV v (charO v)) χ s =
      ((volO v).toReal : ℂ) * (((χ (ϖU v) : ℂ))⁻¹ * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ s) ^ diffExp v *
        zetaIntegral (tateHaarV v) (charO v) χ s := by
  set d := diffExp v
  have h1 : zetaIntegral (tateHaarV v) (fourierV v (charO v)) χ s =
      ((volO v).toReal : ℂ) * zetaIntegral (tateHaarV v)
        (fun x => ballIndV v 0 0 (((ϖU v ^ (d : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x)) χ s := by
    rw [charO_eq_ballIndV, fourierV_charO, zetaIntegral, zetaIntegral, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [zetaIntegrand, ballIndV_neg_eq]
    ring
  rw [h1, zetaIntegral_comp_mul, ← charO_eq_ballIndV]
  have hχ' : ((χ (ϖU v ^ (d : ℤ)) : ℂˣ) : ℂ)⁻¹ = ((χ (ϖU v) : ℂ))⁻¹ ^ d := by
    rw [zpow_natCast, map_pow, Units.val_pow_eq_pow_val, inv_pow]
  have hmod : ((distribHaarChar (v.adicCompletion F) (ϖU v ^ (d : ℤ)) : ℝ) : ℂ) ^ (-s) =
      (((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ s) ^ d := by
    rw [zpow_natCast, distribHaarChar_ϖU_pow, ofReal_pow_cpow (modV_pos' v).le, modV_cpow, neg_neg]
  rw [hχ', hmod, mul_pow]
  ring

/-- **Tate's unramified gamma factor**: for $\chi$ continuous, trivial on $\mathcal O_v^\times$, $|\chi| = |\cdot|_v^a$,
every Schwartz–Bruhat $f$ on $F_v$ and $0<a+\operatorname{Re}s<1$,
$$Z(\hat f,\chi^{-1},1-s) = \operatorname{vol}(\mathcal O_v)\bigl(\chi(\varpi)q^{1-s}\bigr)^{d_v}
\frac{1-\chi(\varpi)q^{-s}}{1-\chi(\varpi)^{-1}q^{-(1-s)}}\,Z(f,\chi,s),\qquad
\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}.$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ρ(c) for unramified c at a finite place)"]
theorem zetaIntegral_fourierV_unram (v : HeightOneSpectrum (𝓞 F)) {f : v.adicCompletion F → ℂ}
    (hf : IsSchwartzBruhatLC v f) {χ : (v.adicCompletion F)ˣ →* ℂˣ} (hχc : Continuous χ)
    (hur : ∀ u ∈ unitsVSub v, χ u = 1) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar (v.adicCompletion F) u : ℝ) ^ a) {s : ℂ}
    (hs0 : 0 < a + s.re) (hs1 : a + s.re < 1) :
    zetaIntegral (tateHaarV v) (fourierV v f) χ⁻¹ (1 - s) =
      ((volO v).toReal : ℂ) * ((χ (ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (1 - s)) ^ diffExp v *
        ((1 - (χ (ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s)) /
          (1 - ((χ (ϖU v) : ℂ))⁻¹ * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-(1 - s)))) *
        zetaIntegral (tateHaarV v) f χ s := by
  set N : ℂ := ((Ideal.absNorm v.asIdeal : ℝ) : ℂ)
  have hs' : 0 < -a + (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have h := zetaIntegral_fourierV_comm v hf (isSchwartzBruhatLC_charO v) hχc hχ hs0 hs1
  have hur' : ∀ u ∈ unitsVSub v, (χ⁻¹) u = 1 := fun u hu => by rw [MonoidHom.inv_apply, hur u hu, inv_one]
  have hZg := zetaIntegral_tateHaarV_charO v hχc hur hχ hs0
  have hZi := zetaIntegral_tateHaarV_charO v (continuous_inv_char v hχc) hur' (norm_inv_apply v hχ) hs'
  have hinvϖ : ((χ⁻¹ (ϖU v) : ℂˣ) : ℂ) = ((χ (ϖU v) : ℂ))⁻¹ := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rw [hinvϖ] at hZi
  rw [zetaIntegral_fourierV_charO, hZi, hinvϖ, inv_inv] at h
  rw [hZg] at h
  have hV : ((((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (pow_pos (by exact_mod_cast normV_pos v) _) _
    exact_mod_cast this.ne'
  have hD := one_sub_char_ϖ_ne_zero v hχ hs0
  generalize ((((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) = W at h hV
  generalize 1 - (χ (ϖU v) : ℂ) * N ^ (-s) = D1 at h hD ⊢
  generalize 1 - ((χ (ϖU v) : ℂ))⁻¹ * N ^ (-(1 - s)) = D2 at h ⊢
  generalize zetaIntegral (tateHaarV v) (fourierV v f) χ⁻¹ (1 - s) = Zh at h ⊢
  have h' : Zh = D1 / W * (W / D1 * Zh) := by field_simp
  rw [h', ← h]
  field_simp
  rfl

/-- **The unramified gamma factor**: $\gamma_v(\chi,s) = N(\mathfrak d_v)^{-1/2}(\chi(\varpi)q^{1-s})^{d_v}
\dfrac{1-\chi(\varpi)q^{-s}}{1-\chi(\varpi)^{-1}q^{-(1-s)}} = \varepsilon_v\,\dfrac{L(1-s,\chi^{-1})}{L(s,\chi)}$ for
$0<a+\operatorname{Re}s<1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ρ(c) for unramified c at a finite place)"]
theorem gammaFactorV_unram (v : HeightOneSpectrum (𝓞 F)) {χ : (v.adicCompletion F)ˣ →* ℂˣ} (hχc : Continuous χ)
    (hur : ∀ u ∈ unitsVSub v, χ u = 1) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar (v.adicCompletion F) u : ℝ) ^ a) {s : ℂ}
    (hs0 : 0 < a + s.re) (hs1 : a + s.re < 1) :
    gammaFactorV v hχc s =
      ((volO v).toReal : ℂ) * ((χ (ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (1 - s)) ^ diffExp v *
        ((1 - (χ (ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s)) /
          (1 - ((χ (ϖU v) : ℂ))⁻¹ * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-(1 - s)))) := by
  have h1 := zetaIntegral_fourierV_eq_gammaFactorV v (isSchwartzBruhatLC_charO v) hχc hχ hs0 hs1
  rw [zetaIntegral_fourierV_unram v (isSchwartzBruhatLC_charO v) hχc hur hχ hs0 hs1] at h1
  have hZ : zetaIntegral (tateHaarV v) (charO v) χ s ≠ 0 := by
    rw [zetaIntegral_tateHaarV_charO v hχc hur hχ hs0]
    refine div_ne_zero ?_ (one_sub_char_ϖ_ne_zero v hχ hs0)
    have : 0 < ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (pow_pos (by exact_mod_cast normV_pos v) _) _
    exact_mod_cast this.ne'
  exact (mul_right_cancel₀ hZ h1).symm

end

end NumberFieldKB.HeckeL
