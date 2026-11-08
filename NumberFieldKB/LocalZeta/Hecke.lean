import NumberFieldKB.LocalZeta.NonArchimedean

/-!
# Local zeta integrals of the components of a Hecke character

For a Hecke character $\chi$ of a number field $F$ (`HeckeCharacter F`) with shift $\sigma$
($|\chi| = \|\cdot\|^\sigma$) and a finite place $v$, the component $\chi_v$ = `χ.finiteComponent v` satisfies
$|\chi_v| = |\cdot|_v^\sigma$ (`norm_finiteComponent_eq_rpow`), so the results of `NonArchimedean.lean` apply:

* **`zetaIntegral_finiteComponent_charO`**: if $\chi$ is unramified at $v$ and $\operatorname{Re}s > -\sigma$,
  $$Z(\mathbf 1_{\mathcal O_v},\chi_v,s) = \frac{N(\mathfrak d_v)^{-1/2}}{1-\chi_v(\varpi_v)N(v)^{-s}},$$
  the Euler factor of the Hecke $L$-function times $N(\mathfrak d_v)^{-1/2}$;
* **`zetaIntegral_fourierV_finiteComponent`**: the local functional equation
  $Z(\hat f,\chi_v^{-1},1-s) = \gamma_v(\chi_v,s)Z(f,\chi_v,s)$ for every Schwartz–Bruhat $f$ and
  $0 < \sigma + \operatorname{Re}s < 1$.
-/

open IsDedekindDomain NumberField MeasureTheory
open QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.LocalZeta

namespace NumberFieldKB.HeckeCharacter

noncomputable section

variable {F : Type} [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))

/-- $|\chi_v(u)| = |u|_v^\sigma$ with $|\cdot|_v$ the modulus of $F_v$. -/
theorem norm_finiteComponent_eq_rpow (u : (v.adicCompletion F)ˣ) :
    ‖(χ.finiteComponent v u : ℂ)‖ = (distribHaarChar (v.adicCompletion F) u : ℝ) ^ χ.shift := by
  rw [norm_finiteComponent_apply, Ideles.distribHaarChar_adicCompletion]

/-- **The unramified local zeta integral of a Hecke character** (Tate, Cassels–Fröhlich Ch. XV, §2.5 and §3.3): at a
finite place $v$ where $\chi$ is unramified, for $\operatorname{Re}s > -\sigma$,
$Z(\mathbf 1_{\mathcal O_v},\chi_v,s) = N(\mathfrak d_v)^{-1/2}(1-\chi_v(\varpi_v)N(v)^{-s})^{-1}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 and §3.3 [unverified locators] (the unramified local factor)"]
theorem zetaIntegral_finiteComponent_charO (hχ : χ.IsUnramifiedAt v) {s : ℂ} (hs : 0 < χ.shift + s.re) :
    zetaIntegral (tateHaarV v) (charO v) (χ.finiteComponent v).toMonoidHom s =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2) : ℝ) /
        (1 - (χ.finiteComponent v (ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s)) :=
  zetaIntegral_tateHaarV_charO v (χ.finiteComponent v).continuous (fun u hu => hχ u hu)
    (norm_finiteComponent_eq_rpow χ v) hs

/-- **The local functional equation for the component of a Hecke character** at a finite place: for every
Schwartz–Bruhat $f$ on $F_v$ and $0 < \sigma + \operatorname{Re}s < 1$,
$Z(\hat f,\chi_v^{-1},1-s) = \gamma_v(\chi_v,s)\,Z(f,\chi_v,s)$. -/
theorem zetaIntegral_fourierV_finiteComponent {f : v.adicCompletion F → ℂ} (hf : IsSchwartzBruhatLC v f) {s : ℂ}
    (hs0 : 0 < χ.shift + s.re) (hs1 : χ.shift + s.re < 1) :
    zetaIntegral (tateHaarV v) (fourierV v f) (χ.finiteComponent v).toMonoidHom⁻¹ (1 - s) =
      gammaFactorV v (χ.finiteComponent v).continuous s *
        zetaIntegral (tateHaarV v) f (χ.finiteComponent v).toMonoidHom s :=
  zetaIntegral_fourierV_eq_gammaFactorV v hf (χ.finiteComponent v).continuous (norm_finiteComponent_eq_rpow χ v)
    hs0 hs1

end

end NumberFieldKB.HeckeCharacter
