import NumberFieldKB.HeckeCharacter.Basic
import NumberFieldKB.Ideles.Measure
import NumberFieldKB.LocalZeta.NonArchimedean
import QuadFormsKB.Tamagawa.Measure.Weil.AdditivePoisson
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleMeasures
import QuadFormsKB.Weil.Archimedean

/-!
# The global zeta integral: definitions

$F$ is a number field, $\mathbb A_F = F_\infty\times\mathbb A_f$ QuadFormsKB's adeles (`Adeles F`, with
$F_\infty$ = `mixedSpace F` $=\mathbb R^{r_1}\times\mathbb C^{r_2}$), $\mathbb A_F^\times$ = `(Adeles F)ˣ` with Tate's
measure $d^\times x$ = `tamIdeles F` (see the `Ideles` directory), and $\|x\|$ = `ideleNorm F x`.

* **`HeckeCharacter.onIdeles χ`**: a Hecke character (a character of Mathlib's idele class group) as a
  character of $\mathbb A_F^\times$, through the isomorphism `ideleGroupEquiv F`; it is continuous
  (`continuous_onIdeles`), trivial on $F^\times$ (`onIdeles_diagUnits`), and $|\chi(x)| = \|x\|^\sigma$ with $\sigma$ the
  shift (`norm_onIdeles`).
* **`SchwartzBruhat F`**: the factorizable Schwartz–Bruhat functions $\Phi = f_\infty\otimes\bigotimes_v f_v$ on
  $\mathbb A_F$: $f_\infty$ a Schwartz function on $F_\infty$, $f_v$ a finite combination of indicators of cosets
  $c+\mathfrak p_v^k$ (QuadFormsKB's `IsSchwartzBruhatV`), and $f_v = \mathbf 1_{\mathcal O_v}$ outside a finite set of
  places. These are the functions of QuadFormsKB's adelic Poisson summation (`adelicPoisson_smul`). Their Fourier
  transform (`SchwartzBruhat.fourier`) is $\hat\Phi = \hat f_\infty\otimes\bigotimes_v\hat f_v$, for QuadFormsKB's
  self-dual measures and standard characters.
* **`globalZeta Φ χ s`** $= Z(\Phi,\chi,s) = \int_{\mathbb A_F^\times}\Phi(x)\chi(x)\|x\|^s\,d^\times x$.

Tate's thesis, Cassels–Fröhlich Ch. XV, §§3–4 [unverified locators]; Ramakrishnan–Valenza, *Fourier Analysis on
Number Fields*, Ch. 7 [unverified].
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal

namespace NumberFieldKB

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "V" => mixedSpace F

open Ideles

/-! ### Hecke characters on QuadFormsKB's ideles -/

namespace HeckeCharacter

/-- **A Hecke character as a character of $\mathbb A_F^\times$** (QuadFormsKB's ideles): $x\mapsto\chi(\text{class of }x)$,
through the isomorphism `ideleGroupEquiv F` with Mathlib's ideles. -/
def onIdeles (χ : HeckeCharacter F) : (Adeles F)ˣ →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
    ((ideleGroupEquiv F).symm : (Adeles F)ˣ →* IdeleGroup (𝓞 F) F))

theorem onIdeles_apply (χ : HeckeCharacter F) (g : (Adeles F)ˣ) :
    χ.onIdeles g = χ (((ideleGroupEquiv F).symm g : IdeleGroup (𝓞 F) F) : IdeleClassGroup (𝓞 F) F) := rfl

theorem continuous_onIdeles (χ : HeckeCharacter F) : Continuous χ.onIdeles :=
  χ.continuous.comp (QuotientGroup.continuous_mk.comp (ideleGroupEquiv F).symm.continuous)

theorem continuous_coe_onIdeles (χ : HeckeCharacter F) : Continuous fun g => (χ.onIdeles g : ℂ) :=
  Units.continuous_val.comp χ.continuous_onIdeles

/-- **A Hecke character is trivial on $F^\times$.** -/
theorem onIdeles_diagUnits (χ : HeckeCharacter F) (ξ : Fˣ) : χ.onIdeles (diagUnits F ξ) = 1 := by
  rw [onIdeles_apply, ← ideleGroupEquiv_unitEmbedding, ContinuousMulEquiv.symm_apply_apply]
  have h : ((IdeleGroup.unitEmbedding (𝓞 F) F ξ : IdeleGroup (𝓞 F) F) : IdeleClassGroup (𝓞 F) F) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (show _ ∈ (IdeleGroup.unitEmbedding (𝓞 F) F).range from ⟨ξ, rfl⟩)
  rw [h, map_one]

theorem onIdeles_diagUnits_mul (χ : HeckeCharacter F) (ξ : Fˣ) (g : (Adeles F)ˣ) :
    χ.onIdeles (diagUnits F ξ * g) = χ.onIdeles g := by
  rw [map_mul, onIdeles_diagUnits, one_mul]

theorem coe_ideleClassNorm_mk_symm (g : (Adeles F)ˣ) :
    (ideleClassNorm F (((ideleGroupEquiv F).symm g : IdeleGroup (𝓞 F) F) : IdeleClassGroup (𝓞 F) F) : ℝ) =
      ideleNorm F g := by
  rw [ideleClassNorm_mk, coe_ideleGroupNorm, norm_eq_ideleNorm, ContinuousMulEquiv.apply_symm_apply]

/-- **$|\chi(x)| = \|x\|^\sigma$** on $\mathbb A_F^\times$, $\sigma$ the shift of $\chi$. -/
theorem norm_onIdeles (χ : HeckeCharacter F) (g : (Adeles F)ˣ) :
    ‖(χ.onIdeles g : ℂ)‖ = ideleNorm F g ^ χ.shift := by
  rw [onIdeles_apply, norm_apply_eq_rpow_shift, coe_ideleClassNorm_mk_symm]

theorem norm_onIdeles_of_isUnitary {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (g : (Adeles F)ˣ) :
    ‖(χ.onIdeles g : ℂ)‖ = 1 :=
  hχ _

theorem normPow_onIdeles (s : ℂ) (g : (Adeles F)ˣ) :
    ((normPow F s).onIdeles g : ℂ) = (ideleNorm F g : ℂ) ^ s := by
  rw [onIdeles_apply, normPow_apply, coe_ideleClassNorm_mk_symm]

@[simp] theorem one_onIdeles (g : (Adeles F)ˣ) : (1 : HeckeCharacter F).onIdeles g = 1 := rfl

theorem inv_onIdeles (χ : HeckeCharacter F) (g : (Adeles F)ˣ) :
    ((χ⁻¹).onIdeles g : ℂ) = (χ.onIdeles g : ℂ)⁻¹ := by
  show (((χ.onIdeles g)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val]

theorem mul_onIdeles (χ ψ : HeckeCharacter F) (g : (Adeles F)ˣ) :
    ((χ * ψ).onIdeles g : ℂ) = (χ.onIdeles g : ℂ) * (ψ.onIdeles g : ℂ) := by
  rw [onIdeles_apply, onIdeles_apply, onIdeles_apply, ContinuousMonoidHom.mul_apply, Units.val_mul]

end HeckeCharacter

/-! ### Factorizable Schwartz–Bruhat functions on the adeles -/

/-- **A factorizable Schwartz–Bruhat function** $\Phi = f_\infty\otimes\bigotimes_v f_v$ on $\mathbb A_F$: $f_\infty$ Schwartz
on $F_\infty$, each $f_v$ a finite combination of coset indicators (QuadFormsKB's `IsSchwartzBruhatV`), and
$f_v = \mathbf 1_{\mathcal O_v}$ (`ballIndV v 0 0`) for $v$ outside the finite set $S$ (Tate's restricted tensor product). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.2 [unverified locator] (the class 𝔅 of functions on the adeles; f = ∏ f_p)"]
structure SchwartzBruhat (F : Type) [Field F] [NumberField F] where
  /-- The archimedean component, a Schwartz function on $F_\infty$. -/
  fInf : SchwartzMap (mixedSpace F) ℂ
  /-- The finite components. -/
  fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ
  /-- The finite set of places where $f_v$ may differ from $\mathbf 1_{\mathcal O_v}$. -/
  S : Finset (HeightOneSpectrum (𝓞 F))
  isSchwartzBruhat : ∀ v ∈ S, Analysis.IsSchwartzBruhatV v (fv v)
  eq_charO : ∀ v ∉ S, fv v = Analysis.ballIndV v 0 0

namespace SchwartzBruhat

variable (Φ : SchwartzBruhat F)

/-- The finite part $x_f\mapsto\prod_v f_v(x_v)$ (a finite product: $x_v\in\mathcal O_v$ for almost every $v$). -/
def finPartFun (x : AF) : ℂ := ∏ᶠ v, Φ.fv v (x v)

/-- **The function $\Phi(x) = f_\infty(x_\infty)\prod_v f_v(x_v)$ on $\mathbb A_F$.** -/
def toFun (x : Adeles F) : ℂ := Φ.fInf x.1 * Φ.finPartFun x.2

instance : CoeFun (SchwartzBruhat F) fun _ => Adeles F → ℂ := ⟨toFun⟩

theorem apply (x : Adeles F) : Φ x = Φ.fInf x.1 * ∏ᶠ v, Φ.fv v (x.2 v) := rfl

/-- The Fourier transform of the archimedean component, as a Schwartz function (QuadFormsKB's
`fourierInf_coe_schwartz`). -/
def fourierInfSchwartz (f : SchwartzMap (mixedSpace F) ℂ) : SchwartzMap (mixedSpace F) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (WeilRep.Tinf (F := F))
    (FourierTransform.fourier (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (WeilRep.Sinf (F := F)).symm f))

theorem coe_fourierInfSchwartz (f : SchwartzMap (mixedSpace F) ℂ) :
    (fourierInfSchwartz f : mixedSpace F → ℂ) = Analysis.fourierInf (f : mixedSpace F → ℂ) :=
  (WeilRep.fourierInf_coe_schwartz f).symm

/-- **The Fourier transform** $\hat\Phi(y) = \hat f_\infty(y_\infty)\prod_v\hat f_v(y_v)$, with QuadFormsKB's local transforms
(`fourierInf`, `fourierV`) for the self-dual measures. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.2 [unverified locator] (f̂ = ∏ f̂_p for f = ∏ f_p)"]
def fourier (y : Adeles F) : ℂ :=
  Analysis.fourierInf (Φ.fInf : mixedSpace F → ℂ) y.1 * ∏ᶠ v, Analysis.fourierV v (Φ.fv v) (y.2 v)

end SchwartzBruhat

/-! ### The global zeta integral -/

/-- The integrand $\Phi(x)\chi(x)\|x\|^s$ of the global zeta integral, for any function $\Phi$ on $\mathbb A_F$. -/
def globalZetaIntegrand (Φ : Adeles F → ℂ) (χ : HeckeCharacter F) (s : ℂ) (x : (Adeles F)ˣ) : ℂ :=
  Φ x * (χ.onIdeles x : ℂ) * (ideleNorm F x : ℂ) ^ s

/-- **The global zeta integral** $Z(\Phi,\chi,s) = \int_{\mathbb A_F^\times}\Phi(x)\chi(x)\|x\|^s\,d^\times x$, for Tate's
measure $d^\times x$ = `tamIdeles F` (equal to `ideleHaar F` on Mathlib's ideles). It converges absolutely for
$\operatorname{Re}s+\sigma>1$, $\sigma$ the shift of $\chi$ (`integrable_globalZetaIntegrand`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (ζ(f, c) = ∫ f(a)c(a) d×a)"]
def globalZeta (Φ : Adeles F → ℂ) (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ∫ x, globalZetaIntegrand Φ χ s x ∂tamIdeles F

end

end NumberFieldKB
