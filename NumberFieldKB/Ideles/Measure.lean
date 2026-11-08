import NumberFieldKB.Ideles.Bridge
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleMeasures

/-!
# The Haar measure on Mathlib's ideles, and its normalization

$F$ is a number field. **Mathlib (v4.35.0) defines no Haar measure on its adeles or ideles**: there is no
`MeasurableSpace`, and not even a `LocallyCompactSpace` instance, on `AdeleRing (𝓞 F) F` or `IdeleGroup (𝓞 F) F`
(checked with `#synth`). So there is no Mathlib normalization to compare with; we transport QuadFormsKB's.

* Instances on Mathlib's types, transported through `adeleRingHomeomorph F` and `ideleGroupEquiv F`: locally compact,
  second countable, Borel.
* **`ideleHaar F`**: the Haar measure on `IdeleGroup (𝓞 F) F` pulled back from QuadFormsKB's `tamIdeles F`
  (`map_ideleHaar`: the comparison constant is $1$).
* **The normalization we fix, and why.** `tamIdeles F` $=\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$ with
  $\omega_v = dx_v/|x_v|_v$, $dx_v$ self-dual for the standard character, and Weil's convergence factor
  $\lambda_v = 1 - N(v)^{-1}$. This is **exactly Tate's measure** $d^\times x$ (Tate's thesis, Cassels–Fröhlich Ch. XV,
  §2.3 and §3.3 [unverified locators]): at a finite place Tate takes $d^\times x_v = \frac{N(v)}{N(v)-1}\frac{dx_v}{|x_v|_v}$
  (`inv_lamV_eq`), so $\operatorname{vol}(\mathcal O_v^\times) = N(\mathfrak d_v)^{-1/2}$; at a real place $dx/|x|$; at a
  complex place $2\,dx\,dy/|z|^2$ (QuadFormsKB's `omegaInf_eq`, the self-dual measure on $\mathbb C$ being $2\,dx\,dy$).
  On the box $\{x : x_\infty\in A,\ x_f\in\hat{\mathcal O}^\times\}$ it is $\omega_\infty(A)\,|d_F|^{-1/2}$
  (**`ideleHaar_box_OHatUnits`**). With this measure the volume of $C_F^1$ is the residue $\rho_F$ of the Dedekind
  zeta function (QuadFormsKB `muIdeleClass_univ_eq_residue`), Tate's $\kappa$, with no stray discriminant factor. The
  other common normalization, $\operatorname{vol}(\hat{\mathcal O}^\times) = 1$, is $|d_F|^{1/2}$ times ours
  (`sqrt_discr_smul_ideleHaar_box_OHatUnits`).
* **`eq_haarScalarFactor_smul_ideleHaar`**: every Haar measure $\mu$ on Mathlib's ideles is $c\cdot$`ideleHaar F`, with
  $c$ = `μ.haarScalarFactor (ideleHaar F)`.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory
open QuadFormsKB.Tamagawa.Measure.Weil
open scoped ENNReal NNReal

namespace NumberFieldKB.Ideles

noncomputable section

variable (F : Type) [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Topological and measurable structure on Mathlib's adeles and ideles -/

instance : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  (adeleRingHomeomorph F).isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  (adeleRingHomeomorph F).isEmbedding.secondCountableTopology

instance : LocallyCompactSpace (IdeleGroup (𝓞 F) F) :=
  (ideleGroupEquiv F).toHomeomorph.isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (IdeleGroup (𝓞 F) F) :=
  (ideleGroupEquiv F).toHomeomorph.isEmbedding.secondCountableTopology

/-- The Borel structure on Mathlib's idele group (Mathlib has none). -/
instance measurableSpace_ideleGroup : MeasurableSpace (IdeleGroup (𝓞 F) F) := borel _

instance : BorelSpace (IdeleGroup (𝓞 F) F) := ⟨rfl⟩

/-! ### The Haar measure -/

/-- **The Haar measure on Mathlib's idele group**: QuadFormsKB's `tamIdeles F` (Tate's $d^\times x$, see the module
docstring) pulled back through `ideleGroupEquiv F`. -/
def ideleHaar : Measure (IdeleGroup (𝓞 F) F) := (tamIdeles F).map (ideleGroupEquiv F).symm

instance : (ideleHaar F).IsHaarMeasure := by
  rw [ideleHaar]; exact (ideleGroupEquiv F).symm.isHaarMeasure_map _

/-- **The comparison constant is $1$**: the push-forward of `ideleHaar F` to QuadFormsKB's ideles is `tamIdeles F`. -/
theorem map_ideleHaar : (ideleHaar F).map (ideleGroupEquiv F) = tamIdeles F := by
  rw [ideleHaar, Measure.map_map (f := ((ideleGroupEquiv F).symm : (Adeles F)ˣ → IdeleGroup (𝓞 F) F))
    (g := (ideleGroupEquiv F : IdeleGroup (𝓞 F) F → (Adeles F)ˣ))
    (ideleGroupEquiv F).continuous.measurable (ideleGroupEquiv F).symm.continuous.measurable]
  have : (ideleGroupEquiv F ∘ (ideleGroupEquiv F).symm) = id := funext (ideleGroupEquiv F).apply_symm_apply
  rw [this, Measure.map_id]

/-- `ideleHaar F` of a preimage is `tamIdeles F` of the set. -/
theorem ideleHaar_preimage (S : Set (Adeles F)ˣ) : ideleHaar F (ideleGroupEquiv F ⁻¹' S) = tamIdeles F S := by
  rw [← map_ideleHaar]
  exact ((ideleGroupEquiv F).toHomeomorph.toMeasurableEquiv.map_apply S).symm

/-- **`ideleHaar` on boxes**: $\mu(\{x : x_\infty\in A,\ x_f\in B\}) = \omega_\infty(A)\cdot\mu_f(B)$ (the infinite part read
in the mixed space). -/
theorem ideleHaar_box (A : Set (mixedSpace F)ˣ) (B : Set AFˣ) :
    ideleHaar F (ideleGroupEquiv F ⁻¹' (idelesEquiv F ⁻¹' (A ×ˢ B))) = omegaInf F A * muFinUnits F B := by
  rw [ideleHaar_preimage, tamIdeles_prod]

/-- **Tate's normalization**: on $\{x : x_\infty\in A,\ x_f\in\hat{\mathcal O}^\times\}$ the measure is
$\omega_\infty(A)\,|d_F|^{-1/2}$, i.e. $\operatorname{vol}(\hat{\mathcal O}^\times) = \prod_v N(\mathfrak d_v)^{-1/2}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.3 [unverified locator] (d*a = ∏ d*a_p, vol(𝔬_p^×) = (N𝔡_p)^{-1/2})"]
theorem ideleHaar_box_OHatUnits (A : Set (mixedSpace F)ˣ) :
    ideleHaar F (ideleGroupEquiv F ⁻¹' (idelesEquiv F ⁻¹' (A ×ˢ (OHatUnits F : Set AFˣ)))) =
      omegaInf F A * ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
  rw [ideleHaar_box, muFinUnits_OHatUnits, ohatVol]

/-- **The normalization $\operatorname{vol}(\hat{\mathcal O}^\times) = 1$** is $|d_F|^{1/2}$ times `ideleHaar F`. -/
theorem sqrt_discr_smul_ideleHaar_box_OHatUnits (A : Set (mixedSpace F)ˣ) :
    (ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) • ideleHaar F)
      (ideleGroupEquiv F ⁻¹' (idelesEquiv F ⁻¹' (A ×ˢ (OHatUnits F : Set AFˣ)))) = omegaInf F A := by
  rw [Measure.smul_apply, ideleHaar_box_OHatUnits, smul_eq_mul, mul_left_comm, ← ENNReal.ofReal_mul
    (Real.sqrt_nonneg _), mul_inv_cancel₀ sqrt_abs_discr_pos.ne', ENNReal.ofReal_one, mul_one]

variable {F} in
/-- **Tate's local factor**: $\lambda_v^{-1} = N(v)/(N(v) - 1)$, so $\lambda_v^{-1}\,dx_v/|x_v|_v$ is Tate's $d^\times x_v$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (d*a = N𝔭/(N𝔭 - 1) · da/|a|)"]
theorem inv_lamV_eq (v : HeightOneSpectrum (𝓞 F)) :
    (lamV v)⁻¹ = (Ideal.absNorm v.asIdeal : ℝ) / ((Ideal.absNorm v.asIdeal : ℝ) - 1) := by
  have h1 := one_lt_absNorm v
  have h0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : (Ideal.absNorm v.asIdeal : ℝ) - 1 ≠ 0 := (sub_pos.mpr h1).ne'
  rw [lamV, inv_eq_iff_eq_inv, inv_div, eq_div_iff h0, sub_mul, inv_mul_cancel₀ h0, one_mul]

/-- **Every Haar measure on Mathlib's ideles is a multiple of `ideleHaar F`.** -/
theorem eq_haarScalarFactor_smul_ideleHaar (μ : Measure (IdeleGroup (𝓞 F) F)) [μ.IsHaarMeasure] :
    μ = μ.haarScalarFactor (ideleHaar F) • ideleHaar F :=
  Measure.isMulLeftInvariant_eq_smul μ (ideleHaar F)

end

end NumberFieldKB.Ideles
