import QuadFormsKB.Tamagawa.Measure.Weil.UnitsHaar

/-!
# Local zeta integrals: the general framework

$K$ is a locally compact nontrivially normed field (in this library: a completion $F_v$ of a number field $F$ at a
finite place, $\mathbb R$ or $\mathbb C$), $dx = \mu$ an additive Haar measure on $K$, and
$|x|_K = \Delta_K(x)$ the **modulus** of $K$ (Mathlib's `distribHaarChar K`: $\mu(xE) = |x|_K\,\mu(E)$). The modulus is the
normalized absolute value: $|x|_v = N(v)^{-\operatorname{ord}_v x}$ at a finite place, $|x|$ on $\mathbb R$, $|z|^2$ on
$\mathbb C$.

* The multiplicative Haar measure $d^\times x = |x|_K^{-1}dx$ on $K^\times$ is QuadFormsKB's `unitsHaar K μ` (Weil's
  $\omega$); Tate's measure is a positive multiple of it, fixed place by place.
  **`integral_unitsHaar_mul_modulus`**: $\int_{K^\times}h(x)|x|_K\,d^\times x = \int_K h\,dx$.
* **`zetaIntegral ν f χ s`** $= Z(f,\chi,s) = \int_{K^\times}f(x)\chi(x)|x|_K^s\,d\nu(x)$ for a measure $\nu$ on $K^\times$
  and a quasi-character $\chi : K^\times\to\mathbb C^\times$ (`zetaIntegrand` is the integrand).
* **`fourier μ ψ f`** $= \hat f(y) = \int_K f(x)\psi(xy)\,dx$ for an additive character $\psi$; QuadFormsKB's `fourierV`
  (finite places) and `fourierR` (real place) are instances (`rfl`).
* **`zetaIntegral_mul_fourier_comm`** (Tate's local functional equation, the symmetric form):
  $$Z(f,\chi,s)\,Z(\hat g,\chi^{-1},1-s) = Z(g,\chi,s)\,Z(\hat f,\chi^{-1},1-s)$$
  whenever $f, g$ are integrable and the four zeta integrals converge absolutely. This is Tate's Fubini argument:
  both sides equal $\int_{K^\times}\chi^{-1}(t)|t|^{1-s}\iint f(x)g(z)\psi(xzt)\,dx\,dz\,d^\times t$. The convergence
  hypotheses are discharged place by place (`NonArchimedean.lean`, `Real.lean`, `Complex.lean`).

Source: Tate's thesis, Cassels–Fröhlich Ch. XV, §2.3 (multiplicative Haar measure and quasi-characters) and §2.4,
Lemma 2.4.1 (the Fubini identity) and Theorem 2.4.1 [unverified locators].
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace NumberFieldKB.LocalZeta

noncomputable section

open QuadFormsKB.Tamagawa.Measure.Weil

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {K : Type*} [NontriviallyNormedField K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]

/-! ### The unit group of $K$ -/

/-- `Units.val : Kˣ → K` is an open embedding onto $K\setminus\{0\}$. -/
theorem isOpenEmbedding_units_val : IsOpenEmbedding (Units.val : Kˣ → K) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have : range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩
  rw [this]
  exact isOpen_compl_singleton

instance : LocallyCompactSpace Kˣ := isOpenEmbedding_units_val.locallyCompactSpace

instance : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology

/-- The modulus $|u|_K = \Delta_K(u)$ is positive. -/
theorem distribHaarChar_pos' (u : Kˣ) : (0 : ℝ) < distribHaarChar K u := by
  exact_mod_cast distribHaarChar_pos

/-! ### Zeta integrals and Fourier transforms -/

variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]

/-- The integrand $f(u)\chi(u)|u|_K^s$ of the local zeta integral, a function on $K^\times$. -/
def zetaIntegrand (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) (u : Kˣ) : ℂ :=
  f u * (χ u : ℂ) * ((distribHaarChar K u : ℝ) : ℂ) ^ s

/-- **The local zeta integral** $Z(f,\chi,s) = \int_{K^\times}f(x)\chi(x)|x|_K^s\,d\nu(x)$ (Tate's
$\zeta(f, c) = \int f(\alpha)c(\alpha)\,d^\times\alpha$ for the quasi-character $c = \chi|\cdot|^s$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (the local zeta function ζ(f, c))"]
def zetaIntegral (ν : Measure Kˣ) (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ u, zetaIntegrand f χ s u ∂ν

/-- **The Fourier transform** $\hat f(y) = \int_K f(x)\psi(xy)\,d\mu(x)$ for an additive character $\psi$ of $K$. -/
def fourier (μ : Measure K) (ψ : AddChar K Circle) (f : K → ℂ) (y : K) : ℂ :=
  ∫ x, f x * (ψ (x * y) : ℂ) ∂μ

/-- A quasi-character is **unitary** if its values have absolute value $1$. -/
def IsUnitary (χ : Kˣ →* ℂˣ) : Prop := ∀ u, ‖(χ u : ℂ)‖ = 1

theorem norm_zetaIntegrand (f : K → ℂ) {χ : Kˣ →* ℂˣ} (hχ : IsUnitary χ) (s : ℂ) (u : Kˣ) :
    ‖zetaIntegrand f χ s u‖ = ‖f u‖ * (distribHaarChar K u : ℝ) ^ s.re := by
  rw [zetaIntegrand, norm_mul, norm_mul, hχ u, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (distribHaarChar_pos' u)]

/-! ### Unfolding the multiplicative measure -/

section Unfold

variable (hΔ : Continuous (distribHaarChar K : Kˣ → ℝ≥0)) (μ : Measure K) [μ.IsAddHaarMeasure]

include hΔ in
/-- **$\int_{K^\times}h(x)|x|_K\,d^\times x = \int_K h\,dx$** for $d^\times x$ = `unitsHaar K μ` $=|x|_K^{-1}dx$. -/
theorem integral_unitsHaar_mul_modulus (h : K → ℂ) :
    ∫ u, h u * ((distribHaarChar K u : ℝ) : ℂ) ∂(unitsHaar K μ) = ∫ x, h x ∂μ := by
  have he := measurableEmbedding_val (isOpenEmbedding_units_val (K := K))
  rw [unitsHaar, integral_withDensity_eq_integral_smul (f := fun u : Kˣ => distribHaarChar K u⁻¹)
    (hΔ.comp continuous_inv).measurable]
  have h1 : ∀ u : Kˣ, (distribHaarChar K u⁻¹ : ℝ≥0) • (h u * ((distribHaarChar K u : ℝ) : ℂ)) = h u := by
    intro u
    rw [NNReal.smul_def, map_inv, NNReal.coe_inv, Complex.real_smul, Complex.ofReal_inv]
    have : ((distribHaarChar K u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (distribHaarChar_pos' u).ne'
    field_simp
  simp_rw [h1]
  rw [← he.integral_map, he.map_comap]
  have hr : range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩
  rw [hr, restrict_compl_singleton]

include hΔ in
/-- The `lintegral` form: $\int_{K^\times}h(x)|x|_K\,d^\times x = \int_K h\,dx$ for $h\ge0$. -/
theorem lintegral_unitsHaar_mul_modulus (h : K → ℝ≥0∞) :
    ∫⁻ u, h u * (distribHaarChar K u : ℝ≥0∞) ∂(unitsHaar K μ) = ∫⁻ x, h x ∂μ := by
  have he := measurableEmbedding_val (isOpenEmbedding_units_val (K := K))
  have hm : Measurable fun u : Kˣ => (distribHaarChar K u⁻¹ : ℝ≥0∞) :=
    measurable_distribHaarChar_inv hΔ
  rw [unitsHaar, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
    (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  have h1 : ∀ u : Kˣ, (distribHaarChar K u⁻¹ : ℝ≥0∞) * (h u * (distribHaarChar K u : ℝ≥0∞)) = h u := by
    intro u
    rw [mul_comm, mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one, mul_one]
  simp_rw [Pi.mul_apply, h1]
  rw [← he.lintegral_map, he.map_comap]
  have hr : range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩
  rw [hr, restrict_compl_singleton]

end Unfold

/-! ### Tate's local functional equation -/

section FunctionalEquation

variable (hΔ : Continuous (distribHaarChar K : Kˣ → ℝ≥0)) (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
  (ψ : AddChar K Circle) (hψ : Continuous ψ)

include hψ in
/-- **The symmetric kernel**: $\int_K f(x)\hat g(xt)\,dx = \int_K g(x)\hat f(xt)\,dx$ for integrable $f, g$ (both are
$\iint f(x)g(z)\psi(xzt)\,dx\,dz$, Fubini). -/
theorem integral_mul_fourier_comm {f g : K → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (t : K) :
    ∫ x, f x * fourier μ ψ g (x * t) ∂μ = ∫ x, g x * fourier μ ψ f (x * t) ∂μ := by
  have hcont : ∀ c : K, Continuous fun p : K × K => ((ψ (p.2 * (p.1 * c)) : Circle) : ℂ) := fun c =>
    continuous_subtype_val.comp (hψ.comp (continuous_snd.mul (continuous_fst.mul continuous_const)))
  have hint : Integrable (Function.uncurry fun x z => f x * (g z * (ψ (z * (x * t)) : ℂ))) (μ.prod μ) := by
    have := (hf.mul_prod hg).mul_bdd (c := 1) (hcont t).aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Circle.norm_coe])
    refine this.congr (Eventually.of_forall fun p => ?_)
    obtain ⟨x, z⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [mul_assoc]
  simp only [fourier, ← integral_const_mul]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [show z * (x * t) = x * (z * t) by ring]
  ring

/-- The pointwise identity behind the change of variables $y = xt$:
$f(x)\chi(x)|x|^s\cdot\hat g(xt)\chi^{-1}(xt)|xt|^{1-s} = f(x)\hat g(xt)|x|\cdot\chi^{-1}(t)|t|^{1-s}$. -/
theorem zetaIntegrand_mul_zetaIntegrand_mul (f h : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) (x t : Kˣ) :
    zetaIntegrand f χ s x * zetaIntegrand h χ⁻¹ (1 - s) (x * t) =
      (f x * h (x * t : Kˣ) * ((distribHaarChar K x : ℝ) : ℂ)) *
        (((χ⁻¹ t : ℂˣ) : ℂ) * ((distribHaarChar K t : ℝ) : ℂ) ^ (1 - s)) := by
  have hx : ((distribHaarChar K x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (distribHaarChar_pos' x).ne'
  have hpow : ((distribHaarChar K x : ℝ) : ℂ) ^ s * ((distribHaarChar K x : ℝ) : ℂ) ^ (1 - s) =
      ((distribHaarChar K x : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hx, add_sub_cancel, Complex.cpow_one]
  have hmul : ((distribHaarChar K (x * t) : ℝ) : ℂ) ^ (1 - s) =
      ((distribHaarChar K x : ℝ) : ℂ) ^ (1 - s) * ((distribHaarChar K t : ℝ) : ℂ) ^ (1 - s) := by
    rw [map_mul, NNReal.coe_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  have hχ : ((χ⁻¹ (x * t) : ℂˣ) : ℂ) = (χ x : ℂ)⁻¹ * ((χ⁻¹ t : ℂˣ) : ℂ) := by
    simp only [MonoidHom.inv_apply, map_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  have hχx : (χ x : ℂ) ≠ 0 := (χ x).ne_zero
  simp only [zetaIntegrand, hmul, hχ]
  calc f ↑x * ↑(χ x) * ((distribHaarChar K x : ℝ) : ℂ) ^ s *
        (h ↑(x * t) * ((χ x : ℂ)⁻¹ * ((χ⁻¹ t : ℂˣ) : ℂ)) *
          (((distribHaarChar K x : ℝ) : ℂ) ^ (1 - s) * ((distribHaarChar K t : ℝ) : ℂ) ^ (1 - s)))
      = f ↑x * h ↑(x * t) * ((χ x : ℂ) * (χ x : ℂ)⁻¹) *
          (((distribHaarChar K x : ℝ) : ℂ) ^ s * ((distribHaarChar K x : ℝ) : ℂ) ^ (1 - s)) *
          (((χ⁻¹ t : ℂˣ) : ℂ) * ((distribHaarChar K t : ℝ) : ℂ) ^ (1 - s)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hχx, hpow, mul_one]

include hΔ in
/-- **Unfolding the product of two zeta integrals** (Tate's Lemma 2.4.1): for absolutely convergent $Z(f,\chi,s)$ and
$Z(h,\chi^{-1},1-s)$,
$$Z(f,\chi,s)\,Z(h,\chi^{-1},1-s) = \int_{K^\times}\chi^{-1}(t)|t|^{1-s}\int_K f(x)h(xt)\,dx\,d^\times t.$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4, Lemma 2.4.1 [unverified locator] (ζ(f, c)ζ(ĝ, ĉ) = ζ(f̂, ĉ)ζ(g, c))"]
theorem zetaIntegral_mul_zetaIntegral (χ : Kˣ →* ℂˣ) (s : ℂ) {f h : K → ℂ}
    (hZf : Integrable (zetaIntegrand f χ s) (unitsHaar K μ))
    (hZh : Integrable (zetaIntegrand h χ⁻¹ (1 - s)) (unitsHaar K μ)) :
    zetaIntegral (unitsHaar K μ) f χ s * zetaIntegral (unitsHaar K μ) h χ⁻¹ (1 - s) =
      ∫ t, (∫ x, f x * h (x * t) ∂μ) * (((χ⁻¹ t : ℂˣ) : ℂ) * ((distribHaarChar K t : ℝ) : ℂ) ^ (1 - s))
        ∂(unitsHaar K μ) := by
  set ν := unitsHaar K μ
  have : ν.IsHaarMeasure := isHaarMeasure_unitsHaar isOpenEmbedding_units_val hΔ μ
  have hmp := measurePreserving_prod_mul ν ν
  have hemb : MeasurableEmbedding fun z : Kˣ × Kˣ => (z.1, z.1 * z.2) :=
    (MeasurableEquiv.shearMulRight Kˣ).measurableEmbedding
  have hint : Integrable (fun p : Kˣ × Kˣ =>
      zetaIntegrand f χ s p.1 * zetaIntegrand h χ⁻¹ (1 - s) (p.1 * p.2)) (ν.prod ν) :=
    (hmp.integrable_comp_emb hemb).mpr (hZf.mul_prod hZh)
  rw [zetaIntegral, zetaIntegral, ← integral_prod_mul, ← hmp.integral_comp hemb]
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [zetaIntegrand_mul_zetaIntegrand_mul]
  rw [integral_mul_const]
  congr 1
  simp_rw [Units.val_mul]
  exact integral_unitsHaar_mul_modulus hΔ μ (fun x => f x * h (x * t))

include hΔ hψ in
/-- **Tate's local functional equation** (symmetric form, Cassels–Fröhlich Ch. XV, Thm. 2.4.1): for integrable
$f, g$ on $K$ whose zeta integrals $Z(f,\chi,s)$, $Z(g,\chi,s)$, $Z(\hat f,\chi^{-1},1-s)$, $Z(\hat g,\chi^{-1},1-s)$
converge absolutely,
$$Z(f,\chi,s)\,Z(\hat g,\chi^{-1},1-s) = Z(g,\chi,s)\,Z(\hat f,\chi^{-1},1-s).$$
Here $d^\times x$ = `unitsHaar K μ` $=|x|^{-1}dx$; the identity is homogeneous in $d^\times x$, so it holds for every
positive multiple (`zetaIntegral_smul_measure`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4, Thm. 2.4.1 and Lemma 2.4.1 [unverified locator]"]
theorem zetaIntegral_mul_fourier_comm (χ : Kˣ →* ℂˣ) (s : ℂ) {f g : K → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hZf : Integrable (zetaIntegrand f χ s) (unitsHaar K μ))
    (hZg : Integrable (zetaIntegrand g χ s) (unitsHaar K μ))
    (hZf' : Integrable (zetaIntegrand (fourier μ ψ f) χ⁻¹ (1 - s)) (unitsHaar K μ))
    (hZg' : Integrable (zetaIntegrand (fourier μ ψ g) χ⁻¹ (1 - s)) (unitsHaar K μ)) :
    zetaIntegral (unitsHaar K μ) f χ s * zetaIntegral (unitsHaar K μ) (fourier μ ψ g) χ⁻¹ (1 - s) =
      zetaIntegral (unitsHaar K μ) g χ s * zetaIntegral (unitsHaar K μ) (fourier μ ψ f) χ⁻¹ (1 - s) := by
  rw [zetaIntegral_mul_zetaIntegral hΔ μ χ s hZf hZg', zetaIntegral_mul_zetaIntegral hΔ μ χ s hZg hZf']
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [integral_mul_fourier_comm μ ψ hψ hf hg]

omit [SecondCountableTopology K] [BorelSpace Kˣ] in
/-- The zeta integral is linear in the measure: $Z_{c\nu} = c\,Z_\nu$. -/
theorem zetaIntegral_smul_measure (ν : Measure Kˣ) (c : ℝ≥0) (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    zetaIntegral (c • ν) f χ s = (c : ℂ) * zetaIntegral ν f χ s := by
  rw [zetaIntegral, zetaIntegral, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end FunctionalEquation

end

end NumberFieldKB.LocalZeta
