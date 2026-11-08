import NumberFieldKB.Pontryagin.Embedding
import NumberFieldKB.Pontryagin.Fubini
import NumberFieldKB.WeilBNT.AbstractFourier

/-!
# The Fourier inversion theorem on a locally compact commutative group, given Bochner

$G$ is a locally compact commutative Hausdorff group with a regular Haar measure $\mu$, $G^*$ its dual.

Following Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., Theorem 4.33 (Fourier inversion), with the
class of functions restricted to compactly supported ones:

* `fhat μ f ξ` $=\hat f(\xi)=\int f(x)\overline{\xi(x)}\,d\mu(x)$ (Folland's transform; Weil's is
  $\Phi^*(\xi)=\hat\Phi(\xi^{-1})$, `fhat_eq_fourierLCA`).
* `IsInvClass μ f`: $f$ continuous, compactly supported, positive definite, with $\hat f\ge0$. It contains every
  autocorrelation $u\star\tilde u$ ($\widehat{u\star\tilde u}=|\hat u|^2$, `fhat_autocorr`), is closed under sums
  and under multiplication by $\bar\eta$, $\eta\in G^*$; for every compact $C\subset G^*$ it contains $g$ with
  $\hat g>0$ on $C$ (`exists_isInvClass_pos_on`).
* `bochnerMeasure hB hf`: the finite inner regular measure $\mu_f$ on $G^*$ with $f(x)=\int\xi(x)\,d\mu_f$.
  Consistency (Folland, proof of 4.33): $\hat g\,\mu_f=\hat f\,\mu_g$ (`withDensity_bochnerMeasure_comm`).
* `inversionFunctional`: the positive linear functional $\psi\mapsto\int\psi/\hat g\,d\mu_g$ on $C_c(G^*)$ ($\hat g>0$ on
  the support of $\psi$; independent of $g$), and **`dualHaar μ`**, its Riesz–Markov–Kakutani measure: a Haar measure
  on $G^*$ (`isHaarMeasure_dualHaar`).
* **`bochnerMeasure_eq_withDensity`**: $\mu_f=\hat f\,\lambda$ for $f$ in the class ($\lambda$ = `dualHaar μ`), hence
  **`inversion_isInvClass`**: $\hat f$ is $\lambda$-integrable and $f(x)=\int\hat f(\xi)\xi(x)\,d\lambda(\xi)$.

Weil's form (dual measure, admissible functions) is in `NumberFieldKB.Pontryagin.DualMeasure`.
-/

open MeasureTheory Topology Filter ComplexConjugate ComplexOrder Pointwise

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

section Transform

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- Folland's Fourier transform $\hat f(\xi)=\int f(x)\overline{\xi(x)}\,d\mu(x)$. -/
def fhat (μ : Measure G) (f : G → ℂ) (ξ : PontryaginDual G) : ℂ := ∫ x, f x * conj ((ξ x : Circle) : ℂ) ∂μ

lemma conj_char_eq_inv (ξ : PontryaginDual G) (x : G) : conj ((ξ x : Circle) : ℂ) = ((ξ x⁻¹ : Circle) : ℂ) := by
  rw [map_inv, Circle.coe_inv_eq_conj]

lemma conj_char_eq_inv' (ξ : PontryaginDual G) (x : G) : conj ((ξ x : Circle) : ℂ) = ((ξ⁻¹ x : Circle) : ℂ) := by
  rw [conj_char_eq_inv, dual_inv_apply, map_inv]

/-- Folland's transform is Weil's transform at the inverse character. -/
lemma fhat_eq_fourierLCA (μ : Measure G) (f : G → ℂ) (ξ : PontryaginDual G) :
    fhat μ f ξ = WeilBNT.AbstractFourier.fourierLCA μ f ξ⁻¹ := by
  unfold fhat WeilBNT.AbstractFourier.fourierLCA
  simp_rw [conj_char_eq_inv']

lemma norm_fhat_le (μ : Measure G) (f : G → ℂ) (ξ : PontryaginDual G) : ‖fhat μ f ξ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1 with x
  simp

lemma continuous_fhat [LocallyCompactSpace G] [T2Space G] (μ : Measure G) [μ.InnerRegularCompactLTTop]
    {f : G → ℂ} (hf : Integrable f μ) : Continuous (fhat μ f) := by
  have : fhat μ f = WeilBNT.AbstractFourier.fourierLCA μ f ∘ (fun ξ => ξ⁻¹) := by
    funext ξ; exact fhat_eq_fourierLCA μ f ξ
  rw [this]
  exact (WeilBNT.AbstractFourier.continuous_fourierLCA_of_innerRegular μ hf).comp continuous_inv

/-- Transform of a translate: $\widehat{f(x\,\cdot)}(\xi)=\xi(x)\hat f(\xi)$. -/
lemma fhat_translate (μ : Measure G) [μ.IsMulLeftInvariant] (f : G → ℂ) (x : G) (ξ : PontryaginDual G) :
    fhat μ (fun w => f (x * w)) ξ = ((ξ x : Circle) : ℂ) * fhat μ f ξ := by
  unfold fhat
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ x⁻¹]
  congr 1 with w
  show f (x * (x⁻¹ * w)) * conj ((ξ (x⁻¹ * w) : Circle) : ℂ) = _
  rw [mul_inv_cancel_left, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj, map_mul,
    Complex.conj_conj]
  ring

end Transform

section InvClass

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

lemma integrable_mul_conj_char {f : G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (ξ : PontryaginDual G) : Integrable (fun x => f x * conj ((ξ x : Circle) : ℂ)) μ :=
  (hf.mul (Complex.continuous_conj.comp (continuous_subtype_val.comp ξ.continuous))).integrable_of_hasCompactSupport
    hc.mul_right

/-- **The transform of an autocorrelation**: $\widehat{u\star\tilde u}=|\hat u|^2$. -/
theorem fhat_autocorr {u : G → ℂ} (hu : Continuous u) (hc : HasCompactSupport u) (ξ : PontryaginDual G) :
    fhat μ (autocorr μ u) ξ = ((‖fhat μ u ξ‖ ^ 2 : ℝ) : ℂ) := by
  set K := tsupport u
  have hK : IsCompact K := hc
  have hcx : Continuous fun x : G => conj ((ξ x : Circle) : ℂ) :=
    Complex.continuous_conj.comp (continuous_subtype_val.comp ξ.continuous)
  -- Fubini on `G × G` (compact support)
  have hswap : ∫ x, (∫ y, u y * conj (u (x⁻¹ * y)) * conj ((ξ x : Circle) : ℂ) ∂μ) ∂μ =
      ∫ y, (∫ x, u y * conj (u (x⁻¹ * y)) * conj ((ξ x : Circle) : ℂ) ∂μ) ∂μ := by
    apply integral_integral_swap_of_hasCompactSupport
    · exact ((hu.comp continuous_snd).mul (Complex.continuous_conj.comp
        (hu.comp (continuous_fst.inv.mul continuous_snd)))).mul (hcx.comp continuous_fst)
    · refine HasCompactSupport.intro ((hK.mul hK.inv).prod hK) fun p hp => ?_
      obtain ⟨x, y⟩ := p
      simp only [Set.mem_prod, not_and_or] at hp
      by_cases hy : y ∈ K
      · have hx : x ∉ K * K⁻¹ := by tauto
        have : x⁻¹ * y ∉ K := by
          intro h
          apply hx
          refine ⟨y, hy, (x⁻¹ * y)⁻¹, by simpa using h, ?_⟩
          simp
        simp [image_eq_zero_of_notMem_tsupport this]
      · simp [image_eq_zero_of_notMem_tsupport hy]
  have hinner : ∀ y, ∫ x, u y * conj (u (x⁻¹ * y)) * conj ((ξ x : Circle) : ℂ) ∂μ =
      u y * conj ((ξ y : Circle) : ℂ) * conj (fhat μ u ξ) := by
    intro y
    rw [← integral_mul_left_eq_self _ y, ← integral_inv_eq_self]
    unfold fhat
    rw [← integral_conj, ← integral_const_mul]
    congr 1 with x
    simp only [mul_inv_rev, inv_inv, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj,
      Complex.conj_conj]
    rw [show x * y⁻¹ * y = x by group]
    ring
  calc fhat μ (autocorr μ u) ξ
      = ∫ x, (∫ y, u y * conj (u (x⁻¹ * y)) * conj ((ξ x : Circle) : ℂ) ∂μ) ∂μ := by
        unfold fhat autocorr
        simp_rw [← integral_mul_const]
    _ = ∫ y, u y * conj ((ξ y : Circle) : ℂ) * conj (fhat μ u ξ) ∂μ := by rw [hswap]; simp_rw [hinner]
    _ = fhat μ u ξ * conj (fhat μ u ξ) := by rw [integral_mul_const]; rfl
    _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The class of functions for which inversion is proved first: continuous, compactly supported, positive definite,
with non-negative transform. -/
structure IsInvClass (f : G → ℂ) : Prop where
  continuous : Continuous f
  hasCompactSupport : HasCompactSupport f
  posDef : IsPositiveDefinite f
  fhat_nonneg : ∀ ξ, 0 ≤ fhat μ f ξ

variable {μ}

lemma IsInvClass.fhat_eq_re {f : G → ℂ} (hf : IsInvClass μ f) (ξ : PontryaginDual G) :
    fhat μ f ξ = ((fhat μ f ξ).re : ℂ) := by
  have := Complex.nonneg_iff.mp (hf.fhat_nonneg ξ)
  apply Complex.ext <;> simp [this.2.symm]

lemma IsInvClass.re_nonneg {f : G → ℂ} (hf : IsInvClass μ f) (ξ : PontryaginDual G) : 0 ≤ (fhat μ f ξ).re :=
  (Complex.nonneg_iff.mp (hf.fhat_nonneg ξ)).1

lemma IsInvClass.integrable {f : G → ℂ} (hf : IsInvClass μ f) : Integrable f μ :=
  hf.continuous.integrable_of_hasCompactSupport hf.hasCompactSupport

lemma IsInvClass.continuous_fhat {f : G → ℂ} (hf : IsInvClass μ f) : Continuous (fhat μ f) :=
  _root_.NumberFieldKB.Pontryagin.continuous_fhat μ hf.integrable

lemma isInvClass_autocorr {u : G → ℂ} (hu : Continuous u) (hc : HasCompactSupport u) :
    IsInvClass μ (autocorr μ u) where
  continuous := continuous_autocorr hu hc
  hasCompactSupport := by
    set K := tsupport u
    have hK : IsCompact K := hc
    refine HasCompactSupport.intro (hK.mul hK.inv) fun x hx => autocorr_eq_zero fun y => ?_
    by_cases hy : y ∈ K
    · right
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hx ⟨y, hy, (x⁻¹ * y)⁻¹, by simpa using h, by simp⟩
    · left; exact image_eq_zero_of_notMem_tsupport hy
  posDef := isPositiveDefinite_autocorr hu hc
  fhat_nonneg ξ := by
    rw [fhat_autocorr μ hu hc]
    exact Complex.zero_le_real.mpr (by positivity)

lemma isInvClass_zero : IsInvClass μ (0 : G → ℂ) where
  continuous := continuous_const
  hasCompactSupport := HasCompactSupport.zero
  posDef n c v := by simp
  fhat_nonneg ξ := by simp [fhat]

lemma fhat_add {f g : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g)
    (hgc : HasCompactSupport g) (ξ : PontryaginDual G) : fhat μ (f + g) ξ = fhat μ f ξ + fhat μ g ξ := by
  unfold fhat
  rw [← integral_add (integrable_mul_conj_char μ hf hfc ξ) (integrable_mul_conj_char μ hg hgc ξ)]
  congr 1 with x
  simp [add_mul]

lemma IsInvClass.add {f g : G → ℂ} (hf : IsInvClass μ f) (hg : IsInvClass μ g) : IsInvClass μ (f + g) where
  continuous := hf.continuous.add hg.continuous
  hasCompactSupport := hf.hasCompactSupport.add hg.hasCompactSupport
  posDef n c v := by
    have := add_nonneg (hf.posDef n c v) (hg.posDef n c v)
    simpa [mul_add, Finset.sum_add_distrib] using this
  fhat_nonneg ξ := by
    rw [fhat_add hf.continuous hf.hasCompactSupport hg.continuous hg.hasCompactSupport]
    exact add_nonneg (hf.fhat_nonneg ξ) (hg.fhat_nonneg ξ)

/-- Twisting by a character: $f\bar\eta$. -/
def twist (f : G → ℂ) (η : PontryaginDual G) (x : G) : ℂ := f x * conj ((η x : Circle) : ℂ)

lemma fhat_twist (f : G → ℂ) (η ξ : PontryaginDual G) : fhat μ (twist f η) ξ = fhat μ f (η * ξ) := by
  unfold fhat twist
  congr 1 with x
  rw [dual_mul_apply, Circle.coe_mul, map_mul, mul_assoc]

lemma IsInvClass.twist {f : G → ℂ} (hf : IsInvClass μ f) (η : PontryaginDual G) :
    IsInvClass μ (twist f η) where
  continuous := hf.continuous.mul (Complex.continuous_conj.comp (continuous_subtype_val.comp η.continuous))
  hasCompactSupport := hf.hasCompactSupport.mul_right
  posDef n c v := by
    have := hf.posDef n (fun i => c i * conj ((η (v i) : Circle) : ℂ)) v
    convert this using 3 with i _ j _
    unfold Pontryagin.twist
    rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj, map_mul, Complex.conj_conj, map_mul,
      Complex.conj_conj]
    ring
  fhat_nonneg ξ := by rw [fhat_twist]; exact hf.fhat_nonneg _

/-- For every character $\xi_0$ there is $g$ in the class with $\hat g(\xi_0)>0$. -/
lemma exists_isInvClass_pos (ξ₀ : PontryaginDual G) :
    ∃ g : G → ℂ, IsInvClass μ g ∧ 0 < (fhat μ g ξ₀).re := by
  obtain ⟨b, hbc, hb0, hb1⟩ := exists_continuous_nonneg_pos (1 : G)
  set u : G → ℂ := fun x => (b x : ℂ) * ((ξ₀ x : Circle) : ℂ) with hu
  have huc : Continuous u :=
    (Complex.continuous_ofReal.comp b.continuous).mul (continuous_subtype_val.comp ξ₀.continuous)
  have hus : HasCompactSupport u :=
    (HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hbc Complex.ofReal_zero).mul_right
  refine ⟨autocorr μ u, isInvClass_autocorr huc hus, ?_⟩
  have hpos : 0 < ∫ x, b x ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero b.continuous hbc hb0 hb1
  have hfu : fhat μ u ξ₀ = ((∫ x, b x ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    unfold fhat
    congr 1 with x
    simp only [hu, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    simp
  rw [fhat_autocorr μ huc hus, hfu, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  positivity

/-- **For every compact set $C\subset G^*$ there is $g$ in the class with $\hat g>0$ on $C$.** -/
theorem exists_isInvClass_pos_on {C : Set (PontryaginDual G)} (hC : IsCompact C) :
    ∃ g : G → ℂ, IsInvClass μ g ∧ ∀ ξ ∈ C, 0 < (fhat μ g ξ).re := by
  refine hC.induction_on (p := fun S => ∃ g : G → ℂ, IsInvClass μ g ∧ ∀ ξ ∈ S, 0 < (fhat μ g ξ).re)
    ⟨0, isInvClass_zero, by simp⟩ (fun S T hST ⟨g, hg, hgT⟩ => ⟨g, hg, fun ξ hξ => hgT ξ (hST hξ)⟩)
    (fun S T ⟨g, hg, hgS⟩ ⟨g', hg', hg'T⟩ => ⟨g + g', hg.add hg', fun ξ hξ => ?_⟩) (fun ξ _ => ?_)
  · rw [fhat_add hg.continuous hg.hasCompactSupport hg'.continuous hg'.hasCompactSupport, Complex.add_re]
    rcases hξ with hξ | hξ
    · exact add_pos_of_pos_of_nonneg (hgS ξ hξ) (hg'.re_nonneg ξ)
    · exact add_pos_of_nonneg_of_pos (hg.re_nonneg ξ) (hg'T ξ hξ)
  · obtain ⟨g, hg, hgξ⟩ := exists_isInvClass_pos (μ := μ) ξ
    have hopen : IsOpen {η : PontryaginDual G | 0 < (fhat μ g η).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp hg.continuous_fhat)
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hgξ), g, hg, fun η hη => hη⟩

end InvClass

section BochnerMeasure

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- The transform of a finite measure is Hermitian: $\overline{\hat\nu(y)}=\hat\nu(y^{-1})$. -/
lemma conj_fourierStieltjes (ν : Measure (PontryaginDual G)) (y : G) :
    conj (fourierStieltjes ν y) = fourierStieltjes ν y⁻¹ := by
  unfold fourierStieltjes
  rw [← integral_conj]
  congr 1 with ξ
  exact conj_char_eq_inv ξ y

lemma continuous_pairing : Continuous fun p : PontryaginDual G × G => ((p.1 p.2 : Circle) : ℂ) := by
  have h : Continuous fun p : PontryaginDual G × G => (p.1 : G →ₜ* Circle).toContinuousMap p.2 :=
    continuous_eval.comp (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
      continuous_fst).prodMk continuous_snd)
  exact continuous_subtype_val.comp h

/-- **Pairing with a finite measure on the dual** (Fubini): $\int\hat h\,d\nu=\int h(y)\overline{\hat\nu(y)}\,dy$. -/
theorem integral_fhat (ν : Measure (PontryaginDual G)) [IsFiniteMeasure ν] [ν.InnerRegular] {h : G → ℂ}
    (hh : Continuous h) (hhi : Integrable h μ) :
    ∫ ξ, fhat μ h ξ ∂ν = ∫ y, h y * conj (fourierStieltjes ν y) ∂μ := by
  unfold fhat
  rw [integral_integral_swap_of_dominated ν μ (F := fun ξ y => h y * conj ((ξ y : Circle) : ℂ))
    (a := fun _ => 1) (b := fun y => ‖h y‖)]
  · congr 1 with y
    unfold fourierStieltjes
    rw [integral_const_mul, integral_conj]
  · exact (hh.comp continuous_snd).mul (Complex.continuous_conj.comp continuous_pairing)
  · exact continuous_const
  · exact fun _ => zero_le_one
  · exact integrable_const _
  · exact hh.norm
  · exact fun _ => norm_nonneg _
  · exact hhi.norm
  · intro ξ y; simp

variable (hB : BochnerTheorem.{u})

/-- The Bochner measure $\mu_f$ of a function of the class: $f(x)=\int\xi(x)\,d\mu_f(\xi)$. -/
def bochnerMeasure {f : G → ℂ} (hf : IsInvClass μ f) : Measure (PontryaginDual G) :=
  Classical.choose (hB.exists_measure G f hf.posDef hf.continuous.continuousAt)

variable {hB}

lemma bochnerMeasure_spec {f : G → ℂ} (hf : IsInvClass μ f) :
    IsFiniteMeasure (bochnerMeasure hB hf) ∧ (bochnerMeasure hB hf).InnerRegular ∧
      ∀ x, fourierStieltjes (bochnerMeasure hB hf) x = f x :=
  Classical.choose_spec (hB.exists_measure G f hf.posDef hf.continuous.continuousAt)

instance {f : G → ℂ} (hf : IsInvClass μ f) : IsFiniteMeasure (bochnerMeasure hB hf) :=
  (bochnerMeasure_spec hf).1

instance {f : G → ℂ} (hf : IsInvClass μ f) : (bochnerMeasure hB hf).InnerRegular :=
  (bochnerMeasure_spec hf).2.1

lemma fourierStieltjes_bochnerMeasure {f : G → ℂ} (hf : IsInvClass μ f) (x : G) :
    fourierStieltjes (bochnerMeasure hB hf) x = f x :=
  (bochnerMeasure_spec hf).2.2 x

lemma IsInvClass.conj_eq (hB : BochnerTheorem.{u}) {f : G → ℂ} (hf : IsInvClass μ f) (y : G) :
    conj (f y) = f y⁻¹ := by
  rw [← fourierStieltjes_bochnerMeasure (hB := hB) hf, conj_fourierStieltjes,
    fourierStieltjes_bochnerMeasure]

/-- The density $\hat f$ as an `ℝ≥0`-valued function. -/
def fhatNN (μ : Measure G) (f : G → ℂ) (ξ : PontryaginDual G) : NNReal := (fhat μ f ξ).re.toNNReal

lemma IsInvClass.coe_fhatNN {f : G → ℂ} (hf : IsInvClass μ f) (ξ : PontryaginDual G) :
    ((fhatNN μ f ξ : ℝ) : ℂ) = fhat μ f ξ := by
  rw [fhatNN, Real.coe_toNNReal _ (hf.re_nonneg ξ), ← hf.fhat_eq_re]

lemma IsInvClass.measurable_fhatNN {f : G → ℂ} (hf : IsInvClass μ f) : Measurable (fhatNN μ f) :=
  (continuous_real_toNNReal.comp (Complex.continuous_re.comp hf.continuous_fhat)).measurable

lemma fhatNN_le (f : G → ℂ) (ξ : PontryaginDual G) :
    (fhatNN μ f ξ : ENNReal) ≤ ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) :=
  ENNReal.ofReal_le_ofReal ((Complex.re_le_norm _).trans (norm_fhat_le μ f ξ))

lemma fourierStieltjes_withDensity (ν : Measure (PontryaginDual G)) {r : PontryaginDual G → NNReal}
    (hr : Measurable r) (x : G) :
    fourierStieltjes (ν.withDensity fun ξ => (r ξ : ENNReal)) x = ∫ ξ, ((r ξ : ℝ) : ℂ) * ((ξ x : Circle) : ℂ) ∂ν := by
  unfold fourierStieltjes
  rw [integral_withDensity_eq_integral_smul hr]
  rfl

lemma IsInvClass.withDensity_finite (ν : Measure (PontryaginDual G)) [IsFiniteMeasure ν] {g : G → ℂ}
    (hg : IsInvClass μ g) : IsFiniteMeasure (ν.withDensity fun ξ => (fhatNN μ g ξ : ENNReal)) := by
  refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top ?_ (lintegral_mono fun ξ => fhatNN_le g ξ))
  rw [lintegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)

lemma IsInvClass.withDensity_innerRegular (ν : Measure (PontryaginDual G)) [IsFiniteMeasure ν]
    [ν.InnerRegular] {g : G → ℂ} (hg : IsInvClass μ g) :
    (ν.withDensity fun ξ => (fhatNN μ g ξ : ENNReal)).InnerRegular := by
  refine innerRegular_withDensity ν (measurable_coe_nnreal_ennreal.comp hg.measurable_fhatNN)
    ENNReal.ofReal_ne_top (fun ξ => fhatNN_le g ξ) ?_
  have := hg.withDensity_finite ν
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
  exact measure_ne_top _ _

/-- Transform of $\hat g\,\nu$ for a finite inner regular $\nu$ with transform $f$:
$x\mapsto\int g(xy)\overline{f(y)}\,dy$. -/
lemma fourierStieltjes_withDensity_fhat (ν : Measure (PontryaginDual G)) [IsFiniteMeasure ν] [ν.InnerRegular]
    {g : G → ℂ} (hg : IsInvClass μ g) (x : G) :
    fourierStieltjes (ν.withDensity fun ξ => (fhatNN μ g ξ : ENNReal)) x =
      ∫ y, g (x * y) * conj (fourierStieltjes ν y) ∂μ := by
  rw [fourierStieltjes_withDensity ν hg.measurable_fhatNN]
  have htr : HasCompactSupport fun w => g (x * w) :=
    hg.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft x)
  have hc : Continuous fun w => g (x * w) := hg.continuous.comp (continuous_const.mul continuous_id)
  rw [← integral_fhat ν hc (hc.integrable_of_hasCompactSupport htr)]
  congr 1 with ξ
  rw [hg.coe_fhatNN, fhat_translate, mul_comm]

/-- **Consistency of the Bochner measures** (Folland, proof of Theorem 4.33): $\hat g\,\mu_f=\hat f\,\mu_g$. -/
theorem withDensity_bochnerMeasure_comm {f g : G → ℂ} (hf : IsInvClass μ f) (hg : IsInvClass μ g) :
    (bochnerMeasure hB hf).withDensity (fun ξ => (fhatNN μ g ξ : ENNReal)) =
      (bochnerMeasure hB hg).withDensity (fun ξ => (fhatNN μ f ξ : ENNReal)) := by
  have := hg.withDensity_finite (bochnerMeasure hB hf)
  have := hf.withDensity_finite (bochnerMeasure hB hg)
  refine hB.ext G _ _ inferInstance inferInstance (hg.withDensity_innerRegular _)
    (hf.withDensity_innerRegular _) fun x => ?_
  rw [fourierStieltjes_withDensity_fhat _ hg, fourierStieltjes_withDensity_fhat _ hf]
  simp_rw [fourierStieltjes_bochnerMeasure]
  rw [← integral_mul_left_eq_self _ x⁻¹, ← integral_inv_eq_self]
  congr 1 with y
  rw [hf.conj_eq hB, show x * (x⁻¹ * y⁻¹) = y⁻¹ by group,
    show (x⁻¹ * y⁻¹)⁻¹ = x * y by rw [mul_inv_rev, inv_inv, inv_inv, mul_comm], ← hg.conj_eq hB, mul_comm]

/-- **Twisting translates the Bochner measure**: $\mu_{f\bar\eta}$ is the image of $\mu_f$ under
$\xi\mapsto\eta^{-1}\xi$. -/
theorem bochnerMeasure_twist {f : G → ℂ} (hf : IsInvClass μ f) (η : PontryaginDual G) :
    bochnerMeasure hB (hf.twist η) = (bochnerMeasure hB hf).map (fun ξ => η⁻¹ * ξ) := by
  refine hB.ext G _ _ inferInstance inferInstance inferInstance inferInstance fun x => ?_
  rw [fourierStieltjes_bochnerMeasure]
  unfold fourierStieltjes
  rw [integral_map (measurable_const_mul _).aemeasurable
    (continuous_apply_dual x).aestronglyMeasurable]
  simp_rw [dual_mul_apply, Circle.coe_mul]
  rw [integral_const_mul]
  have := fourierStieltjes_bochnerMeasure (hB := hB) hf x
  unfold fourierStieltjes at this
  rw [this, twist, dual_inv_apply, Circle.coe_inv_eq_conj, mul_comm]

end BochnerMeasure

section Functional

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] {hB : BochnerTheorem.{u}}

/-- A bounded quotient: if $\hat g>0$ on the support of $\psi$, then $\psi/\hat g$ is integrable for every finite
measure. -/
lemma integrable_div_fhat (ν : Measure (PontryaginDual G)) [IsFiniteMeasure ν] {g : G → ℂ}
    (hg : IsInvClass μ g) (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ)
    (hpos : ∀ ξ ∈ tsupport ψ, 0 < (fhat μ g ξ).re) :
    Integrable (fun ξ => ψ ξ / (fhat μ g ξ).re) ν := by
  have hcre : Continuous fun ξ => (fhat μ g ξ).re := Complex.continuous_re.comp hg.continuous_fhat
  obtain ⟨m, hm, hmK⟩ := (ψ.hasCompactSupport : IsCompact (tsupport ψ)).exists_forall_le'
    hcre.continuousOn hpos
  obtain ⟨M, hM⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  refine Integrable.of_bound ((ψ.continuous.measurable.div hcre.measurable).aestronglyMeasurable) (M / m)
    (Eventually.of_forall fun ξ => ?_)
  by_cases hξ : ξ ∈ tsupport ψ
  · have h1 := hmK ξ hξ
    rw [norm_div, Real.norm_of_nonneg (hm.le.trans h1)]
    exact div_le_div₀ ((norm_nonneg _).trans (hM ξ)) (hM ξ) hm h1
  · rw [image_eq_zero_of_notMem_tsupport hξ, zero_div, norm_zero]
    exact div_nonneg ((norm_nonneg _).trans (hM ξ)) hm.le

lemma div_mul_cancel_of_pos {a b c : ℝ} (h : a ≠ 0 → 0 < b ∧ 0 < c) : a / b = a / (b * c) * c := by
  by_cases ha : a = 0
  · simp [ha]
  · obtain ⟨hb, hc⟩ := h ha
    field_simp

/-- **The functional is independent of the auxiliary function**: if $\hat g,\hat g'>0$ on the support of $\psi$,
then $\int\psi/\hat g\,d\mu_g=\int\psi/\hat g'\,d\mu_{g'}$. -/
theorem integral_div_fhat_eq {g g' : G → ℂ} (hg : IsInvClass μ g) (hg' : IsInvClass μ g')
    (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ)
    (hpos : ∀ ξ ∈ tsupport ψ, 0 < (fhat μ g ξ).re) (hpos' : ∀ ξ ∈ tsupport ψ, 0 < (fhat μ g' ξ).re) :
    ∫ ξ, ψ ξ / (fhat μ g ξ).re ∂(bochnerMeasure hB hg) =
      ∫ ξ, ψ ξ / (fhat μ g' ξ).re ∂(bochnerMeasure hB hg') := by
  have hsupp : ∀ ξ, ψ ξ ≠ 0 → ξ ∈ tsupport ψ := fun ξ h => subset_tsupport _ h
  set F : PontryaginDual G → ℝ := fun ξ => ψ ξ / ((fhat μ g ξ).re * (fhat μ g' ξ).re)
  have h1 : ∀ ξ, ψ ξ / (fhat μ g ξ).re = (fhatNN μ g' ξ : ℝ) • F ξ := by
    intro ξ
    rw [fhatNN, Real.coe_toNNReal _ (hg'.re_nonneg ξ), smul_eq_mul, mul_comm]
    exact div_mul_cancel_of_pos fun h => ⟨hpos ξ (hsupp ξ h), hpos' ξ (hsupp ξ h)⟩
  have h2 : ∀ ξ, ψ ξ / (fhat μ g' ξ).re = (fhatNN μ g ξ : ℝ) • F ξ := by
    intro ξ
    rw [fhatNN, Real.coe_toNNReal _ (hg.re_nonneg ξ), smul_eq_mul, mul_comm]
    have := div_mul_cancel_of_pos (a := ψ ξ) (b := (fhat μ g' ξ).re) (c := (fhat μ g ξ).re)
      fun h => ⟨hpos' ξ (hsupp ξ h), hpos ξ (hsupp ξ h)⟩
    rw [this, mul_comm (fhat μ g' ξ).re]
  simp_rw [h1, h2]
  have e1 := integral_withDensity_eq_integral_smul hg'.measurable_fhatNN (μ := bochnerMeasure hB hg) F
  have e2 := integral_withDensity_eq_integral_smul hg.measurable_fhatNN (μ := bochnerMeasure hB hg') F
  simp only [NNReal.smul_def] at e1 e2 ⊢
  rw [← e1, ← e2, withDensity_bochnerMeasure_comm]

variable (hB μ)

/-- The auxiliary function chosen for $\psi$: $\hat g>0$ on the support of $\psi$. -/
def auxFun (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) : G → ℂ :=
  Classical.choose (exists_isInvClass_pos_on (μ := μ) ψ.hasCompactSupport)

variable {hB μ}

lemma auxFun_spec (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) :
    IsInvClass μ (auxFun μ ψ) ∧ ∀ ξ ∈ tsupport ψ, 0 < (fhat μ (auxFun μ ψ) ξ).re :=
  Classical.choose_spec (exists_isInvClass_pos_on (μ := μ) ψ.hasCompactSupport)

variable (hB μ)

/-- The value $\int\psi/\hat g\,d\mu_g$ of the functional. -/
def invFunctionalValue (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) : ℝ :=
  ∫ ξ, ψ ξ / (fhat μ (auxFun μ ψ) ξ).re ∂(bochnerMeasure hB (auxFun_spec (μ := μ) ψ).1)

variable {hB μ}

lemma invFunctionalValue_eq {g : G → ℂ} (hg : IsInvClass μ g)
    (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) (hpos : ∀ ξ ∈ tsupport ψ, 0 < (fhat μ g ξ).re) :
    invFunctionalValue μ hB ψ = ∫ ξ, ψ ξ / (fhat μ g ξ).re ∂(bochnerMeasure hB hg) :=
  integral_div_fhat_eq _ hg ψ (auxFun_spec ψ).2 hpos

lemma tsupport_add_subset (ψ₁ ψ₂ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) :
    tsupport (ψ₁ + ψ₂ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) ⊆ tsupport ψ₁ ∪ tsupport ψ₂ :=
  (closure_mono (Function.support_add _ _)).trans closure_union.subset

lemma fhat_pos_add {g₁ g₂ : G → ℂ} (h1 : IsInvClass μ g₁) (h2 : IsInvClass μ g₂) {S₁ S₂ : Set (PontryaginDual G)}
    (p1 : ∀ ξ ∈ S₁, 0 < (fhat μ g₁ ξ).re) (p2 : ∀ ξ ∈ S₂, 0 < (fhat μ g₂ ξ).re) :
    ∀ ξ ∈ S₁ ∪ S₂, 0 < (fhat μ (g₁ + g₂) ξ).re := by
  intro ξ hξ
  rw [fhat_add h1.continuous h1.hasCompactSupport h2.continuous h2.hasCompactSupport, Complex.add_re]
  rcases hξ with h | h
  · exact add_pos_of_pos_of_nonneg (p1 ξ h) (h2.re_nonneg ξ)
  · exact add_pos_of_nonneg_of_pos (h1.re_nonneg ξ) (p2 ξ h)

variable (hB μ)

/-- **The inversion functional** $\psi\mapsto\int\psi/\hat g\,d\mu_g$, a positive linear functional on
$C_c(G^*,\mathbb R)$. -/
def inversionFunctional : CompactlySupportedContinuousMap (PontryaginDual G) ℝ →ₚ[ℝ] ℝ where
  toFun := invFunctionalValue μ hB
  map_add' ψ₁ ψ₂ := by
    obtain ⟨h1, p1⟩ := auxFun_spec (μ := μ) ψ₁
    obtain ⟨h2, p2⟩ := auxFun_spec (μ := μ) ψ₂
    have hg := h1.add h2
    have hpos := fhat_pos_add h1 h2 p1 p2
    rw [invFunctionalValue_eq hg _ fun ξ hξ => hpos ξ (tsupport_add_subset ψ₁ ψ₂ hξ),
      invFunctionalValue_eq hg _ fun ξ hξ => hpos ξ (Or.inl hξ),
      invFunctionalValue_eq hg _ fun ξ hξ => hpos ξ (Or.inr hξ),
      ← integral_add (integrable_div_fhat _ hg _ fun ξ hξ => hpos ξ (Or.inl hξ))
        (integrable_div_fhat _ hg _ fun ξ hξ => hpos ξ (Or.inr hξ))]
    congr 1 with ξ
    simp [add_div]
  map_smul' c ψ := by
    obtain ⟨h1, p1⟩ := auxFun_spec (μ := μ) ψ
    rw [invFunctionalValue_eq h1 (c • ψ) fun ξ hξ => p1 ξ (tsupport_smul_subset_right (fun _ => c) ψ (by exact hξ)),
      invFunctionalValue_eq h1 ψ p1, RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1 with ξ
    simp [mul_div_assoc]
  monotone' ψ₁ ψ₂ hle := by
    obtain ⟨h1, p1⟩ := auxFun_spec (μ := μ) ψ₁
    obtain ⟨h2, p2⟩ := auxFun_spec (μ := μ) ψ₂
    have hg := h1.add h2
    have hpos := fhat_pos_add h1 h2 p1 p2
    change invFunctionalValue μ hB ψ₁ ≤ invFunctionalValue μ hB ψ₂
    rw [invFunctionalValue_eq hg _ fun ξ hξ => hpos ξ (Or.inl hξ),
      invFunctionalValue_eq hg _ fun ξ hξ => hpos ξ (Or.inr hξ)]
    refine integral_mono (integrable_div_fhat _ hg _ fun ξ hξ => hpos ξ (Or.inl hξ))
      (integrable_div_fhat _ hg _ fun ξ hξ => hpos ξ (Or.inr hξ)) fun ξ => ?_
    exact div_le_div_of_nonneg_right (hle ξ) (hg.re_nonneg ξ)

/-- **The dual Haar measure** $\lambda$ on $G^*$: the Riesz–Markov–Kakutani measure of the inversion functional. -/
def dualHaar : Measure (PontryaginDual G) := RealRMK.rieszMeasure (inversionFunctional μ hB)

end Functional

section DualHaar

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] {hB : BochnerTheorem.{u}}

instance : (dualHaar μ hB).Regular := by unfold dualHaar; infer_instance

lemma integral_dualHaar (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) :
    ∫ ξ, ψ ξ ∂(dualHaar μ hB) = invFunctionalValue μ hB ψ :=
  RealRMK.integral_rieszMeasure (inversionFunctional μ hB) ψ

/-- $\psi\hat f$ as a compactly supported continuous function. -/
def mulFhat (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) {f : G → ℂ} (hf : IsInvClass μ f) :
    CompactlySupportedContinuousMap (PontryaginDual G) ℝ :=
  ⟨⟨fun ξ => ψ ξ * (fhat μ f ξ).re, ψ.continuous.mul (Complex.continuous_re.comp hf.continuous_fhat)⟩,
    ψ.hasCompactSupport.mul_right⟩

/-- **The functional on $\psi\hat f$ is $\int\psi\,d\mu_f$.** -/
theorem invFunctionalValue_mulFhat (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) {f : G → ℂ}
    (hf : IsInvClass μ f) : invFunctionalValue μ hB (mulFhat ψ hf) = ∫ ξ, ψ ξ ∂(bochnerMeasure hB hf) := by
  obtain ⟨hg, p⟩ := auxFun_spec (μ := μ) ψ
  set g := auxFun μ ψ
  have hsub : tsupport (mulFhat ψ hf) ⊆ tsupport ψ := tsupport_mul_subset_left
  rw [invFunctionalValue_eq hg _ fun ξ hξ => p ξ (hsub hξ)]
  have hsupp : ∀ ξ, ψ ξ ≠ 0 → ξ ∈ tsupport ψ := fun ξ h => subset_tsupport _ h
  have h1 : ∀ ξ, (mulFhat ψ hf) ξ / (fhat μ g ξ).re = (fhatNN μ f ξ : ℝ) • (ψ ξ / (fhat μ g ξ).re) := by
    intro ξ
    rw [fhatNN, Real.coe_toNNReal _ (hf.re_nonneg ξ), smul_eq_mul]
    show ψ ξ * (fhat μ f ξ).re / (fhat μ g ξ).re = _
    ring
  have h2 : ∀ ξ, ψ ξ = (fhatNN μ g ξ : ℝ) • (ψ ξ / (fhat μ g ξ).re) := by
    intro ξ
    rw [fhatNN, Real.coe_toNNReal _ (hg.re_nonneg ξ), smul_eq_mul]
    by_cases h : ψ ξ = 0
    · simp [h]
    · have := p ξ (hsupp ξ h)
      field_simp
  simp_rw [h1]
  conv_rhs => rw [integral_congr_ae (Eventually.of_forall h2)]
  have e1 := integral_withDensity_eq_integral_smul hf.measurable_fhatNN (μ := bochnerMeasure hB hg)
    (fun ξ => ψ ξ / (fhat μ g ξ).re)
  have e2 := integral_withDensity_eq_integral_smul hg.measurable_fhatNN (μ := bochnerMeasure hB hf)
    (fun ξ => ψ ξ / (fhat μ g ξ).re)
  simp only [NNReal.smul_def] at e1 e2
  rw [← e1, ← e2, withDensity_bochnerMeasure_comm hf hg]

/-- **The Bochner measure is $\hat f$ times the dual Haar measure**: $\mu_f=\hat f\,\lambda$ (Folland, Theorem
4.33). -/
theorem bochnerMeasure_eq_withDensity {f : G → ℂ} (hf : IsInvClass μ f) :
    bochnerMeasure hB hf = (dualHaar μ hB).withDensity fun ξ => ENNReal.ofReal (fhat μ f ξ).re := by
  refine eq_withDensity_of_integral_eq (dualHaar μ hB) (bochnerMeasure hB hf)
    (Complex.continuous_re.comp hf.continuous_fhat) (fun ξ => hf.re_nonneg ξ)
    (C := ∫ x, ‖f x‖ ∂μ) (fun ξ => (Complex.re_le_norm _).trans (norm_fhat_le μ f ξ)) fun ψ => ?_
  rw [← invFunctionalValue_mulFhat ψ hf, ← integral_dualHaar]
  rfl

/-- Translating a compactly supported function by $\eta$. -/
def translateCc (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ) (η : PontryaginDual G) :
    CompactlySupportedContinuousMap (PontryaginDual G) ℝ :=
  ⟨⟨fun ξ => ψ (η * ξ), ψ.continuous.comp ((continuous_const.mul continuous_id : Continuous fun ξ : PontryaginDual G => η * ξ))⟩,
    ψ.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft η)⟩

/-- **The functional is translation invariant.** -/
theorem invFunctionalValue_translate (ψ : CompactlySupportedContinuousMap (PontryaginDual G) ℝ)
    (η : PontryaginDual G) : invFunctionalValue μ hB (translateCc ψ η) = invFunctionalValue μ hB ψ := by
  obtain ⟨hg, p⟩ := auxFun_spec (μ := μ) ψ
  set g := auxFun μ ψ
  have hpos : ∀ ξ ∈ tsupport (translateCc ψ η), 0 < (fhat μ (twist g η) ξ).re := by
    intro ξ hξ
    rw [fhat_twist]
    exact p _ (tsupport_comp_subset_preimage ψ ((continuous_const.mul continuous_id : Continuous fun ξ : PontryaginDual G => η * ξ)) hξ)
  rw [invFunctionalValue_eq (hg.twist η) _ hpos, invFunctionalValue_eq hg ψ p, bochnerMeasure_twist hg η]
  have hm : Measurable fun ξ : PontryaginDual G => (translateCc ψ η) ξ / (fhat μ (twist g η) ξ).re :=
    (translateCc ψ η).continuous.measurable.div
      (Complex.continuous_re.comp (hg.twist η).continuous_fhat).measurable
  rw [integral_map (measurable_const_mul _).aemeasurable hm.aestronglyMeasurable]
  congr 1 with ξ
  show ψ (η * (η⁻¹ * ξ)) / (fhat μ (twist g η) (η⁻¹ * ξ)).re = _
  rw [fhat_twist, mul_inv_cancel_left]

/-- **The dual measure is left invariant.** -/
theorem isMulLeftInvariant_dualHaar : (dualHaar μ hB).IsMulLeftInvariant := by
  refine ⟨fun η => ?_⟩
  have : (Measure.map (fun ξ => η * ξ) (dualHaar μ hB)).Regular :=
    Measure.Regular.map (μ := dualHaar μ hB) (Homeomorph.mulLeft η)
  refine Measure.ext_of_integral_eq_on_compactlySupported fun ψ => ?_
  rw [integral_map (φ := fun ξ => η * ξ) (f := fun ξ => ψ ξ) (measurable_const_mul η).aemeasurable
    ψ.continuous.aestronglyMeasurable]
  have := integral_dualHaar (μ := μ) (hB := hB) (translateCc ψ η)
  rw [invFunctionalValue_translate, ← integral_dualHaar] at this
  exact this

/-- A function of the class with $f(1)\ne0$ (an autocorrelation of a bump function). -/
lemma exists_isInvClass_ne_zero : ∃ f : G → ℂ, IsInvClass μ f ∧ f 1 ≠ 0 := by
  obtain ⟨b, hbc, hb0, hb1⟩ := exists_continuous_nonneg_pos (1 : G)
  set u : G → ℂ := fun y => ((b y : ℝ) : ℂ) with hu
  have huc : Continuous u := Complex.continuous_ofReal.comp b.continuous
  have hus : HasCompactSupport u := HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hbc Complex.ofReal_zero
  refine ⟨autocorr μ u, isInvClass_autocorr huc hus, ?_⟩
  have hpos : 0 < ∫ y, b y * b y ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (b.continuous.mul b.continuous)
      hbc.mul_left (fun y => mul_self_nonneg _) (mul_ne_zero hb1 hb1)
  have : autocorr μ u 1 = ((∫ y, b y * b y ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    unfold autocorr
    congr 1 with y
    simp [hu, Complex.conj_ofReal]
  rw [this]
  exact_mod_cast hpos.ne'

/-- **The dual measure is a Haar measure on $G^*$.** -/
theorem isHaarMeasure_dualHaar : (dualHaar μ hB).IsHaarMeasure := by
  have hinv := isMulLeftInvariant_dualHaar (μ := μ) (hB := hB)
  have hne : NeZero (dualHaar μ hB) := by
    refine ⟨fun h0 => ?_⟩
    obtain ⟨f, hf, hf1⟩ := exists_isInvClass_ne_zero (μ := μ)
    have := bochnerMeasure_eq_withDensity (hB := hB) hf
    rw [h0, withDensity_zero_left] at this
    apply hf1
    rw [← fourierStieltjes_bochnerMeasure (hB := hB) hf, this]
    simp [fourierStieltjes]
  exact
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := hinv
      toIsOpenPosMeasure := inferInstance }

/-- **Fourier inversion for the class** (Folland, Theorem 4.33): $\hat f$ is integrable for the dual Haar measure
$\lambda$, and $f(x)=\int\hat f(\xi)\xi(x)\,d\lambda(\xi)$. -/
theorem inversion_isInvClass {f : G → ℂ} (hf : IsInvClass μ f) :
    Integrable (fhat μ f) (dualHaar μ hB) ∧
      ∀ x, f x = ∫ ξ, fhat μ f ξ * ((ξ x : Circle) : ℂ) ∂(dualHaar μ hB) := by
  have heq := bochnerMeasure_eq_withDensity (hB := hB) hf
  have hfun : fhat μ f = fun ξ => (((fhat μ f ξ).re : ℝ) : ℂ) := funext hf.fhat_eq_re
  constructor
  · rw [hfun]
    refine Integrable.ofReal ⟨(Complex.continuous_re.comp hf.continuous_fhat).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => hf.re_nonneg ξ), ← setLIntegral_univ,
      ← withDensity_apply _ MeasurableSet.univ, ← heq]
    exact measure_lt_top _ _
  · intro x
    rw [← fourierStieltjes_bochnerMeasure (hB := hB) hf x, heq]
    have := fourierStieltjes_withDensity (dualHaar μ hB) hf.measurable_fhatNN x
    refine this.trans ?_
    congr 1 with ξ
    rw [hf.coe_fhatNN]

end DualHaar

end NumberFieldKB.Pontryagin
