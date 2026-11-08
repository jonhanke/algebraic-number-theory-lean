import NumberFieldKB.Pontryagin.FourierInversion

/-!
# Functions annihilated by the inversion class vanish

$G$ is a locally compact commutative Hausdorff group with a regular Haar measure $\mu$.

* **`eq_zero_of_forall_integral_isInvClass`**: a continuous $D$ with $\int D(y)k(y^{-1}x)\,d\mu(y)=0$ for every $k$ in
  the inversion class (`IsInvClass`) and every $x$ is zero. Proof: if $D(x_0)\ne0$, take $k=u\star\tilde u$ for a bump
  function $u\ge0$ supported so close to $1$ that $|D(y)-D(x_0)|<|D(x_0)|/2$ whenever $k(y^{-1}x_0)\ne0$; then
  $\left|\int D(y)k(y^{-1}x_0)\,dy-D(x_0)\int k\right|\le\frac12|D(x_0)|\int k$ and $\int k>0$ (an approximate
  identity; Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., Proposition 2.42).
-/

open MeasureTheory Topology Filter ComplexConjugate

noncomputable section

namespace NumberFieldKB.Pontryagin

/-- A non-negative real bump in the inversion class, supported in a given neighbourhood of `1`, with positive
integral. -/
lemma exists_realBump_isInvClass {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ k : G → ℝ, (∀ x, 0 ≤ k x) ∧ (∀ x ∉ U, k x = 0) ∧ Continuous k ∧ HasCompactSupport k ∧
      0 < ∫ x, k x ∂μ ∧ IsInvClass μ (fun x => (k x : ℂ)) := by
  obtain ⟨V, hVo, hV1, hVx⟩ := exists_open_nhds_one_split hU
  set W := V ∩ V⁻¹ with hW
  have hWo : IsOpen W := hVo.inter hVo.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1, by simpa using hV1⟩
  have hWx : ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ U := by
    intro a ha b hb
    exact hVx a ha.1 b⁻¹ (by simpa using hb.2)
  obtain ⟨f, hf1, hfc, hfW, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    isCompact_singleton hWo (Set.singleton_subset_iff.mpr hW1)
  have hf0 : ∀ y, 0 ≤ f y := fun y => (hf01 y).1
  set u : G → ℂ := fun y => ((f y : ℝ) : ℂ) with hu
  have huc : Continuous u := Complex.continuous_ofReal.comp f.continuous
  have hus : HasCompactSupport u := by
    refine HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) ?_ Complex.ofReal_zero
    exact hfc
  have hreal : ∀ x, autocorr μ u x = ((∫ y, f y * f (x⁻¹ * y) ∂μ : ℝ) : ℂ) := by
    intro x
    rw [← integral_complex_ofReal]
    unfold autocorr
    congr 1 with y
    simp [hu, Complex.conj_ofReal]
  have hinv := isInvClass_autocorr (μ := μ) huc hus
  set k : G → ℝ := fun x => ∫ y, f y * f (x⁻¹ * y) ∂μ with hk
  have hkc : ((fun x => (k x : ℂ))) = autocorr μ u := by
    funext x; exact (hreal x).symm
  have h2 : k = fun x => (autocorr μ u x).re := by
    funext x; rw [hreal x, Complex.ofReal_re]
  have hkcont : Continuous k := by
    rw [h2]; exact Complex.continuous_re.comp hinv.continuous
  have hksupp : HasCompactSupport k := by
    rw [h2]
    exact HasCompactSupport.comp_left (g := fun z : ℂ => z.re) hinv.hasCompactSupport (by simp)
  have hk0 : ∀ x, 0 ≤ k x := fun x =>
    integral_nonneg fun y => mul_nonneg (hf0 _) (hf0 _)
  have hkU : ∀ x ∉ U, k x = 0 := by
    intro x hx
    have : autocorr μ u x = 0 := by
      apply autocorr_eq_zero
      intro y
      by_contra hy
      push Not at hy
      have hy1 : y ∈ W := hfW (subset_tsupport _ (fun h => hy.1 (by simp [hu, h])))
      have hy2 : x⁻¹ * y ∈ W := hfW (subset_tsupport _ (fun h => hy.2 (by simp [hu, h])))
      exact hx (by simpa using hWx y hy1 (x⁻¹ * y) hy2)
    rw [h2]; simp [this]
  have hk1 : 0 < k 1 := by
    simp only [hk, inv_one, one_mul]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (f.continuous.mul f.continuous) (show HasCompactSupport f from hfc).mul_left
      (fun y => mul_self_nonneg _) ?_
    have : f 1 = 1 := hf1 rfl
    simp [this]
  refine ⟨k, hk0, hkU, hkcont, hksupp, ?_, ?_⟩
  · exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hkcont hksupp hk0 hk1.ne'
  · rw [hkc]; exact hinv

/-- **A continuous function annihilated by all translates of the inversion class is zero.** -/
theorem eq_zero_of_forall_integral_isInvClass {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] {D : G → ℂ} (hD : Continuous D)
    (h : ∀ k : G → ℂ, IsInvClass μ k → ∀ x, ∫ y, D y * k (y⁻¹ * x) ∂μ = 0) : D = 0 := by
  by_contra hne
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, D x₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  have hpos : 0 < ‖D x₀‖ := norm_pos_iff.mpr hx₀
  set ε : ℝ := ‖D x₀‖ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hUo : IsOpen {w : G | ‖D (x₀ * w⁻¹) - D x₀‖ < ε} :=
    isOpen_lt (by fun_prop) continuous_const
  have hU : {w : G | ‖D (x₀ * w⁻¹) - D x₀‖ < ε} ∈ 𝓝 (1 : G) := by
    refine hUo.mem_nhds ?_
    simp [hεpos]
  obtain ⟨k, hk0, hkU, hkc, hks, hkint, hkcls⟩ := exists_realBump_isInvClass μ hU
  have h0 := h _ hkcls x₀
  -- the reflected translate of `k`
  let φ : G ≃ₜ G := (Homeomorph.inv G).trans (Homeomorph.mulRight x₀)
  have hφ : ∀ y, φ y = y⁻¹ * x₀ := fun y => rfl
  have hKc : Continuous fun y => k (y⁻¹ * x₀) := by fun_prop
  have hKs : HasCompactSupport fun y => k (y⁻¹ * x₀) := hks.comp_homeomorph φ
  have hKint : Integrable (fun y => k (y⁻¹ * x₀)) μ := hKc.integrable_of_hasCompactSupport hKs
  have hKsum : ∫ y, k (y⁻¹ * x₀) ∂μ = ∫ y, k y ∂μ := by
    have e1 : ∫ y, k (y⁻¹ * x₀) ∂μ = ∫ y, (fun z => k (z * x₀)) y⁻¹ ∂μ := rfl
    rw [e1, integral_inv_eq_self (fun z => k (z * x₀)) μ, integral_mul_right_eq_self k x₀]
  have hDK : Integrable (fun y => D y * (k (y⁻¹ * x₀) : ℂ)) μ := by
    refine (hD.mul (Complex.continuous_ofReal.comp hKc)).integrable_of_hasCompactSupport ?_
    exact (HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hKs Complex.ofReal_zero).mul_left
  have hKC : Integrable (fun y => (k (y⁻¹ * x₀) : ℂ)) μ := hKint.ofReal
  have hdiff : ∫ y, (D y - D x₀) * (k (y⁻¹ * x₀) : ℂ) ∂μ = - (D x₀ * ((∫ y, k y ∂μ : ℝ) : ℂ)) := by
    have : (fun y => (D y - D x₀) * (k (y⁻¹ * x₀) : ℂ)) =
        fun y => D y * (k (y⁻¹ * x₀) : ℂ) - D x₀ * (k (y⁻¹ * x₀) : ℂ) := by
      funext y; ring
    rw [this, integral_sub hDK (hKC.const_mul _), h0, integral_const_mul,
      integral_complex_ofReal, hKsum]
    ring
  have hle : ‖∫ y, (D y - D x₀) * (k (y⁻¹ * x₀) : ℂ) ∂μ‖ ≤ ∫ y, ε * k (y⁻¹ * x₀) ∂μ := by
    refine norm_integral_le_of_norm_le (hKint.const_mul ε) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk0 _)]
    by_cases hy : k (y⁻¹ * x₀) = 0
    · simp [hy]
    · have hmem : y⁻¹ * x₀ ∈ {w : G | ‖D (x₀ * w⁻¹) - D x₀‖ < ε} := by
        by_contra hnot
        exact hy (hkU _ hnot)
      have : x₀ * (y⁻¹ * x₀)⁻¹ = y := by group
      simp only [Set.mem_ofPred_eq, this] at hmem
      exact mul_le_mul_of_nonneg_right hmem.le (hk0 _)
  rw [hdiff, integral_const_mul, hKsum, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hkint] at hle
  nlinarith

end NumberFieldKB.Pontryagin
