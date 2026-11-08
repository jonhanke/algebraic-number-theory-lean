import NumberFieldKB.MilneEC.Ch5Differentials

/-!
# Milne, *Elliptic Curves*, Chapter V, Proposition 3.3 in local form: elliptic points

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §3, Proposition 3.3 (pdf p. 199). See
`NumberFieldKB/MilneEC/Ch5Differentials.lean` for the statement and the other two local computations. At an elliptic
point $z_0$ of order $e$ Milne's coordinate is $t = w^e$, $w = (z - z_0)/(z - \bar z_0)$; this file proves that
$f(z)\,dz$, $f$ holomorphic of weight 2, is holomorphic in $t$ (`prop_3_3_elliptic`), so the elliptic points impose
no condition.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Function
open scoped MatrixGroups Real Manifold ComplexConjugate

noncomputable section

namespace NumberFieldKB.MilneEC.V

/-! ### Elliptic points -/

/-- **Proposition 3.3, the local computation at an elliptic point** (pdf p. 199): a holomorphic differential
$\varphi(w)\,dw$ near $0$ invariant under the rotation $w \mapsto \zeta w$ by a primitive $e$-th root of unity
($\varphi(\zeta w)\,\zeta = \varphi(w)$) is $\psi(t)\,dt$ in the coordinate $t = w^e$, $\psi$ holomorphic at $0$:
$\varphi(w) = \psi(w^e)\cdot e\,w^{e-1}$. -/
@[kb "milne2006ec" "Ch. V, Proposition 3.3 (invariant differentials descend along t = w^e), pdf p. 199"]
theorem exists_analyticAt_of_rotation_invariant {e : ℕ} (he : 0 < e) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ e)
    {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0) (hinv : ∀ᶠ w in 𝓝 0, φ (ζ * w) * ζ = φ w) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ ∀ᶠ w in 𝓝 0, φ w = ψ (w ^ e) * (e * w ^ (e - 1)) := by
  obtain ⟨p, r, hp⟩ := hφ
  set a : ℕ → ℂ := p.coeff with ha
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one he.ne'
  have hpa : p = FormalMultilinearSeries.ofScalars ℂ a := by
    ext n
    rw [p.apply_eq_prod_smul_coeff]
    simp [FormalMultilinearSeries.ofScalars, ha, mul_comm]
  have hsum : ∀ y : ℂ, ‖y‖ₑ < r → HasSum (fun n => a n * y ^ n) (φ y) := by
    intro y hy
    have := hp.hasSum (y := y) (by simpa [mem_eball_zero_iff] using hy)
    simpa [hpa, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using this
  have hnorm : ∀ n, ‖p n‖ = ‖a n‖ := fun n => p.norm_apply_eq_norm_coef
  have hbound : ∀ s : NNReal, (s : ENNReal) < r → ∃ C, ∀ n, ‖a n‖ * (s : ℝ) ^ n ≤ C := by
    intro s hs
    obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius (lt_of_lt_of_le hs hp.r_le)
    exact ⟨C, fun n => by simpa [hnorm] using hC n⟩
  -- vanishing
  have hq : HasFPowerSeriesOnBall (fun w => φ (ζ * w) * ζ)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ζ ^ (n + 1) * a n)) 0 r := by
    refine ⟨?_, hp.r_pos, ?_⟩
    · refine ENNReal.le_of_forall_nnreal_lt fun s hs => ?_
      obtain ⟨C, hC⟩ := hbound s hs
      refine FormalMultilinearSeries.le_radius_of_bound _ C fun n => ?_
      rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, FormalMultilinearSeries.coeff_ofScalars]
      simpa [norm_mul, norm_pow, hζn] using hC n
    · intro y hy
      have hy' : ‖y‖ₑ < r := by simpa [mem_eball_zero_iff] using hy
      have hζe : ‖ζ‖ₑ = 1 := by rw [← ofReal_norm, hζn]; simp
      have h1 := (hsum (ζ * y) (by rwa [enorm_mul, hζe, one_mul])).mul_right ζ
      simp only [zero_add]
      convert h1 using 1
      funext n
      simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      ring
  have hq' : HasFPowerSeriesAt φ (FormalMultilinearSeries.ofScalars ℂ (fun n => ζ ^ (n + 1) * a n)) 0 :=
    hq.hasFPowerSeriesAt.congr (by exact hinv)
  have hpq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hq'
  rw [hpa, FormalMultilinearSeries.ofScalars_series_eq_iff] at hpq
  have hv : ∀ n, a n ≠ 0 → e ∣ n + 1 := by
    intro n hn
    have := congrFun hpq n
    have h2 : ζ ^ (n + 1) = 1 := by
      have h0 : a n * (ζ ^ (n + 1) - 1) = 0 := by linear_combination (-1 : ℂ) * this
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hn
      · exact sub_eq_zero.1 h
    exact hζ.dvd_of_pow_eq_one _ h2
  -- the series for ψ
  let b : ℕ → ℂ := fun m => a (m * e + (e - 1)) / e
  obtain ⟨s, hs0, hsr⟩ : ∃ s : NNReal, 0 < s ∧ (s : ENNReal) < r := by
    obtain ⟨s, hs0, hsr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
    exact ⟨s, by exact_mod_cast hs0, hsr⟩
  obtain ⟨C, hC⟩ := hbound s hsr
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs0
  have hrad : ((s ^ e : NNReal) : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ b).radius := by
    refine FormalMultilinearSeries.le_radius_of_bound _ (C / (s : ℝ) ^ (e - 1)) fun m => ?_
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, FormalMultilinearSeries.coeff_ofScalars]
    have h1 := hC (m * e + (e - 1))
    have h2 : (s : ℝ) ^ (m * e + (e - 1)) = ((s ^ e : NNReal) : ℝ) ^ m * (s : ℝ) ^ (e - 1) := by
      push_cast; rw [pow_add, ← pow_mul, mul_comm e m]
    rw [le_div_iff₀ (by positivity)]
    have h3 : ‖b m‖ ≤ ‖a (m * e + (e - 1))‖ := by
      simp only [b, norm_div, Complex.norm_natCast]
      have : (1 : ℝ) ≤ e := by exact_mod_cast he
      exact div_le_self (norm_nonneg _) this
    calc ‖b m‖ * ((s ^ e : NNReal) : ℝ) ^ m * (s : ℝ) ^ (e - 1)
        = ‖b m‖ * (s : ℝ) ^ (m * e + (e - 1)) := by rw [h2]; ring
      _ ≤ ‖a (m * e + (e - 1))‖ * (s : ℝ) ^ (m * e + (e - 1)) := by gcongr
      _ ≤ C := h1
  have hradpos : 0 < (FormalMultilinearSeries.ofScalars ℂ b).radius :=
    lt_of_lt_of_le (by exact_mod_cast pow_pos hs0 e) hrad
  have hψ := (FormalMultilinearSeries.ofScalars ℂ b).hasFPowerSeriesOnBall hradpos
  refine ⟨(FormalMultilinearSeries.ofScalars ℂ b).sum, hψ.analyticAt, ?_⟩
  have hball : Metric.ball (0 : ℂ) s ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hspos
  filter_upwards [hball] with w hw
  have hw' : ‖w‖ < s := by simpa using hw
  have hwe : ‖w ^ e‖ < (s : ℝ) ^ e := by
    rw [norm_pow]; exact pow_lt_pow_left₀ hw' (norm_nonneg _) he.ne'
  have hwe' : ‖w ^ e‖₊ < s ^ e := by rw [← NNReal.coe_lt_coe]; simpa using hwe
  have hmem : w ^ e ∈ Metric.eball (0 : ℂ) (FormalMultilinearSeries.ofScalars ℂ b).radius := by
    rw [mem_eball_zero_iff]
    refine lt_of_lt_of_le ?_ hrad
    rw [enorm_eq_nnnorm]
    exact_mod_cast hwe'
  have h1 := (hψ.hasSum hmem).mul_right ((e : ℂ) * w ^ (e - 1))
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h1
  have hwr : ‖w‖ₑ < r := by
    refine lt_trans ?_ hsr
    rw [enorm_eq_nnnorm]
    have : ‖w‖₊ < s := by rw [← NNReal.coe_lt_coe]; simpa using hw'
    exact_mod_cast this
  have h2 := hsum w hwr
  have hinj : Function.Injective (fun m : ℕ => m * e + (e - 1)) := by
    intro m m' h
    simp only at h
    have : m * e = m' * e := by omega
    exact Nat.eq_of_mul_eq_mul_right he this
  have h3 : HasSum (fun m => a (m * e + (e - 1)) * w ^ (m * e + (e - 1))) (φ w) := by
    refine (hinj.hasSum_iff (f := fun n => a n * w ^ n) (a := φ w) ?_).2 h2
    · intro n hn
      by_contra hne
      apply hn
      have hne' : a n ≠ 0 := fun h => hne (by simp [h])
      obtain ⟨k, hk⟩ := hv n hne'
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      refine ⟨j, ?_⟩
      simp only
      rw [Nat.mul_succ] at hk
      have : j * e = e * j := mul_comm _ _
      omega
  have h4 : (fun m => b m * (w ^ e) ^ m * ((e : ℂ) * w ^ (e - 1))) =
      fun m => a (m * e + (e - 1)) * w ^ (m * e + (e - 1)) := by
    funext m
    have : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
    simp only [b]
    rw [pow_add, ← pow_mul, mul_comm e m]
    field_simp
  rw [h4] at h1
  exact (h3.unique h1)

/-- The inverse of the disc coordinate $w = (z - z_0)/(z - \bar z_0)$ at $z_0 \in \mathbb H$:
$z = (z_0 - \bar z_0 w)/(1 - w)$. -/
def discInv (z₀ : ℍ) (w : ℂ) : ℂ :=
  ((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w)

/-- The rotation factor $\lambda = (cz_0+d)^{-2}$ of $\gamma$ at a fixed point $z_0$ (the derivative of $\gamma$
at $z_0$). -/
def rotationFactor (γ : SL(2, ℤ)) (z₀ : ℍ) : ℂ :=
  (((γ 1 0 : ℂ) * z₀ + γ 1 1) ^ 2)⁻¹

/-- A fixed point satisfies $az_0 + b = z_0(cz_0+d)$ with $cz_0 + d \ne 0$. -/
theorem fixed_eq (γ : SL(2, ℤ)) (z₀ : ℍ) (hfix : γ • z₀ = z₀) :
    ((γ 0 0 : ℂ) * z₀ + γ 0 1 = z₀ * ((γ 1 0 : ℂ) * z₀ + γ 1 1)) ∧
      ((γ 1 0 : ℂ) * z₀ + γ 1 1 ≠ 0) := by
  have hcoe := UpperHalfPlane.coe_specialLinearGroup_apply γ z₀
  rw [hfix] at hcoe
  simp at hcoe
  have hne : (γ 1 0 : ℂ) * z₀ + γ 1 1 ≠ 0 := by
    intro h; rw [h, div_zero] at hcoe; exact z₀.ne_zero hcoe
  exact ⟨by rw [eq_div_iff hne] at hcoe; linear_combination -hcoe, hne⟩

/-- Only $\pm 1$ rotate by the factor $1$: if $\gamma z_0 = z_0$ and $(cz_0+d)^2 = 1$ then $\gamma = \pm 1$.
(So the order of the rotation is the order of the image of $\gamma$ in $\mathrm{PSL}_2(\mathbb Z)$, the $e$ of
Milne's coordinate $t = w^e$.) -/
theorem eq_one_or_eq_neg_one_of_rotationFactor_eq_one (γ : SL(2, ℤ)) (z₀ : ℍ) (hfix : γ • z₀ = z₀)
    (h1 : rotationFactor γ z₀ = 1) : γ = 1 ∨ γ = -1 := by
  have hsq : ((γ 1 0 : ℂ) * z₀ + γ 1 1) ^ 2 = 1 := inv_eq_one.1 h1
  have hpm : (γ 1 0 : ℂ) * z₀ + γ 1 1 = 1 ∨ (γ 1 0 : ℂ) * z₀ + γ 1 1 = -1 := by
    have : ((γ 1 0 : ℂ) * z₀ + γ 1 1 - 1) * ((γ 1 0 : ℂ) * z₀ + γ 1 1 + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have him : ((γ 1 0 : ℂ) * z₀ + γ 1 1).im = 0 := by
    rcases hpm with h | h <;> rw [h] <;> simp
  have hc : γ 1 0 = 0 := by
    have h2 : (γ 1 0 : ℝ) * (z₀ : ℂ).im = 0 := by simpa using him
    have h3 : (γ 1 0 : ℝ) = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact h
      · exact absurd h z₀.im_pos.ne'
    exact_mod_cast h3
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
    have hcc : ((γ 1 0 : ℤ) : ℂ) = 0 := by exact_mod_cast hc
    rcases hpm with h | h
    · left; rw [hcc] at h; simp only [zero_mul, zero_add] at h; exact_mod_cast h
    · right; rw [hcc] at h; simp only [zero_mul, zero_add] at h; exact_mod_cast h
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  rw [hc] at hdet
  have hcoe := (fixed_eq γ z₀ hfix).1
  have hcc : ((γ 1 0 : ℤ) : ℂ) = 0 := by exact_mod_cast hc
  rw [hcc] at hcoe
  simp only [zero_mul, zero_add] at hcoe
  have had : γ 0 0 = γ 1 1 := by
    rcases hd with h | h
    · rw [h] at hdet ⊢; simpa using hdet
    · rw [h] at hdet ⊢; linarith
  have hb : γ 0 1 = 0 := by
    have : ((γ 0 1 : ℤ) : ℂ) = 0 := by
      have had' : ((γ 0 0 : ℤ) : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by exact_mod_cast had
      rw [had'] at hcoe
      linear_combination hcoe
    exact_mod_cast this
  rcases hd with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [had, h, hb, hc]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [had, h, hb, hc]

/-- For $\|w\| < 1$, $\mathrm{discInv}\,z_0\,w \in \mathbb H$. -/
theorem discInv_im_pos (z₀ : ℍ) {w : ℂ} (hw : ‖w‖ < 1) : 0 < (discInv z₀ w).im := by
  have hn : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.normSq_apply w
    have h2 : Complex.normSq w = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w
    nlinarith [norm_nonneg w]
  have hy : 0 < (1 - w).re ^ 2 + (1 - w).im ^ 2 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    nlinarith [sq_nonneg w.im, sq_nonneg (1 - w.re)]
  have hq := z₀.im_pos
  rw [discInv, Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.one_re, Complex.one_im, Complex.normSq_apply]
  have : ((z₀ : ℂ).im - ((z₀ : ℂ).re * w.im + -(z₀ : ℂ).im * w.re)) * (1 - w.re) /
      ((1 - w.re) * (1 - w.re) + (0 - w.im) * (0 - w.im)) -
      ((z₀ : ℂ).re - ((z₀ : ℂ).re * w.re - -(z₀ : ℂ).im * w.im)) * (0 - w.im) /
      ((1 - w.re) * (1 - w.re) + (0 - w.im) * (0 - w.im)) =
      (z₀ : ℂ).im * (1 - (w.re ^ 2 + w.im ^ 2)) / ((1 - w.re) ^ 2 + w.im ^ 2) := by
    have hD : (1 - w.re) * (1 - w.re) + (0 - w.im) * (0 - w.im) = (1 - w.re) ^ 2 + w.im ^ 2 := by
      ring
    rw [hD, ← sub_div]
    congr 1
    ring
  rw [this]
  apply div_pos
  · exact mul_pos hq (by linarith)
  · nlinarith [sq_nonneg w.im, sq_nonneg (1 - w.re)]

theorem alg_DD {a b c d z zb : ℂ} (hz : z - zb ≠ 0) (E1 : a * z + b = z * (c * z + d))
    (E2 : a * zb + b = zb * (c * zb + d)) (hdet : a * d - b * c = 1) :
    (c * z + d) * (c * zb + d) = 1 := by
  have ha : a = c * (z + zb) + d := by
    apply mul_right_cancel₀ hz
    linear_combination E1 - E2
  have hb : b = -c * z * zb := by linear_combination E1 - z * ha
  subst ha hb
  linear_combination hdet

theorem moeb_alg {a b c d z zb w : ℂ} (hw1 : 1 - w ≠ 0) (E1 : a * z + b = z * (c * z + d))
    (E2 : a * zb + b = zb * (c * zb + d)) (hDD : (c * z + d) * (c * zb + d) = 1)
    (hn : ‖c * zb + d‖ = 1) (hwn : ‖w‖ < 1) :
    (a * ((z - zb * w) / (1 - w)) + b) / (c * ((z - zb * w) / (1 - w)) + d) =
      (z - zb * (((c * z + d) ^ 2)⁻¹ * w)) / (1 - ((c * z + d) ^ 2)⁻¹ * w) := by
  have hinvD : ((c * z + d) ^ 2)⁻¹ = (c * zb + d) ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_pow, hDD, one_pow]
  rw [hinvD]
  have hμ : 1 - (c * zb + d) ^ 2 * w ≠ 0 := by
    intro h
    have h1 : (c * zb + d) ^ 2 * w = 1 := by linear_combination -h
    have := congrArg norm h1
    rw [norm_mul, norm_pow, hn] at this
    simp at this
    linarith
  have hDw : (c * z + d) - (c * zb + d) * w ≠ 0 := by
    intro h
    apply hμ
    have : (c * z + d) * (1 - (c * zb + d) ^ 2 * w) = 0 := by
      linear_combination h - (c * zb + d) * w * hDD
    rcases mul_eq_zero.1 this with h' | h'
    · exfalso
      rw [h'] at hDD; simp at hDD
    · exact h'
  have h1 : c * ((z - zb * w) / (1 - w)) + d = ((c * z + d) - (c * zb + d) * w) / (1 - w) := by
    field_simp
    ring
  have h2 : a * ((z - zb * w) / (1 - w)) + b =
      (z * (c * z + d) - zb * (c * zb + d) * w) / (1 - w) := by
    field_simp
    linear_combination E1 - w * E2
  rw [h1, h2, div_div_div_cancel_right₀ hw1, div_eq_div_iff hDw hμ]
  linear_combination ((zb - z) * w * (c * zb + d)) * hDD

theorem DD_eq (γ : SL(2, ℤ)) (z₀ : ℍ) (hfix : γ • z₀ = z₀) :
    ((γ 1 0 : ℂ) * z₀ + γ 1 1) * ((γ 1 0 : ℂ) * conj (z₀ : ℂ) + γ 1 1) = 1 := by
  obtain ⟨E1, -⟩ := fixed_eq γ z₀ hfix
  have E2 := congrArg (starRingEnd ℂ) E1
  simp only [map_add, map_mul, map_intCast] at E2
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  have hz : (z₀ : ℂ) - conj (z₀ : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact z₀.im_pos.ne' this
  exact alg_DD hz E1 E2 hdet

theorem norm_conjD (γ : SL(2, ℤ)) (z₀ : ℍ) (hfix : γ • z₀ = z₀) :
    ‖(γ 1 0 : ℂ) * conj (z₀ : ℂ) + γ 1 1‖ = 1 := by
  have h := DD_eq γ z₀ hfix
  have hc : (γ 1 0 : ℂ) * conj (z₀ : ℂ) + γ 1 1 = conj ((γ 1 0 : ℂ) * z₀ + γ 1 1) := by
    simp [map_add, map_mul]
  have h2 := congrArg norm h
  rw [norm_mul, norm_one] at h2
  rw [hc] at h2 ⊢
  rw [Complex.norm_conj] at h2 ⊢
  have h0 : 0 ≤ ‖(γ 1 0 : ℂ) * z₀ + γ 1 1‖ := norm_nonneg _
  nlinarith

theorem rotationFactor_eq (γ : SL(2, ℤ)) (z₀ : ℍ) (hfix : γ • z₀ = z₀) :
    rotationFactor γ z₀ = ((γ 1 0 : ℂ) * conj (z₀ : ℂ) + γ 1 1) ^ 2 := by
  unfold rotationFactor
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_pow, DD_eq γ z₀ hfix, one_pow]

theorem moebiusC_discInv (γ : SL(2, ℤ)) (z₀ : ℍ) (hfix : γ • z₀ = z₀) {w : ℂ} (hw : ‖w‖ < 1) :
    moebiusC γ (discInv z₀ w) = discInv z₀ (rotationFactor γ z₀ * w) := by
  obtain ⟨E1, -⟩ := fixed_eq γ z₀ hfix
  have E2 := congrArg (starRingEnd ℂ) E1
  simp only [map_add, map_mul, map_intCast] at E2
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this] at hw; simp at hw
  unfold moebiusC discInv
  rw [rotationFactor]
  exact moeb_alg hw1 E1 E2 (DD_eq γ z₀ hfix) (norm_conjD γ z₀ hfix) hw

/-- In the disc coordinate at a fixed point $z_0$ of $\gamma$, the transformation law of weight 2 says that
$\varphi(w)\,dw = f(z)\,dz$ is invariant under the rotation $w \mapsto \lambda w$. -/
theorem rotation_invariant_of_weight_two (γ : SL(2, ℤ)) (z₀ : ℍ) (hfix : γ • z₀ = z₀) (f : ℍ → ℂ)
    (hinv : ∀ z : ℍ, f (γ • z) * deriv (moebiusC γ) z = f z) :
    ∀ᶠ w in 𝓝 0, (f ∘ ofComplex) (discInv z₀ (rotationFactor γ z₀ * w)) *
        deriv (discInv z₀) (rotationFactor γ z₀ * w) * rotationFactor γ z₀ =
      (f ∘ ofComplex) (discInv z₀ w) * deriv (discInv z₀) w := by
  have hlam : ‖rotationFactor γ z₀‖ = 1 := by
    rw [rotationFactor_eq γ z₀ hfix, norm_pow, norm_conjD γ z₀ hfix, one_pow]
  have hdiff : ∀ u : ℂ, ‖u‖ < 1 → DifferentiableAt ℂ (discInv z₀) u := by
    intro u hu
    have hu1 : 1 - u ≠ 0 := by
      intro h
      have : u = 1 := by linear_combination -h
      rw [this] at hu; simp at hu
    unfold discInv
    exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).div
      ((differentiableAt_const _).sub differentiableAt_id) hu1
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ one_pos
  filter_upwards [hball] with w hw
  have hw' : ‖w‖ < 1 := by simpa using hw
  set l := rotationFactor γ z₀ with hl
  have hlw : ‖l * w‖ < 1 := by rw [norm_mul, hlam, one_mul]; exact hw'
  have hx := discInv_im_pos z₀ hw'
  set x := discInv z₀ w with hxdef
  let zz : ℍ := ⟨x, hx⟩
  have hγz : ((γ • zz : ℍ) : ℂ) = discInv z₀ (l * w) := by
    rw [← moebiusC_coe]
    exact moebiusC_discInv γ z₀ hfix hw'
  have e1 : (f ∘ ofComplex) (discInv z₀ (l * w)) = f (γ • zz) := by
    simp only [Function.comp, ← hγz, ofComplex_apply]
  have e2 : (f ∘ ofComplex) x = f zz := by
    show f (ofComplex (zz : ℂ)) = f zz
    rw [ofComplex_apply]
  rw [e1, e2]
  have hd1 : HasDerivAt (fun u => discInv z₀ (l * u)) (deriv (discInv z₀) (l * w) * l) w := by
    have h2 : HasDerivAt (discInv z₀) (deriv (discInv z₀) (l * w)) (l * w) :=
      (hdiff _ hlw).hasDerivAt
    have h3 : HasDerivAt (fun u : ℂ => l * u) l w := by
      simpa using (hasDerivAt_id w).const_mul l
    exact h2.comp w h3
  have hm : HasDerivAt (moebiusC γ) (deriv (moebiusC γ) x) x :=
    (hasDerivAt_moebiusC γ zz).differentiableAt.hasDerivAt
  have hd2 : HasDerivAt (moebiusC γ ∘ discInv z₀) (deriv (moebiusC γ) x * deriv (discInv z₀) w) w :=
    hm.comp w (hdiff w hw').hasDerivAt
  have hd2' : HasDerivAt (fun u => discInv z₀ (l * u))
      (deriv (moebiusC γ) x * deriv (discInv z₀) w) w := by
    refine hd2.congr_of_eventuallyEq ?_
    have hb : Metric.ball (0 : ℂ) 1 ∈ 𝓝 w := Metric.isOpen_ball.mem_nhds hw
    filter_upwards [hb] with u hu
    exact (moebiusC_discInv γ z₀ hfix (by simpa using hu)).symm
  have hkey := hd1.unique hd2'
  have hz := hinv zz
  calc f (γ • zz) * deriv (discInv z₀) (l * w) * l
      = f (γ • zz) * (deriv (discInv z₀) (l * w) * l) := by ring
    _ = f (γ • zz) * (deriv (moebiusC γ) x * deriv (discInv z₀) w) := by rw [hkey]
    _ = (f (γ • zz) * deriv (moebiusC γ) x) * deriv (discInv z₀) w := by ring
    _ = f zz * deriv (discInv z₀) w := by rw [hz]

/-- **Proposition 3.3, elliptic points** (pdf p. 199): if $f$ is holomorphic on $\mathbb H$ and $f(z)\,dz$ is
invariant under $\gamma$ fixing $z_0$, whose rotation factor $\lambda$ is a primitive $e$-th root of unity, then in
Milne's coordinate $t = w^e$ at $z_0$ the differential $f(z)\,dz$ is $\psi(t)\,dt$ with $\psi$ holomorphic at $0$. -/
@[kb "milne2006ec" "Ch. V, Proposition 3.3 (elliptic points), pdf p. 199"]
theorem prop_3_3_elliptic (γ : SL(2, ℤ)) (z₀ : ℍ) (hfix : γ • z₀ = z₀) {e : ℕ} (he : 0 < e)
    (hprim : IsPrimitiveRoot (rotationFactor γ z₀) e) (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ z : ℍ, f (γ • z) * deriv (moebiusC γ) z = f z) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ ∀ᶠ w in 𝓝 0,
      (f ∘ ofComplex) (discInv z₀ w) * deriv (discInv z₀) w = ψ (w ^ e) * (e * w ^ (e - 1)) := by
  have h0 : discInv z₀ 0 = z₀ := by simp [discInv]
  have hd := UpperHalfPlane.mdifferentiable_iff.1 hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hfd : AnalyticAt ℂ (f ∘ ofComplex) (discInv z₀ 0) := by
    rw [h0]
    exact hd.analyticAt (hopen.mem_nhds z₀.im_pos)
  have hdisc : AnalyticAt ℂ (discInv z₀) 0 := by
    unfold discInv
    exact AnalyticAt.div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (analyticAt_const.sub analyticAt_id) (by simp)
  have hφ : AnalyticAt ℂ (fun w => (f ∘ ofComplex) (discInv z₀ w) * deriv (discInv z₀) w) 0 :=
    (hfd.comp hdisc).mul hdisc.deriv
  exact exists_analyticAt_of_rotation_invariant he hprim hφ
    (rotation_invariant_of_weight_two γ z₀ hfix f hinv)

end NumberFieldKB.MilneEC.V
