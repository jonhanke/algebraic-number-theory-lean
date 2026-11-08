import NumberFieldKB.HeckeL.ArchChar

/-!
# The archimedean Γ-factors of a Hecke character

$F$ is a number field and $\chi$ a Hecke character with infinity type: at a real place $w$,
$\chi_w(x) = |x|^{t_w}\epsilon_w^{[x<0]}$ (`realExponent`, `realSign`), and we put $e_w = 0$ if $\epsilon_w = 1$, $e_w = 1$
if $\epsilon_w = -1$ (`signExp`); at a complex place, $\chi_w(z) = |z|^{t_w}(z/|z|)^{k_w}$ (`complexExponent`,
`complexFrequency`).

* **Local computations** (Tate's thesis, Cassels–Fröhlich Ch. XV, §2.5 [unverified locator]):
  $Z(x^{e}e^{-\pi x^2},\chi_w,s) = \Gamma_{\mathbb R}(s+t_w+e_w)$ (`zetaIntegral_real_infType`) and
  $Z(\bar z^{k}e^{-2\pi|z|^2},\chi_w,s) = \pi\Gamma_{\mathbb C}(s+t_w/2+|k_w|/2)$ ($z^{-k}$ if $k<0$;
  `zetaIntegral_complex_infType`).
* **`archTest χ`**: the archimedean test function $f_\infty^\chi = \prod_wx_w^{e_w}e^{-\pi x_w^2}\prod_wq_w(z_w)e^{-2\pi|z_w|^2}$,
  a Schwartz function on $F_\infty$.
* **`gammaInf χ s`** $= L_\infty(s,\chi) = \prod_{w\text{ real}}\Gamma_{\mathbb R}(s+t_w+e_w)\prod_{w\text{ complex}}
  \Gamma_{\mathbb C}(s+t_w/2+|k_w|/2)$, and **`archZeta_archTest`**: $Z_\infty(f_\infty^\chi,\chi,s) = \pi^{r_2}L_\infty(s,\chi)$
  for $\operatorname{Re}s+\sigma>0$.
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ComplexConjugate

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

open GlobalZeta LocalZeta

/-! ### A real place -/

/-- $e = 0$ for the sign $\epsilon = 1$ and $e = 1$ for $\epsilon = -1$. -/
def signExp (ε : ℂ) : ℕ := if ε = 1 then 0 else 1

/-- The test function $x^ee^{-\pi x^2}$ on $\mathbb R$. -/
def fRe (e : ℕ) (x : ℝ) : ℂ := (x : ℂ) ^ e * Analysis.gaussR x

theorem pow_signExp_mul_sign {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (x : ℝ) :
    (x : ℂ) ^ signExp ε * (if x < 0 then ε else 1) = ((|x| : ℝ) : ℂ) ^ signExp ε := by
  rcases hε with rfl | rfl
  · simp [signExp]
  · have : signExp (-1 : ℂ) = 1 := by simp [signExp]; norm_num
    rw [this, pow_one, pow_one]
    split_ifs with h
    · rw [abs_of_neg h]; push_cast; ring
    · rw [abs_of_nonneg (not_lt.mp h), mul_one]

/-- **The real Gaussian zeta integral with a character** $\chi_w(x) = |x|^t\epsilon^{[x<0]}$: for
$\operatorname{Re}(s+t+e)>0$, $Z(x^ee^{-\pi x^2},\chi_w,s) = \Gamma_{\mathbb R}(s+t+e)$, $e$ = `signExp ε`. -/
theorem zetaIntegral_real_infType (c : ℝˣ →* ℂˣ) {t ε : ℂ}
    (hc : ∀ x : ℝˣ, (c x : ℂ) = ((|(x : ℝ)| : ℝ) : ℂ) ^ t * (if (x : ℝ) < 0 then ε else 1))
    (hε : ε = 1 ∨ ε = -1) {s : ℂ} (hs : 0 < (s + t + signExp ε).re) :
    zetaIntegral tateHaarR (fRe (signExp ε)) c s = Complex.Gammaℝ (s + t + signExp ε) := by
  rw [← zetaIntegral_gaussian_real hs]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hu : (u : ℝ) ≠ 0 := u.ne_zero
  have ha : ((|(u : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hu
  simp only [zetaIntegrand, fRe, hc, distribHaarChar_real, MonoidHom.one_apply, Units.val_one, mul_one]
  rw [coe_gaussR_eq]
  have key := pow_signExp_mul_sign hε (u : ℝ)
  calc ((u : ℝ) : ℂ) ^ signExp ε * Analysis.gaussR (u : ℝ) *
        (((|(u : ℝ)| : ℝ) : ℂ) ^ t * (if (u : ℝ) < 0 then ε else 1)) * ((|(u : ℝ)| : ℝ) : ℂ) ^ s
      = Analysis.gaussR (u : ℝ) * (((u : ℝ) : ℂ) ^ signExp ε * (if (u : ℝ) < 0 then ε else 1)) *
          (((|(u : ℝ)| : ℝ) : ℂ) ^ t * ((|(u : ℝ)| : ℝ) : ℂ) ^ s) := by ring
    _ = _ := by
      rw [key, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ ha, mul_assoc, ← Complex.cpow_add _ _ ha]
      congr 2
      ring

/-! ### A complex place -/

/-- $\bar z^{k}$ for $k\ge0$ and $z^{-k}$ for $k<0$. -/
def qC (k : ℤ) (z : ℂ) : ℂ := if 0 ≤ k then (conj z) ^ k.natAbs else z ^ k.natAbs

/-- The test function $q_k(z)e^{-2\pi|z|^2}$ on $\mathbb C$. -/
def fCk (k : ℤ) (z : ℂ) : ℂ := qC k z * Analysis.gaussC z

theorem qC_mul_zpow {k : ℤ} {z : ℂ} (hz : z ≠ 0) :
    qC k z * (z / ((‖z‖ : ℝ) : ℂ)) ^ k = ((‖z‖ : ℝ) : ℂ) ^ k.natAbs := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  have hsq : conj z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  unfold qC
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [Int.natAbs_natCast, zpow_natCast, div_pow, ← mul_div_assoc, ← mul_pow, hsq, ← pow_mul]
    field_simp
    ring
  · obtain ⟨n, hn'⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨k.natAbs, by omega⟩
    subst hn'
    rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, div_pow, inv_div]
    field_simp

/-- $((r^2)^w) = r^{2w}$ for $r>0$ in $\mathbb C$. -/
theorem ofReal_sq_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (((r ^ 2 : ℝ)) : ℂ) ^ w = ((r : ℝ) : ℂ) ^ (2 * w) := by
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast, ← Complex.cpow_mul]
  · push_cast; ring_nf
  · rw [← Complex.ofReal_log hr.le]; simp [Real.pi_pos]
  · rw [← Complex.ofReal_log hr.le]; simp [Real.pi_pos.le]

/-- **The complex Gaussian zeta integral with a character** $\chi_w(z) = |z|^t(z/|z|)^k$: for
$\operatorname{Re}(s+t/2+|k|/2)>0$, $Z(q_k(z)e^{-2\pi|z|^2},\chi_w,s) = \pi\Gamma_{\mathbb C}(s+t/2+|k|/2)$. -/
theorem zetaIntegral_complex_infType (c : ℂˣ →* ℂˣ) {t : ℂ} {k : ℤ}
    (hc : ∀ z : ℂˣ, (c z : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ t * ((z : ℂ) / ‖(z : ℂ)‖) ^ k) {s : ℂ}
    (hs : 0 < (s + t / 2 + k.natAbs / 2).re) :
    zetaIntegral tateHaarC (fCk k) c s = Real.pi * Complex.Gammaℂ (s + t / 2 + k.natAbs / 2) := by
  rw [← zetaIntegral_gaussian_complex hs]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hr : 0 < ‖(u : ℂ)‖ := norm_pos_iff.mpr hu
  have ha : ((‖(u : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [zetaIntegrand, fCk, hc, distribHaarChar_complex, MonoidHom.one_apply, Units.val_one, mul_one]
  rw [coe_gaussCS_eq, ofReal_sq_cpow hr, ofReal_sq_cpow hr]
  have key := qC_mul_zpow (k := k) hu
  calc qC k (u : ℂ) * Analysis.gaussC (u : ℂ) *
        (((‖(u : ℂ)‖ : ℝ) : ℂ) ^ t * ((u : ℂ) / ((‖(u : ℂ)‖ : ℝ) : ℂ)) ^ k) * ((‖(u : ℂ)‖ : ℝ) : ℂ) ^ (2 * s)
      = Analysis.gaussC (u : ℂ) * (qC k (u : ℂ) * ((u : ℂ) / ((‖(u : ℂ)‖ : ℝ) : ℂ)) ^ k) *
          (((‖(u : ℂ)‖ : ℝ) : ℂ) ^ t * ((‖(u : ℂ)‖ : ℝ) : ℂ) ^ (2 * s)) := by ring
    _ = _ := by
      rw [key, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ ha, mul_assoc, ← Complex.cpow_add _ _ ha]
      congr 2
      ring

/-! ### The archimedean test function and $L_\infty(s,\chi)$ -/

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

/-- $e_w\in\{0,1\}$ at a real place: $\chi_w(-1) = (-1)^{e_w}$. -/
def eW (χ : HeckeCharacter F) (w : {w : InfinitePlace F // w.IsReal}) : ℕ := signExp (χ.realSign w.2)

/-- The frequency $k_w$ at a complex place. -/
def kW (χ : HeckeCharacter F) (w : {w : InfinitePlace F // w.IsComplex}) : ℤ := χ.complexFrequency w.2

/-- The polynomial factor $\prod_{w\text{ real}}x_w^{e_w}\prod_{w\text{ complex}}q_{k_w}(z_w)$ of the test function. -/
def archPoly (χ : HeckeCharacter F) (x : V) : ℂ :=
  (∏ w, ((x.1 w : ℝ) : ℂ) ^ eW χ w) * ∏ w, qC (kW χ w) (x.2 w)

theorem hasTemperateGrowth_finsetProd {ι : Type*} (s : Finset ι) (f : ι → V → ℂ)
    (h : ∀ i, (f i).HasTemperateGrowth) : (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact (h a).mul ih

theorem hasTemperateGrowth_archPoly (χ : HeckeCharacter F) : (archPoly χ).HasTemperateGrowth := by
  have hr : ∀ w : {w : InfinitePlace F // w.IsReal},
      (fun x : V => ((x.1 w : ℝ) : ℂ) ^ eW χ w).HasTemperateGrowth := fun w => by
    have h : (fun x : V => ((x.1 w : ℝ) : ℂ)) = (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w).comp
        (ContinuousLinearMap.fst ℝ _ _)) : V →L[ℝ] ℂ) := rfl
    exact (h ▸ ContinuousLinearMap.hasTemperateGrowth _).pow _
  have hc : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (fun x : V => qC (kW χ w) (x.2 w)).HasTemperateGrowth := fun w => by
    unfold qC
    split_ifs
    · have h : (fun x : V => conj (x.2 w)) = (Complex.conjCLE.toContinuousLinearMap.comp
          ((ContinuousLinearMap.proj w).comp (ContinuousLinearMap.snd ℝ _ _)) : V →L[ℝ] ℂ) := rfl
      exact (h ▸ ContinuousLinearMap.hasTemperateGrowth _).pow _
    · have h : (fun x : V => x.2 w) = ((ContinuousLinearMap.proj w).comp
          (ContinuousLinearMap.snd ℝ _ _) : V →L[ℝ] ℂ) := rfl
      exact (h ▸ ContinuousLinearMap.hasTemperateGrowth _).pow _
  exact (hasTemperateGrowth_finsetProd _ _ hr).mul (hasTemperateGrowth_finsetProd _ _ hc)

/-- **The archimedean test function of $\chi$**: $f_\infty^\chi(x) = \prod_{w\text{ real}}x_w^{e_w}e^{-\pi x_w^2}
\prod_{w\text{ complex}}q_{k_w}(z_w)e^{-2\pi|z_w|^2}$, a Schwartz function on $F_\infty$. -/
def archTest (χ : HeckeCharacter F) : SchwartzMap V ℂ :=
  SchwartzMap.smulLeftCLM ℂ (archPoly χ) Analysis.gaussInf

theorem archTest_apply (χ : HeckeCharacter F) (x : V) :
    archTest χ x = (∏ w, fRe (eW χ w) (x.1 w)) * ∏ w, fCk (kW χ w) (x.2 w) := by
  rw [archTest, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_archPoly χ), Analysis.gaussInf_apply,
    smul_eq_mul, archPoly, Analysis.gaussInfFun]
  simp only [fRe, fCk, Finset.prod_mul_distrib]
  ring

/-- **The archimedean factor** $L_\infty(s,\chi) = \prod_{w\text{ real}}\Gamma_{\mathbb R}(s+t_w+e_w)\prod_{w\text{ complex}}
\Gamma_{\mathbb C}(s+t_w/2+|k_w|/2)$ (Mathlib's $\Gamma_{\mathbb R}$, $\Gamma_{\mathbb C}$). -/
@[kb "neukirch1999" "Ch. VII, §8, Def. 8.4 [unverified locator] (the Γ-factor L_∞(X, s) of a Hecke character)"]
def gammaInf (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  (∏ w : {w : InfinitePlace F // w.IsReal}, Complex.Gammaℝ (s + χ.realExponent w.2 + eW χ w)) *
    ∏ w : {w : InfinitePlace F // w.IsComplex},
      Complex.Gammaℂ (s + χ.complexExponent w.2 / 2 + (kW χ w).natAbs / 2)

/-- **$Z_\infty(f_\infty^\chi,\chi,s) = \pi^{r_2}L_\infty(s,\chi)$** for $\operatorname{Re}s+\sigma>0$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (the archimedean ζ-functions)"]
theorem archZeta_archTest (χ : HeckeCharacter F) {s : ℂ} (hs : 0 < s.re + χ.shift) :
    archZeta (archTest χ) χ s = (Real.pi : ℂ) ^ nrComplexPlaces F * gammaInf χ s := by
  rw [archZeta_eq_prod (fr := fun w => fRe (eW χ w)) (fc := fun w => fCk (kW χ w))
    (cr := fun w => (χ.realComponent w.2 : ℝˣ →* ℂˣ)) (cc := fun w => (χ.complexComponent w.2 : ℂˣ →* ℂˣ)) s _ χ
    (archTest_apply χ) (fun u => by rw [onIdeles_infEmb]; rfl)]
  have hr : ∀ w : {w : InfinitePlace F // w.IsReal},
      zetaIntegral tateHaarR (fRe (eW χ w)) (χ.realComponent w.2 : ℝˣ →* ℂˣ) s =
        Complex.Gammaℝ (s + χ.realExponent w.2 + eW χ w) := fun w =>
    zetaIntegral_real_infType _ (χ.realComponent_apply w.2) (χ.realSign_eq w.2) (by
      have := χ.re_realExponent w.2
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (signExp (χ.realSign w.2) : ℝ) := Nat.cast_nonneg _
      linarith)
  have hc : ∀ w : {w : InfinitePlace F // w.IsComplex},
      zetaIntegral tateHaarC (fCk (kW χ w)) (χ.complexComponent w.2 : ℂˣ →* ℂˣ) s =
        Real.pi * Complex.Gammaℂ (s + χ.complexExponent w.2 / 2 + (kW χ w).natAbs / 2) := fun w =>
    zetaIntegral_complex_infType _ (χ.complexComponent_apply w.2) (by
      have := χ.re_complexExponent w.2
      simp only [Complex.add_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
      norm_num
      have : (0 : ℝ) ≤ |(χ.complexFrequency w.2 : ℝ)| := abs_nonneg _
      linarith)
  simp only [hr, hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, gammaInf]
  ring

end

end NumberFieldKB.HeckeL
