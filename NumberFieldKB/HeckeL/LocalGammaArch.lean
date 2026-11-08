import NumberFieldKB.HeckeL.ArchFourier

/-!
# The archimedean gamma factors for every quasi-character (Tate's thesis)

Tate's thesis (Cassels–Fröhlich Ch. XV, §2.5 [unverified locator]; Weil, *Basic Number Theory*, Ch. VII, §2 Props. 4–5
and §7 Prop. 14) computes the factor $\rho(c)$ of the local functional equation
$Z(\hat f,c^{-1},1-s) = \rho\cdot Z(f,c,s)$ at the archimedean places for every quasi-character $c$. The local zeta integrals
(`LocalZeta.zetaIntegral_fourierR_one`, `LocalZeta.zetaIntegral_fourierC_one`) did the trivial character. Here:

* **real place**, $c(x) = |x|^t\epsilon^{[x<0]}$, $\epsilon = \pm1$, $e$ = `signExp ε` $\in\{0,1\}$
  (every quasi-character of $\mathbb R^\times$ has this form, Weil VII §3 Prop. 9):
  $$Z(\hat f,c^{-1},1-s) = i^{e}\,\frac{\Gamma_{\mathbb R}(1-s-t+e)}{\Gamma_{\mathbb R}(s+t+e)}\,Z(f,c,s)
  \qquad(0<\operatorname{Re}(s+t)<1)$$
  (`zetaIntegral_fourierR_infType`);
* **complex place**, $c(z) = |z|^t(z/|z|)^k$:
  $$Z(\hat f,c^{-1},1-s) = i^{|k|}\,\frac{\Gamma_{\mathbb C}(1-s-t/2+|k|/2)}{\Gamma_{\mathbb C}(s+t/2+|k|/2)}\,Z(f,c,s)
  \qquad(0<\operatorname{Re}(s+t/2)<1)$$
  (`zetaIntegral_fourierC_infType`).

$f$ is any Schwartz function, $\hat f$ QuadFormsKB's self-dual transform (`fourierR`, `fourierC`), and the measures are
Tate's (`tateHaarR`, `tateHaarC`). The proof is Tate's: put $g = x^ee^{-\pi x^2}$ (resp. $q_k(z)e^{-2\pi|z|^2}$) in the
local functional equation; $\hat g = i^eg$ (resp. $i^{|k|}g_{-k}$, `fourierR_fRe`, `fourierC_fCk`), and both zeta
integrals of $g$ are $\Gamma$-values (`zetaIntegral_real_infType`, `zetaIntegral_complex_infType`).
-/

open MeasureTheory Filter Set Complex
open scoped ComplexConjugate

namespace NumberFieldKB.HeckeL

noncomputable section

open LocalZeta QuadFormsKB.Analysis

/-! ### Generalities -/

/-- $Z(Cg,\chi,s) = C\,Z(g,\chi,s)$. -/
theorem zetaIntegral_const_mul {K : Type*} [NontriviallyNormedField K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (ν : Measure Kˣ)
    (C : ℂ) (g : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    zetaIntegral ν (fun y => C * g y) χ s = C * zetaIntegral ν g χ s := by
  rw [zetaIntegral, zetaIntegral, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [zetaIntegrand]
  ring

/-! ### A real place -/

theorem hasTemperateGrowth_ofReal_pow (e : ℕ) : (fun x : ℝ => (x : ℂ) ^ e).HasTemperateGrowth :=
  (Complex.ofRealCLM.hasTemperateGrowth).pow e

/-- $x^ee^{-\pi x^2}$ as a Schwartz function. -/
def fReS (e : ℕ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ e) LocalZeta.gaussR

theorem coe_fReS (e : ℕ) : (fReS e : ℝ → ℂ) = fRe e := by
  funext x
  rw [fReS, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_ofReal_pow e), smul_eq_mul, fRe,
    coe_gaussR_eq]

theorem signExp_le_one (ε : ℂ) : signExp ε ≤ 1 := by
  unfold signExp; split_ifs <;> omega

/-- The inverse of $|x|^t\epsilon^{[x<0]}$ is $|x|^{-t}\epsilon^{[x<0]}$ ($\epsilon = \pm1$). -/
theorem inv_apply_real_infType {c : ℝˣ →* ℂˣ} {t ε : ℂ}
    (hc : ∀ x : ℝˣ, (c x : ℂ) = ((|(x : ℝ)| : ℝ) : ℂ) ^ t * (if (x : ℝ) < 0 then ε else 1))
    (hε : ε = 1 ∨ ε = -1) (x : ℝˣ) :
    ((c⁻¹ x : ℂˣ) : ℂ) = ((|(x : ℝ)| : ℝ) : ℂ) ^ (-t) * (if (x : ℝ) < 0 then ε else 1) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hc, mul_inv, cpow_neg]
  congr 1
  split_ifs
  · rcases hε with rfl | rfl <;> norm_num
  · exact inv_one

theorem norm_apply_real_infType {c : ℝˣ →* ℂˣ} {t ε : ℂ}
    (hc : ∀ x : ℝˣ, (c x : ℂ) = ((|(x : ℝ)| : ℝ) : ℂ) ^ t * (if (x : ℝ) < 0 then ε else 1))
    (hε : ε = 1 ∨ ε = -1) (x : ℝˣ) :
    ‖(c x : ℂ)‖ = (distribHaarChar ℝ x : ℝ) ^ t.re := by
  have hpos : 0 < |(x : ℝ)| := abs_pos.mpr x.ne_zero
  rw [hc, norm_mul, norm_cpow_eq_rpow_re_of_pos hpos, distribHaarChar_real]
  have : ‖(if (x : ℝ) < 0 then ε else 1)‖ = 1 := by
    split_ifs
    · rcases hε with rfl | rfl <;> simp
    · simp
  rw [this, mul_one]

/-- **The real gamma factor of $c(x) = |x|^t\epsilon^{[x<0]}$** (Tate's §2.5): for every Schwartz function $f$ on
$\mathbb R$ and $0<\operatorname{Re}(s+t)<1$,
$$Z(\hat f,c^{-1},1-s) = i^{e}\,\frac{\Gamma_{\mathbb R}(1-s-t+e)}{\Gamma_{\mathbb R}(s+t+e)}\,Z(f,c,s),\qquad
e = \texttt{signExp}\ \epsilon.$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ρ(c) at a real place, c = |·|^s or sgn·|·|^s)"]
theorem zetaIntegral_fourierR_infType (f : SchwartzMap ℝ ℂ) {c : ℝˣ →* ℂˣ} (hcc : Continuous c) {t ε : ℂ}
    (hc : ∀ x : ℝˣ, (c x : ℂ) = ((|(x : ℝ)| : ℝ) : ℂ) ^ t * (if (x : ℝ) < 0 then ε else 1))
    (hε : ε = 1 ∨ ε = -1) {s : ℂ} (hs0 : 0 < (s + t).re) (hs1 : (s + t).re < 1) :
    zetaIntegral tateHaarR (fourierR f) c⁻¹ (1 - s) =
      I ^ signExp ε * Gammaℝ (1 - s - t + signExp ε) / Gammaℝ (s + t + signExp ε) *
        zetaIntegral tateHaarR f c s := by
  set e := signExp ε
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
  have hre0 : 0 < t.re + s.re := by rw [add_re] at hs0; linarith
  have hre1 : t.re + s.re < 1 := by rw [add_re] at hs1; linarith
  have h := zetaIntegral_fourierR_comm f (fReS e) hcc (norm_apply_real_infType hc hε) hre0 hre1
  rw [coe_fReS, fourierR_fRe (signExp_le_one ε), zetaIntegral_const_mul] at h
  have h1 : zetaIntegral tateHaarR (fRe e) c⁻¹ (1 - s) = Gammaℝ (1 - s - t + e) := by
    have := zetaIntegral_real_infType c⁻¹ (inv_apply_real_infType hc hε) hε (s := 1 - s)
      (by simp only [add_re, sub_re, one_re, neg_re, natCast_re]; rw [add_re] at hs1; linarith)
    rw [this, ← sub_eq_add_neg]
  have h2 : zetaIntegral tateHaarR (fRe e) c s = Gammaℝ (s + t + e) :=
    zetaIntegral_real_infType c hc hε (by simp only [add_re, natCast_re] at hs0 ⊢; linarith)
  have hne : Gammaℝ (s + t + e) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, natCast_re] at hs0 ⊢; linarith)
  rw [h1, h2] at h
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  linear_combination h.symm

/-! ### A complex place -/

theorem hasTemperateGrowth_qC (k : ℤ) : (qC k).HasTemperateGrowth := by
  unfold qC
  split_ifs
  · exact hasTemperateGrowth_conj_pow _
  · exact hasTemperateGrowth_pow' _

/-- $q_k(z)e^{-2\pi|z|^2}$ as a Schwartz function. -/
def fCkS (k : ℤ) : SchwartzMap ℂ ℂ := SchwartzMap.smulLeftCLM ℂ (qC k) LocalZeta.gaussCS

theorem coe_fCkS (k : ℤ) : (fCkS k : ℂ → ℂ) = fCk k := by
  funext z
  rw [fCkS, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_qC k), smul_eq_mul, fCk, coe_gaussCS_eq]

theorem inv_apply_complex_infType {c : ℂˣ →* ℂˣ} {t : ℂ} {k : ℤ}
    (hc : ∀ z : ℂˣ, (c z : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ t * ((z : ℂ) / ‖(z : ℂ)‖) ^ k) (z : ℂˣ) :
    ((c⁻¹ z : ℂˣ) : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ (-t) * ((z : ℂ) / ‖(z : ℂ)‖) ^ (-k) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hc, mul_inv, cpow_neg, zpow_neg]

theorem norm_apply_complex_infType {c : ℂˣ →* ℂˣ} {t : ℂ} {k : ℤ}
    (hc : ∀ z : ℂˣ, (c z : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ t * ((z : ℂ) / ‖(z : ℂ)‖) ^ k) (z : ℂˣ) :
    ‖(c z : ℂ)‖ = (distribHaarChar ℂ z : ℝ) ^ (t.re / 2) := by
  have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  rw [hc, norm_mul, norm_cpow_eq_rpow_re_of_pos hpos, distribHaarChar_complex, norm_zpow, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_self hpos.ne', one_zpow, mul_one,
    ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  congr 1
  push_cast
  ring

/-- **The complex gamma factor of $c(z) = |z|^t(z/|z|)^k$** (Tate's §2.5): for every Schwartz function $f$ on
$\mathbb C$ and $0<\operatorname{Re}(s+t/2)<1$,
$$Z(\hat f,c^{-1},1-s) = i^{|k|}\,\frac{\Gamma_{\mathbb C}(1-s-t/2+|k|/2)}{\Gamma_{\mathbb C}(s+t/2+|k|/2)}\,Z(f,c,s).$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ρ(c) at a complex place, c(z) = |z|^t (z/|z|)^k)"]
theorem zetaIntegral_fourierC_infType (f : SchwartzMap ℂ ℂ) {c : ℂˣ →* ℂˣ} (hcc : Continuous c) {t : ℂ} {k : ℤ}
    (hc : ∀ z : ℂˣ, (c z : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ t * ((z : ℂ) / ‖(z : ℂ)‖) ^ k) {s : ℂ}
    (hs0 : 0 < (s + t / 2).re) (hs1 : (s + t / 2).re < 1) :
    zetaIntegral tateHaarC (fourierC f) c⁻¹ (1 - s) =
      I ^ k.natAbs * Gammaℂ (1 - s - t / 2 + k.natAbs / 2) / Gammaℂ (s + t / 2 + k.natAbs / 2) *
        zetaIntegral tateHaarC f c s := by
  have hk0 : (0 : ℝ) ≤ (k.natAbs : ℝ) := Nat.cast_nonneg _
  have hk1 : (0 : ℝ) ≤ |(k : ℝ)| := abs_nonneg _
  have ht : (s + t / 2).re = s.re + t.re / 2 := by simp [add_re]
  have hre0 : 0 < t.re / 2 + s.re := by linarith
  have hre1 : t.re / 2 + s.re < 1 := by linarith
  have h := zetaIntegral_fourierC_comm f (fCkS k) hcc (norm_apply_complex_infType hc) hre0 hre1
  rw [coe_fCkS, fourierC_fCk, zetaIntegral_const_mul] at h
  have h1 : zetaIntegral tateHaarC (fCk (-k)) c⁻¹ (1 - s) =
      Real.pi * Gammaℂ (1 - s - t / 2 + k.natAbs / 2) := by
    have := zetaIntegral_complex_infType c⁻¹ (inv_apply_complex_infType hc) (k := -k) (t := -t) (s := 1 - s)
      (by
        simp only [add_re, sub_re, one_re, div_re, neg_re, natCast_re, natCast_im, Int.natAbs_neg]
        norm_num
        linarith)
    rw [this, Int.natAbs_neg]; congr 2; ring
  have h2 : zetaIntegral tateHaarC (fCk k) c s = Real.pi * Gammaℂ (s + t / 2 + k.natAbs / 2) :=
    zetaIntegral_complex_infType c hc (by
      simp only [add_re, div_re, natCast_re, natCast_im]
      norm_num
      linarith)
  have hne : Gammaℂ (s + t / 2 + k.natAbs / 2) ≠ 0 :=
    LocalZeta.Gammaℂ_ne_zero_of_re_pos (by
      simp only [add_re, div_re, natCast_re, natCast_im]
      norm_num
      linarith)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h1, h2] at h
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  refine mul_left_cancel₀ hπ ?_
  linear_combination h.symm

end

end NumberFieldKB.HeckeL
