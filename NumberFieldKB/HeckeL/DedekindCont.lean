import NumberFieldKB.HeckeL.Dedekind
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The Dedekind zeta function: continuation, functional equation, residue

$F$ is a number field with $r_1$ real and $r_2$ complex places, discriminant $d_F$, and
$\rho_F = 2^{r_1}(2\pi)^{r_2}h_FR_F/(w_F\sqrt{|d_F|})$ (Mathlib's `dedekindZeta_residue`, the volume of
$F^\times\backslash\mathbb A_F^1$ for Tate's measure). $Z(s)$ is the continuation of the global zeta integral of the test
function $\Phi_0$ (`Dedekind.lean`) and the trivial character (`globalZetaCont`).

* **`heckeL_one_eq_dedekindZeta`**: $L(s,1) = \prod_v(1-N(v)^{-s})^{-1}$ equals Mathlib's `dedekindZeta F s` (the
  Dirichlet series $\sum_{\mathfrak a}N\mathfrak a^{-s}$) for $\operatorname{Re}s>1$.
* **`completedDedekindZeta F s`** $= \Lambda_F(s) = \pi^{-r_2}|d_F|^{(s+1)/2}Z(s)$; for $\operatorname{Re}s>1$ it is
  $|d_F|^{s/2}\Gamma_{\mathbb R}(s)^{r_1}\Gamma_{\mathbb C}(s)^{r_2}\zeta_F(s)$ (`completedDedekindZeta_eq`). It is holomorphic
  away from $0,1$, with simple poles there (residues $\mp\sqrt{|d_F|}\rho_F/\pi^{r_2}$), and satisfies
  **$\Lambda_F(1-s) = \Lambda_F(s)$** (`completedDedekindZeta_one_sub`).
* **`dedekindZetaCont F`**: the continuation of $\zeta_F$, holomorphic on $\mathbb C\setminus\{1\}$
  (`differentiableAt_dedekindZetaCont`), equal to `dedekindZeta F` for $\operatorname{Re}s>1$ (`dedekindZetaCont_eq`),
  with **residue $\rho_F$ at $s=1$** (`tendsto_sub_one_mul_dedekindZetaCont`). At $s = 0$ it is
  $-\sqrt{|d_F|}\rho_F/(2\pi^{r_2})$ if $r_1+r_2 = 1$ and $0$ otherwise (`dedekindZetaCont_zero`).
* **Check against Mathlib** (`tendsto_sub_one_mul_dedekindZeta_nhdsGT'`): Mathlib's class number formula
  `tendsto_sub_one_mul_dedekindZeta_nhdsGT` follows from the residue above.

Tate's thesis, Cassels–Fröhlich Ch. XV, §4.4 [unverified locator]; Neukirch, *Algebraic Number Theory*, Ch. VII,
Cor. 5.11 [unverified locator].
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open Topology
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-! ### The continued zeta integral of $\Phi_0$ -/

variable (F) in
/-- $Z(s)$: the continuation of $Z(\Phi_0,1,s)$. -/
def zetaZero (s : ℂ) : ℂ := globalZetaCont (dedekindPhi F) 1 s

theorem zetaZero_eq {s : ℂ} (hs : 1 < s.re) :
    zetaZero F s = ((Real.sqrt |(discr F : ℝ)|)⁻¹ : ℝ) * gammaInfOne F s * heckeL (1 : HeckeCharacter F) s := by
  rw [zetaZero, globalZetaCont_eq _ _ (by rw [shift_one, add_zero]; exact hs), globalZeta_dedekindPhi hs]

theorem differentiableAt_zetaZero {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : DifferentiableAt ℂ (zetaZero F) s := by
  have h := differentiableAt_globalZetaCont_normPow (dedekindPhi F) 0 (s := s) (by simpa using h0)
    (by simpa using h1)
  rwa [HeckeCharacter.normPow_zero] at h

theorem dedekindPhi_zero : (dedekindPhi F : Adeles F → ℂ) 0 = 1 := by
  rw [SchwartzBruhat.apply]
  have h1 : (dedekindPhi F).fInf (0 : Adeles F).1 = 1 := by
    change Analysis.gaussInf (0 : mixedSpace F) = 1
    rw [Analysis.gaussInf_apply, Analysis.gaussInfFun]
    simp [Analysis.gaussR, Analysis.gaussC]
  have h2 : ∀ v, (dedekindPhi F).fv v ((0 : Adeles F).2 v) = 1 := fun v => by
    rw [dedekindPhi_fv, show ((0 : Adeles F).2 v) = 0 from rfl]
    simp [Analysis.ballIndV]
  rw [h1, finprod_congr h2, finprod_one, one_mul]

theorem fourier_dedekindPhi_zero :
    (dedekindPhi F).fourier 0 = ((Real.sqrt |(discr F : ℝ)|)⁻¹ : ℝ) := by
  rw [← coe_dualPhi, SchwartzBruhat.apply]
  have h1 : (dualPhi F).fInf (0 : Adeles F).1 = 1 := by
    change Analysis.gaussInf (0 : mixedSpace F) = 1
    rw [Analysis.gaussInf_apply, Analysis.gaussInfFun]
    simp [Analysis.gaussR, Analysis.gaussC]
  have h2 : ∀ v, (dualPhi F).fv v ((0 : Adeles F).2 v) = ((volO v).toReal : ℂ) := fun v => by
    change dualFv v 0 = _
    simp [dualFv, Analysis.ballIndV]
  rw [h1, finprod_congr h2, one_mul]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), (volO v).toReal = (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
    rw [← ohatVol, ohatVol_eq_finprod]
    exact finprod_congr fun v => by rw [volO_eq_ofReal, ENNReal.toReal_ofReal measureReal_nonneg]
  rw [← h3]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => (volO v).toReal).Finite := by
    refine (Analysis.finite_support_diffExp (F := F)).subset fun v hv => ?_
    by_contra h
    apply hv
    simp only [Function.mem_support, ne_eq, not_not] at h
    have hd : Analysis.diffExp v = 0 := by exact_mod_cast h
    simp [volO_toReal, hd]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by simp),
    finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      intro h; apply hv; simp [h]),
    Complex.ofReal_prod]

/-- **The residue of $Z$ at $s = 1$**: $|d_F|^{-1/2}\rho_F$. -/
theorem tendsto_zetaZero_residue_one :
    Tendsto (fun s => (s - 1) * zetaZero F s) (𝓝[≠] 1)
      (𝓝 ((((Real.sqrt |(discr F : ℝ)|)⁻¹ : ℝ) : ℂ) * dedekindZeta_residue F)) := by
  have h := tendsto_globalZetaCont_normPow_residue_one (dedekindPhi F) 0
  simp only [sub_zero, HeckeCharacter.normPow_zero, fourier_dedekindPhi_zero] at h
  exact h

/-- **The residue of $Z$ at $s = 0$**: $-\rho_F$. -/
theorem tendsto_zetaZero_residue_zero :
    Tendsto (fun s => s * zetaZero F s) (𝓝[≠] 0) (𝓝 (-(dedekindZeta_residue F : ℂ))) := by
  have h := tendsto_globalZetaCont_normPow_residue_zero (dedekindPhi F) 0
  simp only [add_zero, neg_zero, HeckeCharacter.normPow_zero, dedekindPhi_zero, one_mul] at h
  exact h

/-! ### Comparison with Mathlib's Dedekind zeta function -/

theorem gammaInfOne_ne_zero {s : ℂ} (hs : 0 < s.re) : gammaInfOne F s ≠ 0 := by
  unfold gammaInfOne
  refine mul_ne_zero (pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos hs))
    (pow_ne_zero _ (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (Gammaℂ_ne_zero_of_re_pos hs)))

theorem differentiable_gammaInfOne_inv : Differentiable ℂ fun s => (gammaInfOne F s)⁻¹ := by
  have h : (fun s => (gammaInfOne F s)⁻¹) = fun s =>
      ((Complex.Gammaℝ s)⁻¹) ^ nrRealPlaces F * (((Real.pi : ℂ))⁻¹ * (Complex.Gammaℂ s)⁻¹) ^ nrComplexPlaces F := by
    funext s
    rw [gammaInfOne, mul_inv, ← inv_pow, ← inv_pow, mul_inv]
  rw [h]
  exact (Complex.differentiable_Gammaℝ_inv.pow _).mul
    (((differentiable_const _).mul Complex.differentiable_Gammaℂ_inv).pow _)

/-- $L(s,1) = |d_F|^{1/2}Z(s)/\bigl(\Gamma_{\mathbb R}(s)^{r_1}(\pi\Gamma_{\mathbb C}(s))^{r_2}\bigr)$ for $\operatorname{Re}s>1$. -/
theorem heckeL_one_eq_zetaZero {s : ℂ} (hs : 1 < s.re) :
    heckeL (1 : HeckeCharacter F) s =
      ((Real.sqrt |(discr F : ℝ)|) : ℂ) * zetaZero F s * (gammaInfOne F s)⁻¹ := by
  have hd : ((Real.sqrt |(discr F : ℝ)|) : ℂ) ≠ 0 := by exact_mod_cast sqrt_abs_discr_pos.ne'
  rw [zetaZero_eq hs]
  have := gammaInfOne_ne_zero (F := F) (s := s) (by linarith)
  push_cast
  field_simp

/-- Mathlib's `dedekindZeta` is real on the real axis. -/
theorem ofReal_re_dedekindZeta (x : ℝ) : (((dedekindZeta F x).re : ℝ) : ℂ) = dedekindZeta F x := by
  have h : dedekindZeta F x = ((∑' n : ℕ, (if n = 0 then 0 else
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ x) : ℝ) : ℂ) := by
    rw [dedekindZeta, LSeries, Complex.ofReal_tsum]
    congr 1
    funext n
    rw [LSeries.term_def]
    split_ifs with hn
    · simp
    · push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
  rw [h, Complex.ofReal_re]

/-- On the real axis $x>1$: $L(x,1) = \zeta_F(x)$, by QuadFormsKB's real Euler product `hasProd_dedekindZeta`. -/
theorem heckeL_one_ofReal {x : ℝ} (hx : 1 < x) : heckeL (1 : HeckeCharacter F) x = dedekindZeta F x := by
  have h1 := (QuadFormsKB.NFEuler.hasProd_dedekindZeta (F := F) hx).map Complex.ofRealHom
    Complex.continuous_ofReal
  have h3 := hasProd_heckeL (1 : HeckeCharacter F) (s := x) (by rw [shift_one, add_zero]; simpa using hx)
  rw [← ofReal_re_dedekindZeta]
  refine h3.unique ?_
  convert h1 using 1
  · funext v
    simp only [Function.comp_apply, Complex.ofRealHom_eq_coe, localL_one]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  · rfl

theorem abscissaOfAbsConv_dedekind_le :
    LSeries.abscissaOfAbsConv (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    QuadFormsKB.NFEuler.lSeriesSummable_dedekindZeta (by exact_mod_cast hy)

/-- **$L(s,1) = \zeta_F(s)$** (Mathlib's `dedekindZeta`, the Dirichlet series $\sum_{\mathfrak a}N\mathfrak a^{-s}$) for
$\operatorname{Re}s>1$: the Euler product of Tate's thesis is the Dedekind zeta function. -/
@[kb "neukirch1999" "Ch. VII, §5, Prop. 5.2 [unverified locator] (ζ_K(s) = Π_p (1 − 𝔑(p)^{-s})^{-1})"]
theorem heckeL_one_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    heckeL (1 : HeckeCharacter F) s = dedekindZeta F s := by
  set U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set f : ℂ → ℂ := fun s => ((Real.sqrt |(discr F : ℝ)|) : ℂ) * zetaZero F s * (gammaInfOne F s)⁻¹
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hU
    have hs' : 1 < s.re := hs
    have h0 : s ≠ 0 := fun h => by simp [h] at hs'; linarith
    have h1 : s ≠ 1 := fun h => by simp [h] at hs'
    exact (((differentiableAt_const _).mul (differentiableAt_zetaZero h0 h1)).mul
      (differentiable_gammaInfOne_inv s)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (dedekindZeta F) U := by
    refine (LSeries_analyticOnNhd _).mono fun s hs => ?_
    exact lt_of_le_of_lt abscissaOfAbsConv_dedekind_le (by exact_mod_cast hs)
  have hreal : ∀ x : ℝ, 1 < x → f x = dedekindZeta F x := fun x hx => by
    simp only [f]
    rw [← heckeL_one_eq_zetaZero (by simpa using hx), heckeL_one_ofReal hx]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), f z = dedekindZeta F z := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto (2 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({(2 : ℝ)}ᶜ : Set ℝ)))
        simpa using this
      · intro h
        apply hx
        have h' : (x : ℂ) = 2 := h
        exact_mod_cast h'
    refine ht.frequently ?_
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (2 : ℝ), f x = dedekindZeta F x := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))] with x hx
      exact hreal x hx
    exact hev.frequently
  have heq := hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 1).isPreconnected
    (show (2 : ℂ) ∈ U by simp [U]) hfreq
  rw [heckeL_one_eq_zetaZero hs]
  exact heq hs

/-! ### The completed Dedekind zeta function -/

variable (F) in
/-- $\Gamma_{\mathbb R}(s)^{r_1}\Gamma_{\mathbb C}(s)^{r_2}$ (Mathlib's $\Gamma_{\mathbb R}$, $\Gamma_{\mathbb C}$). -/
def gammaFactor (s : ℂ) : ℂ := Complex.Gammaℝ s ^ nrRealPlaces F * Complex.Gammaℂ s ^ nrComplexPlaces F

theorem gammaInfOne_eq (s : ℂ) : gammaInfOne F s = (Real.pi : ℂ) ^ nrComplexPlaces F * gammaFactor F s := by
  rw [gammaInfOne, gammaFactor, mul_pow]
  ring

theorem gammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) : gammaFactor F s ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos hs)) (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs))

theorem differentiable_gammaFactor_inv : Differentiable ℂ fun s => (gammaFactor F s)⁻¹ := by
  have h : (fun s => (gammaFactor F s)⁻¹) = fun s =>
      ((Complex.Gammaℝ s)⁻¹) ^ nrRealPlaces F * ((Complex.Gammaℂ s)⁻¹) ^ nrComplexPlaces F := by
    funext s
    rw [gammaFactor, mul_inv, ← inv_pow, ← inv_pow]
  rw [h]
  exact (Complex.differentiable_Gammaℝ_inv.pow _).mul (Complex.differentiable_Gammaℂ_inv.pow _)

theorem gammaFactor_one : gammaFactor F 1 = ((Real.pi : ℂ) ^ nrComplexPlaces F)⁻¹ := by
  rw [gammaFactor, Complex.Gammaℝ_one, Complex.Gammaℂ_one, one_pow, one_mul, one_div, inv_pow]

theorem abs_discr_ne_zero : (((|(discr F : ℝ)| : ℝ)) : ℂ) ≠ 0 := by
  exact_mod_cast (abs_discr_pos (F := F)).ne'

theorem sqrt_abs_discr_eq : ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) = (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (abs_nonneg _)]
  push_cast
  rfl

variable (F) in
/-- **The completed Dedekind zeta function** $\Lambda_F(s) = \pi^{-r_2}|d_F|^{(s+1)/2}Z(s)$, $Z$ the continued zeta
integral of $\Phi_0$; for $\operatorname{Re}s>1$ it is $|d_F|^{s/2}\Gamma_{\mathbb R}(s)^{r_1}\Gamma_{\mathbb C}(s)^{r_2}\zeta_F(s)$
(`completedDedekindZeta_eq`). -/
@[kb "neukirch1999" "Ch. VII, §5, Def. 5.9 and Cor. 5.11 [unverified locator] (Z_K(s) = |d_K|^{s/2} L_∞(s) ζ_K(s))"]
def completedDedekindZeta (s : ℂ) : ℂ :=
  (((Real.pi : ℂ) ^ nrComplexPlaces F))⁻¹ * (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ ((s + 1) / 2) * zetaZero F s

/-- **$\Lambda_F(s) = |d_F|^{s/2}\Gamma_{\mathbb R}(s)^{r_1}\Gamma_{\mathbb C}(s)^{r_2}\zeta_F(s)$** for $\operatorname{Re}s>1$, with
Mathlib's `dedekindZeta`. -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta F s =
      (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (s / 2) * gammaFactor F s * dedekindZeta F s := by
  rw [completedDedekindZeta, zetaZero_eq hs, ← heckeL_one_eq_dedekindZeta hs, gammaInfOne_eq,
    Complex.ofReal_inv, sqrt_abs_discr_eq, add_div, Complex.cpow_add _ _ abs_discr_ne_zero]
  have hπ : ((Real.pi : ℂ) ^ nrComplexPlaces F) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have hd : (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => abs_discr_ne_zero h.1
  field_simp

theorem differentiableAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (completedDedekindZeta F) s :=
  ((differentiableAt_const _).mul (((differentiableAt_id.add_const 1).div_const 2).const_cpow
    (Or.inl abs_discr_ne_zero))).mul (differentiableAt_zetaZero h0 h1)

/-- The functional equation of the continued zeta integral of $\Phi_0$ in the half-plane of convergence:
$Z(1-s) = |d_F|^{s-1/2}Z(s)$ for $\operatorname{Re}s>1$ (Tate's $Z(\Phi_0,1,1-s) = Z(\hat\Phi_0,1,s)$). -/
theorem zetaZero_one_sub_of_re {s : ℂ} (hs : 1 < s.re) :
    zetaZero F (1 - s) = (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (s - 1 / 2) * zetaZero F s := by
  rw [zetaZero, globalZetaCont_one_sub _ _ (by rw [shift_one, sub_zero]; exact hs), globalZeta_inv_one, ← coe_dualPhi,
    globalZeta_dualPhi hs, ← globalZetaCont_eq _ _ (by rw [shift_one, add_zero]; exact hs)]
  rfl

/-- $Z(1-s) = |d_F|^{s-1/2}Z(s)$ for all $s\ne0,1$ (identity theorem on $\mathbb C\setminus\{0,1\}$). -/
theorem zetaZero_one_sub {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    zetaZero F (1 - s) = (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (s - 1 / 2) * zetaZero F s := by
  set V : Set ℂ := ({0, 1} : Set ℂ)ᶜ
  have hV : IsOpen V := (Set.toFinite ({0, 1} : Set ℂ)).isClosed.isOpen_compl
  have hpc : IsPreconnected V :=
    ((Set.toFinite ({0, 1} : Set ℂ)).countable.isPathConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isConnected.isPreconnected
  have hmem : ∀ {t : ℂ}, t ∈ V ↔ t ≠ 0 ∧ t ≠ 1 := by
    intro t; simp [V, not_or]
  have hf : AnalyticOnNhd ℂ (fun s => zetaZero F (1 - s)) V := by
    refine DifferentiableOn.analyticOnNhd (fun t ht => ?_) hV
    obtain ⟨ht0, ht1⟩ := hmem.mp ht
    have h0' : 1 - t ≠ 0 := fun h => ht1 (by linear_combination -h)
    have h1' : 1 - t ≠ 1 := fun h => ht0 (by linear_combination -h)
    exact ((differentiableAt_zetaZero h0' h1').comp t ((differentiableAt_const _).sub differentiableAt_id)
      ).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun s => (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (s - 1 / 2) * zetaZero F s) V := by
    refine DifferentiableOn.analyticOnNhd (fun t ht => ?_) hV
    obtain ⟨ht0, ht1⟩ := hmem.mp ht
    exact ((differentiableAt_id.sub_const _).const_cpow (Or.inl abs_discr_ne_zero)).mul
      (differentiableAt_zetaZero ht0 ht1) |>.differentiableWithinAt
  have hev : (fun s => zetaZero F (1 - s)) =ᶠ[𝓝 (2 : ℂ)]
      fun s => (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (s - 1 / 2) * zetaZero F s := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with t ht
    exact zetaZero_one_sub_of_re ht
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hpc (hmem.mpr ⟨two_ne_zero, by norm_num⟩) hev
    (hmem.mpr ⟨h0, h1⟩)

/-- **The functional equation of the Dedekind zeta function**: $\Lambda_F(1-s) = \Lambda_F(s)$ for $s\ne0,1$. -/
@[kb "neukirch1999" "Ch. VII, §5, Cor. 5.11 [unverified locator] (Z_K(s) = Z_K(1 − s))"]
theorem completedDedekindZeta_one_sub {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta F (1 - s) = completedDedekindZeta F s := by
  rw [completedDedekindZeta, completedDedekindZeta, zetaZero_one_sub h0 h1, ← mul_assoc,
    mul_assoc _ ((((|(discr F : ℝ)| : ℝ)) : ℂ) ^ ((1 - s + 1) / 2)),
    ← Complex.cpow_add _ _ abs_discr_ne_zero]
  congr 3
  ring

/-- **The residue of $\Lambda_F$ at $s = 1$**: $\sqrt{|d_F|}\,\rho_F/\pi^{r_2}$. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s => (s - 1) * completedDedekindZeta F s) (𝓝[≠] 1)
      (𝓝 ((((Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F : ℝ)) : ℂ) / (Real.pi : ℂ) ^ nrComplexPlaces F)) := by
  have hc : Continuous fun s : ℂ => (((Real.pi : ℂ) ^ nrComplexPlaces F))⁻¹ *
      (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ ((s + 1) / 2) :=
    continuous_const.mul (((continuous_id.add continuous_const).div_const 2).const_cpow (Or.inl abs_discr_ne_zero))
  have h := ((hc.tendsto 1).mono_left nhdsWithin_le_nhds).mul (tendsto_zetaZero_residue_one (F := F))
  have hval : (((Real.pi : ℂ) ^ nrComplexPlaces F))⁻¹ * (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (((1 : ℂ) + 1) / 2) *
      ((((Real.sqrt |(discr F : ℝ)|)⁻¹ : ℝ) : ℂ) * dedekindZeta_residue F) =
      (((Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F : ℝ)) : ℂ) / (Real.pi : ℂ) ^ nrComplexPlaces F := by
    have hs : Real.sqrt |(discr F : ℝ)| ≠ 0 := sqrt_abs_discr_pos.ne'
    have hsq : (((|(discr F : ℝ)| : ℝ)) : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (abs_nonneg _)]
    norm_num
    rw [hsq]
    field_simp
  rw [← hval]
  refine h.congr fun s => ?_
  rw [completedDedekindZeta]
  ring

/-- **The residue of $\Lambda_F$ at $s = 0$**: $-\sqrt{|d_F|}\,\rho_F/\pi^{r_2}$. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s => s * completedDedekindZeta F s) (𝓝[≠] 0)
      (𝓝 (-((((Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F : ℝ)) : ℂ) /
        (Real.pi : ℂ) ^ nrComplexPlaces F))) := by
  have hc : Continuous fun s : ℂ => (((Real.pi : ℂ) ^ nrComplexPlaces F))⁻¹ *
      (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ ((s + 1) / 2) :=
    continuous_const.mul (((continuous_id.add continuous_const).div_const 2).const_cpow (Or.inl abs_discr_ne_zero))
  have h := ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).mul (tendsto_zetaZero_residue_zero (F := F))
  have hval : (((Real.pi : ℂ) ^ nrComplexPlaces F))⁻¹ * (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (((0 : ℂ) + 1) / 2) *
      (-(dedekindZeta_residue F : ℂ)) =
      -((((Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F : ℝ)) : ℂ) / (Real.pi : ℂ) ^ nrComplexPlaces F) := by
    rw [zero_add, ← sqrt_abs_discr_eq]
    push_cast
    ring
  rw [← hval]
  refine h.congr fun s => ?_
  rw [completedDedekindZeta]
  ring

/-! ### The continuation of $\zeta_F$ -/

theorem one_le_nrPlaces : 1 ≤ nrRealPlaces F + nrComplexPlaces F := by
  have h := card_add_two_mul_card_eq_rank F
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  omega

variable (F) in
/-- The value of $\zeta_F$ at $s = 0$: $-\sqrt{|d_F|}\rho_F/(2\pi^{r_2})$ times $\Gamma_{\mathbb R}(0)^{-(r_1+r_2-1)}$, which
is $1$ if $r_1+r_2 = 1$ and $0$ otherwise (Mathlib's convention $\Gamma(0) = 0$; `dedekindZetaCont_zero`). -/
def dedekindZetaAtZero : ℂ :=
  -((((Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F : ℝ)) : ℂ) / (Real.pi : ℂ) ^ nrComplexPlaces F) *
    ((Complex.Gammaℝ 0)⁻¹) ^ (nrRealPlaces F + nrComplexPlaces F - 1) / 2

variable (F) in
/-- **The continuation of the Dedekind zeta function**: $\zeta_F(s) = |d_F|^{-s/2}\Lambda_F(s)/
\bigl(\Gamma_{\mathbb R}(s)^{r_1}\Gamma_{\mathbb C}(s)^{r_2}\bigr)$ for $s\ne0$, and its limit at $s = 0$
(`dedekindZetaAtZero`). It is holomorphic on $\mathbb C\setminus\{1\}$ and equals Mathlib's `dedekindZeta F s` for
$\operatorname{Re}s>1$. -/
@[kb "neukirch1999" "Ch. VII, §5, Cor. 5.11 [unverified locator] (ζ_K has a continuation to C ∖ {1})"]
def dedekindZetaCont : ℂ → ℂ :=
  Function.update (fun s => (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (-s / 2) * completedDedekindZeta F s / gammaFactor F s)
    0 (dedekindZetaAtZero F)

theorem dedekindZetaCont_of_ne {s : ℂ} (hs : s ≠ 0) :
    dedekindZetaCont F s =
      (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (-s / 2) * completedDedekindZeta F s / gammaFactor F s := by
  rw [dedekindZetaCont, Function.update_of_ne hs]

/-- **The continuation agrees with Mathlib's Dedekind zeta function** for $\operatorname{Re}s>1$. -/
theorem dedekindZetaCont_eq {s : ℂ} (hs : 1 < s.re) : dedekindZetaCont F s = dedekindZeta F s := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  rw [dedekindZetaCont_of_ne h0, completedDedekindZeta_eq hs]
  have hg := gammaFactor_ne_zero (F := F) (s := s) (by linarith)
  have hd : (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => abs_discr_ne_zero h.1
  rw [neg_div, Complex.cpow_neg]
  field_simp

/-- **$\zeta_F$ is holomorphic on $\mathbb C\setminus\{1\}$** (the pole of $\Lambda_F$ at $0$ is cancelled by the
zero of $1/\Gamma_{\mathbb R}(s)$). -/
@[kb "neukirch1999" "Ch. VII, §5, Cor. 5.11 [unverified locator]"]
theorem differentiableAt_dedekindZetaCont {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ (dedekindZetaCont F) s := by
  set n := nrRealPlaces F + nrComplexPlaces F
  set r₂ := nrComplexPlaces F
  set Λ' : ℂ → ℂ := fun t => (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (-t / 2) * completedDedekindZeta F t *
    ((Complex.Gammaℝ t)⁻¹) ^ (n - 1) * ((Complex.Gammaℝ (t + 1))⁻¹) ^ r₂
  set R : ℂ := -((((Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F : ℝ)) : ℂ) / (Real.pi : ℂ) ^ r₂)
  set L : ℂ := (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (-(0 : ℂ) / 2) * R * ((Complex.Gammaℝ 0)⁻¹) ^ (n - 1) * ((Complex.Gammaℝ (0 + 1))⁻¹) ^ r₂
  have hcpow : Differentiable ℂ fun t : ℂ => (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (-t / 2) := fun t =>
    (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl abs_discr_ne_zero)
  have hG1 : Differentiable ℂ fun t : ℂ => (Complex.Gammaℝ (t + 1))⁻¹ :=
    Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
  have hf : ∀ t, t ≠ 0 → t ≠ 1 → DifferentiableAt ℂ Λ' t := fun t ht0 ht1 =>
    ((((hcpow t).mul (differentiableAt_completedDedekindZeta ht0 ht1)).mul
      ((Complex.differentiable_Gammaℝ_inv t).pow _)).mul ((hG1 t).pow _))
  have hlim : Tendsto (fun t => t * Λ' t) (𝓝[≠] 0) (𝓝 L) := by
    have h1 : Tendsto (fun t : ℂ => (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (-t / 2)) (𝓝[≠] 0) (𝓝 ((((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (-(0 : ℂ) / 2))) :=
      (hcpow.continuous.tendsto 0).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℂ => ((Complex.Gammaℝ t)⁻¹) ^ (n - 1)) (𝓝[≠] 0)
        (𝓝 (((Complex.Gammaℝ 0)⁻¹) ^ (n - 1))) :=
      ((Complex.differentiable_Gammaℝ_inv.continuous.pow _).tendsto 0).mono_left nhdsWithin_le_nhds
    have h4 : Tendsto (fun t : ℂ => ((Complex.Gammaℝ (t + 1))⁻¹) ^ r₂) (𝓝[≠] 0)
        (𝓝 (((Complex.Gammaℝ (0 + 1))⁻¹) ^ r₂)) :=
      ((hG1.continuous.pow _).tendsto 0).mono_left nhdsWithin_le_nhds
    have h := ((h1.mul (tendsto_mul_completedDedekindZeta_zero (F := F))).mul h3).mul h4
    refine h.congr fun t => ?_
    simp only [Λ']
    ring
  have hmain := HurwitzZeta.differentiableAt_update_of_residue hf hlim s hs
  have hn : 1 ≤ n := one_le_nrPlaces
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hfun : dedekindZetaCont F = Function.update (fun t => Λ' t / Complex.Gammaℝ t) 0 (L / 2) := by
    funext t
    rcases eq_or_ne t 0 with rfl | ht
    · rw [dedekindZetaCont, Function.update_self, Function.update_self, dedekindZetaAtZero]
      simp only [L, R, zero_add, Complex.Gammaℝ_one, inv_one, one_pow, mul_one, neg_zero, zero_div,
        Complex.cpow_zero, one_mul]
      rfl
    · rw [dedekindZetaCont_of_ne ht, Function.update_of_ne ht]
      simp only [Λ']
      have hG : gammaFactor F t = Complex.Gammaℝ t ^ (m + 1) * Complex.Gammaℝ (t + 1) ^ r₂ := by
        rw [gammaFactor, ← Complex.Gammaℝ_mul_Gammaℝ_add_one, mul_pow, ← mul_assoc, ← pow_add]
        congr 2
      rw [hG, hm, Nat.add_sub_cancel, div_eq_mul_inv, div_eq_mul_inv, mul_inv, pow_succ, mul_inv]
      simp only [inv_pow]
      ring
  rw [hfun]
  exact hmain

/-- **$\zeta_F$ at $s = 0$**: $-\sqrt{|d_F|}\rho_F/(2\pi^{r_2}) = -h_FR_F/w_F$ if $r_1+r_2 = 1$ ($F = \mathbb Q$ or
imaginary quadratic), and $0$ otherwise. -/
theorem dedekindZetaCont_zero :
    dedekindZetaCont F 0 = if nrRealPlaces F + nrComplexPlaces F = 1 then
      -((((Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F : ℝ)) : ℂ) / (2 * (Real.pi : ℂ) ^ nrComplexPlaces F))
      else 0 := by
  rw [dedekindZetaCont, Function.update_self, dedekindZetaAtZero]
  have hG0 : Complex.Gammaℝ 0 = 0 := by simp [Complex.Gammaℝ, Complex.Gamma_zero]
  rw [hG0, inv_zero]
  have hn := one_le_nrPlaces (F := F)
  split_ifs with h
  · rw [h, Nat.sub_self, pow_zero, mul_one]
    ring
  · rw [zero_pow (by omega), mul_zero, zero_div]

/-- **The residue of $\zeta_F$ at $s = 1$ is $\rho_F$** $= 2^{r_1}(2\pi)^{r_2}h_FR_F/(w_F\sqrt{|d_F|})$ (Mathlib's
`dedekindZeta_residue`), as a limit in $\mathbb C$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (residue of ζ_k at s = 1, the class number formula)"]
theorem tendsto_sub_one_mul_dedekindZetaCont :
    Tendsto (fun s => (s - 1) * dedekindZetaCont F s) (𝓝[≠] 1) (𝓝 (dedekindZeta_residue F : ℂ)) := by
  set dC : ℂ := (((|(discr F : ℝ)| : ℝ)) : ℂ)
  have hc : Continuous fun s : ℂ => dC ^ (-s / 2) * (gammaFactor F s)⁻¹ :=
    ((continuous_id.neg.div_const 2).const_cpow (Or.inl abs_discr_ne_zero)).mul
      differentiable_gammaFactor_inv.continuous
  have h := ((hc.tendsto 1).mono_left nhdsWithin_le_nhds).mul (tendsto_sub_one_mul_completedDedekindZeta (F := F))
  have hval : dC ^ (-(1 : ℂ) / 2) * (gammaFactor F 1)⁻¹ *
      ((((Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F : ℝ)) : ℂ) / (Real.pi : ℂ) ^ nrComplexPlaces F) =
      dedekindZeta_residue F := by
    have hπ : ((Real.pi : ℂ) ^ nrComplexPlaces F) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hsq : dC ^ (-(1 : ℂ) / 2) * ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) = 1 := by
      rw [sqrt_abs_discr_eq, neg_div, Complex.cpow_neg, inv_mul_cancel₀]
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => abs_discr_ne_zero h.1
    rw [gammaFactor_one, inv_inv]
    push_cast
    calc dC ^ (-(1 : ℂ) / 2) * (Real.pi : ℂ) ^ nrComplexPlaces F *
          (((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) * (dedekindZeta_residue F : ℂ) / (Real.pi : ℂ) ^ nrComplexPlaces F)
        = (dC ^ (-(1 : ℂ) / 2) * ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)) * (dedekindZeta_residue F : ℂ) := by
          field_simp
      _ = _ := by rw [hsq, one_mul]
  rw [← hval]
  refine h.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0))] with s hs
  rw [dedekindZetaCont_of_ne hs]
  ring

/-- **Check against Mathlib**: Mathlib's analytic class number formula `tendsto_sub_one_mul_dedekindZeta_nhdsGT`,
re-derived from Tate's thesis (`tendsto_sub_one_mul_dedekindZetaCont` and `dedekindZetaCont_eq`). -/
theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT' :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta F s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue F)) := by
  have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    · intro h
      have h' : (x : ℂ) = 1 := h
      have : x = 1 := by exact_mod_cast h'
      exact (ne_of_gt (Set.mem_Ioi.mp hx)) this
  refine ((tendsto_sub_one_mul_dedekindZetaCont (F := F)).comp ht).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply]
  rw [dedekindZetaCont_eq (by simpa using hx)]

end

end NumberFieldKB.HeckeL
