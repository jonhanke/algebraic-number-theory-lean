import NumberFieldKB.MilneEC.Ch5ModularForms
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Milne, *Elliptic Curves*, Chapter V, Proposition 3.3 in local form: weight 2 cusp forms are holomorphic differentials

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §3, Proposition 3.3 (pdf p. 199).

Milne: pulling back holomorphic differentials along $\mathbb H \to \Gamma_0(N)\backslash\mathbb H^*$ identifies the
holomorphic differentials on $X_0(N)$ with $S_2(\Gamma_0(N))$, $f \leftrightarrow f(z)\,dz$. A differential on
$X_0(N)$ is a $\Gamma_0(N)$-invariant differential $f(z)\,dz$ on $\mathbb H$ that is holomorphic in Milne's local
coordinates: $z$ at ordinary points, $t = w^e$ at an elliptic point of order $e$ ($w$ a disc coordinate centred
there), and $q = e^{2\pi i z/h}$ at a cusp. The proof is the three local computations below, which are proved here.

* **Invariance** (`weight_two_iff_differential_invariant`): $f(\gamma z) = (cz+d)^2 f(z)$ if and only if
  $f(\gamma z)\,d(\gamma z) = f(z)\,dz$, since $d(\gamma z)/dz = (cz+d)^{-2}$; the pullback $\gamma^*(f\,dz)$ is the
  weight 2 slash $f|_2\gamma$ (`pullback_eq_slash`).
* **Cusps** (`differentialHolomorphicAtInfty_iff`, headline `prop_3_3_cusps`): for an $h$-periodic holomorphic $f$,
  $f(z)\,dz = \frac{h}{2\pi i}\,F(q)\,q^{-1}\,dq$ with $F$ the cusp function ($f(z) = F(e^{2\pi i z/h})$), so the
  differential is holomorphic at $q = 0$ if and only if $f$ vanishes at $i\infty$. Hence a holomorphic $f$ with
  $f(z)\,dz$ invariant under $\Gamma_0(N)$ is a weight 2 cusp form if and only if $f(z)\,dz$ is holomorphic at every
  cusp $\gamma\infty$ in the coordinate $q = e^{2\pi i z/N}$ (after pulling back by $\gamma$). Milne's chart at a
  cusp of width $w \mid N$ is $q_w = e^{2\pi i z/w}$ (he writes out $w = 1$ at $\infty$); since
  `differentialHolomorphicAtInfty_iff` holds for every period $h$, holomorphy in $q_w$ and in $q_N$ are both
  equivalent to the vanishing of $f|_2\gamma$ at $i\infty$, so the condition is the same.
* The elliptic points are in `NumberFieldKB/MilneEC/Ch5DifferentialsElliptic.lean`.
* **Elliptic points** (`exists_analyticAt_of_rotation_invariant`, `prop_3_3_elliptic`): an invariant holomorphic
  differential $\varphi(w)\,dw$ on a disc under the rotation $w \mapsto \zeta w$ of order $e$ has the form
  $\psi(t)\,dt$, $t = w^e$, with $\psi$ holomorphic; for $f$ of weight 2 fixed by $\gamma$ at $z_0$, in the disc
  coordinate $w = (z - z_0)/(z - \bar z_0)$, $\gamma$ is the rotation by $\lambda = (cz_0+d)^{-2}$, so $f(z)\,dz$ is
  holomorphic in Milne's coordinate $t = w^e$ at an elliptic point: no condition is imposed there.

**What is not here.** The identification of the space of such differentials with the holomorphic differentials of
the Riemann surface $X_0(N)$ is the statement that Milne's coordinates are the charts of $X_0(N)$: Tau Ceti proves that
these charts form a Riemann surface (`Subgroup.CompactifiedQuotient.instIsManifold`, not importable here). Corollary
3.4 ($\dim S_2(\Gamma_0(N))$ is the genus) is proved algebraically instead, with the genus of the function field
(`NumberFieldKB.ModularCurves.cor_3_4`).
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Function
open scoped MatrixGroups Real Manifold ComplexConjugate

noncomputable section

namespace NumberFieldKB.MilneEC.V

/-! ### Invariance -/

/-- The Möbius map $w \mapsto (aw+b)/(cw+d)$ of $\gamma \in \mathrm{SL}_2(\mathbb Z)$, as a function on $\mathbb C$. -/
def moebiusC (γ : SL(2, ℤ)) (w : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)

theorem moebiusC_coe (γ : SL(2, ℤ)) (z : ℍ) : moebiusC γ z = ((γ • z : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [moebiusC]

/-- $d(\gamma z)/dz = (cz+d)^{-2}$. -/
theorem hasDerivAt_moebiusC (γ : SL(2, ℤ)) (z : ℍ) :
    HasDerivAt (moebiusC γ) (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)⁻¹ z := by
  have hd := denom_aux γ z
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have h1 : HasDerivAt (fun w : ℂ => (γ 0 0 : ℂ) * w + γ 0 1) (γ 0 0 : ℂ) (z : ℂ) := by
    simpa using ((hasDerivAt_id (z : ℂ)).const_mul (γ 0 0 : ℂ)).add_const (γ 0 1 : ℂ)
  have h2 : HasDerivAt (fun w : ℂ => (γ 1 0 : ℂ) * w + γ 1 1) (γ 1 0 : ℂ) (z : ℂ) := by
    simpa using ((hasDerivAt_id (z : ℂ)).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)
  have := h1.div h2 hd
  refine HasDerivAt.congr_deriv (f := moebiusC γ) this ?_
  have hn : (γ 0 0 : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) - ((γ 0 0 : ℂ) * z + γ 0 1) * γ 1 0 = 1 := by
    linear_combination hdet
  rw [hn, one_div]

/-- The pullback $\gamma^*(f\,dz) = f(\gamma z)\,d(\gamma z)$ is $(f|_2\gamma)(z)\,dz$. -/
theorem pullback_eq_slash (γ : SL(2, ℤ)) (f : ℍ → ℂ) (z : ℍ) :
    f (γ • z) * deriv (moebiusC γ) z = (f ∣[(2 : ℤ)] γ) z := by
  have h := slash_mapGL_apply 2 f γ z
  have h' : (f ∣[(2 : ℤ)] γ) z = (f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) z := rfl
  rw [h', h, (hasDerivAt_moebiusC γ z).deriv, zpow_neg, mul_comm]
  norm_cast

/-- **Proposition 3.3, invariance** (Remark 3.2, pdf p. 198): $f(\gamma z) = (cz+d)^2f(z)$ for all $z$ if and only
if $f(\gamma z)\,d(\gamma z) = f(z)\,dz$. -/
@[kb "milne2006ec" "Ch. V, Proposition 3.3 (invariance of f(z)dz, Remark 3.2), pdf p. 199"]
theorem weight_two_iff_differential_invariant (γ : SL(2, ℤ)) (f : ℍ → ℂ) :
    (∀ z : ℍ, f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 * f z) ↔
      ∀ z : ℍ, f (γ • z) * deriv (moebiusC γ) z = f z := by
  refine forall_congr' fun z => ?_
  have hd := pow_ne_zero 2 (denom_aux γ z)
  rw [(hasDerivAt_moebiusC γ z).deriv]
  generalize (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) = D at hd ⊢
  generalize f (γ • z) = A
  generalize f z = B
  constructor
  · rintro rfl; field_simp
  · rintro rfl; field_simp

/-! ### Cusps -/

/-- The coefficient of $f(z)\,dz$ in the coordinate $q = e^{2\pi i z/h}$ at the cusp $\infty$:
$f(z)\,dz = \frac{h}{2\pi i}F(q)q^{-1}\,dq$, $F$ the cusp function of $f$. -/
def qCoeff (h : ℝ) (f : ℍ → ℂ) (q : ℂ) : ℂ :=
  h / (2 * π * I) * (Periodic.cuspFunction h (f ∘ ofComplex) q / q)

private theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (Periodic.qParam h) (2 * π * I / h * Periodic.qParam h z) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * π * I * w / h) (2 * π * I / h) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * π * I)).div_const (h : ℂ)
  have := h1.cexp
  unfold Periodic.qParam
  convert this using 1
  ring

/-- $f(z)\,dz = \mathrm{qCoeff}(q)\,dq$ along $q = e^{2\pi i z/h}$. -/
theorem qCoeff_mul_deriv {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : Periodic (f ∘ ofComplex) h) (z : ℍ) :
    qCoeff h f (Periodic.qParam h z) * deriv (Periodic.qParam h) z = f z := by
  have hd := hasDerivAt_qParam h (z : ℂ)
  have hF : Periodic.cuspFunction h (f ∘ ofComplex) (Periodic.qParam h z) = f z := by
    exact UpperHalfPlane.eq_cuspFunction z hh.ne' hf
  have hq := Periodic.qParam_ne_zero (h := h) (z : ℂ)
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [hd.deriv, qCoeff, hF]
  field_simp

/-- The differential $f(z)\,dz$ is holomorphic at the cusp $\infty$ in the coordinate $q = e^{2\pi i z/h}$: its
coefficient extends holomorphically over $q = 0$. -/
def DifferentialHolomorphicAtInfty (h : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ q in 𝓝[≠] 0, g q = qCoeff h f q

/-- **Proposition 3.3 at the cusp $\infty$**: for an $h$-periodic holomorphic $f$, the differential $f(z)\,dz$ is
holomorphic at $q = 0$ if and only if $f$ vanishes at $i\infty$. -/
@[kb "milne2006ec" "Ch. V, Proposition 3.3 (the cusp at infinity), pdf p. 199"]
theorem differentialHolomorphicAtInfty_iff {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hhol : MDiff f)
    (hf : Periodic (f ∘ ofComplex) h) :
    DifferentialHolomorphicAtInfty h f ↔ IsZeroAtImInfty f := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · rintro ⟨g, hg, hev⟩
    set F := Periodic.cuspFunction h (f ∘ ofComplex) with hFdef
    have hFev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), F q = 2 * π * I / h * (q * g q) := by
      filter_upwards [hev, self_mem_nhdsWithin] with q hq hq0
      have hq0 : q ≠ 0 := hq0
      rw [hq, qCoeff]
      field_simp
      rfl
    have hlim : Tendsto F (𝓝[≠] 0) (𝓝 0) := by
      have h3 : Tendsto (fun q : ℂ => 2 * π * I / h * (q * g q)) (𝓝[≠] 0) (𝓝 0) := by
        have : ContinuousAt (fun q : ℂ => 2 * π * I / h * (q * g q)) 0 :=
          continuousAt_const.mul (continuousAt_id.mul hg.continuousAt)
        simpa using this.tendsto.mono_left nhdsWithin_le_nhds
      exact h3.congr' (hFev.mono fun q hq => hq.symm)
    have hcomp := hlim.comp ((Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty)
    refine hcomp.congr fun τ => ?_
    exact UpperHalfPlane.eq_cuspFunction τ hh.ne' hf
  · intro hz
    have hbdd := hz.isBoundedAtImInfty
    have hana := UpperHalfPlane.analyticAt_cuspFunction_zero hh hf hhol hbdd
    have hF0 : UpperHalfPlane.cuspFunction h f 0 = 0 := hz.cuspFunction_apply_zero hh
    obtain ⟨p, hp⟩ := hana
    refine ⟨fun q => h / (2 * π * I) * dslope (UpperHalfPlane.cuspFunction h f) 0 q,
      analyticAt_const.mul hp.has_fpower_series_dslope_fslope.analyticAt, ?_⟩
    refine eventually_nhdsWithin_of_forall fun q hq => ?_
    have hq : q ≠ 0 := hq
    beta_reduce
    rw [dslope_of_ne _ hq, slope_def_field, hF0, qCoeff]
    simp [UpperHalfPlane.cuspFunction]

private theorem slash_invariant_of_hinv (N : ℕ) (f : ℍ → ℂ)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z : ℍ, f (γ • z) * deriv (moebiusC γ) z = f z)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 N) : f ∣[(2 : ℤ)] δ = f := by
  funext z
  rw [← pullback_eq_slash]
  exact hinv δ hδ z

private theorem slash_periodic (N : ℕ) (f : ℍ → ℂ)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z : ℍ, f (γ • z) * deriv (moebiusC γ) z = f z)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(2 : ℤ)] γ) ((N : ℝ) +ᵥ τ) = (f ∣[(2 : ℤ)] γ) τ := by
  set T' : SL(2, ℤ) := ModularGroup.T ^ (N : ℤ) with hT'
  have hT'mem : T' ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma_mem]
    have h : (T' : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] :=
      ModularGroup.coe_T_zpow (N : ℤ)
    have e00 : (T' 0 0 : ℤ) = 1 := by simpa using congrFun (congrFun h 0) 0
    have e01 : (T' 0 1 : ℤ) = N := by simpa using congrFun (congrFun h 0) 1
    have e10 : (T' 1 0 : ℤ) = 0 := by simpa using congrFun (congrFun h 1) 0
    have e11 : (T' 1 1 : ℤ) = 1 := by simpa using congrFun (congrFun h 1) 1
    rw [e00, e01, e10, e11]
    simp
  have hδ : γ * T' * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    have := (CongruenceSubgroup.Gamma_normal N).conj_mem T' hT'mem γ
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp this).2.2.1
  have key : (f ∣[(2 : ℤ)] γ) ∣[(2 : ℤ)] T' = f ∣[(2 : ℤ)] γ := by
    rw [← SlashAction.slash_mul]
    have : γ * T' = (γ * T' * γ⁻¹) * γ := by simp
    rw [this, SlashAction.slash_mul, slash_invariant_of_hinv N f hinv _ hδ]
  have hc : (T' 1 0 : ℂ) * τ + T' 1 1 = 1 := by
    have h : (T' : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] :=
      ModularGroup.coe_T_zpow (N : ℤ)
    have e10 : (T' 1 0 : ℤ) = 0 := by simpa using congrFun (congrFun h 1) 0
    have e11 : (T' 1 1 : ℤ) = 1 := by simpa using congrFun (congrFun h 1) 1
    rw [e10, e11]; simp
  have := congrFun key τ
  have h2 : ((f ∣[(2 : ℤ)] γ) ∣[(2 : ℤ)] T') τ
      = (T' 1 0 * (τ : ℂ) + T' 1 1) ^ (-(2 : ℤ)) * (f ∣[(2 : ℤ)] γ) (T' • τ) :=
    slash_mapGL_apply 2 _ T' τ
  rw [h2, hc, one_zpow, one_mul, hT', UpperHalfPlane.modular_T_zpow_smul] at this
  exact this

/-- **Proposition 3.3, cusps** (pdf p. 199). For $N \ge 1$ and $f$ holomorphic on $\mathbb H$ with $f(z)\,dz$
invariant under $\Gamma_0(N)$: $f \in S_2(\Gamma_0(N))$ if and only if $f(z)\,dz$ is holomorphic at every cusp
$\gamma\infty$, $\gamma \in \mathrm{SL}_2(\mathbb Z)$, in the coordinate $q = e^{2\pi i z/N}$ of the pullback
$\gamma^*(f\,dz)$. -/
@[kb "milne2006ec" "Ch. V, Proposition 3.3 (S_2(Gamma_0(N)) and differentials holomorphic at the cusps), pdf p. 199"]
theorem prop_3_3_cusps (N : ℕ) [NeZero N] (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z : ℍ, f (γ • z) * deriv (moebiusC γ) z = f z) :
    IsCuspFormMilne (CongruenceSubgroup.Gamma0 N) 1 f ↔
      ∀ γ : SL(2, ℤ), DifferentialHolomorphicAtInfty N (fun z ↦ f (γ • z) * deriv (moebiusC γ) z) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hG : ∀ γ : SL(2, ℤ), (fun z ↦ f (γ • z) * deriv (moebiusC γ) z) = f ∣[(2 : ℤ)] γ :=
    fun γ => funext fun z => pullback_eq_slash γ f z
  have hGhol : ∀ γ : SL(2, ℤ), MDiff (fun z ↦ f (γ • z) * deriv (moebiusC γ) z) := by
    intro γ
    rw [hG γ]
    exact MDifferentiable.slash hf 2 (Matrix.SpecialLinearGroup.mapGL ℝ γ)
  have hGper : ∀ γ : SL(2, ℤ),
      Periodic ((fun z ↦ f (γ • z) * deriv (moebiusC γ) z) ∘ ofComplex) (N : ℝ) := by
    intro γ
    refine UpperHalfPlane.periodic_comp_ofComplex fun τ => ?_
    rw [pullback_eq_slash, pullback_eq_slash]
    exact slash_periodic N f hinv γ τ
  have hG3 : ∀ γ : SL(2, ℤ),
      (fun z : ℍ ↦ ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-(2 * ((1 : ℕ) : ℤ))) * f (γ • z)) =
        fun z ↦ f (γ • z) * deriv (moebiusC γ) z := by
    intro γ
    rw [hG γ]
    funext z
    have := slash_mapGL_apply 2 f γ z
    rw [show (2 * ((1 : ℕ) : ℤ)) = 2 by norm_num]
    exact this.symm
  constructor
  · rintro ⟨_, _, h3⟩ γ
    rw [differentialHolomorphicAtInfty_iff hNpos (hGhol γ) (hGper γ), ← hG3 γ]
    exact h3 γ
  · intro H
    refine ⟨hf, ?_, fun γ => ?_⟩
    · intro γ hγ z
      have := (weight_two_iff_differential_invariant γ f).mpr (hinv γ hγ) z
      simpa using this
    · rw [hG3 γ]
      exact (differentialHolomorphicAtInfty_iff hNpos (hGhol γ) (hGper γ)).mp (H γ)

end NumberFieldKB.MilneEC.V
