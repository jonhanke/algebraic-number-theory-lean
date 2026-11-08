import NumberFieldKB.ModularCurves.Theorem23
import NumberFieldKB.ModularCurves.JLocal
import NumberFieldKB.MilneEC.Ch5Differentials
import NumberFieldKB.MilneEC.Ch5ModularForms
import NumberFieldKB.ModularCurves.Rationality

/-!
# $f/j'$ is a modular function for a weight 2 cusp form $f$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 3.3 and Corollary 3.4 (pdf p. 199): for
$f \in S_2(\Gamma_0(N))$, the differential $f(z)\,dz = (f/j')\,dj$, and $f/j'$ is a modular function for
$\Gamma_0(N)$ (`isModularFunction_div_jD`), so Theorem 2.3 applies to it.

Here $j' = \frac{d}{dz} j$ is `jD`, in the coordinate $z$ of $\mathbb C$. It is weight 2 invariant under all of
$\mathrm{SL}_2(\mathbb Z)$ (`jD_smul`: $j'(\gamma z)\,\gamma'(z) = j'(z)$, the chain rule for $j \circ \gamma = j$).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology ModularForm EisensteinSeries
open scoped MatrixGroups Manifold

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- $j'(z) = \frac{d}{dz} j(z)$. -/
def jD (z : ℍ) : ℂ := deriv (jFun ∘ ofComplex) (z : ℂ)

/-- **$j'$ is weight 2 invariant**: $j'(\gamma z)\,\gamma'(z) = j'(z)$. -/
theorem jD_smul (γ : SL(2, ℤ)) (z : ℍ) : jD (γ • z) * deriv (moebiusC γ) z = jD z := by
  set F : ℂ → ℂ := jFun ∘ ofComplex
  have hU : ∀ᶠ w in 𝓝 (z : ℂ), 0 < w.im := isOpen_upperHalfPlaneSet.mem_nhds z.im_pos
  have heq : F ∘ moebiusC γ =ᶠ[𝓝 (z : ℂ)] F := by
    filter_upwards [hU] with w hw
    have hw' : ((ofComplex w : ℍ) : ℂ) = w := by rw [ofComplex_apply_of_im_pos hw]
    have h1 : moebiusC γ w = ((γ • ofComplex w : ℍ) : ℂ) := by rw [← moebiusC_coe, hw']
    simp only [F, Function.comp_apply, h1, ofComplex_apply, jFun_smul]
  have hm : DifferentiableAt ℂ (moebiusC γ) (z : ℂ) := (hasDerivAt_moebiusC γ z).differentiableAt
  have hF : DifferentiableAt ℂ F (moebiusC γ (z : ℂ)) := by
    rw [moebiusC_coe]
    exact (analyticAt_jFun (γ • z)).differentiableAt
  have h := deriv_comp (z : ℂ) hF hm
  rw [heq.deriv_eq, moebiusC_coe] at h
  exact h.symm

theorem deriv_moebiusC_ne_zero (γ : SL(2, ℤ)) (z : ℍ) : deriv (moebiusC γ) z ≠ 0 := by
  rw [(hasDerivAt_moebiusC γ z).deriv]
  exact inv_ne_zero (pow_ne_zero _ (denom_aux γ z))

/-- $\gamma T^N \gamma^{-1} \in \Gamma_0(N)$ ($T^N \in \Gamma(N)$, a normal subgroup contained in $\Gamma_0(N)$). -/
theorem conj_T_zpow_mem_Gamma0 (N : ℕ) (γ : SL(2, ℤ)) :
    γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
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
  have := (CongruenceSubgroup.Gamma_normal N).conj_mem T' hT'mem γ
  rw [CongruenceSubgroup.Gamma0_mem]
  exact (CongruenceSubgroup.Gamma_mem.mp this).2.2.1

/-- $j' = -2\pi i \cdot 1728\, B/A$ with $A = E_4^3 - E_6^2$, $B = E_4^2 E_6$, hence $g/j' = g \cdot c A / B$. -/
theorem div_jD_eq (g : ℂ) (z : ℍ) :
    g / jD z = g * ((-(2 * Real.pi * Complex.I * 1728))⁻¹ * (E₄ z ^ 3 - E₆ z ^ 2)) / (E₄ z ^ 2 * E₆ z) := by
  have hA : (E₄ z ^ 3 - E₆ z ^ 2 : ℂ) ≠ 0 := E4_cube_sub_E6_sq_ne_zero z
  have h2 : (2 * Real.pi * Complex.I * 1728 : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [jD, deriv_jFun]
  by_cases hB : (E₄ z ^ 2 * E₆ z : ℂ) = 0
  · have : -(2 * Real.pi * Complex.I) * 1728 * E₄ z ^ 2 * E₆ z / (E₄ z ^ 3 - E₆ z ^ 2) = 0 := by
      rw [mul_assoc (-(2 * Real.pi * Complex.I) * 1728), hB, mul_zero, zero_div]
    rw [this, hB, div_zero, div_zero]
  · field_simp

theorem IsQExp.vadd_nat {F : ℍ → ℂ} (hF : IsQExp F) (n : ℕ) (z : ℍ) : F ((n : ℝ) +ᵥ z) = F z := by
  have e3 : (((n : ℝ) +ᵥ z : ℍ) : ℂ) = (z : ℂ) + (n : ℂ) * 1 := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  calc F ((n : ℝ) +ᵥ z) = (F ∘ ofComplex) (((n : ℝ) +ᵥ z : ℍ) : ℂ) := by
        rw [Function.comp_apply, ofComplex_apply]
    _ = (F ∘ ofComplex) ((z : ℂ) + (n : ℂ) * 1) := by rw [e3]
    _ = (F ∘ ofComplex) (z : ℂ) := hF.periodic.nat_mul n (z : ℂ)
    _ = F z := by rw [Function.comp_apply, ofComplex_apply]

/-- **$f/j'$ is a modular function for $\Gamma_0(N)$**, for $f \in S_2(\Gamma_0(N))$. -/
theorem isModularFunction_div_jD {N : ℕ} [NeZero N] {f : ℍ → ℂ}
    (hf : IsCuspFormMilne (CongruenceSubgroup.Gamma0 N) 1 f) :
    IsModularFunction (CongruenceSubgroup.Gamma0 N) (fun z => f z / jD z) := by
  obtain ⟨hhol, hinv0, hcusp⟩ := hf
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z, f (γ • z) * deriv (moebiusC γ) z = f z := fun γ hγ =>
    (weight_two_iff_differential_invariant γ f).1 (by simpa using hinv0 γ hγ)
  have key : ∀ (γ : SL(2, ℤ)) z, f (γ • z) / jD (γ • z) = (f ∣[(2 : ℤ)] γ) z / jD z := by
    intro γ z
    rw [← pullback_eq_slash, ← jD_smul γ z, mul_div_mul_right _ _ (deriv_moebiusC_ne_zero γ z)]
  have hinvar : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z, f (γ • z) / jD (γ • z) = f z / jD z := by
    intro γ hγ z
    rw [key, ← pullback_eq_slash, hinv γ hγ z]
  refine ⟨?_, hinvar, fun γ => ?_⟩
  · intro x hx
    set τ : ℍ := ⟨x, hx⟩
    have hfa : AnalyticAt ℂ (f ∘ ofComplex) x := analyticAt_comp_ofComplex hhol τ
    have hda : AnalyticAt ℂ (deriv (jFun ∘ ofComplex)) x := (analyticAt_jFun τ).deriv
    refine (hfa.meromorphicAt.div hda.meromorphicAt).congr ?_
    have hU : ∀ᶠ w in 𝓝 x, 0 < w.im := isOpen_upperHalfPlaneSet.mem_nhds hx
    filter_upwards [nhdsWithin_le_nhds hU] with w hw
    simp only [Function.comp_apply, Pi.div_apply, jD]
    rw [ofComplex_apply_of_im_pos hw]
  · -- the cusp $\gamma\infty$: period $N$, and $f(\gamma z)/j'(\gamma z) = (f|\gamma)(z)\,cA(z)/B(z)$
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    set P : ℍ → ℂ := f ∣[(2 : ℤ)] γ with hPdef
    set c : ℂ := (-(2 * Real.pi * Complex.I * 1728))⁻¹
    set A : ℍ → ℂ := c • ((E₄ : ℍ → ℂ) ^ 3 - (E₆ : ℍ → ℂ) ^ 2) with hAdef
    set B : ℍ → ℂ := (E₄ : ℍ → ℂ) ^ 2 * (E₆ : ℍ → ℂ) with hBdef
    have hg : ∀ z, f (γ • z) / jD (γ • z) = P z * A z / B z := fun z => by
      rw [key γ z, div_jD_eq]
      rfl
    have hE4 := IsQExp.of_modularForm E₄
    have hE6 := IsQExp.of_modularForm E₆
    have hAq : IsQExp A := by
      have := ((hE4.pow 3).add ((hE6.pow 2).smul (-1))).smul c
      convert this using 1
      funext z
      simp [hAdef, sub_eq_add_neg]
      ring
    have hBq : IsQExp B := (hE4.pow 2).mul hE6
    -- periodicity
    have hslash : ∀ δ ∈ CongruenceSubgroup.Gamma0 N, f ∣[(2 : ℤ)] δ = f := fun δ hδ => by
      funext z
      rw [← pullback_eq_slash]
      exact hinv δ hδ z
    have hPper' : ∀ τ : ℍ, P ((N : ℝ) +ᵥ τ) = P τ := by
      intro τ
      set T' : SL(2, ℤ) := ModularGroup.T ^ (N : ℤ)
      have keyT : P ∣[(2 : ℤ)] T' = P := by
        rw [hPdef, ← SlashAction.slash_mul]
        have : γ * T' = (γ * T' * γ⁻¹) * γ := by simp
        rw [this, SlashAction.slash_mul, hslash _ (conj_T_zpow_mem_Gamma0 N γ)]
      have hc : (T' 1 0 : ℂ) * τ + T' 1 1 = 1 := by
        have h : (T' : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] := ModularGroup.coe_T_zpow (N : ℤ)
        have e10 : (T' 1 0 : ℤ) = 0 := by simpa using congrFun (congrFun h 1) 0
        have e11 : (T' 1 1 : ℤ) = 1 := by simpa using congrFun (congrFun h 1) 1
        rw [e10, e11]; simp
      have := congrFun keyT τ
      have h2 : (P ∣[(2 : ℤ)] T') τ = (T' 1 0 * (τ : ℂ) + T' 1 1) ^ (-(2 : ℤ)) * P (T' • τ) :=
        slash_mapGL_apply 2 _ T' τ
      rw [h2, hc, one_zpow, one_mul, UpperHalfPlane.modular_T_zpow_smul] at this
      exact_mod_cast this
    have hgper : Function.Periodic ((fun z => f (γ • z) / jD (γ • z)) ∘ ofComplex) N := by
      refine UpperHalfPlane.periodic_comp_ofComplex fun z => ?_
      simp only [hg]
      rw [hPper', hAq.vadd_nat, hBq.vadd_nat]
    -- the cusp functions
    have hPmd : MDiff P := MDifferentiable.slash hhol 2 (Matrix.SpecialLinearGroup.mapGL ℝ γ)
    have hPbd : IsBoundedAtImInfty P := by
      have h := (hcusp γ).boundedAtFilter
      refine (Asymptotics.isBigO_congr (Eventually.of_forall fun z => ?_)
        (Eventually.of_forall fun _ => rfl)).mp h
      have := slash_mapGL_apply 2 f γ z
      rw [show (2 * ((1 : ℕ) : ℤ)) = 2 by norm_num]
      exact this.symm
    have hPa : AnalyticAt ℂ (cuspFunction N P) 0 :=
      analyticAt_cuspFunction_zero hNpos (UpperHalfPlane.periodic_comp_ofComplex hPper') hPmd hPbd
    have hper1 : ∀ {F : ℍ → ℂ}, IsQExp F → Function.Periodic (F ∘ ofComplex) N := fun hF =>
      UpperHalfPlane.periodic_comp_ofComplex fun z => hF.vadd_nat N z
    have hAa : AnalyticAt ℂ (cuspFunction N A) 0 :=
      analyticAt_cuspFunction_zero hNpos (hper1 hAq) hAq.mdiff hAq.bounded
    have hBa : AnalyticAt ℂ (cuspFunction N B) 0 :=
      analyticAt_cuspFunction_zero hNpos (hper1 hBq) hBq.mdiff hBq.bounded
    refine ⟨N, hNpos, hgper, ((hPa.meromorphicAt.mul hAa.meromorphicAt).div hBa.meromorphicAt).congr ?_⟩
    have hball : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ≠ 0 ∧ ‖q‖ < 1 := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
        with q hq hq1
      exact ⟨hq, by simpa using hq1⟩
    filter_upwards [hball] with q ⟨hq0, hq1⟩
    obtain ⟨z, -, hz⟩ := exists_point_cuspFunction' hNpos hq0 hq1
    simp only [Pi.div_apply, Pi.mul_apply]
    rw [hz, hz, hz, hz, hg]

end NumberFieldKB.ModularCurves
