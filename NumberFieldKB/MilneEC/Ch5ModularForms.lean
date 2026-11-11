import NumberFieldKB.MilneEC.Ch5Defs
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.LFunction

/-!
# Milne, *Elliptic Curves*, Chapter V §3: modular forms

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §3 (pdf pp. 197–201), with the comparison of
Milne's normalisations (Chapter III and V §2) with Mathlib's.

Mathlib's `ModularForm Γ w` (for `Γ : Subgroup (GL (Fin 2) ℝ)`, integer weight `w`) is Definition 3.1 with
$w = 2k$; `def_3_1` proves the comparison with the three conditions (a)–(c) as Milne states them.

Proposition 3.3 (holomorphic differentials on $X_0(N)$ are $S_2(\Gamma_0(N))$) is proved in local form in
`NumberFieldKB/MilneEC/Ch5Differentials.lean` and `Ch5DifferentialsElliptic.lean`. Not formalized (no Riemann
surface structure on $\Gamma_0(N)\backslash\mathbb H^*$ and no genus in Mathlib): Corollary 3.4
($\dim S_2(\Gamma_0(N))$ is the genus).
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold ArithmeticFunction.sigma

namespace NumberFieldKB.MilneEC.V

/-! ### Comparison of Milne's normalisations with Mathlib's -/

/-- $G_w(z)$ as a sum over pairs of integers, in the form used by Mathlib's Eisenstein series. -/
theorem eisG_eq_tsum {w : ℕ} (z : ℍ) :
    eisG w z = ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand w v z := by
  unfold eisG PeriodPair.G
  rw [← ((finTwoArrowEquiv ℤ).trans (periodPairOf z).latticeEquivProd.symm.toEquiv).tsum_eq]
  refine tsum_congr fun x => ?_
  have h := (periodPairOf z).latticeEquiv_symm_apply (x 0, x 1)
  have h2 : (((finTwoArrowEquiv ℤ).trans (periodPairOf z).latticeEquivProd.symm.toEquiv) x : ℂ)
      = x 0 * z + x 1 := by
    refine h.trans ?_
    simp [periodPairOf]
  rw [h2]
  simp [EisensteinSeries.eisSummand]

/-- $G_w(z) = 2\zeta(w)E_w(z)$ for $w \ge 3$, where `ModularForm.E` is Mathlib's normalised Eisenstein series
(constant term $1$). -/
theorem eisG_eq {w : ℕ} (hw : 3 ≤ w) (z : ℍ) : eisG w z = 2 * riemannZeta w * E hw z := by
  rw [eisG_eq_tsum, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hw z,
    show E hw z = (1 / 2 : ℂ) • EisensteinSeries.eisensteinSeriesSIF (N := 1) 0 w z from rfl,
    EisensteinSeries.eisensteinSeriesSIF_apply 0 w z]
  simp only [smul_eq_mul]
  ring

/-- $\zeta(6) = \pi^6/945$ (from Mathlib's formula for $\zeta(2k)$ and $B_6 = 1/42$). -/
theorem riemannZeta_six' : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h6 : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
    have c2 : Nat.choose 6 2 = 15 := by decide
    have c3 : Nat.choose 6 3 = 20 := by decide
    have c4 : Nat.choose 6 4 = 15 := by decide
    have c5 : Nat.choose 6 5 = 6 := by decide
    norm_num [Finset.sum_range_succ, c2, c3, c4, c5, h5]
  have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show (2 * 3 : ℕ) = 6 by norm_num, h6] at this
  norm_num [Nat.factorial] at this ⊢
  rw [this]
  ring

/-- $g_4 = \tfrac43\pi^4E_4$ (from $\zeta(4) = \pi^4/90$). -/
theorem g4_eq (z : ℍ) : g4 z = 4 / 3 * π ^ 4 * E₄ z := by
  unfold g4 PeriodPair.g₂
  have := eisG_eq (w := 4) (by norm_num) z
  unfold eisG at this
  rw [this, Nat.cast_ofNat, riemannZeta_four]
  push_cast
  ring

/-- $g_6 = \tfrac{8}{27}\pi^6E_6$ (from $\zeta(6) = \pi^6/945$). -/
theorem g6_eq (z : ℍ) : g6 z = 8 / 27 * π ^ 6 * E₆ z := by
  unfold g6 PeriodPair.g₃
  have := eisG_eq (w := 6) (by norm_num) z
  unfold eisG at this
  rw [this, Nat.cast_ofNat, riemannZeta_six']
  push_cast
  ring

/-- Milne's $\Delta = g_4^3 - 27g_6^2$ is $(2\pi)^{12}$ times Mathlib's `ModularForm.discriminant`
($\eta^{24} = (E_4^3 - E_6^2)/1728$). -/
theorem discr_eq (z : ℍ) : discr z = (2 * π) ^ 12 * ModularForm.discriminant z := by
  unfold discr
  rw [g4_eq, g6_eq, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

/-- The discriminant form $\Delta(z)$ is nonzero for every $z$ in the upper half plane. -/
theorem discr_ne_zero (z : ℍ) : discr z ≠ 0 := by
  rw [discr_eq]
  exact mul_ne_zero (pow_ne_zero _ (by simp [Real.pi_ne_zero])) (ModularForm.discriminant_ne_zero z)

/-- $j = E_4^3/\Delta_{\mathrm{Mathlib}} = 1728E_4^3/(E_4^3 - E_6^2)$. -/
theorem jFun_eq (z : ℍ) : jFun z = E₄ z ^ 3 / ModularForm.discriminant z := by
  have hΔ := ModularForm.discriminant_ne_zero z
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold jFun
  rw [discr_eq, g4_eq]
  field_simp
  ring

/-- The $j$-function is $1728 E_4^3 / (E_4^3 - E_6^2)$. -/
theorem jFun_eq' (z : ℍ) : jFun z = 1728 * E₄ z ^ 3 / (E₄ z ^ 3 - E₆ z ^ 2) := by
  rw [jFun_eq, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  have h := ModularForm.discriminant_ne_zero z
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq] at h
  have h' : E₄ z ^ 3 - E₆ z ^ 2 ≠ 0 := fun h0 => h (by rw [h0]; simp)
  field_simp

/-! ### Definition 3.1 -/

/-- Milne's conditions (Definition 3.1, pdf p. 198) for $f : \mathbb H \to \mathbb C$ to be a modular form of
weight $2k$ for a subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb Z)$: (a) $f$ is holomorphic on $\mathbb H$;
(b) $f(\gamma z) = (cz+d)^{2k}f(z)$ for $\gamma \in \Gamma$; (c) $f$ is holomorphic at the cusps. For (c), at the
cusp $\gamma\infty$ ($\gamma \in \mathrm{SL}_2(\mathbb Z)$) Milne asks that "$f \circ \gamma$ be holomorphic at
$\infty$"; for weight $2k \ne 0$ the function to test is $(cz+d)^{-2k}f(\gamma z)$ (the slash $f|_{2k}\gamma$), and,
being periodic, it is holomorphic at $\infty$ in the variable $q$ if and only if it is bounded as
$\Im z \to \infty$ (Riemann's removable singularity theorem). -/
@[kb "milne2006ec" "Ch. V, Definition 3.1, pdf p. 198"]
def IsModularFormMilne (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ (∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * f z) ∧
    ∀ γ : SL(2, ℤ), IsBoundedAtImInfty fun z : ℍ ↦ ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-(2 * k : ℤ)) * f (γ • z)

/-- Milne's cusp forms (Definition 3.1, pdf p. 198): modular forms that are zero at the cusps. -/
@[kb "milne2006ec" "Ch. V, Definition 3.1 (cusp forms), pdf p. 198"]
def IsCuspFormMilne (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ (∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * f z) ∧
    ∀ γ : SL(2, ℤ), IsZeroAtImInfty fun z : ℍ ↦ ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-(2 * k : ℤ)) * f (γ • z)

/-- The denominator $cz+d$ is nonzero on the upper half plane. -/
theorem denom_aux (γ : SL(2, ℤ)) (z : ℍ) : ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero (mapGL ℝ γ) z
  simpa [UpperHalfPlane.denom] using this

/-- The weight $w$ slash action of $\gamma \in \mathrm{SL}_2(\mathbb Z)$ (viewed in $\mathrm{GL}_2(\mathbb R)$):
$(f|_w\gamma)(z) = (cz+d)^{-w}f(\gamma z)$. -/
theorem slash_mapGL_apply (w : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (z : ℍ) :
    (f ∣[w] (mapGL ℝ γ)) z = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-w) * f (γ • z) := by
  have h := ModularForm.SL_slash_apply (k := w) f γ z
  rw [mul_comm] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · congr 2

/-- Natural-number powers of the denominator match the integer powers in the slash action. -/
theorem denom_pow_aux (k : ℕ) (c : ℂ) : c ^ (2 * k) = c ^ (2 * (k : ℤ)) := by
  exact_mod_cast (zpow_natCast c (2 * k)).symm

/-- **Definition 3.1** (pdf p. 198) agrees with Mathlib's `ModularForm`: for $\Gamma$ of finite index in
$\mathrm{SL}_2(\mathbb Z)$, $f$ satisfies (a)–(c) if and only if it is a Mathlib modular form of weight $2k$ for the
image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$. -/
@[kb "milne2006ec" "Ch. V, Definition 3.1, pdf p. 198"]
theorem def_3_1 (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℕ) (f : ℍ → ℂ) :
    IsModularFormMilne Γ k f ↔ ∃ F : ModularForm (Γ.map (mapGL ℝ)) (2 * k : ℤ), ⇑F = f := by
  constructor
  · rintro ⟨hol, hinv, hbd⟩
    refine ⟨{ toFun := f, slash_action_eq' := ?_, holo' := hol, bdd_at_cusps' := ?_ }, rfl⟩
    · rintro _ ⟨γ, hγ, rfl⟩
      funext z
      rw [slash_mapGL_apply, hinv γ hγ z, zpow_neg, ← denom_pow_aux,
        inv_mul_cancel_left₀ (pow_ne_zero _ (denom_aux γ z))]
    · intro c hc
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      refine (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ => ?_
      have := hbd γ
      convert this using 1
      funext z
      exact slash_mapGL_apply _ _ γ z
  · rintro ⟨F, rfl⟩
    refine ⟨F.holo', ?_, ?_⟩
    · intro γ hγ z
      have h := congrFun (F.slash_action_eq' (mapGL ℝ γ) ⟨γ, hγ, rfl⟩) z
      rw [slash_mapGL_apply] at h
      have hd := denom_aux γ z
      rw [zpow_neg, ← denom_pow_aux] at h
      change ((_ : ℂ) ^ (2 * k))⁻¹ * F (γ • z) = F z at h
      rw [← h]
      field_simp
    · intro γ
      have := ModularFormClass.bdd_at_infty_slash F γ
      convert this using 1
      funext z
      exact (slash_mapGL_apply _ _ γ z).symm

/-- **Definition 3.1** for cusp forms agrees with Mathlib's `CuspForm`. -/
@[kb "milne2006ec" "Ch. V, Definition 3.1 (cusp forms), pdf p. 198"]
theorem def_3_1_cusp (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℕ) (f : ℍ → ℂ) :
    IsCuspFormMilne Γ k f ↔ ∃ F : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℤ), ⇑F = f := by
  constructor
  · rintro ⟨hol, hinv, hbd⟩
    refine ⟨{ toFun := f, slash_action_eq' := ?_, holo' := hol, zero_at_cusps' := ?_ }, rfl⟩
    · rintro _ ⟨γ, hγ, rfl⟩
      funext z
      rw [slash_mapGL_apply, hinv γ hγ z, zpow_neg, ← denom_pow_aux,
        inv_mul_cancel_left₀ (pow_ne_zero _ (denom_aux γ z))]
    · intro c hc
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      refine (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun γ _ => ?_
      have := hbd γ
      convert this using 1
      funext z
      exact slash_mapGL_apply _ _ γ z
  · rintro ⟨F, rfl⟩
    refine ⟨F.holo', ?_, ?_⟩
    · intro γ hγ z
      have h := congrFun (F.slash_action_eq' (mapGL ℝ γ) ⟨γ, hγ, rfl⟩) z
      rw [slash_mapGL_apply] at h
      have hd := denom_aux γ z
      rw [zpow_neg, ← denom_pow_aux] at h
      change ((_ : ℂ) ^ (2 * k))⁻¹ * F (γ • z) = F z at h
      rw [← h]
      field_simp
    · intro γ
      have := CuspFormClass.zero_at_infty_slash F γ
      convert this using 1
      funext z
      exact (slash_mapGL_apply _ _ γ z).symm

/-- Running text, pdf p. 199: a modular form of weight $0$ is constant, $M_0(\Gamma) = \mathbb C$ (Mathlib's
`ModularForm.eq_const_of_weight_zero`, proved by norm maps down to level one). -/
@[kb "milne2006ec" "Ch. V, §3, M₀(Γ) = ℂ (running text), pdf p. 199"]
theorem modularForm_weight_zero_const (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : ModularForm (Γ.map (mapGL ℝ)) 0) : ∃ c : ℂ, ⇑f = Function.const ℍ c :=
  ModularForm.eq_const_of_weight_zero f

/-- Running text, pdf p. 199: the product of a modular form of weight $2k$ and one of weight $2k'$ is a modular
form of weight $2(k+k')$, which is a cusp form if one of the two is (so $\bigoplus_k M_{2k}(\Gamma)$ is a graded
$\mathbb C$-algebra; Mathlib's `ModularForm.mul` and the graded ring `⨁ k, ModularForm Γ k`). -/
@[kb "milne2006ec" "Ch. V, §3, products of modular forms (running text), pdf p. 199"]
theorem cuspForm_mul_modularForm (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {w w' : ℤ}
    (f : CuspForm (Γ.map (mapGL ℝ)) w) (g : ModularForm (Γ.map (mapGL ℝ)) w') :
    ∃ F : CuspForm (Γ.map (mapGL ℝ)) (w + w'), ⇑F = ⇑f * ⇑g :=
  ⟨{ toSlashInvariantForm := f.1.mul g.1
     holo' := f.holo'.mul g.holo'
     zero_at_cusps' := fun hc γ hγ => by
       simpa [mul_slash] using! ((f.zero_at_cusps' hc γ hγ).mul_boundedAtFilter
         (g.bdd_at_cusps' hc γ hγ)).smul _ }, rfl⟩

/-- Running text after Corollary 3.4 (pdf p. 199), from the genus formulas of p. 180 (Shimura 1971, Mazur 1973):
$S_2(\Gamma_0(N)) = 0$ for $N \le 10$ and $\dim S_2(\Gamma_0(11)) = 1$. A named statement (the genus formula for
$X_0(N)$ is out of reach: Mathlib has no genus of a compact Riemann surface). -/
@[kb "milne2006ec" "Ch. V, §3, dim S₂(Γ₀(N)) for N ≤ 11 (running text after Corollary 3.4), pdf p. 199"]
structure DimS2Small : Prop where
  eq_zero : ∀ N : ℕ, 1 ≤ N → N ≤ 10 → Module.rank ℂ (CuspForm (Gamma0GL N) 2) = 0
  eq_one : Module.rank ℂ (CuspForm (Gamma0GL 11) 2) = 1

/-! ### Level one: Proposition 3.5, Theorem 3.6, Theorem 3.7 -/

/-- $\gamma z = (az+b)/(cz+d)$ as complex numbers, for $\gamma \in \mathrm{SL}_2(\mathbb Z)$. -/
theorem smul_coe_aux (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [coe_specialLinearGroup_apply]
  simp

/-- $\Lambda(\gamma z, 1) = (cz+d)^{-1}\Lambda(z, 1)$ for $\gamma \in \mathrm{SL}_2(\mathbb Z)$. -/
theorem lattice_smul (γ : SL(2, ℤ)) (z : ℍ) :
    (periodPairOf (γ • z)).lattice =
      (periodPairOf z).lattice.map (LinearMap.mul ℤ ℂ (((γ 1 0 : ℂ) * z + γ 1 1))⁻¹) := by
  have hc := denom_aux γ z
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  have h1 : (periodPairOf z).lattice =
      Submodule.span ℤ {(γ 0 0 : ℂ) * z + γ 0 1, (γ 1 0 : ℂ) * z + γ 1 1} := by
    unfold PeriodPair.lattice
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      have hz : (z : ℂ) = (γ 1 1 : ℤ) • ((γ 0 0 : ℂ) * z + γ 0 1) -
          (γ 0 1 : ℤ) • ((γ 1 0 : ℂ) * z + γ 1 1) := by
        simp only [zsmul_eq_mul]; linear_combination (-(z : ℂ)) * hdet
      have h1' : (1 : ℂ) = (γ 0 0 : ℤ) • ((γ 1 0 : ℂ) * z + γ 1 1) -
          (γ 1 0 : ℤ) • ((γ 0 0 : ℂ) * z + γ 0 1) := by
        simp only [zsmul_eq_mul]; linear_combination (-1 : ℂ) * hdet
      rcases hx with rfl | rfl
      · have hm : (γ 1 1 : ℤ) • ((γ 0 0 : ℂ) * z + γ 0 1) - (γ 0 1 : ℤ) • ((γ 1 0 : ℂ) * z + γ 1 1) ∈
            Submodule.span ℤ {(γ 0 0 : ℂ) * z + γ 0 1, (γ 1 0 : ℂ) * z + γ 1 1} :=
          Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        rw [← hz] at hm
        simpa [periodPairOf] using hm
      · have hm : (γ 0 0 : ℤ) • ((γ 1 0 : ℂ) * z + γ 1 1) - (γ 1 0 : ℤ) • ((γ 0 0 : ℂ) * z + γ 0 1) ∈
            Submodule.span ℤ {(γ 0 0 : ℂ) * z + γ 0 1, (γ 1 0 : ℂ) * z + γ 1 1} :=
          Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        rw [← h1'] at hm
        simpa [periodPairOf] using hm
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · have : (γ 0 0 : ℂ) * z + γ 0 1 =
            (γ 0 0 : ℤ) • ((periodPairOf z).ω₁) + (γ 0 1 : ℤ) • (periodPairOf z).ω₂ := by
          simp [periodPairOf]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · have : (γ 1 0 : ℂ) * z + γ 1 1 =
            (γ 1 0 : ℤ) • ((periodPairOf z).ω₁) + (γ 1 1 : ℤ) • (periodPairOf z).ω₂ := by
          simp [periodPairOf]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  rw [h1, Submodule.map_span]
  unfold PeriodPair.lattice
  congr 1
  simp only [periodPairOf, smul_coe_aux]
  rw [Set.image_pair]
  simp [div_eq_inv_mul, hc]

/-- Running text, pdf p. 200: a function $F$ on lattices with $F(\lambda\Lambda) = \lambda^{-2k}F(\Lambda)$ gives
$f(z) = F(\Lambda(z,1))$ with $f(\gamma z) = (cz+d)^{2k}f(z)$ for $\gamma \in \mathrm{SL}_2(\mathbb Z)$. -/
@[kb "milne2006ec" "Ch. V, §3, functions on lattices give (3.1b) (running text), pdf p. 200"]
theorem lattice_function_transform (k : ℕ) (F : Submodule ℤ ℂ → ℂ)
    (hF : ∀ (c : ℂ) (Λ : Submodule ℤ ℂ), c ≠ 0 → F (Λ.map (LinearMap.mul ℤ ℂ c)) = c ^ (-(2 * k : ℤ)) * F Λ)
    (γ : SL(2, ℤ)) (z : ℍ) :
    F (periodPairOf (γ • z)).lattice = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * F (periodPairOf z).lattice := by
  rw [lattice_smul, hF _ _ (inv_ne_zero (denom_aux γ z))]
  simp only [neg_neg, inv_zpow']
  rw [show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

/-- Equation (35) (pdf p. 191, from Serre 1973, VII): for $k \ge 2$,
$G_{2k}(z) = 2\zeta(2k) + 2\frac{(2\pi i)^{2k}}{(2k-1)!}\sum_{n\ge1}\sigma_{2k-1}(n)q^n$, $q = e^{2\pi iz}$. -/
@[kb "milne2006ec" "Ch. V, §2, equation (35), pdf p. 191"]
theorem eq_35 {k : ℕ} (hk : 2 ≤ k) (z : ℍ) :
    eisG (2 * k) z = 2 * riemannZeta (2 * k) + 2 * (2 * π * I) ^ (2 * k) / (2 * k - 1).factorial *
      ∑' n : ℕ+, (σ (2 * k - 1) n : ℂ) * cexp (2 * π * I * z) ^ (n : ℕ) := by
  have h3 : 3 ≤ 2 * k := by omega
  rw [eisG_eq_tsum, tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow h3 (even_two_mul k) z]
  push_cast
  rw [show (-2 * π * I : ℂ) = -(2 * π * I) by ring, Even.neg_pow (even_two_mul k)]
  ring

/-- **Proposition 3.5** (pdf p. 200), first part: for $k > 1$, $G_{2k}$ is a modular form of weight $2k$ for
$\Gamma_0(1) = \mathrm{SL}_2(\mathbb Z)$. -/
@[kb "milne2006ec" "Ch. V, Proposition 3.5, pdf p. 200"]
theorem prop_3_5_eisenstein {k : ℕ} (hk : 1 < k) : ∃ F : ModularForm 𝒮ℒ (2 * k : ℤ), ⇑F = eisG (2 * k) := by
  have h3 : 3 ≤ 2 * k := by omega
  rw [show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring]
  refine ⟨(2 * riemannZeta (2 * k) : ℂ) • E h3, ?_⟩
  funext z
  rw [eisG_eq h3 z]
  simp

/-- **Proposition 3.5** (pdf p. 200), second part: $\Delta$ is a cusp form of weight $12$ for
$\mathrm{SL}_2(\mathbb Z)$. -/
@[kb "milne2006ec" "Ch. V, Proposition 3.5, pdf p. 200"]
theorem prop_3_5_discr : ∃ F : CuspForm 𝒮ℒ 12, ⇑F = discr := by
  refine ⟨((2 * π : ℂ) ^ 12) • CuspForm.discriminant, ?_⟩
  funext z
  rw [discr_eq]
  simp

/-- **Theorem 3.7** (Jacobi, pdf p. 201): $\Delta = (2\pi)^{12}q\prod_{n\ge1}(1-q^n)^{24}$, $q = e^{2\pi iz}$. -/
@[kb "milne2006ec" "Ch. V, Theorem 3.7 (Jacobi), pdf p. 201"]
theorem thm_3_7 (z : ℍ) :
    discr z = (2 * π) ^ 12 * cexp (2 * π * I * z) * ∏' n : ℕ, (1 - cexp (2 * π * I * z) ^ (n + 1)) ^ 24 := by
  rw [discr_eq, ModularForm.discriminant_eq_q_prod]
  simp [Function.Periodic.qParam, eta_q, mul_assoc]

end NumberFieldKB.MilneEC.V
