import NumberFieldKB.MilneEC.Ch5ModularForms
import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Milne, *Elliptic Curves*, Chapter V §2: the modular invariant $j$ and $X_0(N)$ over $\mathbb Q$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2 (pdf pp. 189–197).

Formalized: the properties of $j$ used in §2 (invariance, holomorphy, $j(i) = 1728$, $j(\rho) = 0$, the simple
pole at $\infty$), Propositions 2.1 and 2.2 (uniqueness of $J$ and $j$ among holomorphic invariant functions with a
simple pole at the cusp; surjectivity of $j$), the invariance of $j_N$ under $\Gamma_0(N)$, the complex moduli
description of $\Gamma_0(N)\backslash\mathbb H$ (pdf pp. 195–196). Named statements: equation (37), injectivity of
$j$ on $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$, the rationality of modular functions in $j$ (Proposition 2.2,
last sentence), Theorem 2.3, the modular polynomial $F_N$ and Proposition 2.4.

Not formalized (no algebraic curves over $\mathbb Q$ with their points, no desingularisation, no genus in
Mathlib): the curve $X_0(N)$ over $\mathbb Q$, Theorem 2.7 and the functor $\mathcal E_0(N)$, Remark 2.6, the
variants $X_1(N)$.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold CongruenceSubgroup

namespace NumberFieldKB.MilneEC.V

local notation "Δ" => ModularForm.discriminant

/-! ### Helper lemmas: the transformation law of level-one forms -/

/-- The transformation law of a level-one modular form under $\mathrm{SL}_2(\mathbb Z)$. -/
lemma levelOne_smul {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} [SlashInvariantFormClass F 𝒮ℒ k]
    (f : F) (γ : SL(2, ℤ)) (z : ℍ) : f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * f z := by
  have : SlashInvariantFormClass F Γ(1) k :=
    CongruenceSubgroup.Gamma_one_coe_eq_SL ▸ ‹_›
  have := SlashInvariantForm.slash_action_eqn_SL'' f (CongruenceSubgroup.mem_Gamma_one γ) z
  rw [this]
  simp [UpperHalfPlane.denom, mul_comm]

/-- The automorphy factor $cz + d$ never vanishes on the upper half-plane. -/
lemma denom_ne_zero' (γ : SL(2, ℤ)) (z : ℍ) : ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  simpa [UpperHalfPlane.denom, mul_comm] using this

/-- Mathlib's discriminant transforms with weight $12$. -/
lemma disc_smul (γ : SL(2, ℤ)) (z : ℍ) :
    ModularForm.discriminant (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 12 * ModularForm.discriminant z :=
  levelOne_smul (CuspForm.discriminant) γ z

/-- $j(\gamma z) = j(z)$ for $\gamma \in \mathrm{SL}_2(\mathbb Z)$: $j(z)$ depends only on the lattice
$\mathbb Zz + \mathbb Z$ (pdf p. 191). -/
@[kb "milne2006ec" "Ch. V, §2, j is invariant under SL₂(ℤ) (running text), pdf p. 191"]
theorem jFun_smul (γ : SL(2, ℤ)) (z : ℍ) : jFun (γ • z) = jFun z := by
  rw [jFun_eq, jFun_eq, levelOne_smul E₄ γ z, disc_smul]
  have h := denom_ne_zero' γ z
  have := ModularForm.discriminant_ne_zero z
  field_simp

/-- $j$ is holomorphic on $\mathbb H$ ($\Delta$ has no zeros on $\mathbb H$). -/
theorem jFun_mdifferentiable : MDiff jFun := by
  have h : jFun = fun z => E₄ z ^ 3 / ModularForm.discriminant z := funext jFun_eq
  rw [h]
  rw [show (⇑E₄ : ℍ → ℂ) = E₄ from rfl]
  exact (E₄.holo'.pow 3).div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero

/-- $E_6(i) = 0$, from the invariance under $S$ ($S i = i$, odd power of $i^2 = -1$). -/
lemma E6_I : E₆ UpperHalfPlane.I = 0 := by
  have h := levelOne_smul E₆ ModularGroup.S UpperHalfPlane.I
  have hS : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [UpperHalfPlane.modular_S_smul]; ext; simp
  rw [hS] at h
  simp [ModularGroup.S] at h
  linear_combination h / 2

/-- $E_4(i) \ne 0$ (as $\Delta(i) \ne 0$ and $E_6(i) = 0$). -/
lemma E4_I_ne : E₄ UpperHalfPlane.I ≠ 0 := by
  intro h
  have h1 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq UpperHalfPlane.I
  rw [h, E6_I] at h1
  exact ModularForm.discriminant_ne_zero _ (by simpa using h1)

/-- $j(i) = 1728$ (pdf p. 191). -/
@[kb "milne2006ec" "Ch. V, §2, j(i) = 1728 (running text), pdf p. 191"]
theorem jFun_I : jFun UpperHalfPlane.I = 1728 := by
  rw [jFun_eq, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, E6_I]
  have := E4_I_ne
  field_simp
  norm_num

/-- $(\rho + 1)^4 \ne 1$ for the primitive cube root of unity $\rho$. -/
lemma rho_aux : ((ρ : ℂ) + 1) ^ 4 ≠ 1 := by
  intro h
  have hs := UpperHalfPlane.ρ_sq
  have h2 : (ρ : ℂ) = -2 := by
    linear_combination (-1 : ℂ) * h + ((ρ : ℂ) ^ 2 + 3 * ρ + 2) * hs
  have := congrArg Complex.im h2
  have hp := ρ.im_pos
  simp at this
  linarith

/-- $E_4(\rho) = 0$, from the element $ST$ fixing $\rho$ with $c\rho + d = \rho + 1$. -/
lemma E4_rho : E₄ ρ = 0 := by
  have hfix : (ModularGroup.S * ModularGroup.T) • ρ = ρ :=
    ModularGroup.stabilizer_ρ.mpr (by simp)
  have h := levelOne_smul E₄ (ModularGroup.S * ModularGroup.T) ρ
  rw [hfix] at h
  have hd : (((ModularGroup.S * ModularGroup.T) 1 0 : ℤ) : ℂ) * ρ +
      ((ModularGroup.S * ModularGroup.T) 1 1 : ℤ) = ρ + 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [ModularGroup.S, ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hd] at h
  have : (((ρ : ℂ) + 1) ^ 4 - 1) * E₄ ρ = 0 := by
    simp only [zpow_ofNat] at h
    linear_combination -h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) rho_aux
  · exact h1

/-- $j(\rho) = 0$ (pdf p. 191), for Mathlib's $\rho = e^{2\pi i/3}$. -/
@[kb "milne2006ec" "Ch. V, §2, j(ρ) = 0 (running text), pdf p. 191"]
theorem jFun_rho : jFun ρ = 0 := by
  rw [jFun_eq, E4_rho]; simp

/-- $j(\rho) = 0$ for Milne's $\rho = e^{2\pi i/6} = 1 + e^{2\pi i/3}$ (Proposition 1.3). -/
@[kb "milne2006ec" "Ch. V, §2, j(ρ) = 0 (running text), pdf p. 191"]
theorem jFun_rho' : jFun ((1 : ℝ) +ᵥ ρ) = 0 := by
  rw [← UpperHalfPlane.modular_T_smul, jFun_smul, jFun_rho]

/-- The constant term of $E_4$ at the cusp is $1$. -/
lemma cuspFunction_E4_zero : cuspFunction 1 (E₄ : ℍ → ℂ) 0 = 1 := by
  have := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by norm_num)
  simpa [qExpansion_coeff] using this

/-- $q$-parameter with period $1$ is $e^{2\pi iz}$. -/
lemma qParam_one_eq (z : ℍ) : Function.Periodic.qParam 1 (z : ℂ) = cexp (2 * π * I * z) := by
  simp [Function.Periodic.qParam]

/-- $j$ has a simple pole with residue $1$ at $\infty$: $j - q^{-1}$ is bounded as $\Im z \to \infty$
(the start of equation (37); "the factor $1728$ was included so that it has residue $1$", pdf p. 191). -/
@[kb "milne2006ec" "Ch. V, §2, j has a simple pole with residue 1 at ∞ (running text), pdf p. 191"]
theorem jFun_sub_inv_q_isBoundedAtImInfty :
    IsBoundedAtImInfty fun z : ℍ ↦ jFun z - 1 / cexp (2 * π * I * z) := by
  set A := cuspFunction 1 (E₄ : ℍ → ℂ) with hAdef
  set P : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 with hPdef
  have hA : AnalyticAt ℂ A 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL
  have hP : DifferentiableAt ℂ P 0 :=
    (differentiableOn_tprod_one_sub_pow_pow 24).differentiableAt (Metric.ball_mem_nhds _ one_pos)
  have hF : DifferentiableAt ℂ (fun q => A q ^ 3 - P q) 0 := (hA.differentiableAt.pow 3).sub hP
  have hF0 : A 0 ^ 3 - P 0 = 0 := by
    simp [hPdef, A, cuspFunction_E4_zero]
  have hbig := hF.hasDerivAt.isBigO_sub
  simp only [hF0, sub_zero] at hbig
  have hcomp := hbig.comp_tendsto (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos)
  have hq : ∀ z : ℍ, Function.Periodic.qParam 1 (z : ℂ) ≠ 0 := fun z => by
    simp [Function.Periodic.qParam]
  have hEq : ∀ z : ℍ, A (Function.Periodic.qParam 1 (z : ℂ)) ^ 3 -
      P (Function.Periodic.qParam 1 (z : ℂ))
      = E₄ z ^ 3 - ModularForm.discriminant z / cexp (2 * π * I * z) := by
    intro z
    have h1 : A (Function.Periodic.qParam 1 (z : ℂ)) = E₄ z :=
      SlashInvariantFormClass.eq_cuspFunction E₄ z one_mem_strictPeriods_SL one_ne_zero
    have h2 := ModularForm.discriminant_eq_q_prod z
    rw [h1, ← qParam_one_eq]
    have hq' := hq z
    rw [h2]
    simp only [hPdef]
    field_simp
  have hG : (fun z : ℍ => E₄ z ^ 3 - ModularForm.discriminant z / cexp (2 * π * I * z))
      =O[atImInfty] fun z : ℍ => Function.Periodic.qParam 1 (z : ℂ) := by
    refine (Asymptotics.isBigO_congr ?_ ?_).mp hcomp
    · exact Filter.Eventually.of_forall hEq
    · exact Filter.Eventually.of_forall fun z => by simp
  have hqΔ : (fun z : ℍ => Function.Periodic.qParam 1 (z : ℂ)) =O[atImInfty]
      ModularForm.discriminant := by
    refine Asymptotics.isBigO_norm_left.mp ?_
    refine (Asymptotics.isBigO_congr ?_ ?_).mp ModularForm.exp_isBigO_discriminant
    · exact Filter.Eventually.of_forall fun z => by
        simp [Function.Periodic.qParam, Complex.norm_exp, mul_comm]
    · exact Filter.Eventually.of_forall fun z => rfl
  obtain ⟨c, hc⟩ := (hG.trans hqΔ).bound
  refine Asymptotics.IsBigO.of_bound c ?_
  filter_upwards [hc] with z hz
  have hΔ := ModularForm.discriminant_ne_zero z
  have hq' : cexp (2 * π * I * z) ≠ 0 := Complex.exp_ne_zero _
  have : jFun z - 1 / cexp (2 * π * I * z) =
      (E₄ z ^ 3 - ModularForm.discriminant z / cexp (2 * π * I * z)) /
        ModularForm.discriminant z := by
    rw [jFun_eq]; field_simp
  rw [this, norm_div, Pi.one_apply, norm_one, mul_one, div_le_iff₀ (norm_pos_iff.mpr hΔ)]
  exact hz

/-- Equation (37) (pdf p. 191, from Serre 1973, VII): $j = q^{-1} + 744 + 196884q + 21493760q^2 +
\sum_{n\ge3}c(n)q^n$ with $c(n) \in \mathbb Z$. A named statement. -/
@[kb "milne2006ec" "Ch. V, §2, equation (37), pdf p. 191"]
structure Eq37 : Prop where
  expansion : ∃ c : ℕ → ℤ, c 0 = 744 ∧ c 1 = 196884 ∧ c 2 = 21493760 ∧
    ∀ z : ℍ, HasSum (fun n ↦ (c n : ℂ) * cexp (2 * π * I * z) ^ n) (jFun z - 1 / cexp (2 * π * I * z))

/-- The hypotheses of Propositions 2.1 and 2.2 on a function $f$ on $X_0(1)$, read on $\mathbb H$: holomorphic on
$\mathbb H$, invariant under $\mathrm{SL}_2(\mathbb Z)$, with a simple pole at the cusp $\infty$ (for some
$a \ne 0$, $f - a/q$ is bounded at $\infty$). -/
def IsHolomorphicWithSimplePoleAtCusp (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ (∀ γ : SL(2, ℤ), ∀ z, f (γ • z) = f z) ∧
    ∃ a : ℂ, a ≠ 0 ∧ IsBoundedAtImInfty fun z : ℍ ↦ f z - a / cexp (2 * π * I * z)

/-! ### Helper lemmas: building level-one forms, and the polynomial structure of invariant functions -/

/-- A function with the level-one transformation law is slash-invariant. -/
lemma slash_eq_of_transform {k : ℤ} {f : ℍ → ℂ}
    (h : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * f z)
    (γ : SL(2, ℤ)) : f ∣[k] γ = f := by
  funext z
  rw [SL_slash_apply, h γ z]
  have hd := denom_ne_zero' γ z
  have : UpperHalfPlane.denom γ z = (γ 1 0 : ℂ) * z + γ 1 1 := by
    simp [UpperHalfPlane.denom, mul_comm]
  rw [this, zpow_neg]
  field_simp

/-- Build a level-one modular form from a holomorphic function with the transformation law that is
bounded at infinity. -/
noncomputable def mkLevelOne (k : ℤ) (f : ℍ → ℂ) (hf : MDiff f)
    (h : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * f z)
    (hb : IsBoundedAtImInfty f) : ModularForm 𝒮ℒ k where
  toFun := f
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ slash_eq_of_transform h γ
  holo' := hf
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_eq_of_transform h γ]
    exact hb

/-- Build a level-one cusp form from a holomorphic function with the transformation law that tends to
zero at infinity. -/
noncomputable def mkLevelOneCusp (k : ℤ) (f : ℍ → ℂ) (hf : MDiff f)
    (h : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * f z)
    (hb : IsZeroAtImInfty f) : CuspForm 𝒮ℒ k where
  toFun := f
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ slash_eq_of_transform h γ
  holo' := hf
  zero_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_eq_of_transform h γ]
    exact hb

/-- The transformation law of weight `k` under `SL(2, ℤ)`, with a natural-number weight. -/
def Law (k : ℕ) (f : ℍ → ℂ) : Prop :=
  ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * f z

/-- The transformation law of weight $k$ is multiplicative: weights add under products. -/
lemma Law.mul {k l : ℕ} {f g : ℍ → ℂ} (hf : Law k f) (hg : Law l g) : Law (k + l) (f * g) := by
  intro γ z
  simp only [Pi.mul_apply, hf γ z, hg γ z, pow_add]
  ring

/-- If $f$ obeys the law of weight $k$ then $f^m$ obeys the law of weight $km$. -/
lemma Law.pow {k : ℕ} {f : ℍ → ℂ} (hf : Law k f) (m : ℕ) : Law (k * m) (f ^ m) := by
  intro γ z
  simp only [Pi.pow_apply, hf γ z, mul_pow, pow_mul]

/-- The law of weight $k$ is preserved under differences. -/
lemma Law.sub {k : ℕ} {f g : ℍ → ℂ} (hf : Law k f) (hg : Law k g) : Law k (f - g) := by
  intro γ z
  simp only [Pi.sub_apply, hf γ z, hg γ z]
  ring

/-- The law of weight $k$ is preserved under multiplication by a constant. -/
lemma Law.const_mul {k : ℕ} {f : ℍ → ℂ} (hf : Law k f) (c : ℂ) : Law k (fun z => c * f z) := by
  intro γ z
  simp only [hf γ z]
  ring

/-- The law of weight $k$ stated with the integer weight $k$ in the automorphy factor. -/
lemma Law.toInt {k : ℕ} {f : ℍ → ℂ} (h : Law k f) (γ : SL(2, ℤ)) (z : ℍ) :
    f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (k : ℤ) * f z := by
  simpa using h γ z

/-- The Eisenstein series $E_4$ obeys the law of weight $4$. -/
lemma law_E4 : Law 4 E₄ := fun γ z => by simpa using levelOne_smul E₄ γ z

/-- The discriminant form $\Delta$ obeys the law of weight $12$. -/
lemma law_disc : Law 12 ModularForm.discriminant := fun γ z => by
  simpa using disc_smul γ z

/-- A function invariant under $\mathrm{SL}_2(\mathbb Z)$ obeys the law of weight $0$. -/
lemma law_zero_of_invariant {f : ℍ → ℂ} (h : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = f z) : Law 0 f :=
  fun γ z => by rw [h γ z]; simp

/-- $j \Delta = E_4^3$. -/
lemma jFun_mul_disc (z : ℍ) : jFun z * Δ z = E₄ z ^ 3 := by
  rw [jFun_eq]; field_simp [ModularForm.discriminant_ne_zero z]

/-- $E_4^m$ tends to $1$ as $\operatorname{Im} z \to \infty$. -/
lemma tendsto_E4_pow (m : ℕ) : Tendsto (fun z : ℍ => E₄ z ^ m) atImInfty (𝓝 1) := by
  simpa using (EisensteinSeries.tendsto_E_atImInfty (k := 4)).pow m

/-- A function with a limit at $i\infty$ is bounded at $i\infty$. -/
lemma isBoundedAtImInfty_of_tendsto {f : ℍ → ℂ} {c : ℂ} (h : Tendsto f atImInfty (𝓝 c)) :
    IsBoundedAtImInfty f := h.isBigO_one ℝ

/-- Key lemma: a holomorphic invariant function `f` with `f Δⁿ` bounded at infinity is a polynomial of
degree at most `n` in `j`. -/
theorem key_poly (n : ℕ) : ∀ f : ℍ → ℂ, MDiff f → Law 0 f →
    IsBoundedAtImInfty (fun z => f z * Δ z ^ n) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, f z = P.eval (jFun z) := by
  induction n with
  | zero =>
    intro f hf hl hb
    simp only [pow_zero, mul_one] at hb
    obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero
      (mkLevelOne 0 f hf (fun γ z => by simpa using hl γ z) hb)
    refine ⟨Polynomial.C c, by simp, fun z => ?_⟩
    have := congrFun hc z
    rw [Polynomial.eval_C]
    exact this
  | succ n ih =>
    intro f hf hl hb
    have hFlaw : Law (12 * (n + 1)) (fun z => f z * Δ z ^ (n + 1)) := by
      have := (hl.mul (law_disc.pow (n + 1)))
      rw [zero_add] at this
      exact this
    have hFmd : MDiff (fun z => f z * Δ z ^ (n + 1)) :=
      hf.mul (CuspForm.discriminant.holo'.pow (n + 1))
    let Fm : ModularForm 𝒮ℒ ((12 * (n + 1) : ℕ) : ℤ) :=
      mkLevelOne _ _ hFmd (hFlaw.toInt) hb
    set c : ℂ := (qExpansion 1 Fm).coeff 0 with hcdef
    have hFlim : Tendsto (fun z : ℍ => f z * Δ z ^ (n + 1)) atImInfty (𝓝 c) :=
      ModularFormClass.tendsto_atImInfty Fm one_pos one_mem_strictPeriods_SL
    have hEmd : MDiff (fun z : ℍ => E₄ z ^ (3 * (n + 1))) := E₄.holo'.pow _
    have hElaw : Law (12 * (n + 1)) (fun z : ℍ => E₄ z ^ (3 * (n + 1))) := by
      have := law_E4.pow (3 * (n + 1))
      rw [show 4 * (3 * (n + 1)) = 12 * (n + 1) by ring] at this
      exact this
    have hGlim : Tendsto (fun z : ℍ => f z * Δ z ^ (n + 1) - c * E₄ z ^ (3 * (n + 1)))
        atImInfty (𝓝 0) := by
      have := hFlim.sub ((tendsto_E4_pow (3 * (n + 1))).const_mul c)
      simpa using this
    have hGmd : MDiff (fun z : ℍ => f z * Δ z ^ (n + 1) - c * E₄ z ^ (3 * (n + 1))) :=
      hFmd.sub (hEmd.const_smul c)
    have hGlaw : Law (12 * (n + 1))
        (fun z : ℍ => f z * Δ z ^ (n + 1) - c * E₄ z ^ (3 * (n + 1))) :=
      hFlaw.sub (hElaw.const_mul c)
    let Cusp : CuspForm 𝒮ℒ ((12 * (n + 1) : ℕ) : ℤ) :=
      mkLevelOneCusp _ _ hGmd hGlaw.toInt hGlim
    let Q := CuspForm.discriminantEquiv Cusp
    have hQ : ∀ z, Q z = (f z * Δ z ^ (n + 1) - c * E₄ z ^ (3 * (n + 1))) / Δ z := fun z => rfl
    have hQb : IsBoundedAtImInfty (Q : ℍ → ℂ) := ModularFormClass.bdd_at_infty Q
    have hgb : IsBoundedAtImInfty
        (fun z => (f z - c * jFun z ^ (n + 1)) * Δ z ^ n) := by
      refine (Asymptotics.isBigO_congr ?_ (Eventually.of_forall fun _ => rfl)).mp hQb
      refine Eventually.of_forall fun z => ?_
      have hΔ := ModularForm.discriminant_ne_zero z
      have hj := jFun_mul_disc z
      have hE : E₄ z ^ (3 * (n + 1)) = (jFun z * Δ z) ^ (n + 1) := by rw [hj, ← pow_mul]
      rw [hQ z, hE, div_eq_iff hΔ]
      ring
    obtain ⟨P', hP'deg, hP'⟩ := ih (fun z => f z - c * jFun z ^ (n + 1))
      (hf.sub ((jFun_mdifferentiable.pow (n + 1)).const_smul c))
      (fun γ z => by beta_reduce; rw [hl γ z, jFun_smul]; ring) hgb
    refine ⟨P' + Polynomial.C c * Polynomial.X ^ (n + 1), ?_, fun z => ?_⟩
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le (hP'deg.trans (Nat.le_succ n)) ?_)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · have := hP' z
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      linear_combination this

/-- $\Delta / q \to 1$ as $\Im z \to \infty$. -/
lemma disc_div_q_tendsto :
    Tendsto (fun z : ℍ => Δ z / cexp (2 * π * I * z)) atImInfty (𝓝 1) := by
  refine ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z => ?_
  rw [ModularForm.discriminant_eq_q_prod z, qParam_one_eq]
  have : cexp (2 * π * I * z) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- If $f - a/q$ is bounded at infinity then $f\Delta$ is bounded at infinity. -/
lemma isBounded_mul_disc_of_simple_pole {f : ℍ → ℂ} {a : ℂ}
    (hb : IsBoundedAtImInfty fun z : ℍ ↦ f z - a / cexp (2 * π * I * z)) :
    IsBoundedAtImInfty fun z => f z * Δ z ^ 1 := by
  have h1 : IsBoundedAtImInfty fun z : ℍ => (f z - a / cexp (2 * π * I * z)) * Δ z :=
    BoundedAtFilter.mul hb (ModularForm.discriminant_isZeroAtImInfty.boundedAtFilter)
  have h2 : IsBoundedAtImInfty fun z : ℍ => a * (Δ z / cexp (2 * π * I * z)) :=
    isBoundedAtImInfty_of_tendsto (disc_div_q_tendsto.const_mul a)
  have := BoundedAtFilter.add h1 h2
  refine (Asymptotics.isBigO_congr (Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun _ => rfl)).mp this
  have : cexp (2 * π * I * z) ≠ 0 := Complex.exp_ne_zero _
  simp only [Pi.add_apply, pow_one]
  field_simp
  ring

/-- **Proposition 2.2** (pdf p. 191), existence: $j$ is holomorphic on $X_0(1)$ except for a simple pole at
$\infty$, with $j(i) = 1728$ and $j(\rho) = 0$. -/
@[kb "milne2006ec" "Ch. V, Proposition 2.2, pdf p. 191"]
theorem prop_2_2_exists :
    IsHolomorphicWithSimplePoleAtCusp jFun ∧ jFun UpperHalfPlane.I = 1728 ∧ jFun ρ = 0 :=
  ⟨⟨jFun_mdifferentiable, jFun_smul, 1, one_ne_zero, jFun_sub_inv_q_isBoundedAtImInfty⟩,
    jFun_I, jFun_rho⟩

/-- **Proposition 2.2** (pdf p. 191), uniqueness: $j$ is the only function on $X_0(1)$ holomorphic except for a
simple pole at $\infty$ with $j(i) = 1728$, $j(\rho) = 0$. -/
@[kb "milne2006ec" "Ch. V, Proposition 2.2, pdf p. 191"]
theorem prop_2_2_unique (f : ℍ → ℂ) (hf : IsHolomorphicWithSimplePoleAtCusp f)
    (hi : f UpperHalfPlane.I = 1728) (hρ : f ρ = 0) : f = jFun := by
  obtain ⟨hmd, hinv, a, -, hbd⟩ := hf
  obtain ⟨P, hdeg, hP⟩ := key_poly 1 f hmd (law_zero_of_invariant hinv)
    (isBounded_mul_disc_of_simple_pole hbd)
  have hPeq := Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
  have hform : ∀ z, f z = P.coeff 1 * jFun z + P.coeff 0 := fun z => by
    rw [hP z]; conv_lhs => rw [hPeq]
    simp
  have h1 := hform UpperHalfPlane.I
  have h2 := hform ρ
  rw [hi, jFun_I] at h1
  rw [hρ, jFun_rho] at h2
  have hc0 : P.coeff 0 = 0 := by linear_combination -h2
  have hc1 : P.coeff 1 = 1 := by rw [hc0] at h1; linear_combination -h1 / 1728
  funext z
  rw [hform z, hc0, hc1]; ring

/-- **Proposition 2.1** (pdf p. 190): there is a unique function $J$ on $X_0(1)$, holomorphic except for a simple
pole at $\infty$, with $J(i) = 1$ and $J(\rho) = 0$; it is $J = j/1728$. -/
@[kb "milne2006ec" "Ch. V, Proposition 2.1, pdf p. 190"]
theorem prop_2_1 :
    (IsHolomorphicWithSimplePoleAtCusp (fun z ↦ jFun z / 1728) ∧ jFun UpperHalfPlane.I / 1728 = 1 ∧
      jFun ρ / 1728 = 0) ∧
    ∀ f : ℍ → ℂ, IsHolomorphicWithSimplePoleAtCusp f → f UpperHalfPlane.I = 1 → f ρ = 0 →
      f = fun z ↦ jFun z / 1728 := by
  have hi := jFun_I
  have hρ := jFun_rho
  refine ⟨⟨⟨?_, fun γ z => by simp only [jFun_smul], 1 / 1728, by norm_num, ?_⟩,
    by rw [hi]; norm_num, by rw [hρ]; simp⟩, ?_⟩
  · have : (fun z ↦ jFun z / 1728) = (1 / 1728 : ℂ) • jFun := by
      funext z; simp [div_eq_inv_mul]
    rw [this]
    exact jFun_mdifferentiable.const_smul _
  · have := (jFun_sub_inv_q_isBoundedAtImInfty.const_mul_left (1 / 1728 : ℂ))
    refine (Asymptotics.isBigO_congr (Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun _ => rfl)).mp this
    ring
  · intro f hf hfi hfρ
    have h := prop_2_2_unique (fun z => 1728 * f z)
      ⟨hf.1.const_smul (1728 : ℂ), fun γ z => by beta_reduce; rw [hf.2.1 γ z], by
        obtain ⟨a, ha, hb⟩ := hf.2.2
        refine ⟨1728 * a, mul_ne_zero (by norm_num) ha, ?_⟩
        have := hb.const_mul_left (1728 : ℂ)
        refine (Asymptotics.isBigO_congr (Eventually.of_forall fun z => ?_)
          (Eventually.of_forall fun _ => rfl)).mp this
        ring⟩
      (by rw [hfi]; norm_num) (by rw [hfρ]; simp)
    funext z
    have := congrFun h z
    rw [eq_div_iff (by norm_num)]
    beta_reduce at this
    linear_combination this

/-- $j$ takes every complex value (part of "$j$ defines an isomorphism from $X_0(1)$ onto the Riemann sphere",
Proposition 2.2). -/
@[kb "milne2006ec" "Ch. V, Proposition 2.2 (j is onto), pdf p. 191"]
theorem jFun_surjective : Function.Surjective jFun := by
  intro c
  by_contra hne
  push Not at hne
  set Q : ℍ → ℂ := fun z => E₄ z ^ 3 - c * Δ z with hQdef
  have hQne : ∀ z, Q z ≠ 0 := by
    intro z hz
    apply hne z
    rw [jFun_eq, div_eq_iff (ModularForm.discriminant_ne_zero z)]
    simp only [hQdef] at hz
    linear_combination hz
  have hQmd : MDiff Q := (E₄.holo'.pow 3).sub (CuspForm.discriminant.holo'.const_smul c)
  have hQlaw : Law 12 Q := (law_E4.pow 3).sub (law_disc.const_mul c)
  have hΔ0 : Tendsto (fun z : ℍ => Δ z) atImInfty (𝓝 0) :=
    ModularForm.discriminant_isZeroAtImInfty
  have hQlim : Tendsto Q atImInfty (𝓝 1) := by
    have := (tendsto_E4_pow 3).sub (hΔ0.const_mul c)
    simpa using this
  have hlim : Tendsto (fun z : ℍ => Δ z / Q z) atImInfty (𝓝 0) := by
    have := hΔ0.div hQlim one_ne_zero
    rw [zero_div] at this
    exact this
  have hmd : MDiff (fun z : ℍ => Δ z / Q z) :=
    CuspForm.discriminant.holo'.div hQmd hQne
  have hl : Law 0 (fun z : ℍ => Δ z / Q z) := by
    intro γ z
    beta_reduce
    rw [disc_smul, hQlaw γ z]
    have := denom_ne_zero' γ z
    have := hQne z
    field_simp
  obtain ⟨c0, hc0⟩ := ModularForm.eq_const_of_weight_zero
    (mkLevelOne 0 _ hmd (fun γ z => by simpa using hl γ z) (isBoundedAtImInfty_of_tendsto hlim))
  have hconst : ∀ z, Δ z / Q z = c0 := fun z => congrFun hc0 z
  have hlim' : Tendsto (fun z : ℍ => Δ z / Q z) atImInfty (𝓝 c0) := by
    simp only [hconst]
    exact tendsto_const_nhds
  have : c0 = 0 := tendsto_nhds_unique hlim' hlim
  have h0 := hconst UpperHalfPlane.I
  rw [this] at h0
  exact div_ne_zero (ModularForm.discriminant_ne_zero _) (hQne _) h0

/-- The other half of "$j$ defines an isomorphism from $X_0(1)$ onto the Riemann sphere" (Proposition 2.2):
$j(z) = j(w)$ only if $z$, $w$ are in the same $\mathrm{SL}_2(\mathbb Z)$-orbit. A named statement (Milne deduces it
from the genus-zero isomorphism $X_0(1) \cong S$ of §1; Serre 1973, VII, Proposition 5, by the valence formula). -/
@[kb "milne2006ec" "Ch. V, Proposition 2.2 (j is injective on SL₂(ℤ)∖ℍ), pdf p. 191"]
structure JInjective : Prop where
  orbit : ∀ z w : ℍ, jFun z = jFun w → ∃ γ : SL(2, ℤ), γ • z = w

/-- A function meromorphic at the cusp $\infty$ times a high enough power of $\Delta$ is bounded
at $\infty$ ($f = O(q^{-m/h})$ while $\Delta^n = O(q^n)$). -/
lemma exists_pow_disc_bounded {f : ℍ → ℂ} (hmer : IsMeromorphicAtImInfty f) :
    ∃ n : ℕ, IsBoundedAtImInfty (fun z => f z * Δ z ^ n) := by
  obtain ⟨h, hh, hper, m, hm⟩ := hmer
  set F := cuspFunction h f with hF
  set G : ℂ → ℂ := fun z => (z - 0) ^ m • F z with hG
  have hGc : ContinuousAt G 0 := hm.continuousAt
  have hev : ∀ᶠ q in 𝓝 (0 : ℂ), ‖G q‖ < ‖G 0‖ + 1 :=
    Filter.Tendsto.eventually_lt_const (lt_add_one ‖G 0‖) hGc.tendsto.norm
  have hevz : ∀ᶠ z : ℍ in atImInfty, ‖G (Function.Periodic.qParam h (z : ℂ))‖ < ‖G 0‖ + 1 :=
    (UpperHalfPlane.qParam_tendsto_atImInfty (h := h) hh).eventually hev
  obtain ⟨K, hK⟩ := (CuspFormClass.exp_decay_atImInfty CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL).bound
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  refine ⟨⌈(m : ℝ) / h⌉₊, Asymptotics.IsBigO.of_bound ((‖G 0‖ + 1) * K' ^ ⌈(m : ℝ) / h⌉₊) ?_⟩
  filter_upwards [hevz, hK] with z hz hKz
  have hy : 0 < z.im := z.im_pos
  have hpi := Real.pi_pos
  have hqn : ‖Function.Periodic.qParam h (z : ℂ)‖ = Real.exp (-2 * π * z.im / h) := by
    simp [Function.Periodic.norm_qParam]
  have hfq : F (Function.Periodic.qParam h (z : ℂ)) = f z :=
    UpperHalfPlane.eq_cuspFunction z hh.ne' hper
  have hGz : ‖Function.Periodic.qParam h (z : ℂ)‖ ^ m * ‖f z‖ < ‖G 0‖ + 1 := by
    have : G (Function.Periodic.qParam h (z : ℂ)) =
        Function.Periodic.qParam h (z : ℂ) ^ m * f z := by
      simp only [hG, sub_zero, smul_eq_mul, hfq]
    rw [this, norm_mul, norm_pow] at hz
    exact hz
  have hΔz : ‖Δ z‖ ≤ K' * Real.exp (-2 * π * z.im / 1) := by
    have := hKz
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  set n := ⌈(m : ℝ) / h⌉₊ with hn
  have hmn : (m : ℝ) / h ≤ n := Nat.le_ceil _
  have hpow : ‖Δ z‖ ^ n ≤ K' ^ n * ‖Function.Periodic.qParam h (z : ℂ)‖ ^ m := by
    calc ‖Δ z‖ ^ n ≤ (K' * Real.exp (-2 * π * z.im / 1)) ^ n :=
          pow_le_pow_left₀ (norm_nonneg _) hΔz n
      _ = K' ^ n * Real.exp (n * (-2 * π * z.im / 1)) := by
          rw [mul_pow, ← Real.exp_nat_mul]
      _ ≤ K' ^ n * Real.exp (m * (-2 * π * z.im / h)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg hK'0 _)
          have h1 : (m : ℝ) * (-2 * π * z.im / h) = (-2 * π * z.im) * ((m : ℝ) / h) := by ring
          rw [h1]
          have h2 : 0 ≤ 2 * π * z.im := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hmn h2]
      _ = K' ^ n * ‖Function.Periodic.qParam h (z : ℂ)‖ ^ m := by
          rw [hqn, ← Real.exp_nat_mul]
  rw [norm_mul, norm_pow, Pi.one_apply, norm_one, mul_one]
  calc ‖f z‖ * ‖Δ z‖ ^ n ≤ ‖f z‖ * (K' ^ n * ‖Function.Periodic.qParam h (z : ℂ)‖ ^ m) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = K' ^ n * (‖Function.Periodic.qParam h (z : ℂ)‖ ^ m * ‖f z‖) := by ring
    _ ≤ K' ^ n * (‖G 0‖ + 1) := mul_le_mul_of_nonneg_left hGz.le (pow_nonneg hK'0 _)
    _ = (‖G 0‖ + 1) * K' ^ n := by ring

/-- A holomorphic $\mathrm{SL}_2(\mathbb Z)$-invariant function on $\mathbb H$ that is meromorphic at $\infty$ is a
polynomial in $j$ (the holomorphic case of the last sentence of Proposition 2.2). -/
theorem holomorphic_modularFunction_eq_polynomial_jFun (f : ℍ → ℂ) (hf : MDiff f)
    (hmod : IsModularFunction ⊤ f) : ∃ P : Polynomial ℂ, f = fun z ↦ P.eval (jFun z) := by
  have hmer : IsMeromorphicAtImInfty f := by
    simpa using hmod.meromorphic_cusps 1
  obtain ⟨n, hn⟩ := exists_pow_disc_bounded hmer
  obtain ⟨P, -, hP⟩ := key_poly n f hf
    (law_zero_of_invariant fun γ z => hmod.invariant γ (Subgroup.mem_top γ) z) hn
  exact ⟨P, funext hP⟩

/-- A holomorphic function on $\mathbb H$ is meromorphic on $\mathbb H$. -/
lemma isMeromorphicOnUpperHalfPlane_of_mdiff {f : ℍ → ℂ} (hf : MDiff f) :
    IsMeromorphicOnUpperHalfPlane f :=
  ((UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd
    isOpen_upperHalfPlaneSet).meromorphicOn

/-- For $0 < |q| < 1$, the cusp functions (period $1$) of all functions on $\mathbb H$ are evaluations at
one common point $z$ with $e^{2\pi iz} = q$. -/
lemma exists_point_cuspFunction {q : ℂ} (hq0 : q ≠ 0) (hqb : ‖q‖ < 1) :
    ∃ z : ℍ, ∀ f : ℍ → ℂ, cuspFunction 1 f q = f z := by
  have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hqb hq0
  refine ⟨⟨_, him⟩, fun f => ?_⟩
  simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq0,
    ofComplex_apply_of_im_pos him]

/-- $j$ has period $1$. -/
lemma jFun_periodic : Function.Periodic (jFun ∘ ofComplex) 1 :=
  UpperHalfPlane.periodic_comp_ofComplex fun τ => by
    rw [← UpperHalfPlane.modular_T_smul, jFun_smul]

/-- $j$ is meromorphic at the cusp $\infty$ (a quotient of the analytic cusp functions of $E_4^3$ and
$\Delta$). -/
lemma isMeromorphicAtImInfty_jFun : IsMeromorphicAtImInfty jFun := by
  refine ⟨1, one_pos, by simpa using jFun_periodic, ?_⟩
  have hA : AnalyticAt ℂ (cuspFunction 1 (E₄ : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL
  have hD : AnalyticAt ℂ (cuspFunction 1 (Δ : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL
  have hm : MeromorphicAt
      (fun q => cuspFunction 1 (E₄ : ℍ → ℂ) q ^ 3 / cuspFunction 1 (Δ : ℍ → ℂ) q) 0 :=
    (hA.pow 3).meromorphicAt.div hD.meromorphicAt
  refine hm.congr ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
    with q hq0 hqb
  obtain ⟨z, hz⟩ := exists_point_cuspFunction hq0 (by simpa using hqb)
  rw [hz jFun, hz E₄, hz Δ, jFun_eq]

/-- $j$ is a modular function for $\mathrm{SL}_2(\mathbb Z)$. -/
theorem isModularFunction_jFun : IsModularFunction ⊤ jFun where
  meromorphic := isMeromorphicOnUpperHalfPlane_of_mdiff jFun_mdifferentiable
  invariant := fun γ _ z => jFun_smul γ z
  meromorphic_cusps := fun γ => by
    have : (fun z => jFun (γ • z)) = jFun := funext (jFun_smul γ)
    rw [this]
    exact isMeromorphicAtImInfty_jFun

/-- Last sentence of **Proposition 2.2** (pdf p. 191; Milne writes $X_0(N)$ for $X_0(1)$, an erratum): the field
of meromorphic functions on $X_0(1)$ is $\mathbb C(j)$: every modular function for $\mathrm{SL}_2(\mathbb Z)$ is,
away from a discrete set, a rational function of $j$. A named statement (Milne deduces it from
$X_0(1) \cong S$). -/
@[kb "milne2006ec" "Ch. V, Proposition 2.2 (meromorphic functions on X₀(1) are ℂ(j)), pdf p. 191"]
structure Prop2_2Rational : Prop where
  rational : ∀ f : ℍ → ℂ, IsModularFunction ⊤ f → ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
    f =ᶠ[codiscrete ℍ] fun z ↦ P.eval (jFun z) / Q.eval (jFun z)

/-- The matrix $\begin{pmatrix}a & Nb\\ c/N & d\end{pmatrix}$ of $\mathrm{SL}_2(\mathbb Z)$ attached to
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(N)$, where $c = Nc'$. -/
def conjGamma0 {N : ℕ} (γ : SL(2, ℤ)) (c' : ℤ) (hc : γ 1 0 = N * c') : SL(2, ℤ) :=
  ⟨!![γ 0 0, (N : ℤ) * γ 0 1; c', γ 1 1], by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this ⊢
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hc] at this
    linear_combination this⟩

/-- An element of $\Gamma_0(N)$ has lower left entry divisible by $N$. -/
lemma mem_gamma0_dvd {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ c' : ℤ, γ 1 0 = N * c' := by
  have := (CongruenceSubgroup.Gamma0_mem.mp hγ)
  exact ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp this)

/-- $j_N(\gamma z) = j_N(z)$ for $\gamma \in \Gamma_0(N)$ (pdf pp. 191–192), $N \ge 1$. -/
@[kb "milne2006ec" "Ch. V, §2, j_N is invariant under Γ₀(N) (running text), pdf p. 191"]
theorem jN_smul {N : ℕ} (hN : 1 ≤ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    jN N (γ • z) = jN N z := by
  obtain ⟨c', hc⟩ := mem_gamma0_dvd hγ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have him : ∀ w : ℍ, 0 < ((N : ℂ) * w).im := fun w => by
    simp [Complex.mul_im]
    positivity
  let w : ℍ := ⟨(N : ℂ) * z, him z⟩
  have h1 : ofComplex ((N : ℂ) * (γ • z : ℍ)) = conjGamma0 γ c' hc • w := by
    rw [ofComplex_apply_of_im_pos (him _)]
    ext
    show (N : ℂ) * ((γ • z : ℍ) : ℂ) = ((conjGamma0 γ c' hc • w : ℍ) : ℂ)
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
    have hd := denom_ne_zero' γ z
    have hc' : (γ 1 0 : ℂ) = N * c' := by exact_mod_cast hc
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp only [w, conjGamma0, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_mul, Int.cast_natCast]
    rw [hc'] at hd ⊢
    have hd2 : (c' : ℂ) * (N * z) + γ 1 1 ≠ 0 := by
      intro h; apply hd; linear_combination h
    field_simp
  have h2 : ofComplex ((N : ℂ) * z) = w := ofComplex_apply_of_im_pos (him z)
  unfold jN
  rw [h1, h2, jFun_smul]

/-! ### Helper lemmas: $j$ at the points $(gz + B)/D$ (the cusps of $j_N$) -/

/-- The imaginary part of $(gw + B)/D$ for integers $g, B, D$. -/
lemma aff_im (g B D : ℤ) (w : ℂ) : (((g : ℂ) * w + B) / D).im = g * w.im / D := by
  rw [show ((D : ℂ)) = ((D : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
  simp [Complex.add_im, Complex.mul_im]

/-- The point $(gz + B)/D$ of the upper half-plane, for integers $g, D > 0$. -/
noncomputable def affPt (g B D : ℤ) (hg : 0 < g) (hD : 0 < D) (z : ℍ) : ℍ :=
  ⟨((g : ℂ) * z + B) / D, by
    rw [aff_im]
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    exact div_pos (mul_pos hg' z.im_pos) hD'⟩

/-- The coercion to $\mathbb C$ of the affine point with parameters $g, B, D$. -/
lemma affPt_coe (g B D : ℤ) (hg : 0 < g) (hD : 0 < D) (z : ℍ) :
    (affPt g B D hg hD z : ℂ) = ((g : ℂ) * z + B) / D := rfl

/-- The affine point with parameters $g, B, D$ evaluated at a complex number of positive imaginary part. -/
lemma affPt_ofComplex (g B D : ℤ) (hg : 0 < g) (hD : 0 < D) {w : ℂ} (hw : 0 < w.im) :
    affPt g B D hg hD (ofComplex w) = ofComplex (((g : ℂ) * w + B) / D) := by
  have h1 : 0 < (((g : ℂ) * w + B) / D).im := by
    rw [aff_im]
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    exact div_pos (mul_pos hg' hw) hD'
  ext
  rw [ofComplex_apply_of_im_pos h1]
  simp [affPt_coe, ofComplex_apply_of_im_pos hw]

/-- Holomorphy of $z \mapsto j((gz+B)/D)$. -/
lemma jFun_affPt_mdiff (g B D : ℤ) (hg : 0 < g) (hD : 0 < D) :
    MDiff (fun z => jFun (affPt g B D hg hD z)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hj := UpperHalfPlane.mdifferentiable_iff.mp jFun_mdifferentiable
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ((g : ℂ) * w + B) / D) {w : ℂ | 0 < w.im} := by
    fun_prop (disch := exact hD0)
  have hmaps : Set.MapsTo (fun w : ℂ => ((g : ℂ) * w + B) / D) {w : ℂ | 0 < w.im}
      {w : ℂ | 0 < w.im} := by
    intro w hw
    have hw' : 0 < w.im := hw
    show 0 < (((g : ℂ) * w + B) / D).im
    rw [aff_im]
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    exact div_pos (mul_pos hg' hw') hD'
  refine (hj.comp hdiff hmaps).congr fun w hw => ?_
  simp only [Function.comp_apply]
  rw [affPt_ofComplex g B D hg hD hw]

/-- For $0 < |q| < 1$ there is a point $z$ with $e^{2\pi iz/h} = q$ at which all cusp functions of
period $h$ are evaluated. -/
lemma exists_point_cuspFunction' {h : ℝ} (hh : 0 < h) {q : ℂ} (hq0 : q ≠ 0) (hqb : ‖q‖ < 1) :
    ∃ z : ℍ, Function.Periodic.qParam h (z : ℂ) = q ∧ ∀ f : ℍ → ℂ, cuspFunction h f q = f z := by
  have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one hh hqb hq0
  refine ⟨⟨_, him⟩, Function.Periodic.qParam_right_inv hh.ne' hq0, fun f => ?_⟩
  simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero h _ hq0,
    ofComplex_apply_of_im_pos him]

/-- $j(\tau)q_\tau$ is bounded as $\Im\tau \to \infty$. -/
lemma jFun_mul_q_isBoundedAtImInfty :
    IsBoundedAtImInfty fun τ : ℍ => jFun τ * cexp (2 * π * I * τ) := by
  have hq : Tendsto (fun τ : ℍ => cexp (2 * π * I * τ)) atImInfty (𝓝 0) := by
    have := UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos
    simpa [qParam_one_eq] using this
  have h1 : IsBoundedAtImInfty fun τ : ℍ =>
      (jFun τ - 1 / cexp (2 * π * I * τ)) * cexp (2 * π * I * τ) :=
    BoundedAtFilter.mul jFun_sub_inv_q_isBoundedAtImInfty (ZeroAtFilter.boundedAtFilter hq)
  have h2 := BoundedAtFilter.add h1 (const_boundedAtFilter atImInfty (1 : ℂ))
  refine (Asymptotics.isBigO_congr (Eventually.of_forall fun τ => ?_)
    (Eventually.of_forall fun _ => rfl)).mp h2
  have : cexp (2 * π * I * τ) ≠ 0 := Complex.exp_ne_zero _
  simp only [Pi.add_apply, Function.const_apply]
  field_simp
  ring

/-- $j((gz+B)/D)$ is meromorphic at the cusp $\infty$ (for integers $g, D > 0$). -/
lemma isMeromorphicAtImInfty_jFun_affPt (g B D : ℤ) (hg : 0 < g) (hD : 0 < D) :
    IsMeromorphicAtImInfty (fun z => jFun (affPt g B D hg hD z)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, g = m := ⟨g.toNat, (Int.toNat_of_nonneg hg.le).symm⟩
  set F : ℍ → ℂ := fun z => jFun (affPt (m : ℤ) B D hg hD z) with hF
  have hh : (0 : ℝ) < D := by exact_mod_cast hD
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hshift : ∀ z : ℍ, affPt (m : ℤ) B D hg hD ((D : ℝ) +ᵥ z) =
      ((m : ℤ) : ℝ) +ᵥ affPt (m : ℤ) B D hg hD z := by
    intro z
    ext
    simp only [affPt_coe, UpperHalfPlane.coe_vadd]
    push_cast
    field_simp
    ring
  have hFper : ∀ z : ℍ, F ((D : ℝ) +ᵥ z) = F z := by
    intro z
    simp only [hF]
    rw [hshift, ← UpperHalfPlane.modular_T_zpow_smul, jFun_smul]
  have hperF : Function.Periodic (F ∘ ofComplex) (D : ℝ) :=
    UpperHalfPlane.periodic_comp_ofComplex hFper
  set Fm : ℍ → ℂ := fun z => F z * cexp (2 * π * I * m * z / D) with hFm
  have hFmd : MDiff Fm := by
    have h1 : MDiff F := jFun_affPt_mdiff _ _ _ hg hD
    have h2 : MDiff (fun z : ℍ => cexp (2 * π * I * m * z / D)) :=
      (Differentiable.mdifferentiable (f := fun w : ℂ => cexp (2 * π * I * m * w / D))
        (by fun_prop)).comp (UpperHalfPlane.mdifferentiable_coe)
    exact h1.mul h2
  have hFmper : Function.Periodic (Fm ∘ ofComplex) (D : ℝ) := by
    refine UpperHalfPlane.periodic_comp_ofComplex fun z => ?_
    simp only [hFm]
    rw [hFper]
    congr 1
    have : (2 * π * I * m * (((D : ℝ) +ᵥ z : ℍ) : ℂ) / D) =
        2 * π * I * m * (z : ℂ) / D + m * (2 * π * I) := by
      simp only [UpperHalfPlane.coe_vadd]
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  have hτ : Tendsto (affPt (m : ℤ) B D hg hD) atImInfty atImInfty := by
    simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
    have hg' : (0 : ℝ) < ((m : ℤ) : ℝ) := by exact_mod_cast hg
    have : ∀ z : ℍ, (affPt (m : ℤ) B D hg hD z).im = ((m : ℤ) : ℝ) * z.im / D := fun z =>
      aff_im (m : ℤ) B D z
    simp only [this]
    exact ((tendsto_comap (f := UpperHalfPlane.im) (x := atTop)).const_mul_atTop hg').atTop_div_const hh
  have hFmb : IsBoundedAtImInfty Fm := by
    have h1 := (jFun_mul_q_isBoundedAtImInfty.comp_tendsto hτ).const_mul_left
      (cexp (-(2 * π * I * B / D)))
    refine (Asymptotics.isBigO_congr (Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun _ => rfl)).mp h1
    simp only [hFm, hF, Function.comp_apply, affPt_coe]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  have hA : AnalyticAt ℂ (cuspFunction (D : ℝ) Fm) 0 :=
    analyticAt_cuspFunction_zero hh hFmper hFmd hFmb
  have hm : MeromorphicAt (fun q => cuspFunction (D : ℝ) Fm q / q ^ m) 0 :=
    hA.meromorphicAt.div (analyticAt_id.pow m).meromorphicAt
  refine ⟨(D : ℝ), hh, hperF, hm.congr ?_⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
    with q hq0 hqb
  obtain ⟨z, hzq, hz⟩ := exists_point_cuspFunction' hh hq0 (by simpa using hqb)
  have hq0' : q ≠ 0 := hq0
  rw [hz Fm, hz F]
  have : cexp (2 * π * I * m * z / D) = q ^ m := by
    rw [← hzq]
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simp only [hFm, this]
  have : q ^ m ≠ 0 := pow_ne_zero _ hq0'
  field_simp

/-- Hermite normal form: $\begin{pmatrix}N&0\\0&1\end{pmatrix}\gamma = \delta\begin{pmatrix}g&B\\0&D\end{pmatrix}$
with $\delta \in \mathrm{SL}_2(\mathbb Z)$, $g, D > 0$, $gD = N$, read as an identity of Möbius
transformations on $\mathbb H$. -/
lemma exists_hermite_spec {N : ℕ} (hN : 1 ≤ N) (γ : SL(2, ℤ)) :
    ∃ (δ : SL(2, ℤ)) (g B D : ℤ) (hg : 0 < g) (hD : 0 < D),
      g * D = N ∧ g = (Int.gcd (N * γ 0 0) (γ 1 0) : ℤ) ∧
      ∀ z : ℍ, ofComplex ((N : ℂ) * (γ • z : ℍ)) = δ • affPt g B D hg hD z := by
  set a' : ℤ := γ 0 0
  set b' : ℤ := γ 0 1
  set c' : ℤ := γ 1 0
  set d' : ℤ := γ 1 1
  have hdet : a' * d' - b' * c' = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  set g : ℤ := (Int.gcd (N * a') c' : ℤ) with hgdef
  have hgpos : 0 < g := by
    have h0 : 0 ≤ g := Int.natCast_nonneg _
    rcases h0.eq_or_lt with h | h
    · exfalso
      have h1 : Int.gcd (N * a') c' = 0 := by omega
      rw [Int.gcd_eq_zero_iff] at h1
      obtain ⟨h2, h3⟩ := h1
      have : a' = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · omega
        · exact h
      rw [this, h3] at hdet
      simp at hdet
    · exact h
  obtain ⟨p', q', hcop, hp, hq⟩ := Int.exists_gcd_one (m := N * a') (n := c')
    (Int.natCast_pos.mp hgpos)
  obtain ⟨x, y, hxy⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hg1 : g * p' = N * a' := by rw [hp]; ring
  have hg2 : g * q' = c' := by rw [hq]; ring
  set B : ℤ := x * N * b' + y * d' with hBdef
  set D : ℤ := -q' * N * b' + p' * d' with hDdef
  have hgD : g * D = N := by
    have : g * D = -(g * q') * N * b' + (g * p') * d' := by rw [hDdef]; ring
    rw [this, hg1, hg2]
    linear_combination N * hdet
  have hDpos : 0 < D := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hgpos.le h]
  let δ : SL(2, ℤ) := ⟨!![p', -y; q', x], by simp [Matrix.det_fin_two]; linarith⟩
  refine ⟨δ, g, B, D, hgpos, hDpos, hgD, hgdef, fun z => ?_⟩
  have hNz : 0 < ((N : ℂ) * (γ • z : ℍ)).im := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    simp [Complex.mul_im]
    positivity
  ext
  rw [ofComplex_apply_of_im_pos hNz]
  show (N : ℂ) * ((γ • z : ℍ) : ℂ) = ((δ • affPt g B D hgpos hDpos z : ℍ) : ℂ)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [δ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, algebraMap_int_eq, eq_intCast,
    Complex.ofReal_intCast, affPt_coe]
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hden : (c' : ℂ) * z + d' ≠ 0 := denom_ne_zero' γ z
  have hg1' : (g : ℂ) * p' = N * a' := by exact_mod_cast hg1
  have hg2' : (g : ℂ) * q' = c' := by exact_mod_cast hg2
  have hB1' : (p' : ℂ) * B - y * D = N * b' := by
    have : p' * B - y * D = N * b' := by
      rw [hBdef, hDdef]; linear_combination (N * b') * hxy
    exact_mod_cast this
  have hB2' : (q' : ℂ) * B + x * D = d' := by
    have : q' * B + x * D = d' := by
      rw [hBdef, hDdef]; linear_combination d' * hxy
    exact_mod_cast this
  have hτ : (D : ℂ) * (((g : ℂ) * z + B) / D) = g * z + B := by field_simp
  have e1 : (D : ℂ) * ((q' : ℂ) * (((g : ℂ) * z + B) / D) + x) = c' * z + d' := by
    linear_combination (q' : ℂ) * hτ + (z : ℂ) * hg2' + hB2'
  have e2 : (D : ℂ) * ((p' : ℂ) * (((g : ℂ) * z + B) / D) + (-y : ℤ)) = N * (a' * z + b') := by
    push_cast
    linear_combination (p' : ℂ) * hτ + (z : ℂ) * hg1' + hB1'
  have hQ : (q' : ℂ) * (((g : ℂ) * z + B) / D) + x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact hden e1.symm
  rw [mul_div_assoc', div_eq_div_iff hden hQ]
  refine mul_left_cancel₀ hD0 ?_
  linear_combination (N * (a' * z + b') : ℂ) * e1 - ((c' : ℂ) * z + d') * e2

/-- Hermite normal form (the Möbius identity of `exists_hermite_spec` without the arithmetic data). -/
lemma exists_hermite {N : ℕ} (hN : 1 ≤ N) (γ : SL(2, ℤ)) :
    ∃ (δ : SL(2, ℤ)) (g B D : ℤ) (hg : 0 < g) (hD : 0 < D),
      ∀ z : ℍ, ofComplex ((N : ℂ) * (γ • z : ℍ)) = δ • affPt g B D hg hD z := by
  obtain ⟨δ, g, B, D, hg, hD, -, -, h⟩ := exists_hermite_spec hN γ
  exact ⟨δ, g, B, D, hg, hD, h⟩

/-- $j_N(z) = j((Nz + 0)/1)$. -/
lemma jN_eq_affPt {N : ℕ} (hN : 1 ≤ N) (z : ℍ) :
    jN N z = jFun (affPt N 0 1 (by exact_mod_cast hN) one_pos z) := by
  unfold jN
  congr 1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 0 < ((N : ℂ) * z).im := by simp [Complex.mul_im]; positivity
  ext
  rw [ofComplex_apply_of_im_pos h1]
  simp [affPt_coe]

/-- $j_N$ is holomorphic on $\mathbb H$. -/
lemma jN_mdifferentiable {N : ℕ} (hN : 1 ≤ N) : MDiff (jN N) := by
  have : jN N = fun z => jFun (affPt N 0 1 (by exact_mod_cast hN) one_pos z) :=
    funext (jN_eq_affPt hN)
  rw [this]
  exact jFun_affPt_mdiff _ _ _ _ _

/-- $j_N$ is a modular function for $\Gamma_0(N)$ ("$j_N$ defines a meromorphic function on $X_0(N)$",
pdf p. 192), $N \ge 1$. -/
@[kb "milne2006ec" "Ch. V, §2, j_N is a meromorphic function on X₀(N) (running text), pdf p. 192"]
theorem isModularFunction_jN {N : ℕ} (hN : 1 ≤ N) : IsModularFunction (CongruenceSubgroup.Gamma0 N) (jN N) where
  meromorphic := isMeromorphicOnUpperHalfPlane_of_mdiff (jN_mdifferentiable hN)
  invariant := fun γ hγ z => jN_smul hN hγ z
  meromorphic_cusps := fun γ => by
    obtain ⟨δ, g, B, D, hg, hD, h⟩ := exists_hermite hN γ
    have : (fun z => jN N (γ • z)) = fun z => jFun (affPt g B D hg hD z) := by
      funext z
      unfold jN
      rw [h z, jFun_smul]
    rw [this]
    exact isMeromorphicAtImInfty_jFun_affPt g B D hg hD

/-- Evaluation of $G \in \mathbb C[X][Y]$ at $(X, Y) = (j(z), j_N(z))$. -/
noncomputable def evalJJN (N : ℕ) (G : Polynomial (Polynomial ℂ)) (z : ℍ) : ℂ :=
  (G.map (Polynomial.evalRingHom (jFun z))).eval (jN N z)

/-- **Theorem 2.3** (pdf p. 192): the field of meromorphic functions on $X_0(N)$ is $\mathbb C(j, j_N)$: every
modular function for $\Gamma_0(N)$ is, away from a discrete set, a rational function of $j$ and $j_N$ (the converse
inclusion is `isModularFunction_jFun`, `isModularFunction_jN`). A named statement. -/
@[kb "milne2006ec" "Ch. V, Theorem 2.3, pdf p. 192"]
structure Thm2_3 : Prop where
  rational : ∀ N : ℕ, 1 ≤ N → ∀ f : ℍ → ℂ, IsModularFunction (CongruenceSubgroup.Gamma0 N) f →
    ∃ P Q : Polynomial (Polynomial ℂ), (∃ z, evalJJN N Q z ≠ 0) ∧
      f =ᶠ[codiscrete ℍ] fun z ↦ evalJJN N P z / evalJJN N Q z

/-- The modular polynomial (pdf p. 193): $F_N(X, Y) \in \mathbb C[X][Y]$, monic of degree
$m = (\Gamma_0(1) : \Gamma_0(N))$ in $Y$, with $F_N(j, j_N) = 0$, generating the ideal of all $G$ with
$G(j, j_N) = 0$ (hence the unique such monic polynomial of degree $m$). A named statement (shown in the proof of
Theorem 2.3). -/
@[kb "milne2006ec" "Ch. V, §2, the modular polynomial F_N (running text), pdf p. 193"]
structure ModularPolynomial (N : ℕ) : Prop where
  exists_poly : ∃ F : Polynomial (Polynomial ℂ), F.Monic ∧ F.natDegree = (CongruenceSubgroup.Gamma0 N).index ∧
    (∀ z, evalJJN N F z = 0) ∧ ∀ G : Polynomial (Polynomial ℂ), (∀ z, evalJJN N G z = 0) → F ∣ G

/-- **Proposition 2.4** (pdf p. 193): the modular polynomial $F_N(X, Y)$ has coefficients in $\mathbb Q$. A named
statement: there is a monic $F \in \mathbb Q[X][Y]$ of degree $(\Gamma_0(1) : \Gamma_0(N))$ in $Y$ whose image in
$\mathbb C[X][Y]$ has the properties of `ModularPolynomial`. -/
@[kb "milne2006ec" "Ch. V, Proposition 2.4, pdf p. 193"]
structure Prop2_4 (N : ℕ) : Prop where
  exists_poly : ∃ F : Polynomial (Polynomial ℚ), F.Monic ∧
    F.natDegree = (CongruenceSubgroup.Gamma0 N).index ∧
    (∀ z, evalJJN N (F.map (Polynomial.mapRingHom (algebraMap ℚ ℂ))) z = 0) ∧
    ∀ G : Polynomial (Polynomial ℂ), (∀ z, evalJJN N G z = 0) →
      F.map (Polynomial.mapRingHom (algebraMap ℚ ℂ)) ∣ G

/-- Proposition 2.4 implies the existence statement for $F_N$. -/
theorem Prop2_4.modularPolynomial {N : ℕ} (h : Prop2_4 N) : ModularPolynomial N := by
  obtain ⟨F, hmonic, hdeg, hzero, hdiv⟩ := h.exists_poly
  have hinj : Function.Injective (Polynomial.mapRingHom (algebraMap ℚ ℂ)) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective
  refine ⟨_, hmonic.map _, ?_, hzero, hdiv⟩
  rw [Polynomial.natDegree_map_eq_of_injective hinj]
  exact hdeg

/-! ### The complex points of $Y_0(N)$ (pdf pp. 195–196) -/

/-- An oriented basis $(\omega_1, \omega_2)$ ($\Im(\omega_1/\omega_2) > 0$), Milne's set $M$ (pdf p. 195). -/
def OrientedBasis : Type := {ω : ℂ × ℂ // 0 < (ω.1 / ω.2).im}

/-- The lattice $\Lambda(\omega_1, \omega_2) = \mathbb Z\omega_1 + \mathbb Z\omega_2$. -/
def OrientedBasis.lattice (ω : OrientedBasis) : Submodule ℤ ℂ := Submodule.span ℤ {ω.1.1, ω.1.2}

/-- The cyclic subgroup $S = \langle \omega_2/N \rangle$ of $\mathbb C/\Lambda(\omega_1, \omega_2)$, recorded by its
preimage $\Lambda + \mathbb Z\omega_2/N$ in $\mathbb C$ (subgroups of $\mathbb C/\Lambda$ are the subgroups of
$\mathbb C$ containing $\Lambda$). -/
noncomputable def OrientedBasis.cyclicSubgroup (N : ℕ) (ω : OrientedBasis) : AddSubgroup ℂ :=
  ω.lattice.toAddSubgroup ⊔ AddSubgroup.zmultiples (ω.1.2 / N)

/-- For subgroups $\Lambda \le L$ of $\mathbb C$: $L/\Lambda$ is cyclic of order $N$. -/
def IsCyclicOfOrder (N : ℕ) (Λ L : AddSubgroup ℂ) : Prop :=
  Λ ≤ L ∧ IsAddCyclic (L ⧸ Λ.addSubgroupOf L) ∧ Nat.card (L ⧸ Λ.addSubgroupOf L) = N

/-- The action of $\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$ on oriented bases:
$(\omega_1, \omega_2) \mapsto (a\omega_1 + b\omega_2, c\omega_1 + d\omega_2)$. -/
def OrientedBasis.smul (γ : SL(2, ℤ)) (ω : ℂ × ℂ) : ℂ × ℂ :=
  ((γ 0 0 : ℂ) * ω.1 + γ 0 1 * ω.2, (γ 1 0 : ℂ) * ω.1 + γ 1 1 * ω.2)

/-! ### Helper lemmas: cyclic quotients, oriented bases and the three parts of the bijection -/

/-- If $kt \in \Lambda$ exactly when $N \mid k$, then $(\Lambda + \mathbb Zt)/\Lambda$ is cyclic of order $N$. -/
lemma isCyclicOfOrder_of_gen {N : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ}
    (h : ∀ k : ℤ, k • t ∈ Λ ↔ (N : ℤ) ∣ k) :
    IsCyclicOfOrder N Λ (Λ ⊔ AddSubgroup.zmultiples t) := by
  set L := Λ ⊔ AddSubgroup.zmultiples t with hL
  have htL : t ∈ L := AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples t)
  let ψ : ℤ →+ L ⧸ Λ.addSubgroupOf L :=
    (QuotientAddGroup.mk' _).comp (zmultiplesHom L ⟨t, htL⟩)
  have hψ : ∀ k : ℤ, ψ k = 0 ↔ (N : ℤ) ∣ k := by
    intro k
    rw [← h k]
    simp only [ψ, AddMonoidHom.comp_apply, zmultiplesHom_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨l, hl, s, hs, rfl⟩ := AddSubgroup.mem_sup.mp hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hs
    refine ⟨k, ?_⟩
    simp only [ψ, AddMonoidHom.comp_apply, zmultiplesHom_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq]
    simp [AddSubgroup.mem_addSubgroupOf, hl]
  refine ⟨le_sup_left, isAddCyclic_of_surjective ψ hsurj, ?_⟩
  have hN : ψ (N : ℤ) = 0 := (hψ _).mpr dvd_rfl
  let ψ' : ZMod N →+ L ⧸ Λ.addSubgroupOf L := ZMod.lift N ⟨ψ, hN⟩
  have hψ' : ∀ k : ℤ, ψ' (k : ZMod N) = ψ k := fun k => ZMod.lift_coe N ⟨ψ, hN⟩ k
  have hbij : Function.Bijective ψ' := by
    constructor
    · rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
      have : ψ k = 0 := by rw [← hψ']; exact hx
      have := (hψ k).mp this
      simpa [AddSubgroup.mem_bot, (ZMod.intCast_zmod_eq_zero_iff_dvd k N)] using this
    · intro q
      obtain ⟨k, rfl⟩ := hsurj q
      exact ⟨k, hψ' k⟩
  rw [← Nat.card_zmod N]
  exact (Nat.card_congr (Equiv.ofBijective ψ' hbij)).symm

/-- A cyclic extension $L/\Lambda$ of order $N$ is generated by an element $t$ with $kt \in \Lambda$
exactly when $N \mid k$. -/
lemma gen_of_isCyclicOfOrder {N : ℕ} {Λ L : AddSubgroup ℂ} (h : IsCyclicOfOrder N Λ L) :
    ∃ t : ℂ, L = Λ ⊔ AddSubgroup.zmultiples t ∧ ∀ k : ℤ, k • t ∈ Λ ↔ (N : ℤ) ∣ k := by
  obtain ⟨hle, hcyc, hcard⟩ := h
  obtain ⟨g, hg⟩ := hcyc.exists_zsmul_surjective
  obtain ⟨⟨t, ht⟩, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hmk : ∀ k : ℤ, ((k • (QuotientAddGroup.mk (⟨t, ht⟩ : L) : L ⧸ Λ.addSubgroupOf L)) = 0) ↔
      k • t ∈ Λ := by
    intro k
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  refine ⟨t, le_antisymm ?_ (sup_le hle (AddSubgroup.zmultiples_le.mpr ht)), fun k => ?_⟩
  · intro x hx
    obtain ⟨k, hk⟩ := hg (QuotientAddGroup.mk ⟨x, hx⟩)
    simp only at hk
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hk
    have h1 : -(k • t) + x ∈ Λ := hk
    exact AddSubgroup.mem_sup.mpr ⟨-(k • t) + x, h1, k • t,
      AddSubgroup.mem_zmultiples_iff.mpr ⟨k, rfl⟩, by abel⟩
  · rw [← hmk, ← addOrderOf_dvd_iff_zsmul_eq_zero]
    rw [addOrderOf_eq_card_of_forall_mem_zmultiples
      (g := (QuotientAddGroup.mk (⟨t, ht⟩ : L) : L ⧸ Λ.addSubgroupOf L)) ?_, hcard]
    intro x
    obtain ⟨k, hk⟩ := hg x
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, hk⟩

/-- The second vector of an oriented basis is nonzero. -/
lemma OrientedBasis.snd_ne_zero (ω : OrientedBasis) : ω.1.2 ≠ 0 := by
  intro h
  have := ω.2
  rw [h] at this
  simp at this

/-- The two components of an oriented basis are linearly independent over $\mathbb R$. -/
lemma OrientedBasis.indep (ω : OrientedBasis) {r s : ℝ} (h : (r : ℂ) * ω.1.1 + s * ω.1.2 = 0) :
    r = 0 ∧ s = 0 := by
  have h2 := ω.snd_ne_zero
  have h3 : (r : ℂ) * (ω.1.1 / ω.1.2) + s = 0 := by
    field_simp
    linear_combination h
  have h4 := congrArg Complex.im h3
  simp at h4
  have hr : r = 0 := by
    rcases h4 with h4 | h4
    · exact h4
    · exact absurd h4 ω.2.ne'
  subst hr
  simp at h3
  refine ⟨rfl, ?_⟩
  exact_mod_cast h3

/-- The two vectors of an oriented basis are linearly independent over $\mathbb Z$. -/
lemma OrientedBasis.indep_int (ω : OrientedBasis) {m n : ℤ}
    (h : (m : ℂ) * ω.1.1 + n * ω.1.2 = 0) : m = 0 ∧ n = 0 := by
  have := ω.indep (r := m) (s := n) (by exact_mod_cast h)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- Membership in the lattice of an oriented basis, in terms of integer coordinates. -/
lemma OrientedBasis.mem_lattice (ω : OrientedBasis) (x : ℂ) :
    x ∈ ω.lattice ↔ ∃ m n : ℤ, (m : ℂ) * ω.1.1 + n * ω.1.2 = x := by
  unfold OrientedBasis.lattice
  rw [Submodule.mem_span_pair]
  simp [zsmul_eq_mul]

/-- Membership in the lattice of an oriented basis, in an alternative form. -/
lemma OrientedBasis.mem_lattice' (ω : OrientedBasis) (x : ℂ) :
    x ∈ ω.lattice.toAddSubgroup ↔ ∃ m n : ℤ, (m : ℂ) * ω.1.1 + n * ω.1.2 = x :=
  ω.mem_lattice x

/-- $k\omega_2/N \in \Lambda$ exactly when $N \mid k$. -/
lemma OrientedBasis.gen (ω : OrientedBasis) {N : ℕ} (hN : 1 ≤ N) (k : ℤ) :
    k • (ω.1.2 / N) ∈ ω.lattice.toAddSubgroup ↔ (N : ℤ) ∣ k := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [ω.mem_lattice']
  constructor
  · rintro ⟨m, n, h⟩
    have h1 : ((-(m : ℝ) : ℝ) : ℂ) * ω.1.1 + ((k / N - n : ℝ) : ℂ) * ω.1.2 = 0 := by
      push_cast
      rw [zsmul_eq_mul] at h
      field_simp at h ⊢
      linear_combination -h
    have h2 := (ω.indep h1).2
    have h3 : (k : ℝ) = N * n := by
      have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      field_simp at h2
      linarith
    exact ⟨n, by exact_mod_cast h3⟩
  · rintro ⟨j, rfl⟩
    refine ⟨0, j, ?_⟩
    push_cast
    rw [zsmul_eq_mul]
    push_cast
    field_simp
    ring

/-- Part (i): the subgroup $\langle\omega_2/N\rangle$ is cyclic of order $N$ modulo $\Lambda$. -/
lemma OrientedBasis.isCyclicOfOrder (ω : OrientedBasis) {N : ℕ} (hN : 1 ≤ N) :
    IsCyclicOfOrder N ω.lattice.toAddSubgroup (ω.cyclicSubgroup N) :=
  isCyclicOfOrder_of_gen (ω.gen hN)

/-- Acting by $\gamma \in \mathrm{SL}_2(\mathbb Z)$ preserves the lattice. -/
lemma OrientedBasis.lattice_eq_of_smul {ω ω' : OrientedBasis} {γ : SL(2, ℤ)}
    (h : ω'.1 = OrientedBasis.smul γ ω.1) : ω'.lattice = ω.lattice := by
  have h1 : ω'.1.1 = (γ 0 0 : ℂ) * ω.1.1 + γ 0 1 * ω.1.2 := by rw [h]; rfl
  have h2 : ω'.1.2 = (γ 1 0 : ℂ) * ω.1.1 + γ 1 1 * ω.1.2 := by rw [h]; rfl
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdet
  ext x
  rw [ω'.mem_lattice, ω.mem_lattice]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * γ 0 0 + n * γ 1 0, m * γ 0 1 + n * γ 1 1, ?_⟩
    rw [h1, h2]
    push_cast
    ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * γ 1 1 - n * γ 1 0, -(m * γ 0 1) + n * γ 0 0, ?_⟩
    rw [h1, h2]
    push_cast
    linear_combination (m * ω.1.1 + n * ω.1.2 : ℂ) * hdetC

/-- The imaginary part of a Möbius transformation, multiplied by $|c\tau + d|^2$. -/
lemma im_div_formula (a b c d : ℝ) (τ : ℂ) (h : (c : ℂ) * τ + d ≠ 0) :
    ((a * τ + b) / (c * τ + d)).im * Complex.normSq (c * τ + d) = (a * d - b * c) * τ.im := by
  have hn : Complex.normSq (c * τ + d) ≠ 0 := (Complex.normSq_pos.mpr h).ne'
  rw [Complex.div_im]
  set n := Complex.normSq (c * τ + d) with hn_def
  have h1 : ((a * τ + b).im * (c * τ + d).re / n - (a * τ + b).re * (c * τ + d).im / n) * n =
      (a * τ + b).im * (c * τ + d).re - (a * τ + b).re * (c * τ + d).im := by
    field_simp
  rw [h1]
  simp
  ring

/-- For an oriented basis $\omega$ and a matrix with integer entries, the orientation of the image is
the sign of the determinant. -/
lemma OrientedBasis.im_formula (ω : OrientedBasis) (a b c d : ℤ)
    (h : (c : ℂ) * ω.1.1 + d * ω.1.2 ≠ 0) :
    ((((a : ℂ) * ω.1.1 + b * ω.1.2) / ((c : ℂ) * ω.1.1 + d * ω.1.2)).im) *
      Complex.normSq ((c : ℂ) * (ω.1.1 / ω.1.2) + d) = (a * d - b * c) * (ω.1.1 / ω.1.2).im := by
  have h2 := ω.snd_ne_zero
  have hden : (c : ℂ) * (ω.1.1 / ω.1.2) + d ≠ 0 := by
    intro h0
    apply h
    have : (c : ℂ) * ω.1.1 + d * ω.1.2 = ((c : ℂ) * (ω.1.1 / ω.1.2) + d) * ω.1.2 := by
      field_simp
    rw [this, h0, zero_mul]
  have e : ((a : ℂ) * ω.1.1 + b * ω.1.2) / ((c : ℂ) * ω.1.1 + d * ω.1.2) =
      (((a : ℝ) : ℂ) * (ω.1.1 / ω.1.2) + ((b : ℝ) : ℂ)) /
        (((c : ℝ) : ℂ) * (ω.1.1 / ω.1.2) + ((d : ℝ) : ℂ)) := by
    push_cast
    have : (c : ℂ) * ω.1.1 + d * ω.1.2 = ((c : ℂ) * (ω.1.1 / ω.1.2) + d) * ω.1.2 := by
      field_simp
    rw [this]
    field_simp
  rw [e]
  have := im_div_formula a b c d (ω.1.1 / ω.1.2) (by push_cast; exact hden)
  push_cast at this ⊢
  exact this

/-- If two oriented bases span the same lattice, the integer matrix between them has positive
determinant. -/
lemma OrientedBasis.det_pos (ω ω' : OrientedBasis) {a b c d : ℤ}
    (h1 : ω'.1.1 = a * ω.1.1 + b * ω.1.2) (h2 : ω'.1.2 = c * ω.1.1 + d * ω.1.2) :
    0 < a * d - b * c := by
  have hne : (c : ℂ) * ω.1.1 + d * ω.1.2 ≠ 0 := by
    rw [← h2]; exact ω'.snd_ne_zero
  have hf := ω.im_formula a b c d hne
  rw [← h1, ← h2] at hf
  have hpos := ω'.2
  have hnorm : 0 < Complex.normSq ((c : ℂ) * (ω.1.1 / ω.1.2) + d) := by
    apply Complex.normSq_pos.mpr
    intro h0
    apply hne
    have : (c : ℂ) * ω.1.1 + d * ω.1.2 = ((c : ℂ) * (ω.1.1 / ω.1.2) + d) * ω.1.2 := by
      field_simp [ω.snd_ne_zero]
    rw [this, h0, zero_mul]
  have h3 : 0 < (((a * d - b * c : ℤ) : ℝ)) * (ω.1.1 / ω.1.2).im := by
    push_cast
    rw [← hf]
    exact mul_pos hpos hnorm
  have h4 := ω.2
  have : (0 : ℝ) < ((a * d - b * c : ℤ) : ℝ) := by
    by_contra hle
    push Not at hle
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hle h4.le]
  exact_mod_cast this

/-- Acting by $\gamma \in \Gamma_0(N)$ preserves the cyclic subgroup. -/
lemma OrientedBasis.cyclicSubgroup_eq_of_smul {N : ℕ} (hN : 1 ≤ N) {ω ω' : OrientedBasis}
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (h : ω'.1 = OrientedBasis.smul γ ω.1) : ω'.cyclicSubgroup N = ω.cyclicSubgroup N := by
  have h1 : ω'.1.1 = (γ 0 0 : ℂ) * ω.1.1 + γ 0 1 * ω.1.2 := by rw [h]; rfl
  have h2 : ω'.1.2 = (γ 1 0 : ℂ) * ω.1.1 + γ 1 1 * ω.1.2 := by rw [h]; rfl
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  obtain ⟨c', hc'⟩ : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hc'C : (γ 1 0 : ℂ) = N * c' := by exact_mod_cast hc'
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * (N * c') = 1 := by
    rw [← hc'C]; exact_mod_cast hdet
  have hlat := OrientedBasis.lattice_eq_of_smul h
  unfold OrientedBasis.cyclicSubgroup
  rw [hlat]
  have hs' : ω'.1.2 / N = (c' : ℂ) * ω.1.1 + γ 1 1 * (ω.1.2 / N) := by
    rw [h2, hc'C]; field_simp
  have hs : ω.1.2 / N = (γ 0 0 : ℤ) * (ω'.1.2 / N) - ((γ 0 0 * c' : ℤ) : ℂ) * ω.1.1
      - ((γ 0 1 * c' : ℤ) : ℂ) * ω.1.2 := by
    rw [hs']
    push_cast
    field_simp
    linear_combination -(ω.1.2 : ℂ) * hdetC
  apply le_antisymm
  · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    rw [hs']
    refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left ?_) (AddSubgroup.mem_sup_right ?_)
    · exact (ω.mem_lattice' _).mpr ⟨c', 0, by simp⟩
    · simp
  · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    rw [hs]
    refine AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ ?_ (AddSubgroup.mem_sup_left ?_))
      (AddSubgroup.mem_sup_left ?_)
    · exact AddSubgroup.mem_sup_right (by simp)
    · exact (ω.mem_lattice' _).mpr ⟨γ 0 0 * c', 0, by simp⟩
    · exact (ω.mem_lattice' _).mpr ⟨0, γ 0 1 * c', by simp⟩

/-- The action of $\mathrm{SL}_2(\mathbb Z)$ on oriented bases. -/
noncomputable def OrientedBasis.act (δ : SL(2, ℤ)) (ω : OrientedBasis) : OrientedBasis :=
  ⟨OrientedBasis.smul δ ω.1, by
    have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
      have := δ.det_coe
      rw [Matrix.det_fin_two] at this
      exact this
    have hne : ((δ 1 0 : ℤ) : ℂ) * ω.1.1 + (δ 1 1 : ℤ) * ω.1.2 ≠ 0 := by
      intro h0
      obtain ⟨h1, h2⟩ := ω.indep_int h0
      rw [h1, h2] at hdet
      simp at hdet
    have hf := ω.im_formula (δ 0 0) (δ 0 1) (δ 1 0) (δ 1 1) hne
    have hnorm : 0 < Complex.normSq (((δ 1 0 : ℤ) : ℂ) * (ω.1.1 / ω.1.2) + (δ 1 1 : ℤ)) := by
      apply Complex.normSq_pos.mpr
      intro h0
      apply hne
      have : ((δ 1 0 : ℤ) : ℂ) * ω.1.1 + (δ 1 1 : ℤ) * ω.1.2 =
          (((δ 1 0 : ℤ) : ℂ) * (ω.1.1 / ω.1.2) + (δ 1 1 : ℤ)) * ω.1.2 := by
        field_simp [ω.snd_ne_zero]
      rw [this, h0, zero_mul]
    have hdetR : (((δ 0 0 : ℤ) : ℝ) * (δ 1 1 : ℤ) - (δ 0 1 : ℤ) * (δ 1 0 : ℤ)) = 1 := by
      exact_mod_cast hdet
    rw [hdetR, one_mul] at hf
    show 0 < ((((δ 0 0 : ℤ) : ℂ) * ω.1.1 + (δ 0 1 : ℤ) * ω.1.2) /
      (((δ 1 0 : ℤ) : ℂ) * ω.1.1 + (δ 1 1 : ℤ) * ω.1.2)).im
    by_contra hle
    push Not at hle
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hle hnorm.le, ω.2]⟩

/-- Part (ii), forward direction: bases with the same lattice and cyclic subgroup differ by an element
of $\Gamma_0(N)$. -/
lemma OrientedBasis.exists_gamma0 {N : ℕ} (hN : 1 ≤ N) {ω ω' : OrientedBasis}
    (hΛ : ω.lattice = ω'.lattice) (hL : ω.cyclicSubgroup N = ω'.cyclicSubgroup N) :
    ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ω'.1 = OrientedBasis.smul γ ω.1 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hm1 : ω'.1.1 ∈ ω.lattice := by
    rw [hΛ]; exact Submodule.subset_span (by simp)
  have hm2 : ω'.1.2 ∈ ω.lattice := by
    rw [hΛ]; exact Submodule.subset_span (by simp)
  have hm3 : ω.1.1 ∈ ω'.lattice := by
    rw [← hΛ]; exact Submodule.subset_span (by simp)
  have hm4 : ω.1.2 ∈ ω'.lattice := by
    rw [← hΛ]; exact Submodule.subset_span (by simp)
  obtain ⟨a, b, h1⟩ := (ω.mem_lattice _).mp hm1
  obtain ⟨c, d, h2⟩ := (ω.mem_lattice _).mp hm2
  obtain ⟨a2, b2, h3⟩ := (ω'.mem_lattice _).mp hm3
  obtain ⟨c2, d2, h4⟩ := (ω'.mem_lattice _).mp hm4
  have E1 := ω.indep_int (m := a2 * a + b2 * c - 1) (n := a2 * b + b2 * d) (by
    push_cast
    rw [← h1, ← h2] at h3
    linear_combination h3)
  have E2 := ω.indep_int (m := c2 * a + d2 * c) (n := c2 * b + d2 * d - 1) (by
    push_cast
    rw [← h1, ← h2] at h4
    linear_combination h4)
  have hprod : (a * d - b * c) * (a2 * d2 - b2 * c2) = 1 := by
    obtain ⟨E11, E12⟩ := E1
    obtain ⟨E21, E22⟩ := E2
    linear_combination (c2 * b + d2 * d) * E11 + E22 - (c2 * a + d2 * c) * E12
  have hpos := ω.det_pos ω' (a := a) (b := b) (c := c) (d := d) h1.symm h2.symm
  have hdet : a * d - b * c = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h | h
    · exact h
    · omega
  have hmem : ω'.1.2 / N ∈ ω.cyclicSubgroup N := by
    rw [hL]
    exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)
  obtain ⟨l, hl, z, hz, hsum⟩ := AddSubgroup.mem_sup.mp hmem
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  obtain ⟨m, n, rfl⟩ := (ω.mem_lattice' l).mp hl
  rw [← h2] at hsum
  have E3 := ω.indep_int (m := c - N * m) (n := d - N * n - k) (by
    push_cast
    rw [zsmul_eq_mul] at hsum
    field_simp at hsum
    linear_combination -hsum)
  have hcN : (N : ℤ) ∣ c := ⟨m, by linarith [E3.1]⟩
  refine ⟨⟨!![a, b; c, d], by simp [Matrix.det_fin_two, hdet]⟩, ?_, ?_⟩
  · refine CongruenceSubgroup.Gamma0_mem.mpr ?_
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd c N).mpr hcN
  · ext
    · simp [OrientedBasis.smul, ← h1]
    · simp [OrientedBasis.smul, ← h2]

/-- Part (iii): every cyclic subgroup of order $N$ modulo the lattice of $\omega$ is attained. -/
lemma OrientedBasis.exists_of_cyclic {N : ℕ} (hN : 1 ≤ N) (ω : OrientedBasis) {L : AddSubgroup ℂ}
    (hL : IsCyclicOfOrder N ω.lattice.toAddSubgroup L) :
    ∃ ω' : OrientedBasis, ω'.lattice = ω.lattice ∧ ω'.cyclicSubgroup N = L := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  obtain ⟨t, hLt, hk⟩ := gen_of_isCyclicOfOrder hL
  have hNt : (N : ℤ) • t ∈ ω.lattice.toAddSubgroup := (hk N).mpr dvd_rfl
  obtain ⟨a, b, hab⟩ := (ω.mem_lattice' _).mp hNt
  rw [zsmul_eq_mul] at hab
  push_cast at hab
  by_cases hg : Int.gcd a b = 0
  · obtain ⟨ha0, hb0⟩ := Int.gcd_eq_zero_iff.mp hg
    subst ha0 hb0
    have ht0 : t = 0 := by
      have : (N : ℂ) * t = 0 := by simpa using hab.symm
      exact (mul_eq_zero.mp this).resolve_left hN0
    have hN1 : N = 1 := by
      have := (hk 1).mp (by simp [ht0])
      exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this
    subst hN1
    refine ⟨ω, rfl, ?_⟩
    rw [hLt, ht0]
    unfold OrientedBasis.cyclicSubgroup
    apply le_antisymm
    · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
      exact AddSubgroup.mem_sup_left ((ω.mem_lattice' _).mpr ⟨0, 1, by simp⟩)
    · exact sup_le le_sup_left (by simp)
  · have hgpos : 0 < Int.gcd a b := Nat.pos_of_ne_zero hg
    obtain ⟨a1, b1, hcop, ha, hb⟩ := Int.exists_gcd_one hgpos
    set g0 : ℤ := (Int.gcd a b : ℤ) with hg0
    have ha' : (a : ℂ) = a1 * g0 := by exact_mod_cast ha
    have hb' : (b : ℂ) = b1 * g0 := by exact_mod_cast hb
    have hT : (N : ℂ) * t = g0 * (a1 * ω.1.1 + b1 * ω.1.2) := by
      rw [← hab, ha', hb']; ring
    have hcopg : IsCoprime g0 (N : ℤ) := by
      have hNne : (N : ℤ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have hpos : 0 < Int.gcd g0 N := Int.gcd_pos_of_ne_zero_right _ hNne
      obtain ⟨g', N', hc2, hg', hN'⟩ := Int.exists_gcd_one hpos
      set e : ℤ := (Int.gcd g0 N : ℤ) with he
      have hepos : 0 < e := Int.natCast_pos.mpr hpos
      have hN'pos : 0 < N' := by
        by_contra h
        push Not at h
        have : (0 : ℤ) < N := by exact_mod_cast hN
        nlinarith
      have hNt' : (N' : ℤ) • t ∈ ω.lattice.toAddSubgroup := by
        rw [ω.mem_lattice']
        refine ⟨g' * a1, g' * b1, ?_⟩
        have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast hepos.ne'
        have hN'C : (N : ℂ) = N' * e := by exact_mod_cast hN'
        have hg'C : (g0 : ℂ) = g' * e := by exact_mod_cast hg'
        have h1 : (e : ℂ) * ((N' : ℂ) * t) = e * (g' * (a1 * ω.1.1 + b1 * ω.1.2)) := by
          calc (e : ℂ) * ((N' : ℂ) * t) = (N : ℂ) * t := by rw [hN'C]; ring
            _ = g0 * (a1 * ω.1.1 + b1 * ω.1.2) := hT
            _ = _ := by rw [hg'C]; ring
        have h2 := mul_left_cancel₀ he0 h1
        rw [zsmul_eq_mul]
        push_cast
        linear_combination -h2
      obtain ⟨r, hr⟩ := (hk N').mp hNt'
      have h1 : N' * (e * r) = N' * 1 := by
        calc N' * (e * r) = (N' * e) * r := by ring
          _ = N * r := by rw [← hN']
          _ = N' * 1 := by rw [← hr]; ring
      have h2 : e * r = 1 := mul_left_cancel₀ hN'pos.ne' h1
      have he1 : e = 1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with h | h
        · exact h
        · omega
      rw [Int.isCoprime_iff_gcd_eq_one]
      have h3 : (Int.gcd g0 N : ℤ) = 1 := he1
      exact_mod_cast h3
    obtain ⟨u, v, huv⟩ := hcopg
    have hab_cop : IsCoprime a1 b1 := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    obtain ⟨δ, hδ1, hδ2⟩ := IsCoprime.exists_SL2_row hab_cop 1
    have hlat : (ω.act δ).lattice = ω.lattice := OrientedBasis.lattice_eq_of_smul rfl
    refine ⟨ω.act δ, hlat, ?_⟩
    have hw2 : (ω.act δ).1.2 = a1 * ω.1.1 + b1 * ω.1.2 := by
      show ((δ 1 0 : ℤ) : ℂ) * ω.1.1 + (δ 1 1 : ℤ) * ω.1.2 = _
      rw [hδ1, hδ2]
    unfold OrientedBasis.cyclicSubgroup
    rw [hlat, hLt, hw2]
    have hmem : (a1 * ω.1.1 + b1 * ω.1.2 : ℂ) ∈ ω.lattice.toAddSubgroup :=
      (ω.mem_lattice' _).mpr ⟨a1, b1, rfl⟩
    apply le_antisymm
    · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
      have e1 : (a1 * ω.1.1 + b1 * ω.1.2 : ℂ) / N =
          (u : ℤ) • t + (v : ℤ) • (a1 * ω.1.1 + b1 * ω.1.2 : ℂ) := by
        have huvC : (u : ℂ) * g0 + v * N = 1 := by exact_mod_cast huv
        rw [zsmul_eq_mul, zsmul_eq_mul]
        field_simp
        linear_combination -(a1 * ω.1.1 + b1 * ω.1.2 : ℂ) * huvC - (u : ℂ) * hT
      rw [e1]
      exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_right (AddSubgroup.zsmul_mem_zmultiples ..))
        (AddSubgroup.mem_sup_left (AddSubgroup.zsmul_mem _ hmem _))
    · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
      have e2 : t = g0 • ((a1 * ω.1.1 + b1 * ω.1.2 : ℂ) / N) := by
        rw [zsmul_eq_mul]
        field_simp
        linear_combination hT
      rw [e2]
      exact AddSubgroup.mem_sup_right (AddSubgroup.zsmul_mem_zmultiples ..)

/-- The bijection $\Gamma_0(N)\backslash M \to \{(\Lambda, S)\}$ (pdf p. 195), $(\omega_1, \omega_2) \mapsto
(\Lambda(\omega_1,\omega_2), \langle\omega_2/N\rangle)$, onto the pairs of a lattice and a cyclic subgroup of order
$N$ of $\mathbb C/\Lambda$: (i) the image subgroup is cyclic of order $N$; (ii) two bases have the same image if and
only if they are in the same $\Gamma_0(N)$-orbit; (iii) every pair $(\Lambda, S)$ with $\Lambda$ the lattice of an
oriented basis and $S$ cyclic of order $N$ is attained. -/
@[kb "milne2006ec" "Ch. V, §2, Γ₀(N)∖M ≅ pairs (Λ, S) (running text), pdf p. 195"]
theorem gamma0_orbits_eq_lattice_subgroup_pairs {N : ℕ} (hN : 1 ≤ N) :
    (∀ ω : OrientedBasis, IsCyclicOfOrder N ω.lattice.toAddSubgroup (ω.cyclicSubgroup N)) ∧
    (∀ ω ω' : OrientedBasis, (ω.lattice = ω'.lattice ∧ ω.cyclicSubgroup N = ω'.cyclicSubgroup N) ↔
      ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ω'.1 = OrientedBasis.smul γ ω.1) ∧
    ∀ (ω : OrientedBasis) (L : AddSubgroup ℂ), IsCyclicOfOrder N ω.lattice.toAddSubgroup L →
      ∃ ω' : OrientedBasis, ω'.lattice = ω.lattice ∧ ω'.cyclicSubgroup N = L :=
  ⟨fun ω => ω.isCyclicOfOrder hN,
    fun ω ω' => ⟨fun ⟨h1, h2⟩ => ω.exists_gamma0 hN h1 h2, fun ⟨γ, hγ, h⟩ =>
      ⟨(OrientedBasis.lattice_eq_of_smul h).symm,
        (OrientedBasis.cyclicSubgroup_eq_of_smul hN hγ h).symm⟩⟩,
    fun ω L hL => OrientedBasis.exists_of_cyclic hN ω hL⟩

end NumberFieldKB.MilneEC.V
