import NumberFieldKB.MilneEC.Ch5Defs
import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Milne, *Elliptic Curves*, Chapter V: finite dimensionality of spaces of modular forms of level $\Gamma_0(N)$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §3–4: the spaces $M_{2k}(\Gamma_0(N))$ and
$S_{2k}(\Gamma_0(N))$ are finite-dimensional (used implicitly with the spectral theorem, pdf p. 214, and in
Corollary 3.4).

Proof: a Sturm-type bound. If $f \in M_w(\Gamma_0(N))$ has $q$-expansion of high order at $\infty$, its norm down to
level one (Mathlib's `ModularForm.norm`, a product of $f$ with forms bounded at $\infty$) has high order too, so it
vanishes by Mathlib's `ModularForm.sturm_bound_levelOne`, hence $f = 0$ (`ModularForm.norm_eq_zero_iff`). So a
finite initial segment of the $q$-expansion determines $f$.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold

namespace NumberFieldKB.MilneEC.V

variable {N : ℕ} [NeZero N]

open Asymptotics

local notation "𝕢" => Function.Periodic.qParam

/-- The first `B` coefficients of the `q`-expansion of `g` vanish exactly when the analytic order of the cusp
function of `g` at zero is at least `B`. -/
lemma coeff_vanish_iff_le_order {g : ℍ → ℂ} (B : ℕ) (hg : AnalyticAt ℂ (cuspFunction 1 g) 0) :
    (∀ m < B, (qExpansion 1 g).coeff m = 0) ↔ (B : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 g) 0 := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
  refine forall_congr' fun m => imp_congr_right fun _ => ?_
  simp [qExpansion_coeff, Nat.factorial_ne_zero]

/-- A function whose cusp function vanishes to order at least `B` at zero is `O(q^B)` at infinity. -/
lemma isBigO_qParam_pow_of_le_order {g : ℍ → ℂ} (B : ℕ) (hg : AnalyticAt ℂ (cuspFunction 1 g) 0)
    (hper : ∀ τ : ℍ, cuspFunction 1 g (𝕢 1 τ) = g τ)
    (h : (B : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 g) 0) :
    g =O[atImInfty] fun τ : ℍ => (𝕢 1 τ) ^ B := by
  obtain ⟨u, hu, hev⟩ := (natCast_le_analyticOrderAt hg).1 h
  have hu1 : u =O[𝓝 0] fun _ : ℂ => (1 : ℂ) := hu.continuousAt.isBigO
  have h0 : (fun z : ℂ => z ^ B * u z) =O[𝓝 0] fun z : ℂ => z ^ B := by
    simpa using (isBigO_refl (fun z : ℂ => z ^ B) (𝓝 0)).mul hu1
  have h2 : cuspFunction 1 g =ᶠ[𝓝 0] fun z => z ^ B * u z := by
    filter_upwards [hev] with z hz using by simpa using hz
  have h1 : cuspFunction 1 g =O[𝓝 0] fun z : ℂ => z ^ B := h2.trans_isBigO h0
  exact (h1.comp_tendsto (qParam_tendsto_atImInfty one_pos)).congr_left fun τ => hper τ

/-- Conversely, a function that is `O(q^B)` at infinity has a cusp function of order at least `B`. -/
lemma le_order_of_isBigO_qParam_pow {g : ℍ → ℂ} (B : ℕ) (hg : AnalyticAt ℂ (cuspFunction 1 g) 0)
    (hper : ∀ τ : ℍ, cuspFunction 1 g (𝕢 1 τ) = g τ)
    (hO : g =O[atImInfty] fun τ : ℍ => (𝕢 1 τ) ^ B) :
    (B : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 g) 0 := by
  by_cases htop : analyticOrderAt (cuspFunction 1 g) 0 = ⊤
  · rw [htop]; exact le_top
  have hΘ := hg.isTheta_pow_sub htop
  set n := analyticOrderNatAt (cuspFunction 1 g) 0 with hn
  have hΘ' : g =Θ[atImInfty] fun τ : ℍ => (𝕢 1 τ) ^ n := by
    have := hΘ.comp_tendsto (qParam_tendsto_atImInfty (h := 1) one_pos)
    simpa [Function.comp_def, hper] using this
  rw [← Nat.cast_analyticOrderNatAt htop, ← hn, Nat.cast_le]
  by_contra hlt
  push Not at hlt
  have hO2 : (fun τ : ℍ => (𝕢 1 τ) ^ n) =O[atImInfty] fun τ : ℍ => (𝕢 1 τ) ^ B :=
    hΘ'.symm.isBigO.trans hO
  obtain ⟨C, hC⟩ := hO2.bound
  have hq0 := qParam_tendsto_atImInfty (h := 1) one_pos
  have hnorm : Tendsto (fun τ : ℍ => ‖𝕢 1 τ‖) atImInfty (𝓝 0) := by simpa using hq0.norm
  have ht : Tendsto (fun τ : ℍ => C * ‖𝕢 1 τ‖ ^ (B - n)) atImInfty (𝓝 0) := by
    have := (hnorm.pow (B - n)).const_mul C
    rwa [zero_pow (by omega), mul_zero] at this
  have h1 : ∀ᶠ τ : ℍ in atImInfty, C * ‖𝕢 1 τ‖ ^ (B - n) < 1 := ht.eventually (gt_mem_nhds one_pos)
  obtain ⟨τ, h, h'⟩ := (hC.and h1).exists
  have hne : 𝕢 1 τ ≠ 0 := by simp [Function.Periodic.qParam, Complex.exp_ne_zero]
  have hpos : 0 < ‖𝕢 1 τ‖ ^ n := pow_pos (norm_pos_iff.2 hne) n
  have hB : ‖𝕢 1 τ‖ ^ B = ‖𝕢 1 τ‖ ^ n * ‖𝕢 1 τ‖ ^ (B - n) := by
    rw [← pow_add]; congr 1; omega
  rw [norm_pow, norm_pow, hB] at h
  nlinarith [mul_lt_mul_of_pos_right h' hpos]

omit [NeZero N] in
/-- The group `Γ₀(N)` contains the translation by one. -/
lemma one_mem_strictPeriods_Gamma0GL : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
  have h1 : (Gamma0GL N) = (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := rfl
  rw [h1, CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

/-- Every translate of a form of level `Γ₀(N)` by an element of `SL₂(ℤ)` is bounded at infinity. -/
lemma isBoundedAtImInfty_quotientFunc (w : ℤ) (f : ModularForm (Gamma0GL N) w)
    (q : 𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) :
    IsBoundedAtImInfty (SlashInvariantForm.quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨g, hg⟩ := r.2
    have hr : r.val⁻¹ = ((g⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by rw [← hg, ← map_inv]; rfl
    have := ModularFormClass.bdd_at_infty_slash f g⁻¹
    rw [ModularForm.SL_slash] at this
    simpa [SlashInvariantForm.quotientFunc_mk, hr] using this

/-- The Sturm-type bound for `Γ₀(N)`: a form of weight `w` whose first `B` coefficients vanish is zero. -/
lemma exists_sturm_bound_Gamma0 (w : ℤ) :
    ∃ B : ℕ, ∀ f : ModularForm (Gamma0GL N) w, (∀ m < B, (qExpansion 1 f).coeff m = 0) → f = 0 := by
  classical
  let _ : Fintype (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  refine ⟨(w * (Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12 + 1, fun f hf => ?_⟩
  set B := (w * (Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12 + 1 with hB
  have hΓ := one_mem_strictPeriods_Gamma0GL (N := N)
  obtain ⟨P, hPb, hFP⟩ : ∃ P : ℍ → ℂ, IsBoundedAtImInfty P ∧
      ⇑(ModularForm.norm 𝒮ℒ f) = ⇑f * P := by
    refine ⟨fun τ => ∏ q ∈ Finset.univ.erase
      (⟦1⟧ : 𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ), SlashInvariantForm.quotientFunc f q τ, ?_, ?_⟩
    · have := IsBigO.finsetProd (l := atImInfty)
        (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ))
        (f := fun q τ => SlashInvariantForm.quotientFunc f q τ) (g := fun _ _ => (1 : ℝ))
        (fun q _ => isBoundedAtImInfty_quotientFunc w f q)
      simp only [Finset.prod_const_one] at this
      exact this
    · ext τ
      rw [ModularForm.coe_norm, Finset.prod_apply,
        ← Finset.mul_prod_erase (Finset.univ : Finset (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ))
          (fun q => SlashInvariantForm.quotientFunc f q τ) (Finset.mem_univ ⟦1⟧)]
      simp [SlashInvariantForm.quotientFunc]
      exact Or.inl rfl
  have hanf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have hanF := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.norm 𝒮ℒ f) one_pos
    one_mem_strictPeriods_SL
  have hfper : ∀ τ : ℍ, cuspFunction 1 f (𝕢 1 τ) = f τ :=
    fun τ => SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero
  have hFper : ∀ τ : ℍ, cuspFunction 1 (ModularForm.norm 𝒮ℒ f) (𝕢 1 τ) = ModularForm.norm 𝒮ℒ f τ :=
    fun τ => SlashInvariantFormClass.eq_cuspFunction _ τ one_mem_strictPeriods_SL one_ne_zero
  have hbigf := isBigO_qParam_pow_of_le_order B hanf hfper
    ((coeff_vanish_iff_le_order B hanf).1 hf)
  have hbigF : (⇑(ModularForm.norm 𝒮ℒ f)) =O[atImInfty] fun τ : ℍ => (𝕢 1 τ) ^ B := by
    have hPb' : P =O[atImInfty] fun _ : ℍ => (1 : ℂ) := by
      obtain ⟨C, hC⟩ := (hPb : P =O[atImInfty] fun _ : ℍ => (1 : ℝ)).bound
      exact IsBigO.of_bound C (by simpa using hC)
    have := hbigf.mul hPb'
    rw [hFP]
    simp only [mul_one] at this
    exact this
  have hord := le_order_of_isBigO_qParam_pow B hanF hFper hbigF
  have hco := (coeff_vanish_iff_le_order B hanF).2 hord
  have hq : (B : ℕ∞) ≤ (qExpansion 1 (ModularForm.norm 𝒮ℒ f)).order :=
    PowerSeries.nat_le_order _ _ hco
  have hF0 : ModularForm.norm 𝒮ℒ f = 0 :=
    ModularForm.sturm_bound_levelOne (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hq)
  have := (ModularForm.norm_eq_zero_iff (𝒢 := Gamma0GL N) 𝒮ℒ (f := f)).1 hF0
  ext τ
  simpa using congr_fun this τ

/-- $M_w(\Gamma_0(N))$ is finite-dimensional. -/
instance finiteDimensional_modularForm_Gamma0 (w : ℤ) : FiniteDimensional ℂ (ModularForm (Gamma0GL N) w) := by
  obtain ⟨B, hB⟩ := exists_sturm_bound_Gamma0 (N := N) w
  have hΓ := one_mem_strictPeriods_Gamma0GL (N := N)
  let φ : ModularForm (Gamma0GL N) w →ₗ[ℂ] (Fin B → ℂ) :=
    { toFun := fun f i => (qExpansion 1 f).coeff i
      map_add' := fun f g => by ext i; simp [ModularForm.qExpansion_add one_pos hΓ]
      map_smul' := fun a f => by ext i; simp [ModularForm.qExpansion_smul one_pos hΓ] }
  refine Module.Finite.of_injective φ ((injective_iff_map_eq_zero φ).2 fun f hf => hB f fun m hm => ?_)
  simpa [φ] using congr_fun hf ⟨m, hm⟩

/-- $S_w(\Gamma_0(N))$ is finite-dimensional. -/
instance finiteDimensional_cuspForm_Gamma0 (w : ℤ) : FiniteDimensional ℂ (CuspForm (Gamma0GL N) w) :=
  Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

end NumberFieldKB.MilneEC.V
