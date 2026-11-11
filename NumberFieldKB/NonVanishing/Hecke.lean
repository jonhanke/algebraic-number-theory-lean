import NumberFieldKB.NonVanishing.NaturalOrder
import NumberFieldKB.NonVanishing.Landau
import NumberFieldKB.HeckeL.Completed
import QuadFormsKB.Siegel.RegProd
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.Algebra.Group.Units

/-!
# Hecke $L$-functions on $\operatorname{Re}s = 1$ and the Euler product at $s = 1$

$F$ is a number field, $\chi$ a Hecke character, $L(s,\chi)$ = `heckeL χ s` its Euler product and
`heckeLCont χ` its continuation, entire unless $\chi = \|\cdot\|^c$ (`differentiable_heckeLCont`).

* `heckeCoeff χ v` $= \chi_v(\varpi_v)$ if $\chi$ is unramified at $v$, $0$ otherwise; the Euler factor
  `localL χ s v` is `eulerFactor (heckeCoeff χ) s v` (`localL_eq_eulerFactor`), so for unitary $\chi$ the results of
  `Euler.lean`, `Landau.lean` and `NaturalOrder.lean` apply.
* Twisting by the norm: $L(s,\chi\|\cdot\|^c) = L(s+c,\chi)$ (`heckeL_mul_normPow`, and for the continuations
  `heckeLCont_mul_normPow`, by the identity theorem).
* **Non-vanishing on $\operatorname{Re}s = 1$** (`heckeLCont_ne_zero_of_re_eq_one`): for unitary $\chi$ that is not a
  power of the norm, $L(1+it,\chi)\ne0$ for every real $t$. If $\chi^2\ne\|\cdot\|^{-2it}$ this is the 3-4-1 argument
  (`heckeLCont_ne_zero_of_sq_ne`; $L(s,\chi^2)$ or $\zeta_F(s+c)$ is continuous at $1+2it$); otherwise
  $\chi' = \chi\|\cdot\|^{it}$ is quadratic, $L(1+it,\chi) = L(1,\chi')$, and Landau's argument applies
  (`heckeLCont_one_ne_zero_of_sq_eq_one`). For a general $\chi = \chi_0\|\cdot\|^\sigma$ the line is
  $\operatorname{Re}s = 1-\sigma$ (`heckeLCont_ne_zero_of_re_eq_one_sub_shift`). The excluded characters
  $\chi = \|\cdot\|^c$ have $L(s,\chi) = \zeta_F(s+c)$ (`heckeL_normPow`), covered by `dedekindZetaCont_ne_zero`
  (with the pole at $s = 1-c$).
* **The Euler product at $s = 1$ in the natural order** (`hasProd_localL_one_normOrder`): for $\chi\ne1$ of finite
  order, $\prod_{N(v)\le X}L_v(1,\chi)\to L(1,\chi)$ (the summation filter `normOrder`).
-/

open Complex Filter Topology IsDedekindDomain NumberField
open QuadFormsKB QuadFormsKB.NFEuler NumberFieldKB.HeckeL NumberFieldKB.HeckeCharacter
open scoped Classical

namespace NumberFieldKB.NonVanishing

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### The Euler coefficients of a Hecke character -/

/-- **The Euler coefficient** $a_\chi(v) = \chi_v(\varpi_v)$ at an unramified place, $0$ at a ramified one. -/
def heckeCoeff (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if χ.IsUnramifiedAt v then (χ.finiteComponent v (Analysis.ϖU v) : ℂ) else 0

theorem localL_eq_eulerFactor (χ : HeckeCharacter F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    localL χ s v = eulerFactor (heckeCoeff χ) s v := by
  unfold localL heckeCoeff eulerFactor
  by_cases h : χ.IsUnramifiedAt v
  · simp only [if_pos h]
  · simp [if_neg h]

theorem heckeCoeff_eq_zero_or_norm_eq_one {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (v : HeightOneSpectrum (𝓞 F)) :
    heckeCoeff χ v = 0 ∨ ‖heckeCoeff χ v‖ = 1 := by
  unfold heckeCoeff
  split_ifs
  · right
    rw [norm_finiteComponent_apply, (shift_eq_zero_iff χ).mpr hχ, Real.rpow_zero]
  · left; rfl

theorem norm_heckeCoeff_le {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (v : HeightOneSpectrum (𝓞 F)) :
    ‖heckeCoeff χ v‖ ≤ 1 := by
  rcases heckeCoeff_eq_zero_or_norm_eq_one hχ v with h | h
  · rw [h]; simp
  · exact h.le

/-- $L(s,\chi) = \exp(\texttt{logEuler}\ a_\chi\ s)$ for unitary $\chi$ and $\operatorname{Re}s>1$. -/
theorem heckeL_eq_exp {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) :
    heckeL χ s = cexp (logEuler (heckeCoeff χ) s) := by
  have h1 := hasProd_heckeL χ (s := s) (by rw [(shift_eq_zero_iff χ).mpr hχ, add_zero]; exact hs)
  have h2 := hasProd_eulerFactor (norm_heckeCoeff_le hχ) hs
  refine h1.unique ?_
  convert h2 using 1
  funext v
  exact localL_eq_eulerFactor χ s v

theorem heckeLCont_eq_exp {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) :
    heckeLCont χ s = cexp (logEuler (heckeCoeff χ) s) := by
  rw [heckeLCont_eq χ (by rw [(shift_eq_zero_iff χ).mpr hχ, add_zero]; exact hs)]
  exact heckeL_eq_exp hχ hs

/-- Powers of a Hecke character act by powers. -/
theorem pow_apply_aux (χ : HeckeCharacter F) (n : ℕ) (c : IdeleClassGroup (𝓞 F) F) :
    (χ ^ n) c = (χ c) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ContinuousMonoidHom.mul_apply, ih, pow_succ]

/-- The finite component of a product. -/
theorem finiteComponent_mul_aux (χ ψ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    (χ * ψ).finiteComponent v u = χ.finiteComponent v u * ψ.finiteComponent v u := by
  simp only [finiteComponent_apply, ContinuousMonoidHom.mul_apply]

/-- The finite component of a power. -/
theorem finiteComponent_pow_aux (χ : HeckeCharacter F) (n : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    (χ ^ n).finiteComponent v u = χ.finiteComponent v u ^ n := by
  simp only [finiteComponent_apply, pow_apply_aux]

/-- On the unramified places, $a_{\chi^2} = a_\chi^2$. -/
theorem heckeCoeff_sq (χ : HeckeCharacter F) {v : HeightOneSpectrum (𝓞 F)} (hv : χ.IsUnramifiedAt v) :
    heckeCoeff (χ ^ 2) v = heckeCoeff χ v ^ 2 := by
  have hv2 : (χ ^ 2).IsUnramifiedAt v := fun u hu => by
    rw [finiteComponent_pow_aux, hv u hu, one_pow]
  unfold heckeCoeff
  rw [if_pos hv2, if_pos hv, finiteComponent_pow_aux]
  push_cast
  rfl

/-- **Changing the coefficients at finitely many places**: if $a = b$ off a finite set $S$ and $|a|,|b|\le1$, then
$\exp(\texttt{logEuler}\ a\ s) = \exp(\texttt{logEuler}\ b\ s)\prod_{v\in S}(1-b(v)N(v)^{-s})/(1-a(v)N(v)^{-s})$ for
$\operatorname{Re}s>1$. -/
theorem exp_logEuler_congr_finite {a b : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) (hb : ∀ v, ‖b v‖ ≤ 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, a v = b v) {s : ℂ} (hs : 1 < s.re) :
    cexp (logEuler a s) =
      cexp (logEuler b s) * ∏ v ∈ S, (1 - b v * nps v s) / (1 - a v * nps v s) := by
  set g : HeightOneSpectrum (𝓞 F) → ℂ :=
    fun v => if v ∈ S then (1 - b v * nps v s) / (1 - a v * nps v s) else 1 with hg
  have hgp : HasProd g (∏ v ∈ S, g v) := hasProd_prod_of_ne_finset_one fun v hv => by simp [hg, hv]
  have hprod : ∏ v ∈ S, g v = ∏ v ∈ S, (1 - b v * nps v s) / (1 - a v * nps v s) :=
    Finset.prod_congr rfl fun v hv => by simp [hg, hv]
  rw [hprod] at hgp
  have h2 := (hasProd_eulerFactor hb hs).mul hgp
  refine (hasProd_eulerFactor ha hs).unique ?_
  convert h2 using 1
  funext v
  by_cases hv : v ∈ S
  · have hb0 := one_sub_mul_nps_ne_zero hb v hs.le
    simp only [hg, if_pos hv, eulerFactor]
    rw [← mul_div_assoc, inv_mul_cancel₀ hb0, one_div]
  · simp only [hg, if_neg hv, mul_one, eulerFactor, hS v hv]

/-! ### Twisting by the norm -/

theorem isUnramifiedAt_mul_normPow_iff (χ : HeckeCharacter F) (c : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    (χ * normPow F c).IsUnramifiedAt v ↔ χ.IsUnramifiedAt v := by
  constructor
  · intro h u hu
    have := h u hu
    rwa [finiteComponent_mul_aux, isUnramifiedAt_normPow c v u hu, mul_one] at this
  · intro h u hu
    rw [finiteComponent_mul_aux, h u hu, isUnramifiedAt_normPow c v u hu, one_mul]

/-- $(\|\cdot\|^c)_v(\varpi_v) = N(v)^{-c}$. -/
theorem normPow_finiteComponent_ϖU (c : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    (((normPow F c).finiteComponent v (Analysis.ϖU v) : ℂˣ) : ℂ) = ((normP v : ℝ) : ℂ) ^ (-c) := by
  rw [finiteComponent_normPow, ← Ideles.distribHaarChar_adicCompletion,
    show (MeasureTheory.distribHaarChar (v.adicCompletion F) (Analysis.ϖU v) : ℝ) = Analysis.modV v from rfl,
    LocalZeta.modV_cpow]

theorem heckeCoeff_mul_normPow (χ : HeckeCharacter F) (c : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    heckeCoeff (χ * normPow F c) v = heckeCoeff χ v * ((normP v : ℝ) : ℂ) ^ (-c) := by
  unfold heckeCoeff
  by_cases h : χ.IsUnramifiedAt v
  · rw [if_pos ((isUnramifiedAt_mul_normPow_iff χ c v).mpr h), if_pos h, finiteComponent_mul_aux, Units.val_mul,
      normPow_finiteComponent_ϖU]
  · rw [if_neg (fun h' => h ((isUnramifiedAt_mul_normPow_iff χ c v).mp h')), if_neg h, zero_mul]

/-- **$L(s,\chi\|\cdot\|^c) = L(s+c,\chi)$** (Euler products). -/
theorem heckeL_mul_normPow (χ : HeckeCharacter F) (c s : ℂ) : heckeL (χ * normPow F c) s = heckeL χ (s + c) := by
  unfold heckeL
  congr 1
  funext v
  unfold localL
  by_cases h : χ.IsUnramifiedAt v
  · rw [if_pos ((isUnramifiedAt_mul_normPow_iff χ c v).mpr h), if_pos h]
    congr 2
    have hN : ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normP_pos' v).ne'
    rw [GlobalZeta.rV, GlobalZeta.rV, finiteComponent_mul_aux, Units.val_mul, normPow_finiteComponent_ϖU, neg_add, cpow_add _ _ hN]
    change _ = _ * (((normP v : ℝ) : ℂ) ^ (-s) * ((normP v : ℝ) : ℂ) ^ (-c))
    ring
  · rw [if_neg (fun h' => h ((isUnramifiedAt_mul_normPow_iff χ c v).mp h')), if_neg h]

theorem mul_normPow_ne_normPow {χ : HeckeCharacter F} (hnp : ∀ d : ℂ, χ ≠ normPow F d) (c : ℂ) :
    ∀ d : ℂ, χ * normPow F c ≠ normPow F d := by
  intro d h
  refine hnp (d + -c) ?_
  rw [normPow_add, normPow_neg, ← h]
  group

/-- **$L(s,\chi\|\cdot\|^c) = L(s+c,\chi)$ for the continuations** (both entire; the identity theorem). -/
theorem heckeLCont_mul_normPow {χ : HeckeCharacter F} (hnp : ∀ d : ℂ, χ ≠ normPow F d) (c s : ℂ) :
    heckeLCont (χ * normPow F c) s = heckeLCont χ (s + c) := by
  have hd1 : Differentiable ℂ (heckeLCont (χ * normPow F c)) :=
    differentiable_heckeLCont (mul_normPow_ne_normPow hnp c)
  have hd2 : Differentiable ℂ fun s => heckeLCont χ (s + c) :=
    (differentiable_heckeLCont hnp).comp (differentiable_id.add_const c)
  set R : ℝ := |χ.shift| + |c.re| + 2 with hR
  have hopen : IsOpen {w : ℂ | 1 < w.re + (χ.shift + c.re)} := isOpen_lt continuous_const (by fun_prop)
  have hz : ((R : ℝ) : ℂ) ∈ {w : ℂ | 1 < w.re + (χ.shift + c.re)} := by
    simp only [Set.mem_setOf_eq, ofReal_re]
    have := neg_abs_le χ.shift
    have := neg_abs_le c.re
    have := abs_nonneg χ.shift
    have := abs_nonneg c.re
    rw [hR]; linarith
  have key := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U := Set.univ)
    (fun z _ => hd1.analyticAt z) (fun z _ => hd2.analyticAt z) isPreconnected_univ
    (Set.mem_univ ((R : ℝ) : ℂ)) (Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => ?_)
  · exact key (Set.mem_univ s)
  · have hw' : 1 < w.re + (χ.shift + c.re) := hw
    have hw1 : 1 < w.re + (χ * normPow F c).shift := by rw [shift_mul, shift_normPow]; linarith
    have hw2 : 1 < (w + c).re + χ.shift := by rw [add_re]; linarith
    show heckeLCont (χ * normPow F c) w = heckeLCont χ (w + c)
    rw [heckeLCont_eq _ hw1, heckeL_mul_normPow, heckeLCont_eq _ hw2]

/-! ### The 3-4-1 argument -/

/-- Powers of a unitary character are unitary. -/
theorem isUnitary_pow_aux {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (n : ℕ) : (χ ^ n).IsUnitary := fun c => by
  rw [pow_apply_aux, Units.val_pow_eq_pow_val, norm_pow, hχ c, one_pow]

/-- $\exp(\texttt{logEuler}\ a_\chi^2)$ extends continuously to $s_0$ unless $\chi^2 = \|\cdot\|^{1-s_0}$ (the pole of
$\zeta_F(s+c)$ when $\chi^2 = \|\cdot\|^c$). -/
theorem exists_continuousAt_eq_exp_sq {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {s₀ : ℂ}
    (h : χ ^ 2 ≠ normPow F (1 - s₀)) :
    ∃ M : ℂ → ℂ, ContinuousAt M s₀ ∧ ∀ s : ℂ, 1 < s.re → M s = cexp (logEuler (fun v => heckeCoeff χ v ^ 2) s) := by
  have hψ : (χ ^ 2).IsUnitary := isUnitary_pow_aux hχ 2
  have ha1 := norm_heckeCoeff_le hχ
  have hb1 := norm_heckeCoeff_le hψ
  have ha2 : ∀ v, ‖heckeCoeff χ v ^ 2‖ ≤ 1 := fun v => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (ha1 v)
  have hS : ∀ v ∉ ramSet χ, heckeCoeff χ v ^ 2 = heckeCoeff (χ ^ 2) v := fun v hv =>
    (heckeCoeff_sq χ (not_not.mp (fun h' => hv (mem_ramSet.mpr h')))).symm
  set P : ℂ → ℂ := fun s => ∏ v ∈ ramSet χ, (1 - heckeCoeff (χ ^ 2) v * nps v s) with hP
  have hkey : ∀ s : ℂ, 1 < s.re →
      cexp (logEuler (fun v => heckeCoeff χ v ^ 2) s) = cexp (logEuler (heckeCoeff (χ ^ 2)) s) * P s := by
    intro s hs
    rw [exp_logEuler_congr_finite ha2 hb1 (ramSet χ) hS hs]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    have h0 : heckeCoeff χ v = 0 := by
      unfold heckeCoeff; rw [if_neg (mem_ramSet.mp hv)]
    simp [h0]
  have hPc : Continuous P := by
    refine continuous_finsetProd _ fun v _ => ?_
    have : Continuous fun s : ℂ => nps v s :=
      Continuous.const_cpow continuous_neg (Or.inl (by exact_mod_cast (normP_pos' v).ne'))
    exact continuous_const.sub (continuous_const.mul this)
  by_cases hex : ∃ d : ℂ, χ ^ 2 = normPow F d
  · obtain ⟨d, hd⟩ := hex
    have hd0 : d.re = 0 := (isUnitary_normPow_iff d).mp (by rw [← hd]; exact hψ)
    have hne : s₀ + d ≠ 1 := fun h1 => h (by rw [hd]; congr 1; linear_combination h1)
    refine ⟨fun s => dedekindZetaCont F (s + d) * P s, ?_, fun s hs => ?_⟩
    · exact (ContinuousAt.comp (g := dedekindZetaCont F) (f := fun s => s + d)
        (differentiableAt_dedekindZetaCont hne).continuousAt
        (continuousAt_id.add continuousAt_const)).mul hPc.continuousAt
    · show dedekindZetaCont F (s + d) * P s = _
      rw [hkey s hs]
      congr 1
      have hs' : 1 < (s + d).re := by rw [add_re, hd0]; linarith
      rw [dedekindZetaCont_eq hs', ← heckeL_one_eq_dedekindZeta hs', ← heckeL_normPow, ← hd,
        heckeL_eq_exp hψ hs]
  · push_neg at hex
    refine ⟨fun s => heckeLCont (χ ^ 2) s * P s,
      ((differentiable_heckeLCont hex).continuous.mul hPc).continuousAt, fun s hs => ?_⟩
    show heckeLCont (χ ^ 2) s * P s = _
    rw [hkey s hs, heckeLCont_eq_exp hψ hs]

/-- **The 3-4-1 case**: $L(1+it,\chi)\ne0$ if $\chi$ is unitary, not a power of the norm, and $\chi^2\ne\|\cdot\|^{-2it}$. -/
theorem heckeLCont_ne_zero_of_sq_ne {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (hnp : ∀ c : ℂ, χ ≠ normPow F c)
    (t : ℝ) (hsq : χ ^ 2 ≠ normPow F (-(2 * t * I))) : heckeLCont χ (1 + t * I) ≠ 0 := by
  obtain ⟨M, hMc, hM⟩ := exists_continuousAt_eq_exp_sq hχ (s₀ := 1 + 2 * t * I)
    (by rw [show (1 : ℂ) - (1 + 2 * t * I) = -(2 * t * I) by ring]; exact hsq)
  refine ne_zero_of_three_four_one (Z := dedekindZetaCont F) (L₂ := M) (fun x hx => ?_)
    dedekindZetaCont_isBigO_near_one ((differentiable_heckeLCont hnp) _) hMc
  have hx1 : (1 : ℝ) < 1 + x := by linarith
  have h := one_le_norm_prod_three_four_one (F := F) (a := heckeCoeff χ)
    (fun v => heckeCoeff_eq_zero_or_norm_eq_one hχ v) hx1 t
  have e0 : dedekindZetaCont F (1 + x) = cexp (logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ))
      ((1 + x : ℝ) : ℂ)) := by
    rw [dedekindZetaCont_eq_exp (by simpa using hx1)]; push_cast; try rfl
  have e1 : heckeLCont χ (1 + x + t * I) = cexp (logEuler (heckeCoeff χ) (((1 + x : ℝ) : ℂ) + t * I)) := by
    rw [heckeLCont_eq_exp hχ (by simpa using hx1)]; push_cast; try rfl
  have e2 : M (1 + x + 2 * t * I) =
      cexp (logEuler (fun v => heckeCoeff χ v ^ 2) (((1 + x : ℝ) : ℂ) + 2 * t * I)) := by
    rw [hM _ (by simpa using hx1)]; push_cast; try rfl
  rw [e0, e1, e2]
  exact h

/-! ### Quadratic characters: Landau's argument -/

theorem isUnitary_of_pow_eq_one {χ : HeckeCharacter F} {n : ℕ} (hn : n ≠ 0) (h : χ ^ n = 1) : χ.IsUnitary := by
  intro c
  have h1 : ‖((χ ^ n) c : ℂ)‖ = 1 := by rw [h]; simp
  rw [pow_apply_aux, Units.val_pow_eq_pow_val, norm_pow] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1

/-- **$L(1,\chi)\ne0$ for a quadratic character** $\chi$ ($\chi^2 = 1$, $\chi$ not a power of the norm, i.e. $\chi\ne1$). -/
theorem heckeLCont_one_ne_zero_of_sq_eq_one {χ : HeckeCharacter F} (hsq : χ ^ 2 = 1)
    (hnp : ∀ c : ℂ, χ ≠ normPow F c) : heckeLCont χ 1 ≠ 0 := by
  have hχ := isUnitary_of_pow_eq_one (n := 2) two_ne_zero hsq
  refine landau_ne_zero (a := heckeCoeff χ) (fun v => ?_) (differentiable_heckeLCont hnp)
    fun s hs => heckeLCont_eq_exp hχ hs
  by_cases hv : χ.IsUnramifiedAt v
  · right
    have h2 := heckeCoeff_sq χ hv
    rw [hsq] at h2
    have hu1 : (1 : HeckeCharacter F).IsUnramifiedAt v := fun u _ => by simp [finiteComponent_apply]
    have h1 : heckeCoeff (1 : HeckeCharacter F) v = 1 := by
      unfold heckeCoeff
      rw [if_pos hu1]
      simp [finiteComponent_apply]
    rw [h1] at h2
    have : (heckeCoeff χ v - 1) * (heckeCoeff χ v + 1) = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  · left
    unfold heckeCoeff
    rw [if_neg hv]

/-! ### Non-vanishing on $\operatorname{Re}s = 1$ -/

/-- **$L(s,\chi)\ne0$ on $\operatorname{Re}s = 1$** for every unitary Hecke character $\chi$ that is not a power of the
norm (for $\chi = \|\cdot\|^{c}$, $L(s,\chi) = \zeta_F(s+c)$: `dedekindZetaCont_ne_zero`). -/
@[kb "neukirch1999" "Ch. VII, §13 (non-vanishing of L(s, χ) on Re s = 1) [unverified locator]"]
theorem heckeLCont_ne_zero_of_re_eq_one {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (hnp : ∀ c : ℂ, χ ≠ normPow F c)
    {s : ℂ} (hs : s.re = 1) : heckeLCont χ s ≠ 0 := by
  set t := s.im
  have hst : s = 1 + t * I := by
    apply Complex.ext <;> simp [t, hs]
  rw [hst]
  by_cases hsq : χ ^ 2 = normPow F (-(2 * t * I))
  · have h2 : (χ * normPow F (t * I)) ^ 2 = 1 := by
      rw [mul_pow, hsq, pow_two, ← normPow_add, ← normPow_add]
      rw [show -(2 * (t : ℂ) * I) + (t * I + t * I) = 0 by ring, normPow_zero]
    have := heckeLCont_one_ne_zero_of_sq_eq_one h2 (mul_normPow_ne_normPow hnp _)
    rwa [heckeLCont_mul_normPow hnp] at this
  · exact heckeLCont_ne_zero_of_sq_ne hχ hnp t hsq

theorem heckeLCont_ne_zero_of_one_le_re {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (hnp : ∀ c : ℂ, χ ≠ normPow F c)
    {s : ℂ} (hs : 1 ≤ s.re) : heckeLCont χ s ≠ 0 := by
  rcases hs.lt_or_eq with h | h
  · have h' : 1 < s.re + χ.shift := by rw [(shift_eq_zero_iff χ).mpr hχ, add_zero]; exact h
    rw [heckeLCont_eq χ h']
    exact heckeL_ne_zero χ h'
  · exact heckeLCont_ne_zero_of_re_eq_one hχ hnp h.symm

/-- **Any Hecke character** $\chi = \chi_0\|\cdot\|^\sigma$ ($\sigma$ = `χ.shift`) that is not a power of the norm:
$L(s,\chi)\ne0$ on the line $\operatorname{Re}s = 1-\sigma$. -/
theorem heckeLCont_ne_zero_of_re_eq_one_sub_shift {χ : HeckeCharacter F} (hnp : ∀ c : ℂ, χ ≠ normPow F c)
    {s : ℂ} (hs : s.re = 1 - χ.shift) : heckeLCont χ s ≠ 0 := by
  have hnp0 : ∀ c : ℂ, χ.unitaryPart ≠ normPow F c := by
    intro c hc
    apply hnp (c + χ.shift)
    rw [normPow_add, ← hc, unitaryPart_mul_normPow_shift]
  have e : heckeLCont χ s = heckeLCont (χ.unitaryPart * normPow F χ.shift) s := by
    rw [unitaryPart_mul_normPow_shift]
  rw [e, heckeLCont_mul_normPow hnp0]
  exact heckeLCont_ne_zero_of_re_eq_one (isUnitary_unitaryPart χ) hnp0 (by simp [hs])

/-! ### Characters of finite order: the Euler product at $s = 1$ -/

theorem ne_normPow_of_pow_eq_one {χ : HeckeCharacter F} {n : ℕ} (hn : n ≠ 0) (h : χ ^ n = 1) (hne : χ ≠ 1) :
    ∀ c : ℂ, χ ≠ normPow F c := by
  intro c hc
  subst hc
  have hpow : ∀ m : ℕ, (normPow F c) ^ m = normPow F (m * c) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, ← normPow_add]; congr 1; push_cast; ring
  have he : normPow F (n * c) = normPow F 0 := by rw [← hpow, h, normPow_zero]
  have hc0 : (n : ℂ) * c = 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    rcases w.isReal_or_isComplex with hw | hw
    · have h1 : (normPow F (n * c)).realExponent hw = (normPow F 0).realExponent hw := by rw [he]
      rw [realExponent_normPow, realExponent_normPow] at h1
      exact h1
    · have h1 : (normPow F (n * c)).complexExponent hw = (normPow F 0).complexExponent hw := by rw [he]
      rw [complexExponent_normPow, complexExponent_normPow] at h1
      linear_combination h1 / 2
  have hc00 : c = 0 := by
    rcases mul_eq_zero.mp hc0 with h0 | h0
    · exact absurd (by exact_mod_cast h0 : n = 0) hn
    · exact h0
  apply hne
  rw [hc00, normPow_zero]

theorem eulerData_heckeCoeff {χ : HeckeCharacter F} {n : ℕ} (hn : n ≠ 0) (h : χ ^ n = 1) (hne : χ ≠ 1) :
    EulerData (heckeCoeff χ) (heckeLCont χ) := by
  have hχ := isUnitary_of_pow_eq_one hn h
  have hnp := ne_normPow_of_pow_eq_one hn h hne
  have hd := differentiable_heckeLCont hnp
  refine ⟨norm_heckeCoeff_le hχ, ⟨{s | heckeLCont χ s ≠ 0}, ?_,
    fun s hs => heckeLCont_ne_zero_of_one_le_re hχ hnp hs, hd.differentiableOn, fun s hs => hs⟩,
    fun s hs => heckeLCont_eq_exp hχ hs⟩
  exact (isClosed_singleton.isOpen_compl).preimage hd.continuous

/-- **The Euler product of $L(1,\chi)$ in the natural order**, for a Hecke character $\chi\ne1$ of finite order:
$\prod_{N(v)\le X}L_v(1,\chi)\to L(1,\chi)$, i.e. `HasProd` for the summation filter `normOrder F`. -/
@[kb "neukirch1999" "Ch. VII, §13 (prime ideal theorem for χ; here via Newman's Tauberian theorem) [unverified locator]"]
theorem hasProd_localL_one_normOrder {χ : HeckeCharacter F} {n : ℕ} (hn : n ≠ 0) (h : χ ^ n = 1) (hne : χ ≠ 1) :
    HasProd (localL χ 1) (heckeLCont χ 1) (QuadFormsKB.RegProd.normOrder F) := by
  have hE := tendsto_prod_eulerFactor_one (eulerData_heckeCoeff hn h hne)
  unfold HasProd
  show Tendsto _ (Filter.map (primesNormLe F) atTop) _
  rw [Filter.tendsto_map'_iff]
  refine hE.congr fun X => ?_
  show _ = ∏ v ∈ primesNormLe F X, localL χ 1 v
  exact Finset.prod_congr rfl fun v _ => (localL_eq_eulerFactor χ 1 v).symm

end

end NumberFieldKB.NonVanishing
