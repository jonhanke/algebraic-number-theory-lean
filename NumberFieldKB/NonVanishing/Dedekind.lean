import NumberFieldKB.NonVanishing.Euler
import NumberFieldKB.HeckeL.DedekindCont

/-!
# The Dedekind zeta function does not vanish on $\operatorname{Re}s\ge1$

$F$ is a number field and $\zeta_F$ = `dedekindZetaCont F` its continuation (holomorphic on
$\mathbb C\setminus\{1\}$ with residue $\rho_F$ at $1$).

* `dedekindZetaCont_eq_exp`: $\zeta_F(s) = \exp\sum_v-\log(1-N(v)^{-s})$ for $\operatorname{Re}s>1$ (the Euler product
  in the form of `Euler.lean`).
* **`dedekindZetaCont_ne_zero`**: $\zeta_F(s)\ne0$ for $\operatorname{Re}s\ge1$, $s\ne1$ (the 3-4-1 argument with
  $a = 1$; the pole at $s = 1$ gives $\zeta_F(1+x) = O(1/x)$).
* **`zetaRes`**: $(s-1)\zeta_F(s)$, extended by $\rho_F$ at $s = 1$, is entire (`differentiable_zetaRes`) and has
  no zero on $\operatorname{Re}s\ge1$ (`zetaRes_ne_zero`).
-/

open Complex Filter Topology Asymptotics IsDedekindDomain NumberField
open QuadFormsKB.NFEuler NumberFieldKB.HeckeL

namespace NumberFieldKB.NonVanishing

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

theorem localL_one_eq_eulerFactor (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    localL (1 : HeckeCharacter F) s v = eulerFactor (fun _ => 1) s v := by
  rw [localL_one, eulerFactor, one_mul]

/-- **$\zeta_F(s) = \exp\sum_v-\log(1-N(v)^{-s})$** for $\operatorname{Re}s>1$. -/
theorem dedekindZetaCont_eq_exp {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaCont F s = cexp (logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) s) := by
  rw [dedekindZetaCont_eq hs, ← heckeL_one_eq_dedekindZeta hs]
  have h1 := hasProd_heckeL (1 : HeckeCharacter F) (s := s) (by rw [shift_one, add_zero]; exact hs)
  have h2 := hasProd_eulerFactor (F := F) (a := fun _ => 1) (fun _ => by simp) hs
  refine h1.unique ?_
  convert h2 using 1
  funext v
  exact localL_one_eq_eulerFactor s v

/-- $\zeta_F(1+x) = O(1/x)$ as $x\to0^+$ (the pole at $s = 1$). -/
theorem dedekindZetaCont_isBigO_near_one :
    (fun x : ℝ ↦ dedekindZetaCont F (1 + x)) =O[𝓝[>] 0] fun x ↦ (1 : ℂ) / x := by
  have : (fun w : ℂ ↦ dedekindZetaCont F (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * dedekindZetaCont F (1 + w)) (𝓝[≠] 0) (𝓝 (dedekindZeta_residue F : ℂ)) := by
      convert (tendsto_sub_one_mul_dedekindZetaCont (F := F)).comp (f := fun w ↦ 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero, map_le_iff_le_comap] using
          ((Homeomorph.addLeft (1 : ℂ)).map_punctured_nhds_eq 0).le
    exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <| H.isBigO_one ℂ
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhdsGT_le_nhdsNE 0

/-- **$\zeta_F(s)\ne0$ for $\operatorname{Re}s\ge1$, $s\ne1$.** -/
@[kb "neukirch1999" "Ch. VII, §5 and §13 (ζ_K(s) ≠ 0 on Re s = 1) [unverified locator]"]
theorem dedekindZetaCont_ne_zero {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) : dedekindZetaCont F s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · rw [dedekindZetaCont_eq_exp hs]; exact Complex.exp_ne_zero _
  set t := s.im
  have hst : s = 1 + t * I := by
    apply Complex.ext <;> simp [t, ← hs]
  have ht : t ≠ 0 := fun h => hs1 (by rw [hst, h]; simp)
  rw [hst]
  refine ne_zero_of_three_four_one (Z := dedekindZetaCont F) (L₂ := dedekindZetaCont F) (fun x hx => ?_)
    dedekindZetaCont_isBigO_near_one
    (differentiableAt_dedekindZetaCont fun h => ht (by simpa using congrArg im h))
    (differentiableAt_dedekindZetaCont fun h => ht (by
      have := congrArg im h; simp at this; linarith)).continuousAt
  have hx1 : (1 : ℝ) < 1 + x := by linarith
  have h := one_le_norm_prod_three_four_one (F := F) (a := fun _ => 1) (fun _ => Or.inr (by simp)) hx1 t
  have e0 : dedekindZetaCont F (1 + x) = cexp (logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ))
      ((1 + x : ℝ) : ℂ)) := by
    rw [dedekindZetaCont_eq_exp (by simpa using hx1)]; push_cast; rfl
  have e1 : dedekindZetaCont F (1 + x + t * I) = cexp (logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ))
      (((1 + x : ℝ) : ℂ) + t * I)) := by
    rw [dedekindZetaCont_eq_exp (by simpa using hx1)]; push_cast; rfl
  have e2 : dedekindZetaCont F (1 + x + 2 * t * I) = cexp (logEuler (fun v : HeightOneSpectrum (𝓞 F) =>
      (fun _ => (1 : ℂ)) v ^ 2) (((1 + x : ℝ) : ℂ) + 2 * t * I)) := by
    rw [dedekindZetaCont_eq_exp (by simpa using hx1)]; simp only [one_pow]; push_cast; rfl
  rw [e0, e1, e2]
  exact h

/-! ### The entire function $(s-1)\zeta_F(s)$ -/

variable (F) in
/-- **$(s-1)\zeta_F(s)$, extended by the residue $\rho_F$ at $s = 1$**: an entire function (`differentiable_zetaRes`)
without zeros on $\operatorname{Re}s\ge1$ (`zetaRes_ne_zero`). -/
def zetaRes : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * dedekindZetaCont F s) 1 (dedekindZeta_residue F : ℂ)

theorem zetaRes_of_ne {s : ℂ} (hs : s ≠ 1) : zetaRes F s = (s - 1) * dedekindZetaCont F s := by
  rw [zetaRes, Function.update_of_ne hs]

theorem zetaRes_one : zetaRes F 1 = dedekindZeta_residue F := by
  rw [zetaRes, Function.update_self]

/-- **$(s-1)\zeta_F(s)$ is entire.** -/
theorem differentiable_zetaRes : Differentiable ℂ (zetaRes F) := by
  have hne : ∀ t : ℂ, t ≠ 1 → DifferentiableAt ℂ (zetaRes F) t := fun t ht =>
    ((differentiableAt_id.sub (differentiableAt_const 1)).mul
      (differentiableAt_dedekindZetaCont ht)).congr_of_eventuallyEq
      (by filter_upwards [eventually_ne_nhds ht] with u hu using zetaRes_of_ne hu)
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact hne s hs
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht using hne t ht
  · rw [zetaRes, continuousAt_update_same]
    exact tendsto_sub_one_mul_dedekindZetaCont

/-- **$(s-1)\zeta_F(s)\ne0$ for $\operatorname{Re}s\ge1$** (with the value $\rho_F>0$ at $s = 1$). -/
theorem zetaRes_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : zetaRes F s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h
  · rw [zetaRes_one]; exact_mod_cast (dedekindZeta_residue_pos F).ne'
  · rw [zetaRes_of_ne h]; exact mul_ne_zero (sub_ne_zero.mpr h) (dedekindZetaCont_ne_zero hs h)

end

end NumberFieldKB.NonVanishing
