import NumberFieldKB.GlobalZeta.Unfolding
import QuadFormsKB.Tamagawa.IdealEuler
import QuadFormsKB.Analysis.NFEulerProduct

/-!
# Absolute convergence of the global zeta integral

$F$ is a number field, $n = [F:\mathbb Q]$. The global zeta integral converges absolutely for
$\operatorname{Re}s+\sigma>1$, $\sigma$ the shift of the Hecke character ($|\chi| = \|\cdot\|^\sigma$). Tate proves this
with the Euler product; we use instead the ideal model of the ideles (QuadFormsKB's `lintegral_tamIdeles_ideal`,
ported in `QFPort.lean`): a function of $(x_\infty,\mathfrak a(x_f))$ integrates to
$|d_F|^{-1/2}2^{r_2}\sum_{\mathfrak b}\int_{F_\infty}G(x,\mathfrak b)\,dx/N(x)$.

* **`InBox e 𝔞`**: $\operatorname{ord}_v\mathfrak a\ge -e_v$ for every $v$ ($\mathfrak a\subseteq\prod_v\mathfrak p_v^{-e_v}$).
  **`summable_inBox`**: $\sum_{\mathfrak a\in\text{box}}N\mathfrak a^{-\sigma}<\infty$ for $\sigma>1$, by QuadFormsKB's Euler
  product over the fractional ideals (`hasSum_finsupp_finprod`) and the Euler product of $\zeta_F$
  (`hasProd_dedekindZeta`).
* **`lintegral_arch_lt_top`**: $\int_{F_\infty}(1+\|x\|)^{-N}N(x)^{\sigma-1}dx<\infty$ for $\sigma\ge1$, $N>n\sigma$.
* **`IsMajorized Φ`**: $\Phi$ is measurable on $\mathbb A_F^\times$ and, for every $N$,
  $|\Phi(x)|\le C(1+\|x_\infty\|)^{-N}\mathbf 1[\mathfrak a(x_f)\in\text{box}]$. Factorizable Schwartz–Bruhat functions
  and their Fourier transforms have this property (`SchwartzBruhat.isMajorized`,
  `SchwartzBruhat.isMajorized_fourier`).
* **`lintegral_majorant_lt_top`**, **`integrable_globalZetaIntegrand`**: absolute convergence of $Z(\Phi,\chi,s)$ for
  $\operatorname{Re}s+\sigma>1$.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal nonZeroDivisors

namespace NumberFieldKB.GlobalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "V" => mixedSpace F
local notation "FI" => IdeleClass.FracIdeal F

/-! ### Sums over a box of fractional ideals -/

/-- **The box** $\{\mathfrak a : \operatorname{ord}_v\mathfrak a\ge -e_v\ \forall v\}$, i.e. $\mathfrak a\subseteq\prod_v\mathfrak p_v^{-e_v}$. -/
def InBox (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) (𝔞 : FI) : Prop :=
  ∀ v, -e v ≤ FractionalIdeal.count F v (𝔞 : FractionalIdeal (𝓞 F)⁰ F)

/-- $N\mathfrak p_v$ as a real number. -/
abbrev qN (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_qN (v : HeightOneSpectrum (𝓞 F)) : 1 < qN v := one_lt_absNorm v

theorem qN_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < qN v := zero_lt_one.trans (one_lt_qN v)

/-- The local factor $j\mapsto\mathbf 1[j\ge -e_v]\,N\mathfrak p_v^{-\sigma j}$. -/
def boxFactor (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) : ℝ :=
  if -e v ≤ j then qN v ^ (-(σ * j)) else 0

theorem boxFactor_nonneg (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) (σ : ℝ) (v) (j : ℤ) : 0 ≤ boxFactor e σ v j := by
  unfold boxFactor; split_ifs
  · exact (Real.rpow_pos_of_pos (qN_pos v) _).le
  · exact le_rfl

theorem hasSum_boxFactor (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) {σ : ℝ} (hσ : 0 < σ) (v : HeightOneSpectrum (𝓞 F)) :
    HasSum (boxFactor e σ v) (qN v ^ (σ * e v) * (1 - qN v ^ (-σ))⁻¹) := by
  set r := qN v ^ (-σ) with hr
  have hq := qN_pos v
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hq _).le
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (one_lt_qN v) (neg_lt_zero.mpr hσ)
  have hg : HasSum (fun k : ℕ => qN v ^ (σ * e v) * r ^ k) (qN v ^ (σ * e v) * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left _
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - e v := fun a b h => by
    simpa using h
  have hsupp : ∀ j ∉ Set.range fun k : ℕ => (k : ℤ) - e v, boxFactor e σ v j = 0 := by
    intro j hj
    unfold boxFactor
    rw [if_neg]
    intro hle
    exact hj ⟨(j + e v).toNat, show ((j + e v).toNat : ℤ) - e v = j by omega⟩
  refine (hinj.hasSum_iff hsupp).mp ?_
  convert hg using 1
  funext k
  simp only [Function.comp_apply, boxFactor]
  rw [if_pos (by omega), hr, ← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

theorem hasProd_boxFactor (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun v => ∑' j, boxFactor e σ v j)
      ((∏ v ∈ e.support, qN v ^ (σ * e v)) * NFEuler.dedekindZetaR F σ) := by
  have h1 : HasProd (fun v : HeightOneSpectrum (𝓞 F) => qN v ^ (σ * e v)) (∏ v ∈ e.support, qN v ^ (σ * e v)) :=
    hasProd_prod_of_ne_finset_one fun v hv => by
      rw [Finsupp.notMem_support_iff.mp hv]; simp
  have h2 := (h1.mul (NFEuler.hasProd_dedekindZeta (F := F) hσ))
  refine h2.congr_fun fun v => ?_
  rw [(hasSum_boxFactor e (zero_lt_one.trans hσ) v).tsum_eq]

/-- The Euler product over the box: $\prod_v$ of the local factors at $\operatorname{ord}_v\mathfrak a$ is
$\mathbf 1[\mathfrak a\in\text{box}]\,N\mathfrak a^{-\sigma}$. -/
theorem finprod_boxFactor (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) (σ : ℝ) (𝔞 : FI) :
    ∏ᶠ v, boxFactor e σ v (fracIdealEquiv F 𝔞 v) =
      if InBox e 𝔞 then IdeleClass.idealNorm F 𝔞 ^ (-σ) else 0 := by
  set x := fracIdealEquiv F 𝔞
  have hx : ∀ v, x v = FractionalIdeal.count F v (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := fun v =>
    fracIdealEquiv_apply F 𝔞 v
  set T := x.support ∪ e.support
  have hT : ∀ v ∉ T, x v = 0 ∧ e v = 0 := fun v hv => by
    simp only [T, Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hv
    exact hv
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) fun v hv => by
    by_contra h
    apply hv
    obtain ⟨h1, h2⟩ := hT v h
    simp [boxFactor, h1, h2]]
  split_ifs with hbox
  · have hN : IdeleClass.idealNorm F 𝔞 = ∏ v ∈ T, qN v ^ x v := by
      rw [idealNorm_eq_finprod, finprod_eq_prod_of_mulSupport_subset _ (s := T) fun v hv => by
        by_contra h
        apply hv
        simp [← hx, (hT v h).1]]
      exact Finset.prod_congr rfl fun v _ => by rw [hx]
    rw [hN, ← Real.finsetProd_rpow _ _ fun v _ => zpow_nonneg (qN_pos v).le _]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [boxFactor, if_pos (by rw [hx]; exact hbox v), ← Real.rpow_intCast, ← Real.rpow_mul (qN_pos v).le]
    ring_nf
  · simp only [InBox, not_forall, not_le] at hbox
    obtain ⟨v, hv⟩ := hbox
    refine Finset.prod_eq_zero (i := v) ?_ ?_
    · by_contra h
      obtain ⟨h1, h2⟩ := hT v h
      rw [← hx, h1, h2] at hv
      simp at hv
    · rw [boxFactor, if_neg (by rw [hx]; omega)]

/-- **$\sum_{\mathfrak a\in\text{box}}N\mathfrak a^{-\sigma}$ converges for $\sigma>1$.** -/
theorem summable_inBox (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun 𝔞 : FI => if InBox e 𝔞 then IdeleClass.idealNorm F 𝔞 ^ (-σ) else 0 := by
  have hE := hasSum_finsupp_finprod (boxFactor e σ) (boxFactor_nonneg e σ) e.support
    (fun v hv => by rw [boxFactor, Finsupp.notMem_support_iff.mp hv]; simp)
    (fun v => (hasSum_boxFactor e (zero_lt_one.trans hσ) v).summable) (hasProd_boxFactor e hσ)
  have : (fun 𝔞 : FI => if InBox e 𝔞 then IdeleClass.idealNorm F 𝔞 ^ (-σ) else 0) =
      (fun x => ∏ᶠ v, boxFactor e σ v (x v)) ∘ fracIdealEquiv F :=
    funext fun 𝔞 => (finprod_boxFactor e σ 𝔞).symm
  rw [this, (fracIdealEquiv F).summable_iff]
  exact hE.summable

theorem tsum_inBox_lt_top (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) {σ : ℝ} (hσ : 1 < σ) :
    ∑' 𝔞 : FI, ENNReal.ofReal (if InBox e 𝔞 then IdeleClass.idealNorm F 𝔞 ^ (-σ) else 0) < ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun 𝔞 => by
    split_ifs
    · exact (Real.rpow_pos_of_pos (IdeleClass.idealNorm_pos F 𝔞) _).le
    · exact le_rfl) (summable_inBox e hσ)]
  exact ENNReal.ofReal_lt_top

/-! ### The archimedean integral -/

theorem normAtPlace_le_norm (w : InfinitePlace F) (x : V) : normAtPlace w x ≤ ‖x‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w x) (Finset.mem_univ w)

/-- $N(x)\le\|x\|^n$ on $F_\infty$ (sup norm). -/
theorem norm_le_norm_pow (x : V) : mixedEmbedding.norm x ≤ ‖x‖ ^ Module.finrank ℚ F := by
  rw [mixedEmbedding.norm_apply, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _)
    fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg w x) (normAtPlace_le_norm w x) _

/-- **$\int_{F_\infty}(1+\|x\|)^{-N}N(x)^{\sigma}\,\frac{dx}{N(x)}<\infty$** for $\sigma\ge1$ and $N>n\sigma$. -/
theorem lintegral_arch_lt_top {σ : ℝ} (hσ : 1 ≤ σ) {N : ℝ} (hN : Module.finrank ℚ F * σ < N) :
    ∫⁻ x : V, ENNReal.ofReal ((1 + ‖x‖) ^ (-N)) * ENNReal.ofReal (mixedEmbedding.norm x ^ σ) *
      ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ < ⊤ := by
  set n : ℝ := (Module.finrank ℚ F : ℝ)
  set r : ℝ := N - n * (σ - 1)
  have hr : (Module.finrank ℝ V : ℝ) < r := by
    rw [mixedEmbedding.finrank]; simp only [r, n]; nlinarith
  have hint : Integrable (fun x : V => (1 + ‖x‖) ^ (-r)) := integrable_one_add_norm hr
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
  have h1 : 0 < 1 + ‖x‖ := by positivity
  rcases eq_or_lt_of_le (mixedEmbedding.norm_nonneg x) with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith), ENNReal.ofReal_zero, mul_zero, zero_mul]
    exact zero_le
  rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos h1 _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_pos_of_pos h1 _).le (Real.rpow_pos_of_pos hpos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpow : mixedEmbedding.norm x ^ σ * (mixedEmbedding.norm x)⁻¹ = mixedEmbedding.norm x ^ (σ - 1) := by
    rw [Real.rpow_sub hpos, Real.rpow_one, div_eq_mul_inv]
  have hle : mixedEmbedding.norm x ^ (σ - 1) ≤ (1 + ‖x‖) ^ (n * (σ - 1)) := by
    calc mixedEmbedding.norm x ^ (σ - 1) ≤ (‖x‖ ^ Module.finrank ℚ F) ^ (σ - 1) :=
          Real.rpow_le_rpow hpos.le (norm_le_norm_pow x) (by linarith)
      _ = ‖x‖ ^ (n * (σ - 1)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
      _ ≤ (1 + ‖x‖) ^ (n * (σ - 1)) :=
          Real.rpow_le_rpow (norm_nonneg x) (by linarith) (by positivity)
  calc (1 + ‖x‖) ^ (-N) * mixedEmbedding.norm x ^ σ * (mixedEmbedding.norm x)⁻¹
      = (1 + ‖x‖) ^ (-N) * mixedEmbedding.norm x ^ (σ - 1) := by rw [mul_assoc, hpow]
    _ ≤ (1 + ‖x‖) ^ (-N) * (1 + ‖x‖) ^ (n * (σ - 1)) :=
        mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos h1 _).le
    _ = (1 + ‖x‖) ^ (-r) := by rw [← Real.rpow_add h1]; congr 1; ring

/-! ### The majorant class -/

/-- **Majorized functions on the adeles**: measurable on $\mathbb A_F^\times$, and for every $N$ bounded by
$C(1+\|x_\infty\|)^{-N}\mathbf 1[\mathfrak a(x_f)\in\text{box}]$ for some box. -/
structure IsMajorized (Φ : Adeles F → ℂ) : Prop where
  measurable : Measurable fun g : (Adeles F)ˣ => Φ g
  bound : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ e : HeightOneSpectrum (𝓞 F) →₀ ℤ, ∀ g : (Adeles F)ˣ,
    ‖Φ g‖ ≤ C * ((1 + ‖(infPart g : V)‖) ^ N)⁻¹ * (if InBox e (ideleIdeal F (finPart g)) then 1 else 0)

/-- The majorant $\Psi(x) = C(1+\|x_\infty\|)^{-N}\mathbf 1[\mathfrak a(x_f)\in\text{box}]$, as a $[0,\infty]$-valued
function on $\mathbb A_F^\times$. -/
def majorant (N : ℕ) (C : ℝ) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) (g : (Adeles F)ˣ) : ℝ≥0∞ :=
  ENNReal.ofReal (C * ((1 + ‖(infPart g : V)‖) ^ N)⁻¹ * (if InBox e (ideleIdeal F (finPart g)) then 1 else 0))

theorem measurable_majorant (N : ℕ) (C : ℝ) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    Measurable (majorant (F := F) N C e) := by
  have := QFPort.measurable_comp_ideleIdeal (F := F)
    (fun x 𝔞 => ENNReal.ofReal (C * ((1 + ‖x‖) ^ N)⁻¹ * (if InBox e 𝔞 then 1 else 0)))
    (fun 𝔞 => ((measurable_const.mul ((measurable_const.add measurable_norm).pow_const N).inv).mul
      measurable_const).ennreal_ofReal)
  exact this

theorem IsMajorized.enorm_le {Φ : Adeles F → ℂ} {N : ℕ} {C : ℝ} {e : HeightOneSpectrum (𝓞 F) →₀ ℤ}
    (h : ∀ g : (Adeles F)ˣ,
      ‖Φ g‖ ≤ C * ((1 + ‖(infPart g : V)‖) ^ N)⁻¹ * (if InBox e (ideleIdeal F (finPart g)) then 1 else 0))
    (g : (Adeles F)ˣ) : ENNReal.ofReal ‖Φ g‖ ≤ majorant N C e g :=
  ENNReal.ofReal_le_ofReal (h g)

/-- **The majorant is integrable against $\|x\|^\sigma d^\times x$** for $\sigma>1$ and $N>n\sigma$. -/
theorem lintegral_majorant_lt_top {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : Module.finrank ℚ F * σ < N) {C : ℝ}
    (hC : 0 ≤ C) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ∫⁻ g, majorant N C e g * ENNReal.ofReal (ideleNorm F g ^ σ) ∂tamIdeles F < ⊤ := by
  set G : V → FI → ℝ≥0∞ := fun x 𝔞 =>
    ENNReal.ofReal (C * ((1 + ‖x‖) ^ N)⁻¹ * (if InBox e 𝔞 then 1 else 0)) *
      ENNReal.ofReal (IdeleClass.ideleNorm F x 𝔞 ^ σ)
  have hG : ∀ 𝔞, Measurable (G · 𝔞) := fun 𝔞 =>
    (((measurable_const.mul ((measurable_const.add measurable_norm).pow_const N).inv).mul
      measurable_const).ennreal_ofReal).mul
      ((((mixedEmbedding.continuous_norm F).measurable.div_const _).pow_const σ).ennreal_ofReal)
  have hrw : (fun g : (Adeles F)ˣ => majorant N C e g * ENNReal.ofReal (ideleNorm F g ^ σ)) =
      fun g => G (infPart g) (ideleIdeal F (finPart g)) := by
    funext g
    simp only [G, majorant, ideleNorm_eq_ideleClass]
  rw [hrw, QFPort.lintegral_tamIdeles_ideal G hG, IdeleClass.ideleLIntegral]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  set A : V → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 + ‖x‖) ^ (-(N : ℝ))) *
    ENNReal.ofReal (mixedEmbedding.norm x ^ σ) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹
  set B : FI → ℝ≥0∞ := fun 𝔞 => ENNReal.ofReal (if InBox e 𝔞 then IdeleClass.idealNorm F 𝔞 ^ (-σ) else 0)
  have hpt : ∀ x 𝔞, G x 𝔞 * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ = ENNReal.ofReal C * B 𝔞 * A x := by
    intro x 𝔞
    have h1 : 0 < 1 + ‖x‖ := by positivity
    have hN𝔞 := IdeleClass.idealNorm_pos F 𝔞
    have hpowN : ((1 + ‖x‖) ^ N)⁻¹ = (1 + ‖x‖) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg h1.le, Real.rpow_natCast]
    have hdiv : IdeleClass.ideleNorm F x 𝔞 ^ σ = mixedEmbedding.norm x ^ σ * IdeleClass.idealNorm F 𝔞 ^ (-σ) := by
      rw [IdeleClass.ideleNorm, Real.div_rpow (mixedEmbedding.norm_nonneg x) hN𝔞.le, Real.rpow_neg hN𝔞.le,
        div_eq_mul_inv]
    simp only [G, A, B, hpowN, hdiv]
    split_ifs
    · rw [mul_one, ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _)]
      ring
    · simp
  have hAm : Measurable A :=
    (((measurable_const.add measurable_norm).pow_const _).ennreal_ofReal.mul
      ((mixedEmbedding.continuous_norm F).measurable.pow_const σ).ennreal_ofReal).mul
      (IdeleClass.measurable_invNorm F)
  have hint : ∀ 𝔞, ∫⁻ x, G x 𝔞 * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      ENNReal.ofReal C * B 𝔞 * ∫⁻ x, A x := fun 𝔞 => by
    simp_rw [hpt]
    rw [lintegral_const_mul _ hAm]
  simp_rw [hint]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (tsum_inBox_lt_top e hσ)) ?_
  exact lintegral_arch_lt_top hσ.le (by exact_mod_cast hN)

/-- A natural number $N > n\sigma$. -/
theorem exists_nat_gt_finrank_mul (σ : ℝ) : ∃ N : ℕ, Module.finrank ℚ F * σ < N := exists_nat_gt _

/-! ### Absolute convergence of the zeta integral -/

theorem measurable_ideleNorm_cpow (s : ℂ) :
    Measurable fun g : (Adeles F)ˣ => (ideleNorm F g : ℂ) ^ s :=
  (Complex.continuous_ofReal.comp continuous_ideleNorm).measurable.pow_const s

theorem norm_globalZetaIntegrand (Φ : Adeles F → ℂ) (χ : HeckeCharacter F) (s : ℂ) (g : (Adeles F)ˣ) :
    ‖globalZetaIntegrand Φ χ s g‖ = ‖Φ g‖ * ideleNorm F g ^ (s.re + χ.shift) := by
  rw [globalZetaIntegrand, norm_mul, norm_mul, HeckeCharacter.norm_onIdeles,
    Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos g), mul_assoc,
    ← Real.rpow_add (ideleNorm_pos g), add_comm χ.shift]

/-- **Absolute convergence of the global zeta integral** for $\operatorname{Re}s+\sigma>1$, $\sigma$ the shift of
$\chi$: the integrand is integrable for Tate's measure. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (ζ(f, c) converges for σ > 1)"]
theorem integrable_globalZetaIntegrand {Φ : Adeles F → ℂ} (hΦ : IsMajorized Φ) (χ : HeckeCharacter F) {s : ℂ}
    (hs : 1 < s.re + χ.shift) : Integrable (globalZetaIntegrand Φ χ s) (tamIdeles F) := by
  refine ⟨((hΦ.measurable.mul χ.continuous_coe_onIdeles.measurable).mul
    (measurable_ideleNorm_cpow s)).aestronglyMeasurable, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt_finrank_mul (F := F) (s.re + χ.shift)
  obtain ⟨C, hC, e, hb⟩ := hΦ.bound N
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (lintegral_majorant_lt_top hs hN hC e)
  rw [← ofReal_norm, norm_globalZetaIntegrand,
    ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_le_mul_left (IsMajorized.enorm_le hb g) _

end

end NumberFieldKB.GlobalZeta
