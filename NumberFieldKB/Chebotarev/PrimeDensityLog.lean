import NumberFieldKB.NonVanishing.Hecke
import NumberFieldKB.NonVanishing.Dedekind
import Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# Logarithms of Euler products near $s = 1$
$F$ is a number field, $v$ runs over the nonzero primes of $\mathcal O_F$, $N(v)$ = `normP v`, and
$a(v)\in\mathbb C$ with $|a(v)|\le1$. Write $P_a(s) = \sum_va(v)N(v)^{-s}$ (`primeSum a s`).

* **`exists_tendsto_of_tendsto_cexp`** (the topological core): if $\Phi$ is continuous on $(1,\infty)$ and
  $e^{\Phi(s)}\to c\ne0$ as $s\to1^+$, then $\Phi(s)$ converges as $s\to1^+$. (A continuous logarithm of a function
  with a nonzero limit cannot wind: two logarithms differ by a locally constant element of $2\pi i\mathbb Z$.)
* `logEuler_eq_primeSum_add`, `norm_tsum_remLog_le`: $\sum_v-\log(1-a(v)N(v)^{-s}) = P_a(s)+R_a(s)$ with
  $|R_a(s)|\le\sum_vN(v)^{-2}$ for $\operatorname{Re}s\ge1$ (the prime powers contribute $O(1)$).
* **The log-$L$ lemma.** Let $L(s) = \prod_v(1-a(v)N(v)^{-s})^{-1}$ for real $s>1$ (in the form
  $L(s) = \exp(\texttt{logEuler}\ a\ s)$ of `NonVanishing/Euler.lean`; $a(v) = 0$ at finitely many $v$ covers Euler
  products over all but finitely many primes).
  - `isBigO_primeSum_of_tendsto`: if $L(s)\to c\ne0$ as $s\to1^+$, then $P_a(s) = O(1)$;
  - `isBigO_primeSum_sub_log_of_tendsto`: if $(s-1)L(s)\to c\ne0$ (a simple pole), then
    $P_a(s) = \log\frac1{s-1}+O(1)$.
* Instances: **`isBigO_primeSum_heckeCoeff`** ($L(s,\chi)$ for unitary $\chi$ not a power of the norm, in particular
  every finite-order $\chi\ne1$, `isBigO_primeSum_heckeCoeff_of_pow_eq_one`), and for $\zeta_F$:
  **`isBigO_primeIdealZetaSum_sub_log`**: $\sum_vN(v)^{-s} = \log\frac1{s-1}+O(1)$ as $s\to1^+$, hence
  **`tendsto_primeIdealZetaSum_univ`**: $\sum_vN(v)^{-s}\to\infty$. Mathlib v4.35.0's `DirichletDensity.lean`
  defines the density but does not prove this.
* `isBigO_primeSum_sub_of_finite`: changing $a$ at finitely many primes changes $P_a$ by $O(1)$.

Everything is stated for real $s\to1^+$ (`𝓝[>] 1`), the filter of Mathlib's `HasDirichletDensity`.
-/

open Complex Filter Topology Asymptotics IsDedekindDomain NumberField Set
open QuadFormsKB.NFEuler NumberFieldKB.HeckeL NumberFieldKB.HeckeCharacter NumberFieldKB.NonVanishing

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The topological core -/

/-- The closed ball... the open disc $|z-1|<1$ lies in the slit plane. -/
theorem mem_slitPlane_of_mem_ball {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) 1) : z ∈ slitPlane := by
  rw [Metric.mem_ball, dist_eq] at hz
  have h1 := Complex.abs_re_le_norm (z - 1)
  rw [sub_re, one_re] at h1
  have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hz)).1
  exact mem_slitPlane_iff.mpr (Or.inl (by linarith))

/-- **A continuous logarithm of a function with a nonzero limit converges.** If $\Phi$ is continuous on $(1,\infty)$
and $e^{\Phi(s)}\to c\ne0$ as $s\to1^+$, then $\Phi(s)$ has a limit as $s\to1^+$. -/
theorem exists_tendsto_of_tendsto_cexp {Φ : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0) (hΦ : ContinuousOn Φ (Ioi 1))
    (h : Tendsto (fun s => cexp (Φ s)) (𝓝[>] 1) (𝓝 c)) : ∃ ℓ, Tendsto Φ (𝓝[>] 1) (𝓝 ℓ) := by
  set u : ℝ → ℂ := fun s => cexp (Φ s) / c with hu_def
  have hu : Tendsto u (𝓝[>] 1) (𝓝 1) := by
    simpa [hu_def, div_self hc] using h.div_const c
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), u s ∈ Metric.ball (1 : ℂ) 1 := hu (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨b, hb1, hbs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set J := Ioo (1 : ℝ) b
  have hb1' : (1 : ℝ) < b := hb1
  have hI : ∀ s ∈ J, u s ∈ Metric.ball (1 : ℂ) 1 := fun s hs => hbs hs
  set ψ : ℝ → ℂ := fun s => Φ s - log (u s) with hψ_def
  have hu0 : ∀ s ∈ J, u s ≠ 0 := fun s hs h0 => by
    have := hI s hs; rw [h0, Metric.mem_ball, dist_eq] at this; simp at this
  have hexp : ∀ s ∈ J, cexp (ψ s) = c := fun s hs => by
    rw [hψ_def, Complex.exp_sub, Complex.exp_log (hu0 s hs), hu_def]
    field_simp [Complex.exp_ne_zero]
  have hcontu : ContinuousOn u J :=
    ((continuous_exp.comp_continuousOn (hΦ.mono fun s hs => hs.1)).div_const c)
  have hcontψ : ContinuousOn ψ J :=
    (hΦ.mono fun s hs => hs.1).sub (hcontu.clog fun s hs => mem_slitPlane_of_mem_ball (hI s hs))
  set s₀ : ℝ := (1 + b) / 2
  have hs₀ : s₀ ∈ J := ⟨by simp only [s₀]; linarith [hb1'], by simp only [s₀]; linarith [hb1']⟩
  have hint : ∀ s ∈ J, ∃ n : ℤ, ψ s = ψ s₀ + n * (2 * Real.pi * I) := fun s hs =>
    Complex.exp_eq_exp_iff_exists_int.mp ((hexp s hs).trans (hexp s₀ hs₀).symm)
  -- the imaginary part of `ψ s - ψ s₀` lies in the discrete set `2πℤ` and is continuous, hence constant
  have hdisc : IsDiscrete ((AddSubgroup.zmultiples (2 * Real.pi) : AddSubgroup ℝ) : Set ℝ) := by
    rw [SetLike.isDiscrete_iff_discreteTopology]; infer_instance
  have hconst : ∀ s ∈ J, ψ s = ψ s₀ := by
    intro s hs
    have hmaps : MapsTo (fun t => (ψ t - ψ s₀).im) J
        ((AddSubgroup.zmultiples (2 * Real.pi) : AddSubgroup ℝ) : Set ℝ) := by
      intro t ht
      obtain ⟨n, hn⟩ := hint t ht
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n, ?_⟩
      simp [hn, zsmul_eq_mul]
    have hc' : ContinuousOn (fun t => (ψ t - ψ s₀).im) J :=
      continuous_im.comp_continuousOn (hcontψ.sub continuousOn_const)
    have himeq := isPreconnected_Ioo.constant_of_mapsTo hdisc hc' hmaps hs hs₀
    simp only [sub_self, zero_im] at himeq
    obtain ⟨n, hn⟩ := hint s hs
    have hre : (ψ s - ψ s₀).re = 0 := by simp [hn]
    have : ψ s - ψ s₀ = 0 := Complex.ext hre (by simpa using himeq)
    exact sub_eq_zero.mp this
  refine ⟨ψ s₀, ?_⟩
  have hlog : Tendsto (fun s => log (u s)) (𝓝[>] 1) (𝓝 0) := by
    have := ((continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto).comp hu
    simpa [Function.comp_def] using this
  have hmem : J ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT hb1'
  refine (by simpa using (tendsto_const_nhds (x := ψ s₀)).add hlog :
    Tendsto (fun s => ψ s₀ + log (u s)) (𝓝[>] 1) (𝓝 (ψ s₀))).congr' ?_
  filter_upwards [hmem] with s hs
  rw [← hconst s hs, hψ_def]
  ring

variable {F : Type} [Field F] [NumberField F]

/-! ### The prime sum and the logarithm of the Euler product -/

/-- **The prime sum** $P_a(s) = \sum_va(v)N(v)^{-s}$. -/
def primeSum (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) : ℂ := ∑' v, a v * nps v s

/-- The constant $\sum_vN(v)^{-2}$ bounding the prime-power part of $\log L$. -/
def remConst (F : Type) [Field F] [NumberField F] : ℝ :=
  ∑' v : HeightOneSpectrum (𝓞 F), (normP v : ℝ) ^ (-(2 : ℝ))

theorem summable_normP_two : Summable fun v : HeightOneSpectrum (𝓞 F) => (normP v : ℝ) ^ (-(2 : ℝ)) :=
  summable_normP_rpow (σ := 2) (by norm_num)

theorem summable_mul_nps {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v => a v * nps v s :=
  (summable_norm_mul_nps ha hs).of_norm

/-- $\sum_v-\log(1-a(v)N(v)^{-s}) = P_a(s)+\sum_vr_v(s)$ (`remLog`). -/
theorem logEuler_eq_primeSum_add {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : logEuler a s = primeSum a s + ∑' v, remLog a s v := by
  rw [logEuler, primeSum, ← (summable_mul_nps ha hs).tsum_add (summable_remLog ha hs.le)]
  congr 1
  funext v
  simp [remLog]

/-- **The prime powers contribute $O(1)$**: $|\sum_vr_v(s)|\le\sum_vN(v)^{-2}$ for $\operatorname{Re}s\ge1$. -/
theorem norm_tsum_remLog_le {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑' v, remLog a s v‖ ≤ remConst F :=
  tsum_of_norm_bounded summable_normP_two.hasSum (norm_remLog_le ha hs)

theorem isBigO_tsum_remLog {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) :
    (fun s : ℝ => ∑' v, remLog a s v) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
  refine IsBigO.of_bound (remConst F) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [norm_one, mul_one]
  exact norm_tsum_remLog_le ha (by simpa using le_of_lt hs)

theorem continuousOn_logEuler {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) :
    ContinuousOn (fun s : ℝ => logEuler a s) (Ioi 1) := fun s hs =>
  ((hasDerivAt_logEuler ha (s := (s : ℂ)) (by simpa using hs)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-! ### The log-$L$ lemma -/

/-- **The log-$L$ lemma, regular case.** If $L(s) = \prod_v(1-a(v)N(v)^{-s})^{-1}$ for real $s>1$ and
$L(s)\to c\ne0$ as $s\to1^+$, then $\sum_va(v)N(v)^{-s} = O(1)$ as $s\to1^+$. -/
@[kb "neukirch1999" "Ch. VII, §13 (log L(s, χ) = Σ χ(𝔭) N𝔭^{-s} + O(1)) [unverified locator]"]
theorem isBigO_primeSum_of_tendsto {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {L : ℂ → ℂ}
    (hL : ∀ s : ℝ, 1 < s → L s = cexp (logEuler a s)) {c : ℂ} (hc : c ≠ 0)
    (hlim : Tendsto (fun s : ℝ => L s) (𝓝[>] 1) (𝓝 c)) :
    (fun s : ℝ => primeSum a s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
  have hlim' : Tendsto (fun s : ℝ => cexp (logEuler a s)) (𝓝[>] 1) (𝓝 c) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs using hL s hs
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_of_tendsto_cexp hc (continuousOn_logEuler ha) hlim'
  have h1 := hℓ.isBigO_one ℂ
  refine (h1.sub (isBigO_tsum_remLog ha)).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [logEuler_eq_primeSum_add ha (by simpa using hs)]
  ring

/-- **The log-$L$ lemma, simple pole.** If $L(s) = \prod_v(1-a(v)N(v)^{-s})^{-1}$ for real $s>1$ and
$(s-1)L(s)\to c\ne0$ as $s\to1^+$, then $\sum_va(v)N(v)^{-s} = \log\frac1{s-1}+O(1)$ as $s\to1^+$. -/
@[kb "neukirch1999" "Ch. VII, §13 (log ζ_K(s) ~ log 1/(s-1)) [unverified locator]"]
theorem isBigO_primeSum_sub_log_of_tendsto {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1)
    {L : ℂ → ℂ} (hL : ∀ s : ℝ, 1 < s → L s = cexp (logEuler a s)) {c : ℂ} (hc : c ≠ 0)
    (hlim : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * L s) (𝓝[>] 1) (𝓝 c)) :
    (fun s : ℝ => primeSum a s - (Real.log (1 / (s - 1)) : ℂ)) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
  set Φ : ℝ → ℂ := fun s => logEuler a s + (Real.log (s - 1) : ℂ)
  have hexp : ∀ s : ℝ, 1 < s → cexp (Φ s) = ((s : ℂ) - 1) * L s := fun s hs => by
    simp only [Φ]
    rw [Complex.exp_add, ← hL s hs, ← Complex.ofReal_exp, Real.exp_log (by linarith)]
    push_cast; ring
  have hlim' : Tendsto (fun s : ℝ => cexp (Φ s)) (𝓝[>] 1) (𝓝 c) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs using (hexp s hs).symm
  have hcont : ContinuousOn Φ (Ioi 1) := by
    refine (continuousOn_logEuler ha).add ?_
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact (continuousOn_id.sub continuousOn_const).log fun s hs =>
      sub_ne_zero.mpr (ne_of_gt (show (1 : ℝ) < s from hs))
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_of_tendsto_cexp hc hcont hlim'
  refine ((hℓ.isBigO_one ℂ).sub (isBigO_tsum_remLog ha)).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  simp only [Φ]
  rw [logEuler_eq_primeSum_add ha (by simpa using hs'), one_div, Real.log_inv]
  push_cast
  ring

/-- Changing the coefficients at finitely many primes changes the prime sum by $O(1)$. -/
theorem isBigO_primeSum_sub_of_finite {a b : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1)
    (hb : ∀ v, ‖b v‖ ≤ 1) (hab : {v | a v ≠ b v}.Finite) :
    (fun s : ℝ => primeSum a s - primeSum b s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
  set T := hab.toFinset
  refine IsBigO.of_bound (2 * T.card) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  rw [primeSum, primeSum, ← (summable_mul_nps ha hs').tsum_sub (summable_mul_nps hb hs')]
  have hz : ∀ v ∉ T, a v * nps v s - b v * nps v s = 0 := fun v hv => by
    have : a v = b v := by simpa [T] using hv
    rw [this, sub_self]
  rw [tsum_eq_sum hz, norm_one, mul_one]
  refine (norm_sum_le _ _).trans ?_
  have hle : ∀ v ∈ T, ‖a v * nps v s - b v * nps v s‖ ≤ 2 := fun v _ => by
    have h1 := norm_mul_nps_le_half ha v hs'.le
    have h2 := norm_mul_nps_le_half hb v hs'.le
    calc _ ≤ ‖a v * nps v s‖ + ‖b v * nps v s‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  refine (Finset.sum_le_sum hle).trans ?_
  simp [mul_comm]

/-! ### Hecke $L$-functions -/

/-- **$\sum_va_\chi(v)N(v)^{-s} = O(1)$ as $s\to1^+$** for a unitary Hecke character $\chi$ that is not a power of the
norm ($a_\chi$ = `heckeCoeff χ`): $L(s,\chi)$ is entire and $L(1,\chi)\ne0$. -/
theorem isBigO_primeSum_heckeCoeff {χ : HeckeCharacter F} (hχ : χ.IsUnitary)
    (hnp : ∀ c : ℂ, χ ≠ normPow F c) :
    (fun s : ℝ => primeSum (heckeCoeff χ) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
  refine isBigO_primeSum_of_tendsto (norm_heckeCoeff_le hχ) (L := heckeLCont χ)
    (fun s hs => heckeLCont_eq_exp hχ (by simpa using hs))
    (heckeLCont_ne_zero_of_one_le_re hχ hnp (s := 1) (by simp)) ?_
  have hc : ContinuousAt (fun s : ℝ => heckeLCont χ s) 1 :=
    ((differentiable_heckeLCont hnp) (1 : ℂ)).continuousAt.comp_of_eq
      Complex.continuous_ofReal.continuousAt (by simp)
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- **Finite-order characters**: for $\chi\ne1$ with $\chi^n = 1$, $\sum_va_\chi(v)N(v)^{-s} = O(1)$ as $s\to1^+$. -/
theorem isBigO_primeSum_heckeCoeff_of_pow_eq_one {χ : HeckeCharacter F} {n : ℕ} (hn : n ≠ 0) (h : χ ^ n = 1)
    (hne : χ ≠ 1) : (fun s : ℝ => primeSum (heckeCoeff χ) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) :=
  isBigO_primeSum_heckeCoeff (isUnitary_of_pow_eq_one hn h) (ne_normPow_of_pow_eq_one hn h hne)

/-! ### The Dedekind zeta function: $\sum_vN(v)^{-s}\sim\log\frac1{s-1}$ -/

theorem tendsto_ofReal_nhdsGT_nhdsNE :
    Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have : s ≠ 1 := ne_of_gt hs
    simpa using this

/-- $\sum_vN(v)^{-s} = \sum_v1\cdot N(v)^{-s}$ in `primeSum` form, for real $s$. -/
theorem primeIdealZetaSum_univ_eq (s : ℝ) :
    ((Set.univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s : ℂ) = primeSum (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) s := by
  rw [NumberField.Set.primeIdealZetaSum_def,
    tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s), primeSum,
    Complex.ofReal_tsum]
  congr 1
  funext v
  rw [one_mul, nps, Complex.ofReal_cpow (by positivity), Complex.ofReal_neg]

/-- **$\sum_vN(v)^{-s} = \log\frac1{s-1}+O(1)$ as $s\to1^+$** (from the simple pole of $\zeta_F$ at $1$). -/
@[kb "neukirch1999" "Ch. VII, §13 (Σ_𝔭 N𝔭^{-s} ~ log 1/(s-1)) [unverified locator]"]
theorem isBigO_primeIdealZetaSum_sub_log :
    (fun s : ℝ => (Set.univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s - Real.log (1 / (s - 1)))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hC := isBigO_primeSum_sub_log_of_tendsto (F := F) (a := fun _ => 1) (fun _ => by simp)
    (L := dedekindZetaCont F) (fun s hs => dedekindZetaCont_eq_exp (by simpa using hs))
    (c := (dedekindZeta_residue F : ℂ)) (by exact_mod_cast (dedekindZeta_residue_pos F).ne')
    ((tendsto_sub_one_mul_dedekindZetaCont (F := F)).comp tendsto_ofReal_nhdsGT_nhdsNE)
  refine IsBigO.trans ?_ (hC.trans (isBigO_of_le _ fun _ => by simp))
  refine isBigO_of_le _ fun s => le_of_eq ?_
  rw [← primeIdealZetaSum_univ_eq]
  rw [show ((((Set.univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s : ℝ) : ℂ) -
      ((Real.log (1 / (s - 1)) : ℝ) : ℂ)) =
      (((Set.univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s - Real.log (1 / (s - 1)) : ℝ) : ℂ)
      by push_cast; ring, Complex.norm_real]

/-- **$\sum_vN(v)^{-s}\to\infty$ as $s\to1^+$.** -/
theorem tendsto_primeIdealZetaSum_univ :
    Tendsto (fun s : ℝ => (Set.univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s) (𝓝[>] 1) atTop := by
  have hlog : Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] 1) atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    simp only [one_div]
    refine tendsto_inv_nhdsGT_zero.comp ?_
    have h : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] (1 - 1)) :=
      ((continuous_sub_right (1 : ℝ)).continuousWithinAt.tendsto_nhdsWithin
        (fun s (hs : 1 < s) => show 1 - 1 < s - 1 by linarith))
    simpa using h
  obtain ⟨C, hC⟩ := (isBigO_primeIdealZetaSum_sub_log (F := F)).bound
  have hf : ∀ᶠ s in 𝓝[>] (1 : ℝ), -C ≤ (Set.univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s -
      Real.log (1 / (s - 1)) := by
    filter_upwards [hC] with s hs
    rw [norm_one, mul_one, Real.norm_eq_abs] at hs
    linarith [neg_abs_le ((Set.univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s -
      Real.log (1 / (s - 1)))]
  refine (tendsto_atTop_add_left_of_le' _ (-C) hf hlog).congr fun s => ?_
  ring

end

end NumberFieldKB.Chebotarev
