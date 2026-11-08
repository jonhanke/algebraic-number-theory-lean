import NumberFieldKB.Chebotarev.Basic
import NumberFieldKB.Chebotarev.PrimeDensity

/-!
# Density tools for the Chebotarev track

The analytic statements used in the proof of the Chebotarev density theorem, proved from the prime-density results
(`PrimeDensityLog.lean`, `PrimeDensity.lean`): $P_F(s)\to\infty$, $P_E(s)/P_F(s)\to1$, primes of degree one have
density $1$, finite sets have density $0$, the descent lemma (D) along fibres of constant size, and the upper bound for
the density of split primes.
-/

open NumberField IsDedekindDomain Filter Topology Set Asymptotics
open QuadFormsKB.NFEuler

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Density

variable {F : Type} [Field F] [NumberField F]

/-- *Proved* (from `tendsto_primeIdealZetaSum_univ`). **$\sum_{\mathfrak p} N\mathfrak p^{-s} \to \infty$ as $s \to 1^+$**
(from the pole of $\zeta_F$ at $s = 1$). Consequently finite sets have density `0`. -/
theorem tendsto_primeIdealZetaSum_univ_atTop :
    Tendsto (fun s => (univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s) (𝓝[>] 1) atTop :=
  tendsto_primeIdealZetaSum_univ

/-- *Proved* from `isBigO_primeIdealZetaSum_sub_log` for `E` and `F`. **Comparison of prime zeta functions in an extension**: for $E \supseteq F$,
$P_E(s)/P_F(s) \to 1$ as $s \to 1^+$, where $P_F(s) = \sum_{\mathfrak p} N\mathfrak p^{-s}$. Both are
$\log\frac{1}{s-1} + O(1)$ (from $\log\zeta_F(s) = P_F(s) + O(1)$ and the simple pole of $\zeta_F$). -/
theorem tendsto_primeIdealZetaSum_div_primeIdealZetaSum (E : Type) [Field E] [NumberField E] [Algebra F E] :
    Tendsto (fun s => (univ : Set (HeightOneSpectrum (𝓞 E))).primeIdealZetaSum s /
      (univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 1) := by
  have hdiff := (isBigO_primeIdealZetaSum_sub_log (F := E)).sub (isBigO_primeIdealZetaSum_sub_log (F := F))
  have h0 := tendsto_div_primeIdealZetaSum_univ (F := F) hdiff
  have h1 := h0.const_add 1
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [tendsto_primeIdealZetaSum_univ (F := F) |>.eventually_gt_atTop 0] with s hs
  field_simp
  ring

/-- $N\mathfrak p^{f} = N\mathfrak P$ for $\mathfrak P$ over $\mathfrak p$ with inertia degree $f$. -/
theorem absNorm_pow_inertiaDeg_eq (E : Type) [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 F)) [P.asIdeal.LiesOver 𝔭.asIdeal] :
    normP 𝔭 ^ P.asIdeal.inertiaDeg (𝓞 F) = normP P :=
  Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P.asIdeal

/-- A prime of `E` lies over the prime of `F` below it. -/
theorem liesOver_under (E : Type) [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) : P.asIdeal.LiesOver ((P.under (𝓞 F)).asIdeal) := ⟨rfl⟩

/-- *Proved* from `hasDirichletDensity_degOnePrimes`. **Primes of degree one over `F` have density `1`** in an extension $E/F$: the primes of `E`
with inertia degree $\ge 2$ over `F` contribute $\sum N\mathfrak P^{-s} \le [E:F]\sum_{\mathfrak p}N\mathfrak p^{-2s}$,
bounded as $s \to 1^+$. -/
theorem hasDirichletDensity_inertiaDeg_eq_one (E : Type) [Field E] [NumberField E] [Algebra F E] :
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.inertiaDeg (𝓞 F) = 1}.HasDirichletDensity 1 := by
  have hsub : degOnePrimes E ⊆ {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.inertiaDeg (𝓞 F) = 1} := by
    intro P hP
    haveI := liesOver_under (F := F) E P
    have h := absNorm_pow_inertiaDeg_eq (F := F) E P (P.under (𝓞 F))
    have hp : (normP (P.under (𝓞 F)) ^ P.asIdeal.inertiaDeg (𝓞 F)).Prime := by rw [h]; exact hP
    exact (Nat.Prime.eq_one_of_pow hp)
  rw [hasDirichletDensity_iff]
  have hD := hasDirichletDensity_degOnePrimes (F := E)
  rw [hasDirichletDensity_iff] at hD
  have hpos := tendsto_primeIdealZetaSum_univ (F := E) |>.eventually_gt_atTop 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hD tendsto_const_nhds ?_ ?_
  · filter_upwards [hpos, self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
    exact div_le_div_of_nonneg_right (primeIdealZetaSum_mono hsub hs1) hs.le
  · filter_upwards [hpos, self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
    exact (div_le_one hs).2 (primeIdealZetaSum_mono (subset_univ _) hs1)

/-- **Finite sets have density `0`** (a reduction, *proved* from `tendsto_primeIdealZetaSum_univ_atTop`). -/
theorem hasDirichletDensity_zero_of_finite {A : Set (HeightOneSpectrum (𝓞 F))} (hA : A.Finite) :
    A.HasDirichletDensity 0 := by
  rw [hasDirichletDensity_iff]
  have hP := tendsto_primeIdealZetaSum_univ_atTop (F := F)
  have hup : Tendsto (fun s => (A.ncard : ℝ) /
      (univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hP
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hP.eventually_gt_atTop 0] with s hs
    exact div_nonneg (A.primeIdealZetaSum_nonneg s) hs.le
  · filter_upwards [hP.eventually_gt_atTop 0, self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
    exact div_le_div_of_nonneg_right
      (Set.primeIdealZetaSum_le_card_of_finite hA (by linarith)) hs.le

/-- **Density is insensitive to finite changes** (a reduction, *proved* from
`tendsto_primeIdealZetaSum_univ_atTop`): if $S \mathbin\triangle T$ is finite, `S` and `T` have the same density. -/
theorem HasDirichletDensity.congr_finite {S T : Set (HeightOneSpectrum (𝓞 F))} {δ : ℝ}
    (hS : S.HasDirichletDensity δ) (hST : (symmDiff S T).Finite) : T.HasDirichletDensity δ := by
  have h1 : (S \ T).Finite := hST.subset fun x hx => Or.inl hx
  have h2 : (T \ S).Finite := hST.subset fun x hx => Or.inr hx
  have hz1 := hasDirichletDensity_zero_of_finite h1
  have hz2 := hasDirichletDensity_zero_of_finite h2
  rw [hasDirichletDensity_iff] at *
  have := (hS.sub hz1).add hz2
  rw [sub_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have eS : S = (S ∩ T) ∪ (S \ T) := (Set.inter_union_sdiff S T).symm
  have eT : T = (S ∩ T) ∪ (T \ S) := by rw [Set.inter_comm]; exact (Set.inter_union_sdiff T S).symm
  have dS : Disjoint (S ∩ T) (S \ T) := Set.disjoint_sdiff_inter.symm
  have dT : Disjoint (S ∩ T) (T \ S) := by
    rw [Set.inter_comm]; exact Set.disjoint_sdiff_inter.symm
  have hSs := primeIdealZetaSum_union_disjoint dS hs
  have hTs := primeIdealZetaSum_union_disjoint dT hs
  rw [← eS] at hSs
  rw [← eT] at hTs
  simp only [dirichletRatio, hSs, hTs]
  ring

/-! ### Regrouping along the prime below -/

/-- Regrouping a summable series over the fibres of the prime below. -/
theorem tsum_eq_tsum_fibre (E : Type) [Field E] [NumberField E] [Algebra F E]
    (g : HeightOneSpectrum (𝓞 E) → ℝ) (hg : Summable g) :
    (∑' P, g P) = ∑' 𝔭 : HeightOneSpectrum (𝓞 F),
      ∑' P : {P : HeightOneSpectrum (𝓞 E) // P.under (𝓞 F) = 𝔭}, g P.1 := by
  let e := Equiv.sigmaFiberEquiv (fun P : HeightOneSpectrum (𝓞 E) => P.under (𝓞 F))
  have hs : Summable (g ∘ e) := e.summable_iff.2 hg
  rw [← e.tsum_eq g]
  exact Summable.tsum_sigma' (fun 𝔭 => hg.comp_injective Subtype.val_injective) hs

/-- The sum over the fibre of the prime below, as a cardinality times a constant, when the summand is constant
on the chosen part of the fibre. -/
theorem tsum_fibre_eq_card_mul (E : Type) [Field E] [NumberField E] [Algebra F E]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (U : Set (HeightOneSpectrum (𝓞 E))) (g : HeightOneSpectrum (𝓞 E) → ℝ)
    (a : ℝ) (hg : ∀ P ∈ U, P.under (𝓞 F) = 𝔭 → g P = a) :
    ∑' P : {P : HeightOneSpectrum (𝓞 E) // P.under (𝓞 F) = 𝔭}, U.indicator g P.1 =
      {P ∈ U | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard * a := by
  set Fb : Set (HeightOneSpectrum (𝓞 E)) := {P | P.under (𝓞 F) = 𝔭} with hFb
  have h1 : ∑' P : {P : HeightOneSpectrum (𝓞 E) // P.under (𝓞 F) = 𝔭}, U.indicator g P.1 =
      ∑' P, Fb.indicator (U.indicator g) P := tsum_subtype Fb (U.indicator g)
  have hset : {P ∈ U | P.asIdeal.LiesOver 𝔭.asIdeal} = U ∩ Fb := by
    ext P
    simp only [mem_ofPred_eq, mem_inter_iff, hFb, Ideal.liesOver_iff]
    constructor
    · rintro ⟨hU, h⟩
      refine ⟨hU, HeightOneSpectrum.ext ?_⟩
      simpa using h.symm
    · rintro ⟨hU, h⟩
      refine ⟨hU, ?_⟩
      rw [← h]; rfl
  have h2 : (fun P => Fb.indicator (U.indicator g) P) = (U ∩ Fb).indicator (fun _ => a) := by
    funext P
    by_cases hP : P ∈ U ∩ Fb
    · rw [indicator_of_mem hP, indicator_of_mem hP.2, indicator_of_mem hP.1]
      exact hg P hP.1 hP.2
    · rw [indicator_of_notMem hP]
      by_cases h2 : P ∈ Fb
      · rw [indicator_of_mem h2, indicator_of_notMem]
        exact fun h => hP ⟨h, h2⟩
      · rw [indicator_of_notMem h2]
  rw [h1, h2, hset, ← tsum_subtype (U ∩ Fb) (fun _ => a), tsum_const, nsmul_eq_mul,
    Nat.card_coe_set_eq]

open Classical in
/-- *Proved* (analytic descent, from
`tendsto_primeIdealZetaSum_div_primeIdealZetaSum`). Let $E/F$ be an extension, `T` a set of primes of `E` of degree
one over `F`, `S` a set of primes of `F`, and `c ≥ 1`, such that each prime $\mathfrak p$ of `F` has exactly `c`
primes of `T` above it if $\mathfrak p \in S$ and none otherwise. Then $\delta_F(S) = \delta_E(T)/c$.
*Proof*: $N\mathfrak P = N\mathfrak p$ for $\mathfrak P \in T$ above $\mathfrak p$, so
$\sum_{T}N\mathfrak P^{-s} = c\sum_{S}N\mathfrak p^{-s}$; divide by $P_F(s)$ and use $P_E/P_F \to 1$. -/
theorem hasDirichletDensity_of_fiber_card (E : Type) [Field E] [NumberField E] [Algebra F E]
    (T : Set (HeightOneSpectrum (𝓞 E))) (S : Set (HeightOneSpectrum (𝓞 F))) (c : ℕ) (hc : 0 < c)
    (hdeg : ∀ P ∈ T, P.asIdeal.inertiaDeg (𝓞 F) = 1)
    (hfib : ∀ 𝔭 : HeightOneSpectrum (𝓞 F),
      {P ∈ T | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard = if 𝔭 ∈ S then c else 0)
    {δ : ℝ} (hT : T.HasDirichletDensity δ) :
    S.HasDirichletDensity (δ / c) := by
  have key : ∀ s : ℝ, 1 < s → T.primeIdealZetaSum s = c * S.primeIdealZetaSum s := by
    intro s hs
    rw [primeIdealZetaSum_eq_tsum_indicator T s,
      tsum_eq_tsum_fibre (F := F) E _ (summable_indicator_rpow T hs),
      primeIdealZetaSum_eq_tsum_indicator S s, ← tsum_mul_left]
    refine tsum_congr fun 𝔭 => ?_
    rw [tsum_fibre_eq_card_mul E 𝔭 T (fun P => (normP P : ℝ) ^ (-s)) ((normP 𝔭 : ℝ) ^ (-s))]
    · rw [hfib 𝔭]
      by_cases h𝔭 : 𝔭 ∈ S <;> simp [h𝔭]
    · intro P hP hPp
      haveI : P.asIdeal.LiesOver 𝔭.asIdeal := ⟨by rw [← hPp]; rfl⟩
      have h := absNorm_pow_inertiaDeg_eq (F := F) E P 𝔭
      rw [hdeg P hP, pow_one] at h
      rw [h]
  rw [hasDirichletDensity_iff] at hT ⊢
  have hr := tendsto_primeIdealZetaSum_div_primeIdealZetaSum (F := F) E
  have := (hT.mul hr).div_const (c : ℝ)
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin, tendsto_primeIdealZetaSum_univ (F := F) |>.eventually_gt_atTop 0,
    tendsto_primeIdealZetaSum_univ (F := E) |>.eventually_gt_atTop 0] with s hs hF hE
  have hs' : (1 : ℝ) < s := hs
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [dirichletRatio]
  rw [key s hs']
  field_simp

/-- The primes of `E` above a prime of `F` correspond to the primes over it. -/
theorem ncard_fibre_eq (E : Type) [Field E] [NumberField E] [Algebra F E] (𝔭 : HeightOneSpectrum (𝓞 F)) :
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard =
      (𝔭.asIdeal.primesOver (𝓞 E)).ncard := by
  rw [← Set.ncard_image_of_injective _ HeightOneSpectrum.asIdeal_injective]
  congr 1
  ext I
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.isPrime, hP⟩
  · rintro ⟨hI, hIp⟩
    exact ⟨⟨I, hI, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot I⟩, hIp, rfl⟩

/-- *Proved* (elementary). **Split primes have upper density at most $1/[E:F]$**: every prime of `F`
splitting completely in `E` has $[E:F]$ primes of degree one above it, so
$[E:F]\sum_{\mathfrak p\ \mathrm{split}}N\mathfrak p^{-s} \le P_E(s)$, and $P_E/P_F \to 1$. (Used in the cyclotomic case to see
that $\chi\circ N_{F/\mathbb Q}$ is a nontrivial Hecke character when $\chi$ is nontrivial on
$\mathrm{Gal}(F(\zeta_m)/F)$.) -/
theorem splitPrimes_upperBound (E : Type) [Field E] [NumberField E] [Algebra F E] [IsGalois F E] :
    ∀ b > 1 / (Module.finrank F E : ℝ), ∀ᶠ s in 𝓝[>] 1, dirichletRatio (splitPrimes F E) s ≤ b := by
  set n := Module.finrank F E with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hcount : ∀ 𝔭 ∈ splitPrimes F E,
      {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard = n := by
    intro 𝔭 h𝔭
    rw [ncard_fibre_eq]
    have hid := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal (𝓞 E) Gal(E/F)
    obtain ⟨Q⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 E)))
    have h1 := h𝔭 Q
    haveI := Q.2.1
    haveI := Q.2.2
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal Q.1 Gal(E/F),
      Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal Q.1 Gal(E/F), h1.1, h1.2,
      IsGaloisGroup.card_eq_finrank Gal(E/F) F E] at hid
    simpa using hid
  have key : ∀ s : ℝ, 1 < s → (n : ℝ) * (splitPrimes F E).primeIdealZetaSum s ≤
      (univ : Set (HeightOneSpectrum (𝓞 E))).primeIdealZetaSum s := by
    intro s hs
    rw [primeIdealZetaSum_eq_tsum_indicator (univ : Set (HeightOneSpectrum (𝓞 E))) s,
      tsum_eq_tsum_fibre (F := F) E _ (summable_indicator_rpow _ hs),
      primeIdealZetaSum_eq_tsum_indicator (splitPrimes F E) s, ← tsum_mul_left]
    have hg := summable_indicator_rpow (univ : Set (HeightOneSpectrum (𝓞 E))) hs
    have hsig := (Equiv.sigmaFiberEquiv
      (fun P : HeightOneSpectrum (𝓞 E) => P.under (𝓞 F))).summable_iff.2 hg
    refine Summable.tsum_le_tsum (fun 𝔭 => ?_) ((summable_indicator_rpow (splitPrimes F E) hs).mul_left _)
      hsig.sigma
    by_cases h𝔭 : 𝔭 ∈ splitPrimes F E
    · have hc2 : {P ∈ (univ : Set (HeightOneSpectrum (𝓞 E))) | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard = n := by
        simpa using hcount 𝔭 h𝔭
      rw [indicator_of_mem h𝔭, tsum_fibre_eq_card_mul E 𝔭 univ (fun P => (normP P : ℝ) ^ (-s))
        ((normP 𝔭 : ℝ) ^ (-s)), hc2]
      intro P _ hPp
      haveI : P.asIdeal.LiesOver 𝔭.asIdeal := ⟨by rw [← hPp]; rfl⟩
      have h1 := (h𝔭 ⟨P.asIdeal, P.isPrime, this⟩).2
      have h := absNorm_pow_inertiaDeg_eq (F := F) E P 𝔭
      rw [show P.asIdeal.inertiaDeg (𝓞 F) = 1 from h1, pow_one] at h
      rw [h]
    · rw [indicator_of_notMem h𝔭, mul_zero]
      exact tsum_nonneg fun P => indicator_nonneg (fun _ _ => by positivity) _
  intro b hb
  have hb1 : 1 < b * n := by
    have := (div_lt_iff₀ hn').1 hb
    simpa using this
  have hr := tendsto_primeIdealZetaSum_div_primeIdealZetaSum (F := F) E
  filter_upwards [(tendsto_order.1 hr).2 _ hb1, self_mem_nhdsWithin,
    tendsto_primeIdealZetaSum_univ (F := F) |>.eventually_gt_atTop 0] with s hlt hs hF
  have hs' : (1 : ℝ) < s := hs
  have h1 := key s hs'
  rw [div_lt_iff₀ hF] at hlt
  simp only [dirichletRatio]
  rw [div_le_iff₀ hF]
  nlinarith

end Density

end

end NumberFieldKB.Chebotarev
