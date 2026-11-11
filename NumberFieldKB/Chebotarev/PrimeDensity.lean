import NumberFieldKB.Chebotarev.PrimeDensityLog
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real

/-!
# Dirichlet density of sets of primes: basic tools
$F$ is a number field, $\mathfrak p$ runs over the nonzero primes of $\mathcal O_F$, and for a set $S$ of primes
$P_S(s) = \sum_{\mathfrak p\in S}N\mathfrak p^{-s}$ (Mathlib's `primeIdealZetaSum`). Mathlib's
`NumberField.Set.HasDirichletDensity S δ` says $P_S(s)/P(s)\to\delta$ as $s\to1^+$, $P = P_{\text{all}}$.
Mathlib v4.35.0 proves only that densities lie in $[0,1]$ and that $\emptyset$ has density $0$. Here, using
$P(s)\to\infty$ (`tendsto_primeIdealZetaSum_univ`, from the pole of $\zeta_F$):

* **`hasDirichletDensity_of_isBigO`**: if $P_S(s)-\delta P(s) = O(1)$ then $S$ has density $\delta$;
  **`hasDirichletDensity_congr`**: if $P_S-P_T = O(1)$, $S$ and $T$ have the same densities.
* `hasDirichletDensity_univ` (density $1$), **`hasDirichletDensity_of_finite`** (finite sets: $0$),
  **`HasDirichletDensity.union`** (disjoint unions: additive), **`HasDirichletDensity.compl`** ($1-\delta$),
  `HasDirichletDensity.diff` ($T\subseteq S$: $\delta_S-\delta_T$), `HasDirichletDensity.unique`.
* **Degree-one primes** (`degOnePrimes F`: $N\mathfrak p$ is a rational prime, i.e. inertia degree $1$ over $\mathbb Q$).
  The others contribute $O(1)$: $\sum_{\mathfrak p\notin D}N\mathfrak p^{-1}<\infty$ (`summable_inv_normP_not_degOne`;
  at most $[F:\mathbb Q]$ primes lie over each $p$, and $N\mathfrak p\ge p^2$). Hence
  **`hasDirichletDensity_degOnePrimes`** (density $1$) and **`hasDirichletDensity_inter_degOnePrimes_iff`**:
  $S$ has density $\delta$ iff $S\cap D$ does.
-/

open Complex Filter Topology Asymptotics IsDedekindDomain NumberField Set
open QuadFormsKB.NFEuler NumberFieldKB.NonVanishing Function

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

local notation "Pr" => HeightOneSpectrum (𝓞 F)

/-- $P_S(s) = \sum_{\mathfrak p}\mathbf 1_S(\mathfrak p)N\mathfrak p^{-s}$. -/
theorem primeIdealZetaSum_eq_tsum_indicator (S : Set Pr) (s : ℝ) :
    S.primeIdealZetaSum s = ∑' v, S.indicator (fun v : Pr => (normP v : ℝ) ^ (-s)) v := by
  rw [NumberField.Set.primeIdealZetaSum_def]
  exact tsum_subtype S (fun v : Pr => (normP v : ℝ) ^ (-s))

theorem summable_indicator_rpow (S : Set Pr) {s : ℝ} (hs : 1 < s) :
    Summable (S.indicator fun v : Pr => (normP v : ℝ) ^ (-s)) :=
  (summable_normP_rpow hs).indicator S

theorem primeIdealZetaSum_union {S T : Set Pr} (hST : Disjoint S T) {s : ℝ} (hs : 1 < s) :
    (S ∪ T).primeIdealZetaSum s = S.primeIdealZetaSum s + T.primeIdealZetaSum s := by
  simp only [primeIdealZetaSum_eq_tsum_indicator]
  rw [← (summable_indicator_rpow S hs).tsum_add (summable_indicator_rpow T hs)]
  congr 1
  funext v
  rw [indicator_union_of_disjoint hST]

theorem primeIdealZetaSum_mono {S T : Set Pr} (hST : S ⊆ T) {s : ℝ} (hs : 1 < s) :
    S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s := by
  simp only [primeIdealZetaSum_eq_tsum_indicator]
  exact (summable_indicator_rpow S hs).tsum_le_tsum
    (fun v => indicator_le_indicator_of_subset hST (fun _ => by positivity) v) (summable_indicator_rpow T hs)

theorem primeIdealZetaSum_compl (S : Set Pr) {s : ℝ} (hs : 1 < s) :
    Sᶜ.primeIdealZetaSum s = (univ : Set Pr).primeIdealZetaSum s - S.primeIdealZetaSum s := by
  have h := primeIdealZetaSum_union (S := S) (T := Sᶜ) disjoint_compl_right hs
  rw [union_compl_self] at h
  rw [h]
  ring

/-! ### Densities from $O(1)$ estimates -/

theorem eventually_primeIdealZetaSum_univ_pos :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < (univ : Set Pr).primeIdealZetaSum s :=
  tendsto_primeIdealZetaSum_univ.eventually_gt_atTop 0

/-- If $f = O(1)$ then $f(s)/P(s)\to0$. -/
theorem tendsto_div_primeIdealZetaSum_univ {f : ℝ → ℝ} (hf : f =O[𝓝[>] 1] (fun _ => (1 : ℝ))) :
    Tendsto (fun s => f s / (univ : Set Pr).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 0) := by
  have hinv : Tendsto (fun s => ((univ : Set Pr).primeIdealZetaSum s)⁻¹) (𝓝[>] 1) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_primeIdealZetaSum_univ (F := F))
  have h := hf.mul (isBigO_refl (fun s => ((univ : Set Pr).primeIdealZetaSum s)⁻¹) (𝓝[>] 1))
  simp only [one_mul] at h
  simpa [div_eq_mul_inv] using h.trans_tendsto hinv

/-- **Density from an $O(1)$ estimate**: if $P_S(s)-\delta P(s) = O(1)$ as $s\to1^+$, $S$ has density $\delta$. -/
theorem hasDirichletDensity_of_isBigO {S : Set Pr} {δ : ℝ}
    (h : (fun s => S.primeIdealZetaSum s - δ * (univ : Set Pr).primeIdealZetaSum s) =O[𝓝[>] 1]
      (fun _ => (1 : ℝ))) : S.HasDirichletDensity δ := by
  have := (tendsto_div_primeIdealZetaSum_univ (F := F) h).const_add δ
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_primeIdealZetaSum_univ_pos (F := F)] with s hs
  field_simp
  ring

/-- **Sets whose prime sums differ by $O(1)$ have the same densities.** -/
theorem hasDirichletDensity_congr {S T : Set Pr}
    (h : (fun s => S.primeIdealZetaSum s - T.primeIdealZetaSum s) =O[𝓝[>] 1] (fun _ => (1 : ℝ))) {δ : ℝ} :
    S.HasDirichletDensity δ ↔ T.HasDirichletDensity δ := by
  have h0 := tendsto_div_primeIdealZetaSum_univ (F := F) h
  constructor
  · intro hS
    have := hS.sub h0
    rw [sub_zero] at this
    refine this.congr fun s => ?_
    rw [sub_div]; ring
  · intro hT
    have := hT.add h0
    rw [add_zero] at this
    refine this.congr fun s => ?_
    rw [sub_div]; ring

theorem HasDirichletDensity.unique {S : Set Pr} {δ ε : ℝ} (h₁ : S.HasDirichletDensity δ)
    (h₂ : S.HasDirichletDensity ε) : δ = ε :=
  tendsto_nhds_unique h₁ h₂

/-- The set of all primes has density $1$. -/
theorem hasDirichletDensity_univ : (univ : Set Pr).HasDirichletDensity 1 :=
  hasDirichletDensity_of_isBigO ((isBigO_zero _ _).congr' (by
    filter_upwards with s; ring) EventuallyEq.rfl)

/-- **A finite set of primes has density $0$.** -/
theorem hasDirichletDensity_of_finite {S : Set Pr} (hS : S.Finite) : S.HasDirichletDensity 0 := by
  refine hasDirichletDensity_of_isBigO (IsBigO.of_bound S.ncard ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  rw [zero_mul, sub_zero, norm_one, mul_one, Real.norm_of_nonneg (S.primeIdealZetaSum_nonneg s)]
  exact NumberField.Set.primeIdealZetaSum_le_card_of_finite hS (by linarith)

/-- **Density is additive on disjoint unions.** -/
theorem HasDirichletDensity.union {S T : Set Pr} (hST : Disjoint S T) {δ ε : ℝ} (hS : S.HasDirichletDensity δ)
    (hT : T.HasDirichletDensity ε) : (S ∪ T).HasDirichletDensity (δ + ε) := by
  refine (hS.add hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeIdealZetaSum_union hST hs, add_div]

/-- **The complement of a set of density $\delta$ has density $1-\delta$.** -/
theorem HasDirichletDensity.compl {S : Set Pr} {δ : ℝ} (hS : S.HasDirichletDensity δ) :
    Sᶜ.HasDirichletDensity (1 - δ) := by
  refine ((hasDirichletDensity_univ (F := F)).sub hS).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeIdealZetaSum_compl S hs, sub_div]

/-- For $T\subseteq S$: $S\setminus T$ has density $\delta_S-\delta_T$. -/
theorem HasDirichletDensity.diff {S T : Set Pr} (hTS : T ⊆ S) {δ ε : ℝ} (hS : S.HasDirichletDensity δ)
    (hT : T.HasDirichletDensity ε) : (S \ T).HasDirichletDensity (δ - ε) := by
  refine (hS.sub hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have h := primeIdealZetaSum_union (S := T) (T := S \ T) disjoint_sdiff_right hs
  rw [union_sdiff_cancel hTS] at h
  rw [h, ← sub_div]
  ring_nf

/-- Adding or removing finitely many primes does not change the density. -/
theorem hasDirichletDensity_union_finite_iff {S T : Set Pr} (hT : T.Finite) {δ : ℝ} :
    (S ∪ T).HasDirichletDensity δ ↔ S.HasDirichletDensity δ := by
  refine hasDirichletDensity_congr (IsBigO.of_bound (T.ncard) ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  have hU : S ∪ T = S ∪ (T \ S) := (union_sdiff_self).symm
  rw [hU, primeIdealZetaSum_union disjoint_sdiff_right hs, add_sub_cancel_left, norm_one, mul_one,
    Real.norm_of_nonneg ((T \ S).primeIdealZetaSum_nonneg s)]
  calc (T \ S).primeIdealZetaSum s ≤ (T \ S).ncard :=
        NumberField.Set.primeIdealZetaSum_le_card_of_finite (hT.subset sdiff_subset) (by linarith)
    _ ≤ T.ncard := by exact_mod_cast ncard_le_ncard sdiff_subset hT

/-! ### Primes of degree one -/

variable (F) in
/-- **The primes of degree one over $\mathbb Q$**: $N\mathfrak p$ is a rational prime. -/
def degOnePrimes : Set Pr := {v | (normP v).Prime}

/-- The function $N\mathfrak p^{-1}$ on primes of degree $\ge2$, $0$ on primes of degree one. -/
def invNormNotDegOne (v : Pr) : ℝ := (degOnePrimes F)ᶜ.indicator (fun v : Pr => ((normP v : ℝ))⁻¹) v

theorem invNormNotDegOne_nonneg (v : Pr) : 0 ≤ invNormNotDegOne v :=
  indicator_nonneg (fun _ _ => by positivity) v

/-- For $\mathfrak p$ of degree $\ge2$ over $p$: $N\mathfrak p^{-1}\le p^{-2}$. -/
theorem invNormNotDegOne_le (v : Pr) : invNormNotDegOne v ≤ ((primeBelow v : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  unfold invNormNotDegOne
  by_cases hv : v ∈ (degOnePrimes F)ᶜ
  · rw [indicator_of_mem hv]
    have hp := (primeBelow v).2
    set f := v.asIdeal.inertiaDeg ℤ
    have hN : normP v = (primeBelow v : ℕ) ^ f := normP_eq_pow v
    have hf0 : f ≠ 0 := by
      intro h0
      have := two_le_normP v
      rw [hN, h0, pow_zero] at this
      omega
    have hf1 : f ≠ 1 := by
      intro h1
      apply hv
      show (normP v).Prime
      rw [hN, h1, pow_one]
      exact hp
    have hf2 : 2 ≤ f := by omega
    have hp1 : (1 : ℝ) ≤ (primeBelow v : ℕ) := by exact_mod_cast hp.one_lt.le
    rw [hN, Nat.cast_pow, Real.rpow_neg (by positivity), Real.rpow_two]
    refine inv_anti₀ (by positivity) ?_
    exact pow_le_pow_right₀ hp1 hf2
  · rw [indicator_of_notMem hv]
    positivity

/-- **The primes of degree $\ge2$ have a convergent series** $\sum N\mathfrak p^{-1}$. -/
theorem summable_invNormNotDegOne : Summable (invNormNotDegOne (F := F)) := by
  set n := Module.finrank ℚ F
  have hP : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine summable_of_sum_le (c := n * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 : ℝ)))
    (fun v => invNormNotDegOne_nonneg v) fun u => ?_
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := primeBelow) (t := u.image primeBelow)
    (fun v hv => Finset.mem_image_of_mem _ hv)]
  have hfib : ∀ p ∈ u.image primeBelow,
      ∑ v ∈ u with primeBelow v = p, invNormNotDegOne v ≤ n * ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro p _
    calc ∑ v ∈ u with primeBelow v = p, invNormNotDegOne v
        ≤ ∑ v ∈ u with primeBelow v = p, ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have := invNormNotDegOne_le v
          rwa [(Finset.mem_filter.mp hv).2] at this
      _ = (u.filter (primeBelow · = p)).card * ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast card_le_finrank p _ fun v hv => (Finset.mem_filter.mp hv).2
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact hP.sum_le_tsum _ fun p _ => by positivity

/-- **The primes of degree $\ge2$ contribute $O(1)$**: $P_{D^c}(s)\le\sum_{\mathfrak p\notin D}N\mathfrak p^{-1}$
for $s>1$. -/
theorem primeIdealZetaSum_compl_degOnePrimes_le {s : ℝ} (hs : 1 < s) :
    (degOnePrimes F)ᶜ.primeIdealZetaSum s ≤ ∑' v, invNormNotDegOne (F := F) v := by
  rw [primeIdealZetaSum_eq_tsum_indicator]
  refine (summable_indicator_rpow _ hs).tsum_le_tsum (fun v => ?_) summable_invNormNotDegOne
  unfold invNormNotDegOne
  by_cases hv : v ∈ (degOnePrimes F)ᶜ
  · rw [indicator_of_mem hv, indicator_of_mem hv, ← Real.rpow_neg_one]
    have : (1 : ℝ) ≤ normP v := by exact_mod_cast (two_le_normP v).trans' (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le this (by linarith)
  · rw [indicator_of_notMem hv, indicator_of_notMem hv]

theorem isBigO_primeIdealZetaSum_diff_degOnePrimes (S : Set Pr) :
    (fun s => (S \ degOnePrimes F).primeIdealZetaSum s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  refine IsBigO.of_bound (∑' v, invNormNotDegOne (F := F) v) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [norm_one, mul_one, Real.norm_of_nonneg ((S \ degOnePrimes F).primeIdealZetaSum_nonneg s)]
  exact (primeIdealZetaSum_mono (fun v hv => hv.2) hs).trans (primeIdealZetaSum_compl_degOnePrimes_le hs)

/-- **$S$ has density $\delta$ iff its degree-one part $S\cap D$ does.** -/
@[kb "neukirch1999" "Ch. VII, §13 (primes of degree 1 carry the Dirichlet density) [unverified locator]"]
theorem hasDirichletDensity_inter_degOnePrimes_iff {S : Set Pr} {δ : ℝ} :
    (S ∩ degOnePrimes F).HasDirichletDensity δ ↔ S.HasDirichletDensity δ := by
  refine hasDirichletDensity_congr ((isBigO_primeIdealZetaSum_diff_degOnePrimes S).neg_left.congr' ?_
    EventuallyEq.rfl)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have h := primeIdealZetaSum_union (S := S ∩ degOnePrimes F) (T := S \ degOnePrimes F)
    (disjoint_sdiff_inter.symm) hs
  rw [inter_union_sdiff] at h
  rw [h]
  ring

/-- **The primes of degree one have Dirichlet density $1$.** -/
theorem hasDirichletDensity_degOnePrimes : (degOnePrimes F).HasDirichletDensity 1 := by
  have := (hasDirichletDensity_inter_degOnePrimes_iff (S := (univ : Set Pr))).mpr hasDirichletDensity_univ
  rwa [univ_inter] at this


/-! ### Partitions with lower bounds -/

/-- For a finite partition $(S_i)$ of the primes, $\sum_iP_{S_i}(s) = P(s)$ ($s>1$). -/
theorem sum_primeIdealZetaSum_of_partition {ι : Type*} [Fintype ι] {S : ι → Set Pr}
    (hdisj : Pairwise (Disjoint on S)) (hcover : ∀ v, ∃ i, v ∈ S i) {s : ℝ} (hs : 1 < s) :
    ∑ i, (S i).primeIdealZetaSum s = (univ : Set Pr).primeIdealZetaSum s := by
  classical
  simp only [primeIdealZetaSum_eq_tsum_indicator]
  rw [← Summable.tsum_finsetSum fun i _ => summable_indicator_rpow (S i) hs]
  congr 1
  funext v
  obtain ⟨i, hi⟩ := hcover v
  rw [Finset.sum_eq_single i (fun j _ hji => indicator_of_notMem
      (fun hj => (hdisj hji).le_bot ⟨hj, hi⟩) _) (by simp), indicator_of_mem hi, indicator_of_mem (mem_univ v)]

/-- **Densities from lower bounds on a partition.** Let $(S_i)_{i\in\iota}$ be a finite partition of the primes and
$\delta_i$ with $\sum_i\delta_i = 1$. If for every $i$ and $\varepsilon>0$, eventually (as $s\to1^+$)
$P_{S_i}(s)/P(s)\ge\delta_i-\varepsilon$ (lower Dirichlet density $\ge\delta_i$), then each $S_i$ has density
$\delta_i$. (This is the last step of the cyclic case in Chebotarev's argument.) -/
theorem hasDirichletDensity_of_partition {ι : Type*} [Fintype ι] {S : ι → Set Pr}
    (hdisj : Pairwise (Disjoint on S)) (hcover : ∀ v, ∃ i, v ∈ S i) {δ : ι → ℝ} (hsum : ∑ i, δ i = 1)
    (hlow : ∀ i, ∀ ε > 0, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      δ i - ε ≤ (S i).primeIdealZetaSum s / (univ : Set Pr).primeIdealZetaSum s) (i : ι) :
    (S i).HasDirichletDensity (δ i) := by
  classical
  set P := fun s => (univ : Set Pr).primeIdealZetaSum s
  set r := fun j s => (S j).primeIdealZetaSum s / P s
  have hr : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∑ j, r j s = 1 := by
    filter_upwards [self_mem_nhdsWithin, eventually_primeIdealZetaSum_univ_pos (F := F)] with s hs hP
    simp only [r, ← Finset.sum_div, sum_primeIdealZetaSum_of_partition hdisj hcover hs]
    exact div_self hP.ne'
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hlow i ((δ i - a) / 2) (by linarith)] with s hs
    show a < r i s
    linarith
  · set n := Fintype.card ι
    set ε := (b - δ i) / (n + 1)
    have hε : 0 < ε := div_pos (by linarith) (by positivity)
    filter_upwards [hr, (Filter.eventually_all.2 fun j => hlow j ε hε)] with s hs hall
    show r i s < b
    have h1 : r i s = 1 - ∑ j ∈ Finset.univ.erase i, r j s := by
      rw [← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
    have h2 : ∑ j ∈ Finset.univ.erase i, δ j = 1 - δ i := by
      rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
    have h3 : ∑ j ∈ Finset.univ.erase i, (δ j - ε) ≤ ∑ j ∈ Finset.univ.erase i, r j s :=
      Finset.sum_le_sum fun j _ => hall j
    rw [Finset.sum_sub_distrib, Finset.sum_const, h2, nsmul_eq_mul] at h3
    have h4 : ((Finset.univ.erase i).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    have h5 : ((Finset.univ.erase i).card : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right h4 hε.le
    have h6 : (n : ℝ) * ε < b - δ i := by
      have : (n : ℝ) * ε = (b - δ i) * (n / (n + 1)) := by simp only [ε]; field_simp
      rw [this]
      have hn : (n : ℝ) / (n + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
      nlinarith
    linarith

end

end NumberFieldKB.Chebotarev
